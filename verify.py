"""Rebuild and kernel-check the fixed JSP-000623 proof in a fresh checkout."""
from pathlib import Path
from datetime import datetime, timezone
import argparse
import hashlib
import json
import os
import re
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parent
CONFIG_REL = Path('verification-config.json')
CONFIG = json.loads((ROOT / CONFIG_REL).read_text(encoding='utf-8-sig'))


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def lean_code(source):
    """Erase nested comments and strings, keeping token boundaries and line ends."""
    out, i, depth, quoted = [], 0, 0, False
    while i < len(source):
        pair = source[i:i+2]
        if depth:
            if pair == '/-':
                depth += 1
                i += 2
            elif pair == '-/':
                depth -= 1
                i += 2
            else:
                out.append('\n' if source[i] == '\n' else ' ')
                i += 1
        elif quoted:
            if source[i] == '\\':
                out.extend('  ')
                i += 2
            elif source[i] == '"':
                quoted = False
                out.append(' ')
                i += 1
            else:
                out.append('\n' if source[i] == '\n' else ' ')
                i += 1
        elif pair == '/-':
            depth = 1
            out.extend('  ')
            i += 2
        elif pair == '--':
            end = source.find('\n', i)
            end = len(source) if end == -1 else end
            out.extend(' ' * (end - i))
            i = end
        elif source[i] == '"':
            quoted = True
            out.append(' ')
            i += 1
        else:
            out.append(source[i])
            i += 1
    return ''.join(out)


def discover(root):
    excluded_dirs = set(CONFIG['excluded_directories'])
    excluded_files = set(CONFIG['excluded_lean_files'])
    modules = {}
    for directory, subdirs, filenames in os.walk(root):
        subdirs[:] = sorted(d for d in subdirs if d not in excluded_dirs)
        for name in sorted(filenames):
            if name.endswith('.lean'):
                rel = (Path(directory) / name).relative_to(root)
                if rel.as_posix() not in excluded_files:
                    module = '.'.join(rel.with_suffix('').parts)
                    if not re.fullmatch(r'[A-Za-z_][A-Za-z0-9_\'.]*', module):
                        raise ValueError(f'Unsupported module identifier: {module}')
                    modules[module] = rel
    if not modules:
        raise ValueError('No formal modules discovered')
    return dict(sorted(modules.items()))


def main():
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--inspect', action='store_true')
    mode.add_argument('--verify', action='store_true')
    args = parser.parse_args()
    modules = discover(ROOT)
    if args.inspect:
        print(json.dumps({'mode': 'inspection_only_not_verification',
            'scope_review_complete': CONFIG['scope_review_complete'],
            'module_count': len(modules),
            'sources': {m: {'path': p.as_posix(), 'sha256': sha(ROOT / p)}
                        for m, p in modules.items()}}, indent=2))
        return

    # These requirements prevent a staged lemma or conditional wrapper from
    # being reported as a verified complete prize submission.
    if not CONFIG['scope_review_complete']:
        raise ValueError('The full mathematical scope review is not complete')
    if not CONFIG['final_theorems'] or not CONFIG['statement_assertions']:
        raise ValueError('Reviewed final theorem names and exact type checks are required')
    if not CONFIG['scope_review_file'] or not (ROOT / CONFIG['scope_review_file']).is_file():
        raise ValueError('Missing independent scope-review document')
    allowed_axioms = {'propext', 'Classical.choice', 'Quot.sound'}
    if set(CONFIG['allowed_axioms']) != allowed_axioms:
        raise ValueError('Only the standard three proof axioms are permitted')

    stamp = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ')
    out = ROOT / 'verification/full' / stamp
    out.mkdir(parents=True, exist_ok=False)
    result = {'project': CONFIG['project'], 'started_utc': stamp,
              'verdict': 'RUNNING', 'commands': [], 'module_count': len(modules)}

    def save():
        (out / 'result.json').write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')

    def run(command, cwd, label, timeout=3600):
        start = time.monotonic()
        log = out / (label + '.log')
        with log.open('w', encoding='utf-8') as handle:
            try:
                code = subprocess.run(command, cwd=cwd, stdout=handle,
                    stderr=subprocess.STDOUT, timeout=timeout).returncode
            except subprocess.TimeoutExpired:
                code = 'timeout'
        result['commands'].append({'command': command, 'cwd': str(cwd),
            'exit_code': code, 'seconds': round(time.monotonic() - start, 3),
            'log': log.name})
        save()
        if code != 0:
            raise RuntimeError(f'{label} failed with exit code {code}; see {log}')
        return log.read_text(encoding='utf-8', errors='replace').strip()

    try:
        result['source_commit'] = run(['git', 'rev-parse', 'HEAD'], ROOT, 'source-commit')
        dirty = run(['git', 'status', '--porcelain', '--untracked-files=all'], ROOT, 'source-status')
        # The output directory must be covered by the repository's normal ignore
        # rules; no ignore configuration is added by this verifier.
        if dirty:
            raise ValueError('Source checkout must be clean, including untracked files')
        git_root = Path(run(['git', 'rev-parse', '--show-toplevel'], ROOT, 'git-root'))
        project_relative = ROOT.relative_to(git_root)
        with tempfile.TemporaryDirectory(prefix='jsp623-verification-') as temp:
            checkout = Path(temp) / 'source'
            run(['git', 'clone', '--quiet', '--no-hardlinks', '--no-checkout', '--', str(git_root), str(checkout)],
                ROOT, 'fresh-clone')
            run(['git', 'checkout', '--quiet', '--detach', result['source_commit']], checkout, 'fixed-checkout')
            work = checkout / project_relative
            if discover(work) != modules:
                raise ValueError('Discovered sources differ from the committed source set')
            tracked = set(modules.values()) | {Path('lean-toolchain'), Path('lake-manifest.json'),
                Path('lakefile.toml'), CONFIG_REL, Path('verify.py'),
                Path(CONFIG['scope_review_file'])}
            initial_hashes = {p.as_posix(): sha(work / p) for p in sorted(tracked)}
            result['source_sha256'] = initial_hashes
            if (work / 'lean-toolchain').read_text().strip() != CONFIG['lean_toolchain']:
                raise ValueError('Wrong Lean toolchain')
            lock = json.loads((work / 'lake-manifest.json').read_text())
            for package in lock['packages']:
                if package.get('type') != 'git' or not re.fullmatch('[0-9a-f]{40}', package.get('rev', '')):
                    raise ValueError(f'Nonportable or unlocked dependency: {package.get("name")}')
            mathlib = next(p for p in lock['packages'] if p['name'] == 'mathlib')
            if mathlib['rev'] != CONFIG['mathlib_commit']:
                raise ValueError('Wrong Mathlib revision in lock file')
            result['source_scan'] = []
            for module, rel in modules.items():
                code = lean_code((work / rel).read_text(encoding='utf-8-sig'))
                bad = re.search(r'\b(sorry|admit|axiom|native_decide)\b', code)
                if bad:
                    raise ValueError(f'Forbidden proof command {bad.group()} in {rel}')
                result['source_scan'].append(rel.as_posix())
            lean_version = run(['lake', 'env', 'lean', '--version'], work, 'lean-version')
            expected_version = CONFIG['lean_toolchain'].rsplit(':v', 1)[1]
            if not re.search(r'\bversion ' + re.escape(expected_version) + r'\b', lean_version):
                raise ValueError('The actual Lean executable has an unexpected version')
            result['actual_lean_version'] = lean_version
            run(['lake', 'exe', 'cache', 'get'], work, 'dependency-cache')
            result['actual_dependency_revisions'] = {}
            for package in lock['packages']:
                package_dir = work / lock['packagesDir'] / package['name']
                revision = run(['git', 'rev-parse', 'HEAD'], package_dir, 'dependency-' + package['name'])
                if revision != package['rev']:
                    raise ValueError(f'Dependency revision mismatch: {package["name"]}')
                result['actual_dependency_revisions'][package['name']] = revision
            for rel in modules.values():
                if (work / '.lake/build/lib/lean' / rel.with_suffix('.olean')).exists():
                    raise ValueError(f'Local proof artifact existed before clean build: {rel}')
            run(['lake', 'build', *modules], work, 'clean-build-all-modules')
            audit_dir = work / 'verification'
            audit_dir.mkdir(exist_ok=True)
            audit_file = audit_dir / 'FullAudit.lean'
            audit_file.write_text(''.join(f'import {m}\n' for m in modules)
                + '\n'.join(CONFIG['statement_assertions']) + '\n'
                + ''.join(f'#print axioms {t}\n#print {t}\n' for t in CONFIG['final_theorems']),
                encoding='utf-8')
            audit_log = run(['lake', 'env', 'lean', '-j1', str(audit_file)], work, 'final-axioms-and-types')
            audits = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", audit_log)
            audits.extend((name, '') for name in
                re.findall(r"'([^']+)' does not depend on any axioms", audit_log))
            if set(CONFIG['final_theorems']) != {name for name, _ in audits}:
                raise ValueError('Not every final theorem produced an axiom audit')
            result['final_axioms'] = {}
            for name, values in audits:
                actual = {v.strip() for v in values.split(',') if v.strip()}
                if not actual <= allowed_axioms:
                    raise ValueError(f'Unapproved axioms for {name}: {actual}')
                result['final_axioms'][name] = sorted(actual)
            for module in modules:
                run(['lake', 'env', 'leanchecker', module], work,
                    'kernel-' + module.replace('.', '_'), timeout=900)
            if initial_hashes != {p.as_posix(): sha(work / p) for p in sorted(tracked)}:
                raise ValueError('Source or lock files changed during verification')
            result['all_source_hashes_unchanged'] = True
            result['all_discovered_modules_kernel_replayed'] = True
            result['verdict'] = 'PASS'
    except Exception as error:
        result['verdict'] = 'FAIL'
        result['error'] = str(error)
        raise
    finally:
        result['finished_utc'] = datetime.now(timezone.utc).isoformat()
        save()


if __name__ == '__main__':
    main()
