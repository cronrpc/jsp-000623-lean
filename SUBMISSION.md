# JSP-000623 submission and evidence

The theorem is due to John Gimbel and Carsten Thomassen, *Coloring graphs with
fixed genus and girth* (1997), Theorem 3.4. This submission formalizes its full
cochromatic growth statement for ordinary orientable graph embeddings.

## Final statements

`Erdos759.SimpleGraph.ordinary_surface_cochromatic_theta` proves
`ordinaryZSurface(g) = Θ(√g / log g)` as `g → ∞`.
`ordinary_surface_cochromatic_eventual_bounds` supplies uniform constants
`1/256` and `236628`. `ordinaryZSurface_isGreatest` establishes that the
extremum is attained over all finite graph orders.

`EmbedsOrientable.comap` derives induced-subgraph heredity from an ordinary
rotation-system certificate. Its proof uses actual edge deletion, exact face
and component counts, removal of isolated vertices, and graph relabeling.
The final graph class assumes no separate hereditary certificate.

See [README.md](README.md), [SCOPE-REVIEW.md](SCOPE-REVIEW.md), and
[ATTRIBUTION.md](ATTRIBUTION.md) for definitions, boundary cases, original authors,
and the fixed upstream modules reused with their licenses.

## Fixed source and reproduction

- Proof source: [`47c5192a01dc558fee751d18869f912586be33dd`](https://github.com/cronrpc/jsp-000623-lean/tree/47c5192a01dc558fee751d18869f912586be33dd).
- Lean: `leanprover/lean4:v4.34.0`.
- Mathlib: `5ed2965256430c3649e86755f9576b54eca72435`.
- Source and raw verification logs: [release v1.0.0](https://github.com/cronrpc/jsp-000623-lean/releases/tag/v1.0.0).
- Source archive: `jsp-000623-source.tar.gz`, 76890 bytes,
  SHA-256 `c6b0db0f8e23904cd9f415bb96c4509b78685f9bcfe1b040ef130697fd5ea544`.
- [Machine-readable verification summary](verification-summary.json).

```sh
lake exe cache get
lake build
python3 verify.py --verify
```

The clean fixed-source reconstruction passed all 17 proof
modules, the exact final type assertions, the six final-declaration axiom audits,
and every module's Lean kernel replay. The final dependencies use only
`propext`, `Classical.choice`, and `Quot.sound`. The verifier also checks the
entire project's sources and fixed dependencies and records real commands and
exit codes. CI repeats the reconstruction from the submitted commit.

## Recipient placeholder or confirmed public ID

`RECIPIENT-JSP-000623-A`, pending confirmation.

GitHub account: cronrpc
