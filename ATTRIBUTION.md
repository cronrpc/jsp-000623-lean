# Sources and changes

The mathematical surface theorem is due to **John Gimbel and Carsten Thomassen**.
The cochromatic subgraph theorem used in the lower construction is due to
**Noga Alon, Michael Krivelevich, and Benny Sudakov**. The result being submitted
is a formal verification of established mathematics.

The following Apache-2.0 sources are reused from
[plby/lean-proofs at revision 8822f7ddef30fadbd92e1c6ab4ed897af356af5e](https://github.com/plby/lean-proofs/tree/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest):

| Local file | Upstream path | Changes |
| --- | --- | --- |
| `ErdosProblems/Erdos759.lean` | `src/latest/ErdosProblems/Erdos759.lean` | One equivalence term is made explicit for Mathlib 4.34.0 elaboration. |
| `ErdosProblems/Erdos760.lean` | `src/latest/ErdosProblems/Erdos760.lean` | Unchanged. |
| `Util/Ramsey.lean` | `src/latest/Util/Ramsey.lean` | Unchanged. |

All existing file headers and the upstream Apache-2.0 license are retained.
The Erdős 760 formalization includes the attributed work of Matteo Del Vecchio.

The finite-orbit invariance and unique-return arguments in
`PermutationCycleSurgery.lean` adapt the generic arguments in upstream
`src/latest/ErdosProblems/Erdos73/PermutationCutCycles.lean` at the same revision.

The new development proves transposition and deletion cycle counts, exact graph
component and isolated-vertex changes, the correspondence with actual restricted
rotation systems, and ordinary orientable embeddability for induced subgraphs.
The final maximum and asymptotic theorem explicitly use the ordinary embedding
certificate. The upstream definition had included induced-subgraph heredity in
the embedding predicate; this project supplies the missing implication instead
of taking it as a premise.

This development adopts the standard combinatorial definition of orientable
graph genus. It does not define a separate manifold-embedding predicate. The
definition and the full problem scope are reviewed in `SCOPE-REVIEW.md`.

## Contributor to the new development

GitHub account: cronrpc

The new formalization work was initiated, directed and integrated by cronrpc,
who submits that contribution. It comprises the deletion and restriction
arguments for ordinary rotation-system embeddings, their hereditary consequence,
integration with the reused estimates, and the final complete ordinary-surface
statement and verification package. Automated proof-development assistance was
used under the applicant's direction.

The reused modules and adapted arguments remain credited to the upstream
contributors identified above and in their source headers. The contribution
claim concerns the new development and integration, not sole authorship of those
upstream modules. The original mathematical authors retain their stated credit.

Recipient placeholder: `RECIPIENT-JSP-000623-A`.
The existing [claim](https://github.com/TheJustinSunPrize/awards/issues/641)
and [catalog correction](https://github.com/TheJustinSunPrize/awards/pull/642)
identify this contribution. Recipient confirmation remains pending.
