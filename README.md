# JSP-000623: Cochromatic number on orientable surfaces

This project formalizes the theorem of **John Gimbel and Carsten Thomassen** that
the largest cochromatic number of a finite simple graph embeddable on the closed
orientable surface of genus `g` has order

```text
z(S_g) = Θ(√g / log g)  as g → ∞.
```

The cochromatic number is the minimum number of vertex classes, each of which is
a clique or an independent set. The maximum ranges over every finite graph
order. Graphs may be disconnected and may have isolated vertices.

## Mathematical statement

The project uses the standard combinatorial rotation-system model of orientable
graph embeddings. A certificate consists of a cyclic ordering of the neighbors
at each vertex, satisfying

```text
2 * components + edges ≤ vertices + face cycles + isolated vertices + 2 * g.
```

The face cycles are the cycles of the dart permutation. An isolated vertex
contributes one capped boundary component. For a disconnected graph these are
the boundary components of its separate ribbon components, rather than the
complementary regions of one connected ambient surface.

The hereditary property needed in the upper-bound proof is derived from this
ordinary certificate: deleting edges, deleting isolated vertices, and relabeling
vertices preserve the genus bound. It is not an additional hypothesis imposed
on the class of graphs in the final maximum.

The eventual real bounds use the uniform constants `1/256` and `236628` and the
natural logarithm. The asymptotic statement concerns sufficiently large genus;
the underlying definitions and deletion theorems also cover genus zero and
empty graphs.

The main declarations in namespace `Erdos759.SimpleGraph` are:

| Declaration | Statement |
| --- | --- |
| `EmbedsOrientable.comap` | Ordinary embeddability is preserved by every injective vertex map. |
| `embedsOrientable_iff_hereditary` | The ordinary and hereditary graph classes coincide. |
| `ordinaryZSurface_isGreatest` | The extremal cochromatic number is a genuine attained maximum. |
| `ordinary_surface_cochromatic_eventual_bounds` | Eventual bounds with explicit positive constants. |
| `ordinary_surface_cochromatic_theta` | The full `Θ(√g / log g)` theorem. |

## Reproduction

Lean is pinned to **4.34.0**, with Mathlib at
`5ed2965256430c3649e86755f9576b54eca72435`. All transitive Git dependency revisions
are fixed by `lake-manifest.json`.

```sh
lake exe cache get
lake build
python3 verify.py --verify
```

The verifier requires a committed, clean checkout. It clones the exact source
revision to a temporary directory, builds every discovered proof module,
checks the precise final theorem types and axioms, and replays each module with
`leanchecker`. Commands, exit codes, source hashes, and dependency revisions are
written under `verification/full/`. `python3 verify.py --inspect` lists the
modules without claiming a verification result.

## Sources and attribution

- Official catalog: [JSP-000623](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0601-0700.md#JSP-000623).
- Original problem: [Erdős Problem 759](https://www.erdosproblems.com/759).
- J. Gimbel and C. Thomassen, *Coloring graphs with fixed genus and girth*,
  Transactions of the American Mathematical Society **349** (1997), 4555–4564,
  [Theorem 3.4](https://www.ams.org/journals/tran/1997-349-11/S0002-9947-97-01926-0/S0002-9947-97-01926-0.pdf).

The existing cochromatic estimates are reused with their original license and
source attributions. The added rotation-system deletion proof connects those
estimates to the ordinary embedding class. See [ATTRIBUTION.md](ATTRIBUTION.md)
for the fixed upstream sources and changes.
