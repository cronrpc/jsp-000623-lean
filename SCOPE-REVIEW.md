# Scope and dependency review: JSP-000623

Review date: 2026-09-17.

**Status: scope and dependency review complete.** The final theorem covers the
full ordinary rotation-system graph class and both asymptotic bounds. Its exact
statement checks, critical axiom reports, and module kernel replays succeeded.
No unproved hereditary premise, restricted graph family, or conclusion-shaped
assumption remains in the reviewed final interface.

## Target and final statement

[JSP-000623](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0601-0700.md#JSP-000623)
corresponds to [Erdős Problem 759](https://www.erdosproblems.com/759). For a finite
simple graph, the cochromatic number is the minimum number of vertex classes
each inducing a clique or an independent set. The target is the asymptotic order
of the maximum over all finite graphs embeddable on the closed orientable
surface of genus `g`:

```text
z(S_g) = Θ(√g / log g), as g → ∞.
```

This is Theorem 3.4 of John Gimbel and Carsten Thomassen,
[*Coloring graphs with fixed genus and girth*](https://www.ams.org/journals/tran/1997-349-11/S0002-9947-97-01926-0/S0002-9947-97-01926-0.pdf),
Transactions of the American Mathematical Society 349 (1997), 4555–4564.
The paper's other questions about girth, nonorientable surfaces, and polyhedral
graphs are separate results, not additional subparts of this target.

`SurfaceConclusion.lean` defines the value set directly by ordinary embedding
certificates:

```lean
{k | ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
  EmbedsOrientable G g ∧ cochromaticNat G = k}
```

Thus the maximum ranges over every finite vertex count, not over a fixed graph
or a selected family. `ordinaryZSurface_isGreatest` states that its supremum is
an attained maximum. The ultimate statement is:

```lean
(fun g : ℕ => (ordinaryZSurface g : ℝ)) =Θ[atTop]
  (fun g : ℕ => Real.sqrt (g : ℝ) / Real.log (g : ℝ))
```

The adjacent eventual-bounds theorem uses the absolute constants `1/256` and
`236628`. They depend on neither the input graph nor its order nor the genus.
The logarithm in the displayed final statements is the real natural logarithm.

## Combinatorial meaning of orientable embedding

The development adopts the standard rotation-system definition of orientable
graph genus. `RotationSystem G` supplies a duplicate-free list of exactly the
neighbors of each vertex. Its face permutation sends a dart `(v,w)` to
`(w,next(w,v))`. An ordinary certificate consists of a single such rotation
system satisfying

```text
2 * components + edges ≤ vertices + faces + 2 * g.
```

Here `faces` counts the cycles of the dart permutation and one additional face
for each isolated vertex. For a disconnected graph these are the capped
boundary components of its separate ribbon components. Summing their Euler
identities gives twice the sum of their orientable genera. The genus of a
disconnected graph is the sum of the component genera; the inequality therefore
expresses embeddability on a surface of genus at most `g`, or equivalently on the
surface of genus `g` with unused handles allowed.

The classical rotation-system correspondence is described in
[Esperet and Lévêque, Section 3](https://arxiv.org/html/2102.04133).
Component-genus additivity is stated and used in
[White, *On the genus of the composition of two graphs*, p. 276](https://msp.org/pjm/1972/41-1/pjm-v41-n1-p23-p.pdf).
The formal development uses this combinatorial model directly; its vocabulary
does not include a separate manifold-embedding predicate.

The following scope details are accounted for in the definitions and proofs:

| Case | Treatment |
| --- | --- |
| All finite simple graphs | Arbitrary `Fin n`, including `n = 0`; no connectedness assumption. |
| Isolated vertices | Each contributes one component, one vertex, and one face. |
| Empty graph | All four Euler counts are zero; it supplies a value-set witness at every genus. |
| Fixed facial darts | Impossible for a simple graph; the relevant theorem justifies counting the nontrivial face cycles. |
| Fixed points during permutation surgery | Counted explicitly by `totalCycles`; they are compensated by new isolated vertices. |
| Bridges and trees | Treated separately; no unconditional minimum-face-length claim is made. |
| Genus zero | Definitions and deletion theorems apply; a finite bound `7 + 12*g` holds at every genus. |
| Small logarithms | Positivity and large-genus conditions are discharged before division in the asymptotic proof. |
| Natural subtraction | Euler certificates use cross-added inequalities; the other uses have explicit positivity or size guards. |

The original paper initially adopts a connected-graph convention. The official
problem ranges over finite graphs, and the formal statement covers disconnected
graphs directly. It does not rely on the false assertion that a disconnected
graph's cochromatic number is the maximum of its component cochromatic numbers.

## The ordinary-to-hereditary implication

The reused upper-bound development defines `EmbedsOnOrientableSurface` by
requiring ordinary certificates for all finite injective comaps. Its original
implication from this hereditary condition to an ordinary certificate is
immediate. The reverse implication is a real prerequisite for interpreting its
maximum as the maximum in the official problem.

The added proof supplies that reverse implication through concrete operations:

1. `RotationRestriction` filters the actual neighbor lists after deleting an
   existing edge. `FaceDeletion` identifies the resulting face permutation with
   a transposition followed by first-return deletion of the two edge darts.
2. `PermutationCycleSurgery` counts all permutation cycles, including fixed
   points. A transposition merges different cycles or splits a single cycle.
   `DeletionCycles` proves that removing a nonfixed point preserves cycle count
   and removing a fixed point decreases it by one.
3. `EdgeIsolateCounts` identifies those removed fixed points exactly with newly
   isolated endpoints. `GraphDeletionCounts` proves that deleting a bridge adds
   one component, while deleting a nonbridge preserves component count.
4. `EmbeddingDeletion` combines these identities. A bridge also adds one face;
   for a nonbridge, the face count decreases by at most one. With one fewer edge,
   the Euler certificate retains the original genus bound.
5. `SubgraphInduction` iterates actual edge deletion by induction on edge count.
   To induce on a vertex set, first remove all edges incident to omitted
   vertices. `IsolatedRestriction` then removes those genuinely isolated
   vertices, preserving the Euler deficit.
6. `RotationTransport` relabels the resulting rotation system along a vertex
   equivalence. `EmbeddingHereditary` obtains `EmbedsOrientable.comap` for every
   finite injective map, then `embedsOrientable_iff_hereditary`.

`EmbeddingInstances` and `EmbedsOrientable.changeDecidable` remove differences
between finite enumerations and decision procedures by their subsingleton
equalities. These are implementation-instance congruences, not additional
mathematical assumptions on the graph.

None of these final interfaces assumes connectedness, positive genus, a minimum
degree, or a hereditary certificate as input. The sole embedding premise of
`EmbedsOrientable.comap` is the ordinary certificate for the original graph.
`SurfaceConclusion` proves equality of the ordinary and hereditary value sets
and transports the established maximum and both estimates through that equality.

## Upper and lower estimates in the reused closure

The complete non-Mathlib upstream closure consists of `Util.Ramsey`,
`ErdosProblems.Erdos760`, and `ErdosProblems.Erdos759`.

For the upper bound, the source constructs a core of high minimum degree whose
complement has a bounded coloring. Heredity supplies an embedding certificate
for that core. The handshake identity and the surface Euler estimate then bound
its edge count by a constant times genus. A sparse Ramsey argument, followed by
successive homogeneous-set removal on geometric scales, bounds its cochromatic
number in terms of that edge count. Numeric and homogeneous-set hypotheses in
intermediate lemmas are proved before they are used in the final bound; they
are not extra assumptions of the surface theorem.

For the lower bound, the reused Erdős 760 development proves the cochromatic
subgraph theorem of Noga Alon, Michael Krivelevich, and Benny Sudakov,
[*Subgraphs with a Large Cochromatic Number*](https://people.math.ethz.ch/~sudakovb/cochrom.pdf).
Its finite counting proof chooses an actual edge subset. It bounds bad clique
and independent-set configurations and shows that their union cannot exhaust
all subsets. The resulting spanning subgraph, together with a degeneracy
coloring argument and the large-clique case, yields the explicit finite bound.
The surface proof applies it to a complete graph, relabels the actual subgraph,
and constructs a genus certificate with a quadratic vertex-count bound.
Choosing the graph order on the square-root scale supplies the required surface
lower estimate.

The cochromatic number is not assumed finite: finite colorability is proved,
and the natural-number minimum is identified with the upstream extended-natural
definition. Likewise, nonemptiness, boundedness, and attainment of the surface
maximum are proved. The estimates concern that attained maximum, so neither an
infinite cochromatic value nor the default supremum of an unbounded natural set
can make the final assertions vacuous.

The final natural-to-real conversion supplies both sides with uniform positive
constants. Its large-parameter assumptions hold eventually on the natural
genus parameter. No input-size bound survives in the final statement.

## Source versions and attribution

The reused files are pinned to
[revision `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`](https://github.com/plby/lean-proofs/tree/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest).
`Erdos760.lean` and `Util/Ramsey.lean` are byte-identical to those sources.
`Erdos759.lean` has one proof-term compatibility change: a definitionally
reflexive set-congruence equivalence is replaced by `Equiv.refl _`. Its
definitions and mathematical statements are unchanged.

| File | Reviewed SHA-256 |
| --- | --- |
| `Util/Ramsey.lean` | `c1269d71fcd105835310b53e87a588fcb5628f87a76c9f16d7a007697f77b82a` |
| `ErdosProblems/Erdos760.lean` | `63421f9e4e7c85c3c573610e664c93be6abb223aab747d0dea9224b96d4e854c` |
| `ErdosProblems/Erdos759.lean` | `0939cdd554cdf5c92ff2158f9fc3fe198efb9a7d34210cb894a1b20561be3f7c` |

Original mathematical credit belongs to the authors cited above. Reused
formalization headers, authorship, and Apache-2.0 licensing are retained;
`ATTRIBUTION.md` records the changes and the finite-orbit arguments adapted from
the same upstream revision. This project adds the ordinary-embedding deletion
and heredity bridge and its integration with the surface maximum.

## Verification evidence

The environment is Lean 4.34.0 and Mathlib revision
`5ed2965256430c3649e86755f9576b54eca72435`.

The reused closure was checked at its actual local source versions:

- `research/upstream-review-20260917T085607Z/result.json` records 23 of 23
  critical axiom reports, all using only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Fresh `lake env leanchecker` runs for each of the three reused modules exited
  zero, completing at 08:56:34 UTC. Windows and WSL source hashes agreed and
  remained unchanged during these checks.
- `research/REVIEW-SURGERY.md` records the source-level review of the generic
  cycle-count, graph-component, and isolated-vertex proofs. Its evidence includes
  47 intermediate theorem reports and four successful module kernel replays.
  Author checks of `DeletionCycles` and `EdgeIsolateCounts` are identified as
  such in that record.

The final bridge and ordinary-surface statement were then checked against the
complete 16-module local closure. The source files matched between Windows and
WSL and remained unchanged during this run. The scan found no `sorry`, `admit`,
custom `axiom`, `native_decide`, `trustCompiler`, `implemented_by`, or `unsafe`
tokens in those source files.

`research/final-scope-20260917T090956Z/result.json` records the complete source
hash map and the following successful commands:

| Check | Actual result |
| --- | --- |
| `lake env lean research/final-scope-20260917T090956Z/Audit.lean` | Exit 0 at 09:10:00 UTC; all six exact statement assertions and 29 of 29 axiom reports passed. |
| `lake env leanchecker FaceDeletion` | Exit 0 at 09:10:08 UTC. |
| `lake env leanchecker EmbeddingDeletion` | Exit 0 at 09:10:14 UTC. |
| `lake env leanchecker EmbeddingInstances` | Exit 0 at 09:10:21 UTC. |
| `lake env leanchecker EmbeddingHereditary` | Exit 0 at 09:10:28 UTC. |
| `lake env leanchecker SurfaceConclusion` | Exit 0 at 09:10:35 UTC. |

The exact assertions cover arbitrary finite injective comaps, the ordinary and
hereditary equivalence, the definition of the ordinary value set, its attained
maximum, the explicit eventual two-sided bounds, and the complete `Θ` theorem.
All reported axioms belong to the standard set `propext`, `Classical.choice`,
and `Quot.sound`.

The final bridge source has SHA-256
`15fa311b9684bd516788fdc348afa21bcd7a7f82d46f04b950a0b6bb26eba605`.
The final `SurfaceConclusion.lean` has SHA-256
`3fc2dcf3d969a4688ff8f2d2be5fbcb8cadd335bc9cd37964a9792dc67dcf094`.
Its matching module build completed at 09:09:14 UTC with exit zero and no
warnings. `research/REVIEW-DELETION.md` contains the separate review of the two
deletion modules authored by this scope reviewer.

This is a project scope and dependency review. The release verifier checks a
clean source revision separately; those release results belong to its own
`verification/full/` record.
