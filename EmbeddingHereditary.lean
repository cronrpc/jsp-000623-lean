import EmbeddingDeletion
import SubgraphInduction
import IsolatedRestriction
import EmbeddingInstances

noncomputable section
open _root_.SimpleGraph
namespace Erdos759.SimpleGraph
attribute [local instance] Classical.propDecidable Classical.decEq
set_option maxHeartbeats 400000

variable {V : Type*} [Fintype V] {G H : SimpleGraph V} {g : ℕ}

/-- The combinatorial certificate is independent of decision procedures. -/
theorem EmbedsOrientable.changeDecidable (i j : DecidableEq V)
    (p q : DecidableRel G.Adj) (h : @EmbedsOrientable V _ i G p g) :
    @EmbedsOrientable V _ j G q g := by
  cases Subsingleton.elim i j
  cases Subsingleton.elim p q
  exact h

/-- A genuine rotation-system genus bound holds for every spanning subgraph. -/
theorem EmbedsOrientable.mono (hG : EmbedsOrientable G g) (hHG : H ≤ G) :
    EmbedsOrientable H g := by
  refine property_of_single_edge_deletion (fun K ↦ EmbedsOrientable K g) ?_ hHG hG
  intro K d h
  exact EmbedsOrientable.changeDecidable _ _ _ _ (h.delete_dart d)

/-- Vertex deletion preserves ordinary orientable embeddability. -/
theorem EmbedsOrientable.induce (hG : EmbedsOrientable G g) (s : Set V) :
    EmbedsOrientable (G.induce s) g := by
  let K : SimpleGraph V :=
    { Adj := fun v w ↦ G.Adj v w ∧ v ∈ s ∧ w ∈ s
      symm := ⟨by intro v w h; exact ⟨h.1.symm, h.2.2, h.2.1⟩⟩
      loopless := ⟨by intro v h; exact G.irrefl h.1⟩ }
  have hKG : K ≤ G := fun _ _ h ↦ h.1
  have hs : K.support ⊆ s := by
    rintro v ⟨w, hw⟩
    exact hw.2.1
  have hi := (hG.mono hKG).induce_of_support_subset hs
  have he : K.induce s = G.induce s := by
    ext v w
    simp only [induce_adj, K, and_iff_left w.property, and_iff_left v.property]
  exact (embedsOrientable_congr (K.induce s) (G.induce s) he g _ _ _ _ _ _).mp hi

/-- Relabel an induced subgraph along any injective map. -/
theorem EmbedsOrientable.comap {W : Type*} [Fintype W]
    (hG : EmbedsOrientable G g) (f : W ↪ V) :
    EmbedsOrientable (G.comap f) g := by
  let e : W ≃ Set.range f := Equiv.ofInjective f f.injective
  let i : G.comap f ≃g G.induce (Set.range f) :=
    { e with map_rel_iff' := by intro v w; rfl }
  have hi := hG.induce (Set.range f)
  apply (embedsOrientable_instances (G.comap f) g _ _ _ _ _ _).mp
  apply Iso.embedsOrientable (G := G.induce (Set.range f)) (H := G.comap f) i.symm g
  exact (embedsOrientable_instances (G.induce (Set.range f)) g _ _ _ _ _ _).mp hi

/-- Heredity is a theorem about ordinary rotation systems, with no extra input certificate. -/
theorem EmbedsOrientable.hereditary (hG : EmbedsOrientable G g) :
    EmbedsOnOrientableSurface G g := by
  intro W _ _ f _
  exact EmbedsOrientable.changeDecidable _ _ _ _ (hG.comap f)

theorem embedsOrientable_iff_hereditary :
    EmbedsOrientable G g ↔ EmbedsOnOrientableSurface G g :=
  ⟨EmbedsOrientable.hereditary, EmbedsOnOrientableSurface.embedsOrientable⟩

end Erdos759.SimpleGraph
