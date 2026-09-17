import GraphDeletionCounts

/-! Finite subgraphs can be reached by successive deletions of genuine edges. -/

namespace Erdos759.SimpleGraph
open _root_.SimpleGraph
attribute [local instance] Classical.propDecidable Classical.decEq

variable {V : Type*} [Fintype V]

theorem property_of_single_edge_deletion (P : SimpleGraph V → Prop)
    (hdelete : ∀ (G : SimpleGraph V) (d : G.Dart), P G → P (G.deleteEdges {d.edge}))
    {G H : SimpleGraph V} (hHG : H ≤ G) (hG : P G) : P H := by
  have aux : ∀ n : ℕ, ∀ (G : SimpleGraph V), G.edgeFinset.card = n →
      ∀ (H : SimpleGraph V), H ≤ G → P G → P H := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro G hn H hHG hG
      by_cases he : H = G
      · exact he.symm ▸ hG
      have hsub : H.edgeFinset ⊂ G.edgeFinset := edgeFinset_strict_mono (lt_of_le_of_ne hHG he)
      obtain ⟨e, heG, heH⟩ := Finset.exists_of_ssubset hsub
      obtain ⟨u, v⟩ := e
      have hadj : G.Adj u v := by simpa using heG
      let d : G.Dart := ⟨(u, v), hadj⟩
      have hsmall : (G.deleteEdges {d.edge}).edgeFinset.card < n := by
        have hc := edgeCount_delete_dart d
        omega
      have hHdel : H ≤ G.deleteEdges {d.edge} := by
        intro x y hxy
        rw [deleteEdges_adj]
        refine ⟨hHG hxy, ?_⟩
        change s(x, y) ≠ d.edge
        intro hedge
        apply heH
        change d.edge ∈ H.edgeFinset
        rw [← hedge]
        simpa using hxy
      exact ih _ hsmall _ (by congr 1; ext e; simp) H hHdel (hdelete G d hG)
  exact aux _ G rfl H hHG hG

end Erdos759.SimpleGraph
