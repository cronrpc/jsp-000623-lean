import RotationRestriction
import PermutationCycleSurgery

/-! Exact isolated-vertex changes when deleting a genuine unoriented edge. -/

noncomputable section
open _root_.SimpleGraph
namespace Erdos759.SimpleGraph

attribute [local instance] Classical.propDecidable Classical.decEq

variable {V : Type*} {G : SimpleGraph V}

theorem RotationSystem.next_eq_self_iff_unique_neighbor (R : RotationSystem G)
    {v w : V} (hvw : G.Adj v w) :
    R.next v w = w ↔ ∀ z, G.Adj v z → z = w := by
  have hw : w ∈ R.order v := (R.mem_order_iff v w).mpr hvw
  rw [RotationSystem.next,
    List.formPerm_apply_mem_eq_self_iff _ (R.nodup_order v) w hw]
  have hc : (R.order v).toFinset.card = (R.order v).length :=
    List.toFinset_card_of_nodup (R.nodup_order v)
  constructor
  · intro hlen z hz
    have hcard : (R.order v).toFinset.card ≤ 1 := by omega
    exact Finset.card_le_one.mp hcard z
      (by simpa using (R.mem_order_iff v z).mpr hz) w (by simpa using hw)
  · intro h
    have hs : (R.order v).toFinset ⊆ {w} := by
      intro z hz
      exact Finset.mem_singleton.mpr (h z ((R.mem_order_iff v z).mp (List.mem_toFinset.mp hz)))
    have hcard := Finset.card_le_card hs
    simpa only [Finset.card_singleton, hc] using hcard

theorem deleteEdges_adj_fst_iff (d : G.Dart) (w : V) :
    (G.deleteEdges {d.edge}).Adj d.fst w ↔ G.Adj d.fst w ∧ w ≠ d.snd := by
  simp [deleteEdges_adj, Dart.edge, Prod.ext_iff, Prod.swap, d.fst_ne_snd]

theorem isolated_deleteEdge_fst_iff (d : G.Dart) :
    (∀ w, ¬ (G.deleteEdges {d.edge}).Adj d.fst w) ↔
      ∀ w, G.Adj d.fst w → w = d.snd := by
  simp only [deleteEdges_adj_fst_iff, not_and, not_not]

theorem isolated_deleteEdge_other_iff (d : G.Dart) {v : V}
    (hv : v ≠ d.fst) (hv' : v ≠ d.snd) :
    (∀ w, ¬ (G.deleteEdges {d.edge}).Adj v w) ↔ ∀ w, ¬ G.Adj v w := by
  simp [deleteEdges_adj, Dart.edge, Prod.ext_iff, Prod.swap, hv, hv']

/-- A singleton after cutting the two darts is exactly a newly isolated first endpoint. -/
theorem RotationSystem.cut_fixed_fst_iff (R : RotationSystem G) (d : G.Dart) :
    (R.facePerm * Equiv.swap d d.symm) d = d ↔
      ∀ w, ¬ (G.deleteEdges {d.edge}).Adj d.fst w := by
  rw [isolated_deleteEdge_fst_iff, ← R.next_eq_self_iff_unique_neighbor d.adj]
  simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Dart.ext_iff, Prod.ext_iff,
    RotationSystem.facePerm_fst, RotationSystem.facePerm_snd]
  simp

/-- The analogous correspondence at the other endpoint. -/
theorem RotationSystem.cut_fixed_snd_iff (R : RotationSystem G) (d : G.Dart) :
    (R.facePerm * Equiv.swap d d.symm) d.symm = d.symm ↔
      ∀ w, ¬ (G.deleteEdges {d.edge}).Adj d.snd w := by
  simpa [Equiv.swap_comm d.symm d] using
    R.cut_fixed_fst_iff d.symm

theorem RotationSystem.isolated_deleteEdge_iff (R : RotationSystem G) (d : G.Dart) (v : V) :
    (∀ w, ¬ (G.deleteEdges {d.edge}).Adj v w) ↔
      (∀ w, ¬ G.Adj v w) ∨
        (v = d.fst ∧ (R.facePerm * Equiv.swap d d.symm) d = d) ∨
        (v = d.snd ∧ (R.facePerm * Equiv.swap d d.symm) d.symm = d.symm) := by
  have hnfirst : ¬ (∀ w, ¬ G.Adj d.fst w) := fun h => h _ d.adj
  have hnsecond : ¬ (∀ w, ¬ G.Adj d.snd w) := fun h => h _ d.adj.symm
  by_cases hv : v = d.fst
  · subst v
    simp only [hnfirst, false_or, true_and, d.fst_ne_snd, false_and, or_false]
    exact (R.cut_fixed_fst_iff d).symm
  by_cases hv' : v = d.snd
  · subst v
    simp only [hnsecond, false_or, d.snd_ne_fst, false_and, true_and]
    exact (R.cut_fixed_snd_iff d).symm
  · simpa only [hv, hv', false_and, or_false] using isolated_deleteEdge_other_iff d hv hv'

variable [Fintype V]

/-- The singleton cycles removed by dart deletion are exactly the new isolated vertices. -/
theorem RotationSystem.isolateCount_deleteEdge (R : RotationSystem G) (d : G.Dart) :
    isolateCount (G.deleteEdges {d.edge}) = isolateCount G +
      (if (R.facePerm * Equiv.swap d d.symm) d = d then 1 else 0) +
      (if (R.facePerm * Equiv.swap d d.symm) d.symm = d.symm then 1 else 0) := by
  let old : Finset V := Finset.univ.filter (fun v => ∀ w, ¬ G.Adj v w)
  have ha : d.fst ∉ old := by
    simp only [old, Finset.mem_filter, Finset.mem_univ, true_and]
    exact fun h => h _ d.adj
  have hb : d.snd ∉ old := by
    simp only [old, Finset.mem_filter, Finset.mem_univ, true_and]
    exact fun h => h _ d.adj.symm
  have hset : Finset.univ.filter (fun v => ∀ w, ¬ (G.deleteEdges {d.edge}).Adj v w) =
      (old ∪ (({d.fst} : Finset V).filter (fun _ => (R.facePerm * Equiv.swap d d.symm) d = d))) ∪
        (({d.snd} : Finset V).filter (fun _ => (R.facePerm * Equiv.swap d d.symm) d.symm = d.symm)) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_singleton, old, R.isolated_deleteEdge_iff d v]
    tauto
  unfold isolateCount
  rw [hset]
  change _ = old.card + _ + _
  by_cases hfirst : (R.facePerm * Equiv.swap d d.symm) d = d <;>
    by_cases hsecond : (R.facePerm * Equiv.swap d d.symm) d.symm = d.symm <;>
    simp only [hfirst, hsecond, ↓reduceIte, Finset.filter_true, Finset.filter_false] <;>
    simp [ha, hb, d.snd_ne_fst,
      Finset.union_singleton, Finset.card_insert_of_notMem, Nat.add_comm]

end Erdos759.SimpleGraph
