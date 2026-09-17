import RotationRestriction
import DeletionCycles

noncomputable section

namespace Erdos759.SimpleGraph

open _root_.SimpleGraph
open JSP623.PermutationSurgery
open scoped Classical
attribute [local instance] Classical.propDecidable Classical.decEq

variable {V : Type*} {G : SimpleGraph V}

/-- Identify the darts remaining after an edge deletion. -/
def dartDeleteEquiv (d : G.Dart) : (G.deleteEdges {d.edge}).Dart ≃
    {x : G.Dart // x ≠ d ∧ x ≠ d.symm} where
  toFun x := ⟨⟨x.toProd, (G.deleteEdges_le _) x.adj⟩, by
    have hn := (deleteEdges_adj.mp x.adj).2
    change ¬s(x.fst, x.snd) = d.edge at hn
    exact not_or.mp (hn ∘ (dart_edge_eq_iff _ _).mpr)⟩
  invFun x := ⟨x.val.toProd, dart_adj_delete_edge d x.val x.property.1 x.property.2⟩
  left_inv x := by cases x; rfl
  right_inv x := by apply Subtype.ext; rfl

@[simp] theorem dartDeleteEquiv_fst (d : G.Dart) (x : (G.deleteEdges {d.edge}).Dart) :
    (dartDeleteEquiv d x).val.fst = x.fst := rfl

@[simp] theorem dartDeleteEquiv_snd (d : G.Dart) (x : (G.deleteEdges {d.edge}).Dart) :
    (dartDeleteEquiv d x).val.snd = x.snd := rfl

/-- A boundary walk skips exactly the removed side when it encounters the deleted edge. -/
theorem RotationSystem.deleteEdge_facePerm (R : RotationSystem G) (d : G.Dart)
    (x : (G.deleteEdges {d.edge}).Dart) :
    (dartDeleteEquiv d ((R.deleteEdge d).facePerm x)).val =
      if R.facePerm (dartDeleteEquiv d x).val = d then R.facePerm d.symm
      else if R.facePerm (dartDeleteEquiv d x).val = d.symm then R.facePerm d
      else R.facePerm (dartDeleteEquiv d x).val := by
  classical
  let y := (dartDeleteEquiv d x).val
  change (dartDeleteEquiv d ((R.deleteEdge d).facePerm x)).val =
      if R.facePerm y = d then R.facePerm d.symm
      else if R.facePerm y = d.symm then R.facePerm d else R.facePerm y
  have hy := (dartDeleteEquiv d x).property
  have hyf : y.fst = x.fst := rfl
  have hys : y.snd = x.snd := rfl
  by_cases hu : x.snd = d.fst
  · have hxv : x.fst ≠ d.snd := by
      intro h
      exact hy.2 (Dart.ext _ _ (Prod.ext h hu))
    have hne : R.facePerm y ≠ d.symm := by
      intro h
      have := congrArg (fun z : G.Dart ↦ z.fst) h
      simp only [RotationSystem.facePerm_fst] at this
      exact d.fst_ne_snd (hu.symm.trans this)
    have he : R.facePerm y = d ↔ R.next d.fst x.fst = d.snd := by
      rw [Dart.ext_iff, Prod.ext_iff]
      simp only [RotationSystem.facePerm_fst, RotationSystem.facePerm_snd, hyf, hys, hu,
        true_and]
    simp only [hne, ↓reduceIte, he]
    split_ifs with h
    · apply Dart.ext
      apply Prod.ext
      · exact hu
      · simp only [dartDeleteEquiv_snd, RotationSystem.facePerm_snd, hu,
          RotationSystem.deleteEdge_next_fst_of_ne R d _ hxv, h, ↓reduceIte]
        rfl
    · apply Dart.ext
      apply Prod.ext
      · rfl
      · simp only [dartDeleteEquiv_snd, RotationSystem.facePerm_snd, hu,
          RotationSystem.deleteEdge_next_fst_of_ne R d _ hxv, h, ↓reduceIte, hyf, hys]
  · by_cases hv : x.snd = d.snd
    · have hxu : x.fst ≠ d.fst := by
        intro h
        exact hy.1 (Dart.ext _ _ (Prod.ext h hv))
      have hne : R.facePerm y ≠ d := by
        intro h
        exact hu (congrArg (fun z : G.Dart ↦ z.fst) h)
      have he : R.facePerm y = d.symm ↔ R.next d.snd x.fst = d.fst := by
        rw [Dart.ext_iff, Prod.ext_iff]
        simp only [RotationSystem.facePerm_fst, RotationSystem.facePerm_snd, hyf, hys, hv, Dart.symm, Prod.swap, true_and]
      simp only [hne, ↓reduceIte, he]
      split_ifs with h
      · apply Dart.ext
        apply Prod.ext
        · simpa only [dartDeleteEquiv_fst, RotationSystem.facePerm_fst] using hv
        · simp only [dartDeleteEquiv_snd, RotationSystem.facePerm_snd, hv,
            RotationSystem.deleteEdge_next_snd_of_ne R d _ hxu, h, ↓reduceIte]
      · apply Dart.ext
        apply Prod.ext
        · rfl
        · simp only [dartDeleteEquiv_snd, RotationSystem.facePerm_snd, hv,
            RotationSystem.deleteEdge_next_snd_of_ne R d _ hxu, h, ↓reduceIte, hyf, hys]
    · have hne : R.facePerm y ≠ d := fun h ↦ hu (congrArg (fun z : G.Dart ↦ z.fst) h)
      have hne' : R.facePerm y ≠ d.symm := fun h ↦ hv (congrArg (fun z : G.Dart ↦ z.fst) h)
      simp only [hne, hne', ↓reduceIte]
      apply Dart.ext
      apply Prod.ext
      · rfl
      · exact R.deleteEdge_next_other d x.snd x.fst hu hv

section Finite

variable [Fintype V]

/-- Cut the two sides of an edge apart before deleting them. -/
def RotationSystem.cutEdge (R : RotationSystem G) (d : G.Dart) : Equiv.Perm G.Dart :=
  R.facePerm * Equiv.swap d d.symm

@[simp] theorem RotationSystem.cutEdge_apply (R : RotationSystem G) (d : G.Dart) :
    R.cutEdge d d = R.facePerm d.symm := by simp [RotationSystem.cutEdge]

@[simp] theorem RotationSystem.cutEdge_apply_symm (R : RotationSystem G) (d : G.Dart) :
    R.cutEdge d d.symm = R.facePerm d := by simp [RotationSystem.cutEdge]

theorem RotationSystem.cutEdge_no_two (R : RotationSystem G) (d : G.Dart) :
    ¬(R.cutEdge d d = d.symm ∧ R.cutEdge d d.symm = d) := by
  intro h
  exact R.facePerm_ne d.symm ((R.cutEdge_apply d).symm.trans h.1)

theorem RotationSystem.deleteEdge_facePerm_commutes (R : RotationSystem G) (d : G.Dart)
    (x : (G.deleteEdges {d.edge}).Dart) :
    dartDeleteEquiv d ((R.deleteEdge d).facePerm x) =
      deleteTwoPerm (R.cutEdge d) d d.symm d.symm_ne.symm (dartDeleteEquiv d x) := by
  classical
  apply Subtype.ext
  rw [R.deleteEdge_facePerm, deleteTwoPerm_apply]
  have hx := (dartDeleteEquiv d x).property
  have ht : R.cutEdge d (dartDeleteEquiv d x).val =
      R.facePerm (dartDeleteEquiv d x).val := by
    simp only [RotationSystem.cutEdge, Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne hx.1 hx.2]
  rw [ht, R.cutEdge_apply, R.cutEdge_apply_symm]
  by_cases ha : R.facePerm (dartDeleteEquiv d x).val = d
  · simp only [ha, ↓reduceIte, R.facePerm_ne, ↓reduceIte]
  · by_cases hb : R.facePerm (dartDeleteEquiv d x).val = d.symm
    · simp only [ha, hb, d.symm_ne, ↓reduceIte, R.facePerm_ne, ↓reduceIte]
    · simp only [ha, hb, ↓reduceIte]

theorem RotationSystem.deleteEdge_facePerm_conj (R : RotationSystem G) (d : G.Dart) :
    (dartDeleteEquiv d).symm.trans ((R.deleteEdge d).facePerm.trans (dartDeleteEquiv d)) =
      deleteTwoPerm (R.cutEdge d) d d.symm d.symm_ne.symm := by
  apply Equiv.ext
  intro x
  simpa using R.deleteEdge_facePerm_commutes d ((dartDeleteEquiv d).symm x)

theorem RotationSystem.totalCycles_facePerm (R : RotationSystem G) :
    totalCycles R.facePerm = R.facePerm.cycleType.card := by
  classical
  haveI : IsEmpty {x : G.Dart // R.facePerm x = x} :=
    ⟨fun x ↦ R.facePerm_ne x.val x.property⟩
  simp [totalCycles]
  congr 2

set_option maxHeartbeats 2000000 in
theorem RotationSystem.cycleCount_deleteEdge (R : RotationSystem G) (d : G.Dart) :
    (R.deleteEdge d).facePerm.cycleType.card +
      (if R.cutEdge d d = d then 1 else 0) +
      (if R.cutEdge d d.symm = d.symm then 1 else 0) = totalCycles (R.cutEdge d) := by
  classical
  have h := totalCycles_deleteTwoPerm (R.cutEdge d) d d.symm d.symm_ne.symm
    (R.cutEdge_no_two d)
  have hc : totalCycles (deleteTwoPerm (R.cutEdge d) d d.symm d.symm_ne.symm) =
      (R.deleteEdge d).facePerm.cycleType.card := by
    calc
      _ = totalCycles ((dartDeleteEquiv d).symm.trans
          ((R.deleteEdge d).facePerm.trans (dartDeleteEquiv d))) := by
        congr 1
        exact (R.deleteEdge_facePerm_conj d).symm
      _ = totalCycles (R.deleteEdge d).facePerm := totalCycles_equiv _ _
      _ = _ := by
        haveI : IsEmpty {x : (G.deleteEdges {d.edge}).Dart //
            (R.deleteEdge d).facePerm x = x} :=
          ⟨fun x ↦ (R.deleteEdge d).facePerm_ne x.val x.property⟩
        simp only [totalCycles, Fintype.card_of_isEmpty, Nat.add_zero]
        congr 2 <;> exact Subsingleton.elim _ _
  calc
    _ = totalCycles (deleteTwoPerm (R.cutEdge d) d d.symm d.symm_ne.symm) +
        (if R.cutEdge d d = d then 1 else 0) +
        (if R.cutEdge d d.symm = d.symm then 1 else 0) := by rw [hc]
    _ = _ := by
      convert h using 1
      congr 2
      · exact totalCycles_fintype_irrel _ _ _
      · split_ifs <;> rfl

end Finite

end Erdos759.SimpleGraph
