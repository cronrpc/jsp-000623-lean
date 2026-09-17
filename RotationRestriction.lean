import ErdosProblems.Erdos759

namespace List

variable {α : Type*} [DecidableEq α]

/-- Filtering a cyclic list preserves its cyclic-order equivalence. -/
theorem IsRotated.filter' {l l' : List α} (h : l ~r l') (p : α → Bool) :
    l.filter p ~r l'.filter p := by
  obtain ⟨n, rfl⟩ := h
  rw [rotate_eq_drop_append_take_mod, filter_append]
  conv_lhs => rw [← take_append_drop (n % l.length) l, filter_append]
  exact isRotated_append

/-- Removing one entry from a cyclic order skips that entry and fixes it. -/
theorem formPerm_filter_ne (l : List α) (hl : l.Nodup) (a : α) :
    (l.filter (fun x ↦ decide (x ≠ a))).formPerm =
      Equiv.swap a (l.formPerm a) * l.formPerm := by
  by_cases ha : a ∈ l
  · obtain ⟨s, t, rfl⟩ := mem_iff_append.mp ha
    have hr : s ++ a :: t ~r a :: (t ++ s) := isRotated_append
    have hn : (a :: (t ++ s)).Nodup := hr.nodup_iff.mp hl
    have hp := formPerm_eq_of_isRotated hl hr
    have hq := formPerm_eq_of_isRotated (hl.filter (fun x ↦ decide (x ≠ a)))
      (hr.filter' (fun x ↦ decide (x ≠ a)))
    rw [hp, hq]
    have ht : (t ++ s).filter (fun x ↦ decide (x ≠ a)) = t ++ s := by
      apply filter_eq_self.mpr
      intro x hx
      simp only [decide_eq_true_eq]
      exact fun h ↦ hn.notMem (h ▸ hx)
    simp only [filter_cons, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
      ↓reduceIte, ht]
    generalize ht' : t ++ s = q at hn ⊢
    cases q with
    | nil =>
      simp only [formPerm_nil, formPerm_singleton, Equiv.Perm.one_apply, Equiv.swap_self]
      rfl
    | cons b q =>
      rw [formPerm_apply_head _ _ _ hn, formPerm_cons_cons, ← mul_assoc]
      simp
  · have hf : l.filter (fun x ↦ decide (x ≠ a)) = l := by
      apply filter_eq_self.mpr
      intro x hx
      simp only [decide_eq_true_eq]
      exact fun h ↦ ha (h ▸ hx)
    rw [hf, formPerm_apply_of_notMem ha, Equiv.swap_self]
    rfl

end List

/-!
# Restricting an actual rotation system to a subgraph

The ordinary rotation-system embedding certificate is the starting point.
Hereditary embeddability is proved from it rather than assumed as input.
-/

namespace Erdos759.SimpleGraph

open _root_.SimpleGraph
open scoped Classical

variable {V : Type*} {G H : SimpleGraph V}

/-- Delete the missing neighbours from each cyclic vertex order. -/
noncomputable def RotationSystem.restrict (R : RotationSystem G) (hHG : H ≤ G) :
    RotationSystem H := by
  classical
  exact
    { order := fun v ↦ (R.order v).filter (fun w ↦ decide (H.Adj v w))
      nodup_order := fun v ↦ (R.nodup_order v).filter _
      mem_order_iff := by
        intro v w
        simp only [List.mem_filter, decide_eq_true_eq, R.mem_order_iff]
        exact ⟨fun h ↦ h.2, fun h ↦ ⟨hHG h, h⟩⟩ }

@[simp] theorem RotationSystem.restrict_order (R : RotationSystem G) (hHG : H ≤ G)
    (v : V) :
    (R.restrict hHG).order v =
      (R.order v).filter (fun w ↦ decide (H.Adj v w)) := by
  classical
  rfl

@[simp] theorem RotationSystem.restrict_self_order (R : RotationSystem G) (v : V) :
    (R.restrict le_rfl).order v = R.order v := by
  classical
  rw [RotationSystem.restrict_order]
  apply List.filter_eq_self.mpr
  intro w hw
  simpa using (R.mem_order_iff v w).mp hw

end Erdos759.SimpleGraph

namespace Erdos759.SimpleGraph.RotationSystem

open _root_.SimpleGraph
open scoped Classical

variable {V : Type*} {G : SimpleGraph V}

/-- The cyclic orders left after removing one unoriented edge. -/
noncomputable def deleteEdge (R : RotationSystem G) (d : G.Dart) :
    RotationSystem (G.deleteEdges {d.edge}) := R.restrict (G.deleteEdges_le _)

theorem deleteEdge_order_fst (R : RotationSystem G) (d : G.Dart) :
    (R.deleteEdge d).order d.fst =
      (R.order d.fst).filter (fun w ↦ decide (w ≠ d.snd)) := by
  classical
  apply List.filter_congr
  intro w hw
  have hmem := (R.mem_order_iff _ _).mp hw
  simp [deleteEdges_adj, hmem, Dart.edge, Prod.ext_iff, Prod.swap, d.fst_ne_snd]

theorem deleteEdge_order_snd (R : RotationSystem G) (d : G.Dart) :
    (R.deleteEdge d).order d.snd =
      (R.order d.snd).filter (fun w ↦ decide (w ≠ d.fst)) := by
  classical
  apply List.filter_congr
  intro w hw
  have hmem := (R.mem_order_iff _ _).mp hw
  simp [deleteEdges_adj, hmem, Dart.edge, Prod.ext_iff, Prod.swap, d.snd_ne_fst]

theorem deleteEdge_order_other (R : RotationSystem G) (d : G.Dart) (v : V)
    (hv : v ≠ d.fst) (hv' : v ≠ d.snd) :
    (R.deleteEdge d).order v = R.order v := by
  classical
  apply List.filter_eq_self.mpr
  intro w hw
  have hmem := (R.mem_order_iff _ _).mp hw
  simpa [deleteEdges_adj, hmem, Dart.edge, Prod.ext_iff, Prod.swap, hv, hv']

theorem deleteEdge_next_fst (R : RotationSystem G) (d : G.Dart) (w : V) :
    (R.deleteEdge d).next d.fst w =
      Equiv.swap d.snd (R.next d.fst d.snd) (R.next d.fst w) := by
  classical
  simp only [next, deleteEdge_order_fst, List.formPerm_filter_ne _ (R.nodup_order _),
    Equiv.Perm.mul_apply]

theorem deleteEdge_next_snd (R : RotationSystem G) (d : G.Dart) (w : V) :
    (R.deleteEdge d).next d.snd w =
      Equiv.swap d.fst (R.next d.snd d.fst) (R.next d.snd w) := by
  classical
  simp only [next, deleteEdge_order_snd, List.formPerm_filter_ne _ (R.nodup_order _),
    Equiv.Perm.mul_apply]

theorem deleteEdge_next_other (R : RotationSystem G) (d : G.Dart) (v w : V)
    (hv : v ≠ d.fst) (hv' : v ≠ d.snd) :
    (R.deleteEdge d).next v w = R.next v w := by
  simp only [next, deleteEdge_order_other R d v hv hv']

theorem deleteEdge_next_fst_of_ne (R : RotationSystem G) (d : G.Dart) (w : V)
    (hw : w ≠ d.snd) :
    (R.deleteEdge d).next d.fst w =
      if R.next d.fst w = d.snd then R.next d.fst d.snd else R.next d.fst w := by
  classical
  rw [deleteEdge_next_fst]
  have hn : R.next d.fst w ≠ R.next d.fst d.snd := fun h ↦
    hw ((R.order d.fst).formPerm.injective h)
  split_ifs with h
  · simp [h]
  · exact Equiv.swap_apply_of_ne_of_ne h hn

theorem deleteEdge_next_snd_of_ne (R : RotationSystem G) (d : G.Dart) (w : V)
    (hw : w ≠ d.fst) :
    (R.deleteEdge d).next d.snd w =
      if R.next d.snd w = d.fst then R.next d.snd d.fst else R.next d.snd w := by
  classical
  rw [deleteEdge_next_snd]
  have hn : R.next d.snd w ≠ R.next d.snd d.fst := fun h ↦
    hw ((R.order d.snd).formPerm.injective h)
  split_ifs with h
  · simp [h]
  · exact Equiv.swap_apply_of_ne_of_ne h hn

end Erdos759.SimpleGraph.RotationSystem

namespace Erdos759.SimpleGraph

open _root_.SimpleGraph
open scoped Classical

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

omit [Fintype V] in
/-- A surviving dart is still an edge after deleting a different unoriented edge. -/
theorem dart_adj_delete_edge (d x : G.Dart) (hxd : x ≠ d) (hxrev : x ≠ d.symm) :
    (G.deleteEdges {d.edge}).Adj x.fst x.snd := by
  rw [deleteEdges_adj]
  refine ⟨x.adj, ?_⟩
  change x.edge ∉ ({d.edge} : Set (Sym2 V))
  simpa only [Set.mem_singleton_iff, dart_edge_eq_iff, not_or] using And.intro hxd hxrev

/-- The two sides of a bridge lie on the same boundary walk of every rotation system. -/
theorem RotationSystem.sameCycle_of_isBridge (R : RotationSystem G) (d : G.Dart)
    (hd : G.IsBridge d.edge) : R.facePerm.SameCycle d d.symm := by
  classical
  by_contra hn
  let H := G.deleteEdges {d.edge}
  let p := R.facePerm
  let P : G.Dart → Prop := fun x ↦ p.SameCycle d x ∧ H.Reachable d.fst x.fst
  have back : ∀ x, p.SameCycle d x → H.Reachable d.fst (p x).fst →
      H.Reachable d.fst x.fst := by
    intro x hx hr
    by_cases hxd : x = d
    · subst x
      exact .refl _
    · have hxrev : x ≠ d.symm := fun h ↦ hn (h ▸ hx)
      have hadj := dart_adj_delete_edge d x hxd hxrev
      exact hr.trans hadj.symm.reachable
  have hinv : ∀ x, P x → P (p.symm x) := by
    intro x hx
    have horb : p.SameCycle d (p.symm x) := hx.1.symm_apply_right
    refine ⟨horb, back (p.symm x) horb ?_⟩
    simpa using hx.2
  have hp : P d := ⟨Equiv.Perm.SameCycle.refl _ _, .refl _⟩
  have hf := Equiv.Perm.perm_symm_on_of_perm_on_finite hinv hp
  have hr : H.Reachable d.fst d.snd := by
    simpa [p, RotationSystem.facePerm_fst] using hf.2
  exact hd hr

end Erdos759.SimpleGraph
