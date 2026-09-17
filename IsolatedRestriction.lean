import ErdosProblems.Erdos759
import RotationTransport

/-! Removing any set of isolated vertices preserves the ordinary surface certificate. -/

noncomputable section
open _root_.SimpleGraph
namespace Erdos759.SimpleGraph
attribute [local instance] Classical.propDecidable Classical.decEq

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {s : Set V}

omit [Fintype V] in
theorem reachable_mem_of_support_subset (hs : G.support ⊆ s) {x y : V}
    (h : G.Reachable x y) (hx : x ∈ s) : y ∈ s := by
  by_cases he : x = y
  · exact he ▸ hx
  obtain ⟨z, hz⟩ := h.nonempty_neighborSet_right he
  exact hs hz.mem_support_left

theorem reachable_induce_of_support_subset (hs : G.support ⊆ s) (x y : s) :
    (G.induce s).Reachable x y ↔ G.Reachable x.val y.val := by
  constructor
  · exact fun h => h.map (Embedding.induce s).toHom
  · rintro ⟨p⟩
    exact ⟨p.induce s (fun z hz =>
      reachable_mem_of_support_subset hs (p.takeUntil z hz).reachable x.property)⟩

def isolatedComponentLabel (s : Set V) (x : V) :
    (G.induce s).ConnectedComponent ⊕ {v : V // v ∉ s} :=
  if hx : x ∈ s then Sum.inl ((G.induce s).connectedComponentMk ⟨x, hx⟩)
  else Sum.inr ⟨x, hx⟩

theorem isolatedComponentLabel_eq_iff (hs : G.support ⊆ s) (x y : V) :
    isolatedComponentLabel (G := G) s x = isolatedComponentLabel (G := G) s y ↔
      G.Reachable x y := by
  by_cases hx : x ∈ s <;> by_cases hy : y ∈ s
  · simp only [isolatedComponentLabel, dite_eq_left hx, dite_eq_left hy,
      Sum.inl.injEq, ConnectedComponent.eq]
    exact reachable_induce_of_support_subset hs ⟨x, hx⟩ ⟨y, hy⟩
  · simp only [isolatedComponentLabel, dite_eq_left hx, dite_eq_right hy,
      Sum.inl_ne_inr, false_iff]
    exact fun h => hy (reachable_mem_of_support_subset hs h hx)
  · simp only [isolatedComponentLabel, dite_eq_right hx, dite_eq_left hy,
      Sum.inr_ne_inl, false_iff]
    exact fun h => hx (reachable_mem_of_support_subset hs h.symm hy)
  · simp only [isolatedComponentLabel, dite_eq_right hx, dite_eq_right hy,
      Sum.inr.injEq, Subtype.mk.injEq]
    constructor
    · rintro rfl
      exact .rfl
    · intro h
      by_contra he
      obtain ⟨z, hz⟩ := h.nonempty_neighborSet_left he
      exact hx (hs hz.mem_support_left)

def isolatedComponentEquiv (hs : G.support ⊆ s) :
    G.ConnectedComponent ≃ (G.induce s).ConnectedComponent ⊕ {v : V // v ∉ s} :=
  Equiv.ofBijective
    (Quot.lift (isolatedComponentLabel (G := G) s)
      (fun x y hxy => (isolatedComponentLabel_eq_iff hs x y).mpr hxy)) (by
      constructor
      · intro q r
        refine ConnectedComponent.ind₂ ?_ q r
        intro x y h
        exact ConnectedComponent.sound ((isolatedComponentLabel_eq_iff hs x y).mp h)
      · rintro (q | ⟨x, hx⟩)
        · refine ConnectedComponent.ind ?_ q
          intro x
          refine ⟨G.connectedComponentMk x.val, ?_⟩
          change isolatedComponentLabel s x.val = Sum.inl ((G.induce s).connectedComponentMk x)
          simp [isolatedComponentLabel, x.property]
        · refine ⟨G.connectedComponentMk x, ?_⟩
          change isolatedComponentLabel s x = Sum.inr ⟨x, hx⟩
          simp [isolatedComponentLabel, hx])

theorem componentCount_induce_support (hs : G.support ⊆ s) :
    componentCount G = componentCount (G.induce s) + Fintype.card {v : V // v ∉ s} := by
  simpa only [componentCount, Fintype.card_sum] using
    Fintype.card_congr (isolatedComponentEquiv hs)

omit [Fintype V] in
theorem isolated_induce_iff (hs : G.support ⊆ s) (v : s) :
    (∀ w : s, ¬ (G.induce s).Adj v w) ↔ ∀ w, ¬ G.Adj v.val w := by
  constructor
  · intro h w hw
    exact h ⟨w, hs hw.mem_support_right⟩ hw
  · exact fun h w => h w.val

omit [Fintype V] in
theorem isolated_of_not_mem (hs : G.support ⊆ s) {v : V} (hv : v ∉ s) :
    ∀ w, ¬ G.Adj v w := fun _ h => hv (hs h.mem_support_left)

def isolatedVertexEquiv (hs : G.support ⊆ s) :
    {v : V // ∀ w, ¬ G.Adj v w} ≃
      ({v : s // ∀ w, ¬ (G.induce s).Adj v w} ⊕ {v : V // v ∉ s}) where
  toFun v := if hv : v.val ∈ s then
    Sum.inl ⟨⟨v.val, hv⟩, fun w => v.property w.val⟩ else Sum.inr ⟨v.val, hv⟩
  invFun v := match v with
    | Sum.inl v => ⟨v.val.val, (isolated_induce_iff hs v.val).mp v.property⟩
    | Sum.inr v => ⟨v.val, isolated_of_not_mem hs v.property⟩
  left_inv v := by
    dsimp only
    split_ifs <;> rfl
  right_inv v := by
    cases v with
    | inl v => simp only [dite_eq_left v.val.property]
    | inr v => simp only [dite_eq_right v.property]

theorem isolateCount_eq_card (G : SimpleGraph V) [DecidableRel G.Adj] :
    isolateCount G = Fintype.card {v : V // ∀ w, ¬ G.Adj v w} := by
  simp [isolateCount, Fintype.card_subtype]

theorem isolateCount_induce_support (hs : G.support ⊆ s) :
    isolateCount G = isolateCount (G.induce s) + Fintype.card {v : V // v ∉ s} := by
  rw [isolateCount_eq_card, isolateCount_eq_card]
  simpa only [Fintype.card_sum] using Fintype.card_congr (isolatedVertexEquiv hs)

theorem vertexCount_induce_compl (s : Set V) :
    Fintype.card V = Fintype.card s + Fintype.card {v : V // v ∉ s} := by
  simpa only [Fintype.card_sum] using (Fintype.card_congr (Equiv.sumCompl (· ∈ s))).symm

theorem EmbedsOrientable.induce_of_support_subset {g : ℕ}
    (hG : EmbedsOrientable G g) (hs : G.support ⊆ s) :
    EmbedsOrientable (G.induce s) g := by
  obtain ⟨R, hR⟩ := hG
  let f : s ↪ V := Function.Embedding.subtype (· ∈ s)
  have hcover : RotationSystem.CoversEdges G f := by
    intro v w hvw
    exact ⟨⟨v, hs hvw.mem_support_left⟩, rfl⟩
  let Q := R.pullback f hcover
  refine ⟨Q, ?_⟩
  have hfaces := R.pullback_face_cycle_count f hcover
  have hcomp := componentCount_induce_support hs
  have hiso := isolateCount_induce_support hs
  have hvertices := vertexCount_induce_compl s
  have hedges := card_edgeFinset_induce_of_support_subset hs
  change 2 * componentCount (G.induce s) + (G.induce s).edgeFinset.card ≤
    Fintype.card s + (Q.facePerm.cycleType.card + isolateCount (G.induce s)) + 2 * g
  change 2 * componentCount G + G.edgeFinset.card ≤
    Fintype.card V + (R.facePerm.cycleType.card + isolateCount G) + 2 * g at hR
  have hfaces' : Q.facePerm.cycleType.card = R.facePerm.cycleType.card := by
    convert hfaces using 1
    congr 2
  omega

end Erdos759.SimpleGraph
