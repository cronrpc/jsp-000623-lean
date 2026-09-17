import Mathlib

/-! # Counting all cycles in a finite permutation

Fixed points count as cycles. This convention is necessary when a facial
permutation is cut at the two darts of a deleted edge.

The finite-orbit invariance and unique-return arguments below adapt the
Apache-2.0 licensed `ErdosProblems/Erdos73/PermutationCutCycles.lean` from
plby/lean-proofs, commit 8822f7ddef30fadbd92e1c6ab4ed897af356af5e.
The orbit-counting equivalences and transposition formulas are developed here.
-/

noncomputable section
open Equiv Equiv.Perm
namespace JSP623.PermutationSurgery

attribute [local instance] Classical.propDecidable Classical.decEq

variable {α : Type*} [Fintype α]

def totalCycles (p : Perm α) : ℕ :=
  p.cycleType.card + Fintype.card {x : α // p x = x}

abbrev Orbit (p : Perm α) := Quotient (SameCycle.setoid p)

def orbitLabel (p : Perm α) (x : α) :
    {y : α // p y = y} ⊕ {c : Perm α // c ∈ p.cycleFactorsFinset} :=
  if hx : p x = x then Sum.inl ⟨x, hx⟩
  else Sum.inr ⟨p.cycleOf x, cycleOf_mem_cycleFactorsFinset_iff.mpr (mem_support.mpr hx)⟩

theorem orbitLabel_eq_iff (p : Perm α) (x y : α) :
    orbitLabel p x = orbitLabel p y ↔ p.SameCycle x y := by
  by_cases hx : p x = x <;> by_cases hy : p y = y
  · simp only [orbitLabel, dite_eq_left hx, dite_eq_left hy, Sum.inl.injEq, Subtype.mk.injEq]
    exact ⟨fun h => h.sameCycle p, fun h => h.eq_of_left hx⟩
  · simp only [orbitLabel, dite_eq_left hx, dite_eq_right hy, Sum.inl_ne_inr, false_iff]
    exact fun h => hy (h.apply_eq_self_iff.mp hx)
  · simp only [orbitLabel, dite_eq_right hx, dite_eq_left hy, Sum.inr_ne_inl, false_iff]
    exact fun h => hx (h.apply_eq_self_iff.mpr hy)
  · simp only [orbitLabel, dite_eq_right hx, dite_eq_right hy, Sum.inr.injEq, Subtype.mk.injEq]
    exact (sameCycle_iff_cycleOf_eq_of_mem_support (mem_support.mpr hx)
      (mem_support.mpr hy)).symm

theorem orbitLabel_surjective (p : Perm α) : Function.Surjective (orbitLabel p) := by
  rintro (⟨x, hx⟩ | ⟨c, hc⟩)
  · exact ⟨x, by simp [orbitLabel, hx]⟩
  · obtain ⟨x, hx⟩ := (mem_cycleFactorsFinset_iff.mp hc).1.nonempty_support
    have hpx : p x ≠ x := mem_support.mp (mem_cycleFactorsFinset_support_le hc hx)
    refine ⟨x, ?_⟩
    simp only [orbitLabel, dite_eq_right hpx, Sum.inr.injEq, Subtype.mk.injEq]
    exact ((p.eq_cycleOf_of_mem_cycleFactorsFinset_iff c hc x).mpr hx).symm

def orbitEquiv (p : Perm α) : Orbit p ≃
    ({y : α // p y = y} ⊕ {c : Perm α // c ∈ p.cycleFactorsFinset}) :=
  Equiv.ofBijective (Quotient.lift (orbitLabel p)
    (fun x y h => (orbitLabel_eq_iff p x y).mpr h)) (by
      constructor
      · intro q r
        refine Quotient.inductionOn₂ q r ?_
        intro x y h
        exact Quotient.sound ((orbitLabel_eq_iff p x y).mp h)
      · intro v
        obtain ⟨x, hx⟩ := orbitLabel_surjective p v
        exact ⟨Quotient.mk _ x, hx⟩)

theorem card_orbit (p : Perm α) : Fintype.card (Orbit p) = totalCycles p := by
  have h := Fintype.card_congr (orbitEquiv p)
  simpa [totalCycles, Fintype.card_sum, cycleType_def, Nat.add_comm] using h

theorem support_card_add_fixed (p : Perm α) :
    p.support.card + Fintype.card {x : α // p x = x} = Fintype.card α := by
  classical
  have h := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (p := fun x : α => p x ≠ x)
  simpa [Fintype.card_subtype, support] using h

theorem sign_totalCycles (p : Perm α) :
    p.sign = (-1 : ℤˣ) ^ (Fintype.card α + totalCycles p) := by
  have hcard := support_card_add_fixed p
  have heq : p.cycleType.sum + p.cycleType.card +
      2 * Fintype.card {x : α // p x = x} = Fintype.card α + totalCycles p := by
    rw [sum_cycleType]
    unfold totalCycles
    omega
  rw [sign_of_cycleType, ← heq]
  simp only [pow_add, pow_mul]
  norm_num

theorem invariant_of_sameCycle {p : Perm α} {β : Type*} (f : α → β)
    (hf : ∀ x, f (p x) = f x) {x y : α} (h : p.SameCycle x y) : f x = f y := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction n with
  | zero => rfl
  | succ n ih => simpa [pow_succ', hf] using ih

theorem sameCycle_of_step {p q : Perm α}
    (hstep : ∀ x, p.SameCycle x (q x)) {x y : α} (h : q.SameCycle x y) :
    p.SameCycle x y := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction n with
  | zero => exact SameCycle.rfl
  | succ n ih =>
    rw [pow_succ', mul_apply]
    exact ih.trans (hstep _)

/-- A finite orbit that exits a set must pass its unique reentry point. -/
theorem sameCycle_of_unique_return (p : Perm α) (P : α → Prop) (a b : α)
    (ha : P a) (hout : ¬ P (p a))
    (hreturn : ∀ x, ¬ P x → P (p x) → x = b) : p.SameCycle a b := by
  by_contra hn
  let S : Set α := {x | p.SameCycle a x ∧ ¬ P x}
  have hm : Set.MapsTo p S S := by
    intro x hx
    refine ⟨hx.1.apply_right, ?_⟩
    intro hpx
    exact hn ((hreturn x hx.2 hpx) ▸ hx.1)
  have hb := (S.toFinite.injOn_iff_bijOn_of_mapsTo hm).mp p.injective.injOn
  obtain ⟨x, hx, he⟩ := hb.surjOn (show p a ∈ S from ⟨SameCycle.rfl.apply_right, hout⟩)
  exact hx.2 (p.injective he ▸ ha)

theorem sameCycle_mul_swap_of_not_sameCycle (p : Perm α) {a b : α}
    (h : ¬ p.SameCycle a b) : (p * swap a b).SameCycle a b := by
  have hab : a ≠ b := fun he => h (he.sameCycle p)
  apply sameCycle_of_unique_return (p * swap a b) (fun x => p.SameCycle a x) a b SameCycle.rfl
  · simpa [mul_apply, sameCycle_apply_right] using h
  · intro x hx hpx
    by_contra hxb
    have hxa : x ≠ a := fun he => hx (he ▸ SameCycle.rfl)
    simp only [mul_apply, swap_apply_of_ne_of_ne hxa hxb, sameCycle_apply_right] at hpx
    exact hx hpx

theorem sameCycle_le_mul_swap (p : Perm α) {a b : α}
    (hab : (p * swap a b).SameCycle a b) {x y : α} (hxy : p.SameCycle x y) :
    (p * swap a b).SameCycle x y := by
  apply sameCycle_of_step (q := p) (fun x => ?_) hxy
  by_cases hxa : x = a
  · subst x
    simpa using hab.apply_right
  by_cases hxb : x = b
  · subst x
    simpa using hab.symm.apply_right
  have hx : (p * swap a b).SameCycle x ((p * swap a b) x) := SameCycle.rfl.apply_right
  simpa [mul_apply, swap_apply_of_ne_of_ne hxa hxb] using hx

def collapseLabel (p : Perm α) (a b x : α) : Orbit p :=
  if p.SameCycle b x then Quotient.mk _ a else Quotient.mk _ x

theorem collapseLabel_apply (p : Perm α) (a b x : α) :
    collapseLabel p a b (p x) = collapseLabel p a b x := by
  unfold collapseLabel
  simp only [sameCycle_apply_right]
  split_ifs
  · rfl
  · exact Quotient.sound SameCycle.rfl.apply_right.symm

theorem collapseLabel_swap (p : Perm α) {a b : α} (h : ¬ p.SameCycle a b) (x : α) :
    collapseLabel p a b (swap a b x) = collapseLabel p a b x := by
  have hba : ¬ p.SameCycle b a := fun hba => h hba.symm
  by_cases hxa : x = a
  · subst x
    simp [collapseLabel, hba, SameCycle.refl]
  by_cases hxb : x = b
  · subst x
    simp [collapseLabel, hba, SameCycle.refl]
  rw [swap_apply_of_ne_of_ne hxa hxb]

theorem collapseLabel_ne (p : Perm α) {a b : α} (h : ¬ p.SameCycle a b) (x : α) :
    collapseLabel p a b x ≠ Quotient.mk _ b := by
  unfold collapseLabel
  split_ifs with hx
  · exact fun he => h (Quotient.exact he)
  · exact fun he => hx (Quotient.exact he).symm

theorem collapseLabel_eq_iff (p : Perm α) {a b : α} (h : ¬ p.SameCycle a b)
    (x y : α) : collapseLabel p a b x = collapseLabel p a b y ↔
      (p * swap a b).SameCycle x y := by
  have hab := sameCycle_mul_swap_of_not_sameCycle p h
  have liftSame {x y : α} (hxy : p.SameCycle x y) := sameCycle_le_mul_swap p hab hxy
  constructor
  · intro he
    unfold collapseLabel at he
    split_ifs at he with hx hy hy
    · exact liftSame (hx.symm.trans hy)
    · exact ((liftSame hx.symm).trans hab.symm).trans (liftSame (Quotient.exact he))
    · exact ((liftSame (Quotient.exact he)).trans hab).trans (liftSame hy)
    · exact liftSame (Quotient.exact he)
  · apply invariant_of_sameCycle (collapseLabel p a b)
    intro z
    rw [mul_apply, collapseLabel_apply, collapseLabel_swap p h]

def collapseOrbitEquiv (p : Perm α) {a b : α} (h : ¬ p.SameCycle a b) :
    Orbit (p * swap a b) ≃ {q : Orbit p // q ≠ Quotient.mk _ b} :=
  Equiv.ofBijective
    (Quotient.lift (fun x => ⟨collapseLabel p a b x, collapseLabel_ne p h x⟩)
      (fun x y hxy => Subtype.ext ((collapseLabel_eq_iff p h x y).mpr hxy))) (by
        constructor
        · intro q r
          refine Quotient.inductionOn₂ q r ?_
          intro x y he
          exact Quotient.sound ((collapseLabel_eq_iff p h x y).mp (congrArg Subtype.val he))
        · rintro ⟨q, hq⟩
          obtain ⟨x, rfl⟩ := Quotient.exists_rep q
          have hx : ¬ p.SameCycle b x := fun hx => hq (Quotient.sound hx.symm)
          refine ⟨Quotient.mk _ x, Subtype.ext ?_⟩
          exact ite_eq_right hx)

theorem totalCycles_mul_swap_of_not_sameCycle (p : Perm α) {a b : α}
    (h : ¬ p.SameCycle a b) : totalCycles (p * swap a b) + 1 = totalCycles p := by
  have he := Fintype.card_congr (collapseOrbitEquiv p h)
  have hc := Fintype.card_subtype_compl (p := fun q : Orbit p => q = Quotient.mk _ b)
  have hp : 0 < Fintype.card (Orbit p) := Fintype.card_pos_iff.mpr ⟨Quotient.mk _ b⟩
  simp only [Fintype.card_unique] at hc
  rw [card_orbit] at hp
  rw [card_orbit] at he hc
  have hc' : Fintype.card {q : Orbit p // q ≠ Quotient.mk _ b} = totalCycles p - 1 := by
    calc
      _ = Fintype.card {q : Orbit p // ¬ q = Quotient.mk _ b} := Fintype.card_congr (Equiv.refl _)
      _ = _ := hc
  omega

def orbitEquivOfSameCycles (p q : Perm α)
    (h : ∀ x y, p.SameCycle x y ↔ q.SameCycle x y) : Orbit p ≃ Orbit q where
  toFun := Quotient.map id (fun {x y} hxy => (h x y).mp hxy)
  invFun := Quotient.map id (fun {x y} hxy => (h x y).mpr hxy)
  left_inv z := Quotient.inductionOn z (fun _ => rfl)
  right_inv z := Quotient.inductionOn z (fun _ => rfl)

theorem totalCycles_ne_mul_swap (p : Perm α) {a b : α} (hab : a ≠ b) :
    totalCycles (p * swap a b) ≠ totalCycles p := by
  intro he
  have hs : (p * swap a b).sign = p.sign := by
    rw [sign_totalCycles, sign_totalCycles, he]
  rw [Equiv.Perm.sign_mul, sign_swap hab] at hs
  have bad : (-1 : ℤˣ) = 1 := mul_left_cancel (show p.sign * (-1) = p.sign * 1 by simpa using hs)
  norm_num at bad

theorem not_sameCycle_mul_swap_of_sameCycle (p : Perm α) {a b : α} (hab : a ≠ b)
    (h : p.SameCycle a b) : ¬ (p * swap a b).SameCycle a b := by
  intro ht
  have hback : (p * swap a b * swap a b).SameCycle a b := by simpa [mul_assoc] using h
  have he : ∀ x y, p.SameCycle x y ↔ (p * swap a b).SameCycle x y := by
    intro x y
    constructor
    · exact sameCycle_le_mul_swap p ht
    · intro hxy
      simpa [mul_assoc] using sameCycle_le_mul_swap (p * swap a b) hback hxy
  have hc := Fintype.card_congr (orbitEquivOfSameCycles p (p * swap a b) he)
  rw [card_orbit, card_orbit] at hc
  exact totalCycles_ne_mul_swap p hab hc.symm

theorem totalCycles_mul_swap_of_sameCycle (p : Perm α) {a b : α} (hab : a ≠ b)
    (h : p.SameCycle a b) : totalCycles (p * swap a b) = totalCycles p + 1 := by
  have ht := totalCycles_mul_swap_of_not_sameCycle (p * swap a b)
    (not_sameCycle_mul_swap_of_sameCycle p hab h)
  simpa [mul_assoc] using ht.symm

theorem totalCycles_le_mul_swap_add_one (p : Perm α) (a b : α) :
    totalCycles p ≤ totalCycles (p * swap a b) + 1 := by
  by_cases hab : a = b
  · subst b
    have hp : p * swap a a = p := by ext x; simp
    rw [hp]
    omega
  by_cases h : p.SameCycle a b
  · rw [totalCycles_mul_swap_of_sameCycle p hab h]
    omega
  · exact (totalCycles_mul_swap_of_not_sameCycle p h).ge

end JSP623.PermutationSurgery
