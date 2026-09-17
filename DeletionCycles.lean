import PermutationCycleSurgery

/-! # Deleting one point of a finite permutation

The induced permutation skips the deleted point along its cycle. Fixed points
are counted as cycles throughout.
-/

noncomputable section
open Equiv Equiv.Perm
namespace JSP623.PermutationSurgery

attribute [local instance] Classical.propDecidable Classical.decEq

variable {α : Type*} [Fintype α]

omit [Fintype α] in
theorem totalCycles_fintype_irrel (p : Perm α) (i j : Fintype α) :
    @totalCycles α i p = @totalCycles α j p :=
  congrArg (fun k : Fintype α => @totalCycles α k p) (Subsingleton.elim i j)

/-- Restrict a permutation after removing one of its fixed points. -/
def deleteFixedPoint (p : Perm α) (a : α) (ha : p a = a) : Perm {x : α // x ≠ a} :=
  p.subtypePerm (by
    intro x
    constructor
    · intro hx hxa
      exact hx (hxa ▸ ha)
    · intro hx hpx
      exact hx (p.injective (hpx.trans ha.symm)))

omit [Fintype α] in
@[simp]
theorem deleteFixedPoint_apply (p : Perm α) (a : α) (ha : p a = a)
    (x : {x : α // x ≠ a}) : (deleteFixedPoint p a ha x).val = p x := rfl

def fixedDeletionOrbitMap (p : Perm α) (a : α) (ha : p a = a) :
    Orbit (deleteFixedPoint p a ha) → Orbit p :=
  Quotient.map Subtype.val (by
    intro x y h
    exact (sameCycle_subtypePerm).mp h)

omit [Fintype α] in
theorem fixedDeletionOrbitMap_injective (p : Perm α) (a : α) (ha : p a = a) :
    Function.Injective (fixedDeletionOrbitMap p a ha) := by
  intro q r
  refine Quotient.inductionOn₂ q r ?_
  intro x y h
  exact Quotient.sound (sameCycle_subtypePerm.mpr (Quotient.exact h))

omit [Fintype α] in
theorem fixedDeletionOrbitMap_ne (p : Perm α) (a : α) (ha : p a = a)
    (q : Orbit (deleteFixedPoint p a ha)) :
    fixedDeletionOrbitMap p a ha q ≠ Quotient.mk (SameCycle.setoid p) a := by
  refine Quotient.inductionOn q ?_
  intro x h
  exact x.property ((Quotient.exact h).eq_of_right ha)

def fixedDeletionOrbitEquiv (p : Perm α) (a : α) (ha : p a = a) :
    Orbit (deleteFixedPoint p a ha) ≃
      {q : Orbit p // q ≠ Quotient.mk (SameCycle.setoid p) a} :=
  Equiv.ofBijective
    (fun q => ⟨fixedDeletionOrbitMap p a ha q, fixedDeletionOrbitMap_ne p a ha q⟩)
    (by
      constructor
      · intro q r h
        exact fixedDeletionOrbitMap_injective p a ha (congrArg Subtype.val h)
      · rintro ⟨q, hq⟩
        induction q using Quotient.inductionOn with
        | h x =>
          have hx : x ≠ a := by
            intro he
            exact hq (he ▸ rfl)
          exact ⟨Quotient.mk _ ⟨x, hx⟩, rfl⟩)

/-- Removing a fixed point removes exactly one cycle, including in a singleton type. -/
theorem totalCycles_deleteFixedPoint (p : Perm α) (a : α) (ha : p a = a) :
    totalCycles (deleteFixedPoint p a ha) + 1 = totalCycles p := by
  rw [← card_orbit, ← card_orbit, Fintype.card_congr (fixedDeletionOrbitEquiv p a ha)]
  have h := Fintype.card_subtype_compl
    (fun q : Orbit p => q = Quotient.mk (SameCycle.setoid p) a)
  simp only [Fintype.card_subtype_eq] at h
  have hpos : 0 < Fintype.card (Orbit p) :=
    Fintype.card_pos_iff.mpr ⟨Quotient.mk (SameCycle.setoid p) a⟩
  calc
    _ = (Fintype.card (Orbit p) - 1) + 1 := congrArg (fun n => n + 1) h
    _ = _ := by omega

/-- Make `a` a fixed point while joining its predecessor directly to its successor. -/
def isolatePoint (p : Perm α) (a : α) : Perm α := p * swap a (p.symm a)

omit [Fintype α] in
@[simp]
theorem isolatePoint_apply_self (p : Perm α) (a : α) : isolatePoint p a a = a := by
  simp [isolatePoint]

/-- First return to the complement of one point. At most one point is skipped. -/
def deleteCyclePerm (p : Perm α) (a : α) : Perm {x : α // x ≠ a} :=
  deleteFixedPoint (isolatePoint p a) a (isolatePoint_apply_self p a)

omit [Fintype α] in
theorem deleteCyclePerm_apply_of_ne (p : Perm α) (a : α)
    (x : {x : α // x ≠ a}) (hx : p x ≠ a) :
    (deleteCyclePerm p a x).val = p x := by
  have hxpre : x.val ≠ p.symm a := by
    intro h
    exact hx (h ▸ p.apply_symm_apply a)
  simp [deleteCyclePerm, isolatePoint, mul_apply,
    swap_apply_of_ne_of_ne x.property hxpre]

omit [Fintype α] in
theorem deleteCyclePerm_apply_of_eq (p : Perm α) (a : α)
    (x : {x : α // x ≠ a}) (hx : p x = a) :
    (deleteCyclePerm p a x).val = p a := by
  have hxpre : x.val = p.symm a := p.eq_symm_apply.mpr hx
  simp [deleteCyclePerm, isolatePoint, mul_apply, hxpre]

omit [Fintype α] in
theorem deleteCyclePerm_apply (p : Perm α) (a : α) (x : {x : α // x ≠ a}) :
    (deleteCyclePerm p a x).val = if p x = a then p a else p x := by
  split_ifs with hx
  · exact deleteCyclePerm_apply_of_eq p a x hx
  · exact deleteCyclePerm_apply_of_ne p a x hx

theorem totalCycles_deleteCyclePerm_add_one (p : Perm α) (a : α) :
    totalCycles (deleteCyclePerm p a) + 1 = totalCycles (p * swap a (p.symm a)) :=
  totalCycles_deleteFixedPoint (isolatePoint p a) a (isolatePoint_apply_self p a)

theorem totalCycles_deleteCyclePerm_of_fixed (p : Perm α) (a : α) (ha : p a = a) :
    totalCycles (deleteCyclePerm p a) + 1 = totalCycles p := by
  have hpre : p.symm a = a := (p.symm_apply_eq).mpr ha.symm
  have hs : swap a a = (1 : Perm α) := swap_self a
  simpa only [hpre, hs, mul_one] using totalCycles_deleteCyclePerm_add_one p a

/-- Deleting a point from a nontrivial cycle shortens that cycle without removing it. -/
theorem totalCycles_deleteCyclePerm_of_not_fixed (p : Perm α) (a : α) (ha : p a ≠ a) :
    totalCycles (deleteCyclePerm p a) = totalCycles p := by
  have hne : a ≠ p.symm a := by
    intro h
    exact ha ((congrArg p h).trans (p.apply_symm_apply a))
  have hsame : p.SameCycle a (p.symm a) := SameCycle.rfl.symm_apply_right
  have hsplit := totalCycles_mul_swap_of_sameCycle p hne hsame
  have hdelete := totalCycles_deleteCyclePerm_add_one p a
  omega

/-- The all-cycles count loses exactly the singleton cycle, when there is one. -/
theorem totalCycles_deleteCyclePerm (p : Perm α) (a : α) :
    totalCycles (deleteCyclePerm p a) + (if p a = a then 1 else 0) = totalCycles p := by
  by_cases ha : p a = a
  · simpa [ha] using totalCycles_deleteCyclePerm_of_fixed p a ha
  · simpa [ha] using totalCycles_deleteCyclePerm_of_not_fixed p a ha

variable {β : Type*} [Fintype β]

/-- Relabeling a finite permutation preserves the number of all its cycles. -/
theorem totalCycles_equiv (e : α ≃ β) (p : Perm α) :
    totalCycles (e.symm.trans (p.trans e)) = totalCycles p := by
  let q : Perm β := e.symm.trans (p.trans e)
  let f : Orbit p → Orbit q := Quotient.map e (by
    intro x y h
    apply sameCycle_of_step (p := q) (q := e.symm.trans (p.trans e))
      (fun _ => SameCycle.rfl.apply_right)
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    refine ⟨(n : ℤ), ?_⟩
    have hp : ∀ k : ℕ, (q ^ k) (e x) = e ((p ^ k) x) := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => simp [pow_succ', mul_apply, ih, q]
    simpa using (hp n).trans (congrArg e hn))
  have hf : Function.Bijective f := by
    constructor
    · intro x y
      refine Quotient.inductionOn₂ x y ?_
      intro x y h
      obtain ⟨n, hn⟩ := (Quotient.exact h).exists_nat_pow_eq
      apply Quotient.sound
      refine ⟨(n : ℤ), ?_⟩
      have hp : ∀ k : ℕ, (q ^ k) (e x) = e ((p ^ k) x) := by
        intro k
        induction k with
        | zero => rfl
        | succ k ih => simp [pow_succ', mul_apply, ih, q]
      exact_mod_cast e.injective ((hp n).symm.trans hn)
    · intro y
      refine Quotient.inductionOn y ?_
      intro y
      exact ⟨Quotient.mk _ (e.symm y), by simp [f]⟩
  simpa only [card_orbit] using (Fintype.card_congr (Equiv.ofBijective f hf)).symm

/-- Flatten the two nested complements used when deleting distinct points. -/
def deleteTwoEquiv (a b : α) (hab : a ≠ b) :
    {x : {x : α // x ≠ a} // x ≠ ⟨b, hab.symm⟩} ≃
      {x : α // x ≠ a ∧ x ≠ b} where
  toFun x := ⟨x.val.val, x.val.property, fun h => x.property (Subtype.ext h)⟩
  invFun x := ⟨⟨x.val, x.property.1⟩, fun h => x.property.2 (congrArg Subtype.val h)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- First return after deleting two distinct points, implemented by successive deletion. -/
def deleteTwoPerm (p : Perm α) (a b : α) (hab : a ≠ b) :
    Perm {x : α // x ≠ a ∧ x ≠ b} :=
  (deleteTwoEquiv a b hab).symm.trans
    ((deleteCyclePerm (deleteCyclePerm p a) ⟨b, hab.symm⟩).trans (deleteTwoEquiv a b hab))

omit [Fintype α] in
theorem deleteCyclePerm_fixed_iff (p : Perm α) {a b : α} (hab : a ≠ b)
    (hnoTwo : ¬ (p a = b ∧ p b = a)) :
    deleteCyclePerm p a ⟨b, hab.symm⟩ = ⟨b, hab.symm⟩ ↔ p b = b := by
  rw [Subtype.ext_iff, deleteCyclePerm_apply]
  by_cases hba : p b = a
  · simp only [hba, ↓reduceIte]
    constructor
    · intro h
      exact (hnoTwo ⟨h, hba⟩).elim
    · intro h
      exact (hab h).elim
  · simp [hba]

/-- If the deleted pair is not an entire 2-cycle, only its singleton cycles disappear. -/
theorem totalCycles_deleteTwoPerm (p : Perm α) (a b : α) (hab : a ≠ b)
    (hnoTwo : ¬ (p a = b ∧ p b = a)) :
    totalCycles (deleteTwoPerm p a b hab) +
      (if p a = a then 1 else 0) + (if p b = b then 1 else 0) = totalCycles p := by
  have hfirst := totalCycles_deleteCyclePerm p a
  have hsecond := totalCycles_deleteCyclePerm (deleteCyclePerm p a) ⟨b, hab.symm⟩
  simp only [deleteCyclePerm_fixed_iff p hab hnoTwo] at hsecond
  rw [deleteTwoPerm, totalCycles_equiv]
  calc
    _ = (totalCycles (deleteCyclePerm (deleteCyclePerm p a) ⟨b, hab.symm⟩) +
          (if p b = b then 1 else 0)) + (if p a = a then 1 else 0) := by omega
    _ = totalCycles (deleteCyclePerm p a) + (if p a = a then 1 else 0) := by
      convert congrArg (fun n => n + (if p a = a then 1 else 0)) hsecond using 1
      apply congrArg (fun n : ℕ => (n + (if p b = b then 1 else 0)) +
        (if p a = a then 1 else 0))
      exact totalCycles_fintype_irrel _ _ _
    _ = totalCycles p := hfirst

omit [Fintype α] in
theorem deleteTwoPerm_apply (p : Perm α) (a b : α) (hab : a ≠ b)
    (x : {x : α // x ≠ a ∧ x ≠ b}) :
    (deleteTwoPerm p a b hab x).val =
      if (if p x = a then p a else p x) = b then
        (if p b = a then p a else p b)
      else (if p x = a then p a else p x) := by
  let x' : {x : {x : α // x ≠ a} // x ≠ ⟨b, hab.symm⟩} :=
    (deleteTwoEquiv a b hab).symm x
  have hx' : x'.val.val = x.val := rfl
  change ((deleteCyclePerm (deleteCyclePerm p a) ⟨b, hab.symm⟩ x').val).val = _
  rw [deleteCyclePerm_apply]
  by_cases h : deleteCyclePerm p a x'.val = ⟨b, hab.symm⟩
  · simp only [h, ↓reduceIte]
    have hv : (if p x.val = a then p a else p x.val) = b := by
      have hh := congrArg Subtype.val h
      simpa only [deleteCyclePerm_apply, hx'] using hh
    simp only [hv, ↓reduceIte]
    exact deleteCyclePerm_apply p a ⟨b, hab.symm⟩
  · simp only [h, ↓reduceIte]
    have hv : ¬ (if p x.val = a then p a else p x.val) = b := by
      intro he
      apply h
      apply Subtype.ext
      simpa only [deleteCyclePerm_apply, hx'] using he
    simp only [hv, ↓reduceIte]
    exact deleteCyclePerm_apply p a x'.val

omit [Fintype α] in
theorem deleteTwoPerm_apply_of_ne (p : Perm α) (a b : α) (hab : a ≠ b)
    (x : {x : α // x ≠ a ∧ x ≠ b}) (hxa : p x ≠ a) (hxb : p x ≠ b) :
    (deleteTwoPerm p a b hab x).val = p x := by
  simp [deleteTwoPerm_apply, hxa, hxb]

end JSP623.PermutationSurgery
