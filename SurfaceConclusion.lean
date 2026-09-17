import EmbeddingHereditary

/-!
# The cochromatic maximum for ordinary orientable embeddings

The Gimbel--Thomassen asymptotic theorem is expressed here using a single
rotation system witnessing an ordinary embedding.  Closure under restriction
and relabeling is supplied by the proved embedding heredity theorem.
-/

noncomputable section

namespace Erdos759.SimpleGraph

open _root_.SimpleGraph Erdos760.SimpleGraph Filter
open scoped Topology

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Cochromatic numbers of finite graphs having an ordinary orientable
embedding of genus at most `g`. -/
def ordinarySurfaceCochromaticValues (g : ℕ) : Set ℕ :=
  {k | ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
    EmbedsOrientable G g ∧ cochromaticNat G = k}

/-- The extremal value is defined directly from ordinary embeddings. -/
def ordinaryZSurface (g : ℕ) : ℕ :=
  sSup (ordinarySurfaceCochromaticValues g)

theorem ordinarySurfaceCochromaticValues_eq (g : ℕ) :
    ordinarySurfaceCochromaticValues g = surfaceCochromaticValues g := by
  ext k
  constructor
  · rintro ⟨n, G, hemb, hk⟩
    refine ⟨n, G, ?_, hk⟩
    apply EmbedsOrientable.hereditary
    exact (embedsOrientable_instances G g _ _ _ _ _ _).mp hemb
  · rintro ⟨n, G, hemb, hk⟩
    exact ⟨n, G, (embedsOrientable_instances G g _ _ _ _ _ _).mp
      hemb.embedsOrientable, hk⟩

theorem ordinaryZSurface_eq_zSurface (g : ℕ) :
    ordinaryZSurface g = zSurface g := by
  simp only [ordinaryZSurface, zSurface, ordinarySurfaceCochromaticValues_eq]

theorem ordinarySurfaceCochromaticValues_nonempty (g : ℕ) :
    (ordinarySurfaceCochromaticValues g).Nonempty := by
  rw [ordinarySurfaceCochromaticValues_eq]
  exact surfaceCochromaticValues_nonempty g

theorem ordinarySurfaceCochromaticValues_bddAbove (g : ℕ) :
    BddAbove (ordinarySurfaceCochromaticValues g) := by
  rw [ordinarySurfaceCochromaticValues_eq]
  exact surfaceCochromaticValues_bddAbove g

theorem cochromaticNat_le_ordinaryZSurface {n g : ℕ} {G : SimpleGraph (Fin n)}
    (hemb : EmbedsOrientable G g) : cochromaticNat G ≤ ordinaryZSurface g := by
  apply le_csSup (ordinarySurfaceCochromaticValues_bddAbove g)
  exact ⟨n, G, hemb, rfl⟩

/-- The supremum is attained by a finite graph with an ordinary embedding. -/
theorem exists_graph_cochromaticNat_eq_ordinaryZSurface (g : ℕ) :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
      EmbedsOrientable G g ∧ cochromaticNat G = ordinaryZSurface g := by
  exact Nat.sSup_mem (ordinarySurfaceCochromaticValues_nonempty g)
    (ordinarySurfaceCochromaticValues_bddAbove g)

theorem ordinaryZSurface_isGreatest (g : ℕ) :
    IsGreatest (ordinarySurfaceCochromaticValues g) (ordinaryZSurface g) := by
  refine ⟨exists_graph_cochromaticNat_eq_ordinaryZSurface g, ?_⟩
  rintro k ⟨n, G, hemb, rfl⟩
  exact cochromaticNat_le_ordinaryZSurface hemb

/-- A finite bound at every genus, including genus zero. -/
theorem ordinaryZSurface_le_seven_add_twelve_mul_genus (g : ℕ) :
    ordinaryZSurface g ≤ 7 + 12 * g := by
  obtain ⟨n, G, hemb, hmax⟩ := exists_graph_cochromaticNat_eq_ordinaryZSurface g
  rw [← hmax]
  apply cochromaticNat_le_seven_add_twelve_mul_genus G
  apply EmbedsOrientable.hereditary
  exact (embedsOrientable_instances G g _ _ _ _ _ _).mp hemb

theorem ordinaryZSurface_mono {g h : ℕ} (hgh : g ≤ h) :
    ordinaryZSurface g ≤ ordinaryZSurface h := by
  simpa only [ordinaryZSurface_eq_zSurface] using zSurface_mono hgh

/-- Explicit absolute constants in the eventual two-sided estimate. -/
theorem ordinary_surface_cochromatic_eventual_bounds :
    ∀ᶠ g : ℕ in atTop,
      (1 / 256 : ℝ) * (Real.sqrt (g : ℝ) / Real.log (g : ℝ)) ≤
          (ordinaryZSurface g : ℝ) ∧
        (ordinaryZSurface g : ℝ) ≤
          236628 * (Real.sqrt (g : ℝ) / Real.log (g : ℝ)) := by
  simpa only [ordinaryZSurface_eq_zSurface, erdos759Scale] using erdos759_eventual_bounds

/-- **JSP-000623 / Erdős Problem 759 (Gimbel--Thomassen).** The maximum
cochromatic number over all finite graphs ordinarily embeddable in an
orientable surface of genus `g` has order `sqrt(g) / log(g)`. -/
theorem ordinary_surface_cochromatic_theta :
    (fun g : ℕ => (ordinaryZSurface g : ℝ)) =Θ[atTop]
      (fun g : ℕ => Real.sqrt (g : ℝ) / Real.log (g : ℝ)) := by
  change (fun g : ℕ => (ordinaryZSurface g : ℝ)) =Θ[atTop] erdos759Scale
  simpa only [ordinaryZSurface_eq_zSurface] using erdos_759

end Erdos759.SimpleGraph

#print axioms Erdos759.SimpleGraph.ordinarySurfaceCochromaticValues_eq
#print axioms Erdos759.SimpleGraph.ordinaryZSurface_isGreatest
#print axioms Erdos759.SimpleGraph.ordinary_surface_cochromatic_eventual_bounds
#print axioms Erdos759.SimpleGraph.ordinary_surface_cochromatic_theta
