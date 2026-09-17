import ErdosProblems.Erdos759
import DeletionCycles

/-! Transport of rotation systems along embeddings containing every nonisolated vertex. -/

noncomputable section

namespace Erdos759.SimpleGraph

open _root_.SimpleGraph Equiv

attribute [local instance] Classical.propDecidable Classical.decEq

private theorem formPerm_map_apply {α β : Type*} (f : α → β)
    (hf : Function.Injective f) (l : List α) (x : α) :
    (l.map f).formPerm (f x) = f (l.formPerm x) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases l with
    | nil => simp
    | cons b l =>
      simp only [List.map_cons, List.formPerm_cons_cons, Perm.mul_apply]
      simp only [List.map_cons] at ih
      rw [ih, ← hf.map_swap]

namespace RotationSystem

variable {V W : Type*} {G : SimpleGraph V}

/-- An embedding contains the endpoint of every edge. -/
def CoversEdges (G : SimpleGraph V) (f : W ↪ V) : Prop :=
  ∀ v w, G.Adj v w → ∃ u, f u = v

private def neighborPreimage (R : RotationSystem G) (f : W ↪ V)
    (hcover : CoversEdges G f) (u : W) (v : {v // v ∈ R.order (f u)}) : W :=
  Classical.choose (hcover v.1 (f u) ((R.mem_order_iff _ _).mp v.2).symm)

private theorem neighborPreimage_spec (R : RotationSystem G) (f : W ↪ V)
    (hcover : CoversEdges G f) (u : W) (v : {v // v ∈ R.order (f u)}) :
    f (neighborPreimage R f hcover u v) = v.1 :=
  Classical.choose_spec (hcover v.1 (f u) ((R.mem_order_iff _ _).mp v.2).symm)

private def pullbackOrder (R : RotationSystem G) (f : W ↪ V)
    (hcover : CoversEdges G f) (u : W) : List W :=
  (R.order (f u)).attach.map (neighborPreimage R f hcover u)

private theorem map_pullbackOrder (R : RotationSystem G) (f : W ↪ V)
    (hcover : CoversEdges G f) (u : W) :
    (pullbackOrder R f hcover u).map f = R.order (f u) := by
  unfold pullbackOrder
  rw [List.map_map]
  have h : (fun v : {v // v ∈ R.order (f u)} =>
      f (neighborPreimage R f hcover u v)) = Subtype.val := by
    funext v
    exact neighborPreimage_spec R f hcover u v
  simp only [Function.comp_def, h]
  simp

/-- Pull back the cyclic neighbor lists; covering all edge endpoints makes every list exact. -/
def pullback (R : RotationSystem G) (f : W ↪ V) (hcover : CoversEdges G f) :
    RotationSystem (G.comap f) where
  order := pullbackOrder R f hcover
  nodup_order u := by
    have h := R.nodup_order (f u)
    rw [← map_pullbackOrder R f hcover u] at h
    exact List.Nodup.of_map _ h
  mem_order_iff u v := by
    change v ∈ pullbackOrder R f hcover u ↔ G.Adj (f u) (f v)
    rw [← R.mem_order_iff, ← map_pullbackOrder R f hcover u]
    exact (List.mem_map_of_injective f.injective).symm

@[simp] theorem map_pullback_order (R : RotationSystem G) (f : W ↪ V)
    (hcover : CoversEdges G f) (u : W) :
    ((R.pullback f hcover).order u).map f = R.order (f u) :=
  map_pullbackOrder R f hcover u

theorem pullback_next (R : RotationSystem G) (f : W ↪ V)
    (hcover : CoversEdges G f) (u v : W) :
    f ((R.pullback f hcover).next u v) = R.next (f u) (f v) := by
  unfold next
  rw [← map_pullback_order R f hcover u]
  exact (formPerm_map_apply f f.injective _ _).symm

/-- The darts of the pullback and of the original graph correspond bijectively. -/
def dartEquivPullback (f : W ↪ V) (hcover : CoversEdges G f) :
    (G.comap f).Dart ≃ G.Dart :=
  Equiv.ofBijective (fun d => ⟨(f d.fst, f d.snd), d.adj⟩) (by
    constructor
    · intro a b h
      apply Dart.ext
      apply Prod.ext
      · exact f.injective (congrArg (fun d : G.Dart => d.fst) h)
      · exact f.injective (congrArg (fun d : G.Dart => d.snd) h)
    · intro d
      obtain ⟨u, hu⟩ := hcover d.fst d.snd d.adj
      obtain ⟨v, hv⟩ := hcover d.snd d.fst d.adj.symm
      refine ⟨⟨(u, v), ?_⟩, ?_⟩
      · change G.Adj (f u) (f v)
        simp [hu, hv, d.adj]
      · apply Dart.ext
        exact Prod.ext hu hv)

@[simp] theorem dartEquivPullback_fst (f : W ↪ V) (hcover : CoversEdges G f)
    (d : (G.comap f).Dart) : (dartEquivPullback f hcover d).fst = f d.fst := rfl

@[simp] theorem dartEquivPullback_snd (f : W ↪ V) (hcover : CoversEdges G f)
    (d : (G.comap f).Dart) : (dartEquivPullback f hcover d).snd = f d.snd := rfl

theorem pullback_facePerm (R : RotationSystem G) (f : W ↪ V)
    (hcover : CoversEdges G f) (d : (G.comap f).Dart) :
    dartEquivPullback f hcover ((R.pullback f hcover).facePerm d) =
      R.facePerm (dartEquivPullback f hcover d) := by
  apply Dart.ext
  apply Prod.ext
  · rfl
  · exact pullback_next R f hcover d.snd d.fst

theorem pullback_facePerm_conjugate (R : RotationSystem G) (f : W ↪ V)
    (hcover : CoversEdges G f) :
    (dartEquivPullback f hcover).symm.trans
      ((R.pullback f hcover).facePerm.trans (dartEquivPullback f hcover)) =
        R.facePerm := by
  apply Equiv.ext
  intro d
  change dartEquivPullback f hcover
    ((R.pullback f hcover).facePerm ((dartEquivPullback f hcover).symm d)) = R.facePerm d
  simpa using pullback_facePerm R f hcover ((dartEquivPullback f hcover).symm d)

variable [Fintype V] [Fintype W]

/-- Pullback preserves all face cycles; face permutations have no fixed darts. -/
theorem pullback_face_cycle_count (R : RotationSystem G) (f : W ↪ V)
    (hcover : CoversEdges G f) :
    (R.pullback f hcover).facePerm.cycleType.card = R.facePerm.cycleType.card := by
  have h := JSP623.PermutationSurgery.totalCycles_equiv
    (dartEquivPullback f hcover) (R.pullback f hcover).facePerm
  rw [pullback_facePerm_conjugate] at h
  haveI : IsEmpty {d : G.Dart // R.facePerm d = d} :=
    ⟨fun d => R.facePerm_ne d.val d.property⟩
  haveI : IsEmpty {d : (G.comap f).Dart // (R.pullback f hcover).facePerm d = d} :=
    ⟨fun d => (R.pullback f hcover).facePerm_ne d.val d.property⟩
  simp only [JSP623.PermutationSurgery.totalCycles, Fintype.card_of_isEmpty,
    Nat.add_zero] at h
  convert h.symm using 1 <;> congr 2

end RotationSystem

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- Relabeling vertices by an equivalence preserves ordinary orientable embeddability. -/
theorem embedsOrientable_comap_equiv [Fintype V] [Fintype W]
    (e : W ≃ V) (g : ℕ) (hG : EmbedsOrientable G g) :
    EmbedsOrientable (G.comap e) g := by
  obtain ⟨R, hR⟩ := hG
  have hcover : RotationSystem.CoversEdges G e.toEmbedding := by
    intro v w h
    exact ⟨e.symm v, e.apply_symm_apply v⟩
  let i : G.comap e ≃g G := { e with map_rel_iff' := by intros; rfl }
  have hc : componentCount (G.comap e) = componentCount G :=
    Fintype.card_congr i.connectedComponentEquiv
  have he : (G.comap e).edgeFinset.card = G.edgeFinset.card := i.card_edgeFinset_eq
  have hv : Fintype.card W = Fintype.card V := Fintype.card_congr e
  let ei : {v : W // ∀ w, ¬ (G.comap e).Adj v w} ≃
      {v : V // ∀ w, ¬ G.Adj v w} :=
    e.subtypeEquiv (by
      intro v
      constructor
      · intro h w hw
        exact h (e.symm w) (by simpa using hw)
      · exact fun h w => h (e w))
  have hi : isolateCount (G.comap e) = isolateCount G := by
    simpa only [isolateCount, ← Fintype.card_subtype] using Fintype.card_congr ei
  refine ⟨R.pullback e.toEmbedding hcover, ?_⟩
  have hf := R.pullback_face_cycle_count e.toEmbedding hcover
  dsimp only [faceCount] at hR ⊢
  rw [hc, he, hv, hi]
  convert hR using 1
  congr 2
  congr 1

theorem Iso.embedsOrientable [Fintype V] [Fintype W]
    (e : G ≃g H) (g : ℕ) (h : EmbedsOrientable G g) : EmbedsOrientable H g := by
  have heq : G.comap e.symm.toEquiv = H := by
    ext u v
    exact e.symm.map_adj_iff
  have ht := embedsOrientable_comap_equiv e.symm.toEquiv g h
  simpa only [heq] using ht

theorem Iso.embedsOrientable_iff [Fintype V] [Fintype W]
    (e : G ≃g H) (g : ℕ) : EmbedsOrientable G g ↔ EmbedsOrientable H g :=
  ⟨Iso.embedsOrientable e g, Iso.embedsOrientable e.symm g⟩

end Erdos759.SimpleGraph

#print axioms Erdos759.SimpleGraph.RotationSystem.pullback_face_cycle_count
#print axioms Erdos759.SimpleGraph.Iso.embedsOrientable_iff
