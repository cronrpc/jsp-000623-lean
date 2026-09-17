import ErdosProblems.Erdos759

/-! Exact edge and component counts after deleting one genuine edge. -/

noncomputable section
open _root_.SimpleGraph
namespace Erdos759.SimpleGraph
attribute [local instance] Classical.propDecidable Classical.decEq

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem edgeCount_delete_dart (d : G.Dart) :
    (G.deleteEdges {d.edge}).edgeFinset.card + 1 = G.edgeFinset.card := by
  have hd : d.edge ∈ G.edgeFinset := by simpa using d.edge_mem
  have he : (G.deleteEdges {d.edge}).edgeFinset = G.edgeFinset.erase d.edge := by
    ext e
    simp [edgeSet_deleteEdges]
    tauto
  rw [he]
  exact Finset.card_erase_add_one hd

def componentCollapse (d : G.Dart) (x : V) : (G.deleteEdges {d.edge}).ConnectedComponent :=
  if (G.deleteEdges {d.edge}).Reachable d.snd x
  then (G.deleteEdges {d.edge}).connectedComponentMk d.fst
  else (G.deleteEdges {d.edge}).connectedComponentMk x

theorem componentCollapse_eq_of_reachable (d : G.Dart) {x y : V}
    (h : (G.deleteEdges {d.edge}).Reachable x y) :
    componentCollapse d x = componentCollapse d y := by
  have he : (G.deleteEdges {d.edge}).Reachable d.snd x ↔
      (G.deleteEdges {d.edge}).Reachable d.snd y :=
    ⟨fun hx => hx.trans h, fun hy => hy.trans h.symm⟩
  unfold componentCollapse
  simp only [he]
  split_ifs
  · rfl
  · exact ConnectedComponent.sound h

theorem componentCollapse_endpoints (d : G.Dart) :
    componentCollapse d d.fst = componentCollapse d d.snd := by
  unfold componentCollapse
  simp only [Reachable.rfl, ite_true]
  split_ifs with h
  · rfl
  · rfl

theorem componentCollapse_eq_of_adj (d : G.Dart) {x y : V} (h : G.Adj x y) :
    componentCollapse d x = componentCollapse d y := by
  by_cases he : s(x, y) = d.edge
  · change s(x, y) = s(d.fst, d.snd) at he
    rcases Sym2.eq_iff.mp he with hxy | hxy
    · rcases hxy with ⟨rfl, rfl⟩
      exact componentCollapse_endpoints d
    · rcases hxy with ⟨rfl, rfl⟩
      exact (componentCollapse_endpoints d).symm
  · exact componentCollapse_eq_of_reachable d (deleteEdges_adj.mpr ⟨h, he⟩).reachable

theorem componentCollapse_eq_of_original_reachable (d : G.Dart) {x y : V}
    (h : G.Reachable x y) : componentCollapse d x = componentCollapse d y := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | cons hadj p ih => exact (componentCollapse_eq_of_adj d hadj).trans ih

theorem componentCollapse_eq_iff (d : G.Dart) (x y : V) :
    componentCollapse d x = componentCollapse d y ↔ G.Reachable x y := by
  constructor
  · intro he
    have liftReach {x y : V} (h : (G.deleteEdges {d.edge}).Reachable x y) :
        G.Reachable x y := h.mono (G.deleteEdges_le _)
    unfold componentCollapse at he
    split_ifs at he with hx hy hy
    · exact liftReach (hx.symm.trans hy)
    · exact ((liftReach hx.symm).trans d.adj.symm.reachable).trans
        (liftReach (ConnectedComponent.exact he))
    · exact ((liftReach (ConnectedComponent.exact he)).trans d.adj.reachable).trans
        (liftReach hy)
    · exact liftReach (ConnectedComponent.exact he)
  · exact componentCollapse_eq_of_original_reachable d

theorem componentCollapse_ne_of_isBridge (d : G.Dart) (hb : G.IsBridge d.edge) (x : V) :
    componentCollapse d x ≠ (G.deleteEdges {d.edge}).connectedComponentMk d.snd := by
  unfold componentCollapse
  split_ifs with hx
  · exact fun he => hb (ConnectedComponent.exact he)
  · exact fun he => hx (ConnectedComponent.exact he).symm

def componentDeleteBridgeEquiv (d : G.Dart) (hb : G.IsBridge d.edge) :
    G.ConnectedComponent ≃
      {q : (G.deleteEdges {d.edge}).ConnectedComponent //
        q ≠ (G.deleteEdges {d.edge}).connectedComponentMk d.snd} :=
  Equiv.ofBijective
    (Quot.lift (fun x => ⟨componentCollapse d x, componentCollapse_ne_of_isBridge d hb x⟩)
      (fun x y hxy => Subtype.ext (componentCollapse_eq_of_original_reachable d hxy))) (by
        constructor
        · intro q r
          refine ConnectedComponent.ind₂ ?_ q r
          intro x y he
          exact ConnectedComponent.sound ((componentCollapse_eq_iff d x y).mp
            (congrArg Subtype.val he))
        · rintro ⟨q, hq⟩
          obtain ⟨x, rfl⟩ := Quot.exists_rep q
          have hx : ¬ (G.deleteEdges {d.edge}).Reachable d.snd x :=
            fun hx => hq (ConnectedComponent.sound hx.symm)
          exact ⟨G.connectedComponentMk x, Subtype.ext (if_neg hx)⟩)

theorem componentCount_delete_bridge (d : G.Dart) (hb : G.IsBridge d.edge) :
    componentCount (G.deleteEdges {d.edge}) = componentCount G + 1 := by
  let H := G.deleteEdges {d.edge}
  have he := Fintype.card_congr (componentDeleteBridgeEquiv d hb)
  have hc := Fintype.card_subtype_compl (p := fun q : H.ConnectedComponent =>
    q = H.connectedComponentMk d.snd)
  have hp : 0 < Fintype.card H.ConnectedComponent :=
    Fintype.card_pos_iff.mpr ⟨H.connectedComponentMk d.snd⟩
  simp only [Fintype.card_unique] at hc
  have hc' : Fintype.card {q : H.ConnectedComponent // q ≠ H.connectedComponentMk d.snd} =
      Fintype.card H.ConnectedComponent - 1 := by
    calc
      _ = Fintype.card {q : H.ConnectedComponent // ¬ q = H.connectedComponentMk d.snd} :=
        Fintype.card_congr (Equiv.refl _)
      _ = _ := hc
  unfold componentCount
  change Fintype.card H.ConnectedComponent = Fintype.card G.ConnectedComponent + 1
  have he' : Fintype.card G.ConnectedComponent =
      Fintype.card {q : H.ConnectedComponent // q ≠ H.connectedComponentMk d.snd} := by
    calc
      _ = Fintype.card {q : (G.deleteEdges {d.edge}).ConnectedComponent //
          q ≠ (G.deleteEdges {d.edge}).connectedComponentMk d.snd} := he
      _ = _ := Fintype.card_congr (Equiv.refl _)
  omega

def componentDeleteNonbridgeEquiv (d : G.Dart) (hb : ¬ G.IsBridge d.edge) :
    G.ConnectedComponent ≃ (G.deleteEdges {d.edge}).ConnectedComponent where
  toFun := Quot.map id (fun _ _ h => h.reachable_deleteEdges_of_not_isBridge hb)
  invFun := Quot.map id (fun _ _ h => h.mono (G.deleteEdges_le _))
  left_inv q := ConnectedComponent.ind (fun _ => rfl) q
  right_inv q := ConnectedComponent.ind (fun _ => rfl) q

theorem componentCount_delete_nonbridge (d : G.Dart) (hb : ¬ G.IsBridge d.edge) :
    componentCount (G.deleteEdges {d.edge}) = componentCount G :=
  (Fintype.card_congr (componentDeleteNonbridgeEquiv d hb)).symm

theorem componentCount_delete_dart (d : G.Dart) :
    componentCount (G.deleteEdges {d.edge}) =
      componentCount G + if G.IsBridge d.edge then 1 else 0 := by
  split_ifs with hb
  · exact componentCount_delete_bridge d hb
  · simpa using componentCount_delete_nonbridge d hb

end Erdos759.SimpleGraph
