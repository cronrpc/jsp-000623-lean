import FaceDeletion
import EdgeIsolateCounts
import GraphDeletionCounts

noncomputable section
open _root_.SimpleGraph
open JSP623.PermutationSurgery
namespace Erdos759.SimpleGraph
attribute [local instance] Classical.propDecidable Classical.decEq

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- Isolated-vertex faces exactly replace the singleton cycles removed during surgery. -/
theorem RotationSystem.faceCount_deleteEdge_balance (R : RotationSystem G) (d : G.Dart) :
    faceCount (G.deleteEdges {d.edge}) (R.deleteEdge d) + totalCycles R.facePerm =
      faceCount G R + totalCycles (R.cutEdge d) := by
  have hcycles := R.cycleCount_deleteEdge d
  have hisolates := R.isolateCount_deleteEdge d
  have htotal := R.totalCycles_facePerm
  dsimp only [RotationSystem.cutEdge] at hcycles ⊢
  simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right] at hcycles hisolates
  unfold faceCount
  split_ifs at * <;> omega

/-- A bridge splits one face into two when deleted. -/
theorem RotationSystem.faceCount_deleteEdge_bridge (R : RotationSystem G) (d : G.Dart)
    (hd : G.IsBridge d.edge) :
    faceCount (G.deleteEdges {d.edge}) (R.deleteEdge d) = faceCount G R + 1 := by
  have h := R.faceCount_deleteEdge_balance d
  have hs := totalCycles_mul_swap_of_sameCycle R.facePerm d.symm_ne.symm
    (R.sameCycle_of_isBridge d hd)
  have hs' : totalCycles (R.cutEdge d) = totalCycles R.facePerm + 1 := by
    convert hs using 1 <;> congr 3
    unfold RotationSystem.cutEdge
    congr 2 <;> exact Subsingleton.elim _ _
  omega

/-- Deleting an edge decreases the face count by at most one. -/
theorem RotationSystem.faceCount_le_deleteEdge_add_one (R : RotationSystem G) (d : G.Dart) :
    faceCount G R ≤ faceCount (G.deleteEdges {d.edge}) (R.deleteEdge d) + 1 := by
  have h := R.faceCount_deleteEdge_balance d
  by_cases hs : R.facePerm.SameCycle d d.symm
  · have hc := totalCycles_mul_swap_of_sameCycle R.facePerm d.symm_ne.symm hs
    have hc' : totalCycles (R.cutEdge d) = totalCycles R.facePerm + 1 := by
      convert hc using 1 <;> congr 3
      unfold RotationSystem.cutEdge
      congr 2 <;> exact Subsingleton.elim _ _
    omega
  · have hc := totalCycles_mul_swap_of_not_sameCycle R.facePerm hs
    have hc' : totalCycles (R.cutEdge d) + 1 = totalCycles R.facePerm := by
      convert hc using 1 <;> congr 3
      unfold RotationSystem.cutEdge
      congr 2 <;> exact Subsingleton.elim _ _
    omega

/-- Ordinary rotation-system embeddability is preserved by deletion of a genuine edge. -/
theorem EmbedsOrientable.delete_dart {g : ℕ} (hG : EmbedsOrientable G g) (d : G.Dart) :
    EmbedsOrientable (G.deleteEdges {d.edge}) g := by
  obtain ⟨R, hR⟩ := hG
  refine ⟨R.deleteEdge d, ?_⟩
  have he := edgeCount_delete_dart d
  by_cases hb : G.IsBridge d.edge
  · have hc := componentCount_delete_bridge d hb
    have hf := R.faceCount_deleteEdge_bridge d hb
    omega
  · have hc := componentCount_delete_nonbridge d hb
    have hf := R.faceCount_le_deleteEdge_add_one d
    omega

end Erdos759.SimpleGraph



