import ErdosProblems.Erdos759

/-! Explicit proof that implementation instances do not alter the embedding proposition. -/

namespace Erdos759.SimpleGraph

theorem embedsOrientable_instances {V : Type*} (G : SimpleGraph V) (g : ℕ)
    (i j : Fintype V) (d e : DecidableEq V) (a b : DecidableRel G.Adj) :
    @EmbedsOrientable V i d G a g ↔ @EmbedsOrientable V j e G b g := by
  cases Subsingleton.elim i j
  cases Subsingleton.elim d e
  cases Subsingleton.elim a b
  rfl

theorem embedsOrientable_congr {V : Type*} (G H : SimpleGraph V) (h : G = H) (g : ℕ)
    (i j : Fintype V) (d e : DecidableEq V)
    (a : DecidableRel G.Adj) (b : DecidableRel H.Adj) :
    @EmbedsOrientable V i d G a g ↔ @EmbedsOrientable V j e H b g := by
  subst H
  exact embedsOrientable_instances G g i j d e a b

end Erdos759.SimpleGraph
