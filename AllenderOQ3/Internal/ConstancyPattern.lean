import Mathlib
import AllenderOQ3.Internal.TransitionMonoid

namespace AllenderOQ3.Internal

abbrev ConstancyPattern (w : Nat) := Fin w → Option Bool

def Respects {w : Nat} (σ : ConstancyPattern w) (z : Config w) : Prop :=
  ∀ i b, σ i = some b → z i = b

def AgreeOnLive {w : Nat} (σ : ConstancyPattern w) (z z' : Config w) : Prop :=
  ∀ i, σ i = none → z i = z' i

def emptyPattern (w : Nat) : ConstancyPattern w := fun _ => none

open Classical in
noncomputable def propagate {w : Nat} (g : TransMonoid w) (σ : ConstancyPattern w) : ConstancyPattern w :=
  fun i =>
    if h : ∃ b, ∀ z, Respects σ z → runTrans g z i = b then
      some (Classical.choose h)
    else
      none

open Classical in
theorem respects_propagate {w : Nat} {g : TransMonoid w} {σ : ConstancyPattern w} {z : Config w} (hz : Respects σ z) : Respects (propagate g σ) (runTrans g z) := by
  intro i b h_prop
  dsimp [propagate] at h_prop
  split_ifs at h_prop with h
  · injection h_prop with h_eq
    rw [←h_eq]
    exact Classical.choose_spec h z hz

end AllenderOQ3.Internal
