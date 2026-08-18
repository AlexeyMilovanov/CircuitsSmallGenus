import Mathlib

open Classical

variable {n : Nat}

noncomputable def finsetEmb (S : Finset (Fin n)) : Fin S.toList.length → Fin n :=
  fun i => S.toList.get i

theorem finsetEmb_injective (S : Finset (Fin n)) : Function.Injective (finsetEmb S) := by
  intro i j hij
  unfold finsetEmb at hij
  have hn := Finset.nodup_toList S
  exact List.Nodup.get_inj_iff hn |>.mp hij
