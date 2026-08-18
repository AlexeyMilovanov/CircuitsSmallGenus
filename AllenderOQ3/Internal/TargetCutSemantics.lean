import AllenderOQ3.Internal.TargetCutLift
import AllenderOQ3.Internal.IntervalStart

/-!
Small semantic lemmas for the final G3 target-cut argument.
-/

set_option autoImplicit false

namespace AllenderOQ3
namespace Internal

variable {w : Nat}

/-- Every interval configuration contains a true coordinate. -/
theorem exists_true_of_isIntervalConfig (hw : 0 < w) {y : Config w}
    (hy : IsIntervalConfig y) :
    ∃ p : Fin w, y p = true := by
  obtain ⟨hlen, -, heq⟩ := eq_pieceConfig_canonical hy hw
  refine ⟨startOf hw y, ?_⟩
  calc
    y (startOf hw y) =
        pieceConfig (startOf hw y) (lenOf y) (startOf hw y) :=
      congrFun heq (startOf hw y)
    _ = true := pieceConfig_true_iff.mpr ⟨0, hlen, by simp⟩

/-- A configuration different from `topConfig` contains a false coordinate. -/
theorem exists_false_of_ne_topConfig (hw : 0 < w) {y : Config w}
    (hy : y ≠ topConfig w) :
    ∃ p : Fin w, y p = false := by
  classical
  by_contra h
  apply hy
  funext p
  dsimp [topConfig]
  cases hp : y p with
  | false =>
      exfalso
      exact h ⟨p, hp⟩
  | true => rfl

/-- On a proper interval, any false-to-true boundary is the canonical start. -/
theorem startOf_eq_of_false_true (hw : 0 < w) {y : Config w} {r : Fin w}
    (hy : IsIntervalConfig y) (hne : y ≠ topConfig w)
    (hfalse : y (finPred r) = false) (htrue : y r = true) :
    startOf hw y = r := by
  obtain ⟨hlenpos, hlenle, heq⟩ := eq_pieceConfig_canonical hy hw
  have hlenlt : lenOf y < w := by
    by_contra h
    have hlen : lenOf y = w := by omega
    apply hne
    funext p
    dsimp [topConfig]
    rw [heq, hlen]
    obtain ⟨k, hk, hkp⟩ := finShift_surj_lt (startOf hw y) p
    exact pieceConfig_true_iff.mpr ⟨k, hk, hkp⟩
  have hrise : r ∈ risingEdges y := mem_risingEdges.mpr ⟨hfalse, htrue⟩
  have hedges : risingEdges y = {startOf hw y} := by
    calc
      risingEdges y =
          risingEdges (pieceConfig (startOf hw y) (lenOf y)) :=
        congrArg risingEdges heq
      _ = {startOf hw y} := risingEdges_pieceConfig hlenpos hlenlt
  rw [hedges, Finset.mem_singleton] at hrise
  exact hrise.symm

/-- A true positive AND/OR assignment has a true predecessor arc. -/
theorem exists_true_pred_of_assignmentEval_true
    (P : Fin w → List (Fin w)) (K : Fin w → Bool)
    (hne : ∀ p, P p ≠ []) (z : Config w) {p : Fin w}
    (hp : (if K p then (P p).all (fun q => z q)
      else (P p).any (fun q => z q)) = true) :
    ∃ q ∈ P p, z q = true := by
  cases hK : K p with
  | false =>
      simp only [hK, Bool.false_eq_true, if_false] at hp
      rw [List.any_eq_true] at hp
      exact hp
  | true =>
      simp only [hK, if_true] at hp
      rw [List.all_eq_true] at hp
      obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil (P p) (hne p)
      exact ⟨q, hq, hp q hq⟩

/-- A false positive AND/OR assignment has a false predecessor arc. -/
theorem exists_false_pred_of_assignmentEval_false
    (P : Fin w → List (Fin w)) (K : Fin w → Bool)
    (hne : ∀ p, P p ≠ []) (z : Config w) {p : Fin w}
    (hp : (if K p then (P p).all (fun q => z q)
      else (P p).any (fun q => z q)) = false) :
    ∃ q ∈ P p, z q = false := by
  classical
  cases hK : K p with
  | false =>
      simp only [hK, Bool.false_eq_true, if_false] at hp
      obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil (P p) (hne p)
      refine ⟨q, hq, ?_⟩
      cases hqz : z q with
      | false => rfl
      | true =>
          have : (P p).any (fun q => z q) = true := by
            rw [List.any_eq_true]
            exact ⟨q, hq, hqz⟩
          rw [hp] at this
          exact Bool.noConfusion this
  | true =>
      simp only [hK, if_true] at hp
      by_contra h
      have hall : ∀ q ∈ P p, z q = true := by
        intro q hq
        cases hqz : z q with
        | false => exact False.elim (h ⟨q, hq, hqz⟩)
        | true => rfl
      have : (P p).all (fun q => z q) = true := by
        rw [List.all_eq_true]
        exact hall
      rw [hp] at this
      exact Bool.noConfusion this

/-- All arcs of a true AND block are true. -/
theorem all_true_of_and_assignmentEval_true
    (P : Fin w → List (Fin w)) (K : Fin w → Bool)
    (z : Config w) {p : Fin w} (hK : K p = true)
    (hp : (if K p then (P p).all (fun q => z q)
      else (P p).any (fun q => z q)) = true) :
    ∀ q ∈ P p, z q = true := by
  simp only [hK, if_true] at hp
  rwa [List.all_eq_true] at hp

/-- All arcs of a false OR block are false. -/
theorem all_false_of_or_assignmentEval_false
    (P : Fin w → List (Fin w)) (K : Fin w → Bool)
    (z : Config w) {p : Fin w} (hK : K p = false)
    (hp : (if K p then (P p).all (fun q => z q)
      else (P p).any (fun q => z q)) = false) :
    ∀ q ∈ P p, z q = false := by
  intro q hq
  simp only [hK, Bool.false_eq_true, if_false] at hp
  cases hqz : z q with
  | false => rfl
  | true =>
      have : (P p).any (fun q => z q) = true := by
        rw [List.any_eq_true]
        exact ⟨q, hq, hqz⟩
      rw [hp] at this
      exact Bool.noConfusion this

end Internal
end AllenderOQ3
