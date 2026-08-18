import AllenderOQ3.Internal.TargetRiseHelpers

/-!
# Final local Boolean leaf for G3

`SourceCutLift` proves that the source cut exposes exactly the true-source
arcs followed by the false-source arcs.  `TargetCutLift` locates that cut in
one target block, computes the correct AND/OR candidate, and reduces the
global start identity to `TargetCutCandidateRises` below.
-/

set_option autoImplicit false

namespace AllenderOQ3
namespace Internal

variable {w : Nat}

/-- **The sole remaining load-bearing G3 leaf.**  At a known cut inside one
target block, the target selected by the local AND/OR rule is a false-to-true
boundary of the proper interval output. -/
theorem targetCutCandidateRises : TargetCutCandidateRises w := by
  intro hw P K hne z y p j hj PT PF hpart hPT hPF hexact
    hsemAll hsemAny hy hproper
  have hyEval := eq_positiveAssignmentEval P K z y hsemAll hsemAny
  subst y
  obtain ⟨qt, hqt⟩ := exists_true_of_isIntervalConfig hw hy
  obtain ⟨qf, hqf⟩ := exists_false_of_ne_topConfig hw hproper
  have htf : qt ≠ qf := by
    intro h
    rw [h, hqf] at hqt
    exact Bool.noConfusion hqt
  have hvalne : qt.val ≠ qf.val := by
    intro h
    exact htf (Fin.ext h)
  have hw2 : 1 < w := by omega
  let D := (arcBlock P p).drop j
  let U := targetOthers p
  let M := U.flatMap (arcBlock P)
  let C := (arcBlock P p).take j
  have hshape : (arcPairWord P).rotate (targetBoundary P p.val + j) =
      D ++ (M ++ C) := by
    simpa [D, U, M, C, targetOthers, List.append_assoc] using
      (rotate_arcPairWord_insideBlock P p j (Nat.le_of_lt hj))
  have hseg : D ++ (M ++ C) = PT ++ PF := hshape.symm.trans hpart
  have hord : (D ++ (M ++ C)).Pairwise (TruthBefore z) :=
    pairwise_truthBefore_of_partition z hseg hPT hPF
  obtain ⟨hDord, hMCord, hDcross⟩ := List.pairwise_append.mp hord
  obtain ⟨hMord, hCord, hMcross⟩ := List.pairwise_append.mp hMCord
  have hUne : U ≠ [] := targetOthers_ne_nil hw2 p
  have hDne : D ≠ [] := by
    intro hnil
    have hlen := congrArg List.length hnil
    dsimp [D] at hlen
    rw [List.length_drop, arcBlock, List.length_map] at hlen
    omega
  by_cases hj0 : j = 0
  · have hordCycle : ((p :: U).flatMap (arcBlock P)).Pairwise
        (TruthBefore z) := by
      simpa [D, C, M, hj0] using hord
    have hcycleNe : p :: U ≠ [] := by simp
    have hqtCycle : qt ∈ p :: U := by
      rw [List.mem_cons, mem_targetOthers_iff_ne]
      exact eq_or_ne qt p
    have hqfCycle : qf ∈ p :: U := by
      rw [List.mem_cons, mem_targetOthers_iff_ne]
      exact eq_or_ne qf p
    have hpTrue := first_target_true_of_truthOrdered P K hne z
      (p :: U) hcycleNe hordCycle ⟨qt, hqtCycle, hqt⟩
    simp only [List.head_cons] at hpTrue
    have hlast := last_target_false_of_truthOrdered P K hne z
      (p :: U) hcycleNe hordCycle ⟨qf, hqfCycle, hqf⟩
    have hlastEq : (p :: U).getLast hcycleNe = finPred p := by
      calc
        (p :: U).getLast hcycleNe = U.getLast hUne := List.getLast_cons hUne
        _ = finPred p := targetOthers_getLast hw2 p
    have hpredFalse : positiveAssignmentEval P K z (finPred p) = false := by
      rw [← hlastEq]
      exact hlast
    simpa [targetCutCandidate, hj0] using And.intro hpredFalse hpTrue
  · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
    cases hK : K p with
    | false =>
        have hpTrue : positiveAssignmentEval P K z p = true := by
          by_cases hqtp : qt = p
          · simpa [hqtp] using hqt
          · have hqtU : qt ∈ U := (mem_targetOthers_iff_ne p qt).2 hqtp
            have hqtRaw : (if K qt then (P qt).all (fun q => z q)
                else (P qt).any (fun q => z q)) = true := hqt
            obtain ⟨u, huP, huz⟩ :=
              exists_true_pred_of_assignmentEval_true P K hne z hqtRaw
            let b : Fin w × Fin w := (u, qt)
            have hbM : b ∈ M := by
              dsimp [M]
              rw [List.mem_flatMap]
              exact ⟨qt, hqtU, List.mem_map.mpr ⟨u, huP, rfl⟩⟩
            have hbRest : b ∈ M ++ C := List.mem_append_left C hbM
            have hallD := true_of_mem_left_of_true_mem_right z hord hbRest huz
            obtain ⟨e, heD⟩ := List.exists_mem_of_ne_nil D hDne
            have heBlock : e ∈ arcBlock P p := List.mem_of_mem_drop heD
            obtain ⟨u', hu'P, rfl⟩ := List.mem_map.mp heBlock
            exact positiveAssignmentEval_or_true_of_exists_true P K z hK
              hu'P (hallD _ heD)
        have hqfp : qf ≠ p := by
          intro h
          rw [h, hpTrue] at hqf
          exact Bool.noConfusion hqf
        have hqfU : qf ∈ U := (mem_targetOthers_iff_ne p qf).2 hqfp
        have hlast := last_target_false_of_truthOrdered P K hne z U hUne
          hMord ⟨qf, hqfU, hqf⟩
        have hpredFalse : positiveAssignmentEval P K z (finPred p) = false := by
          rw [← targetOthers_getLast hw2 p]
          exact hlast
        simpa [targetCutCandidate, hK] using And.intro hpredFalse hpTrue
    | true =>
        have hCne : C ≠ [] := by
          intro hnil
          have hlen := congrArg List.length hnil
          dsimp [C] at hlen
          rw [List.length_take, arcBlock, List.length_map,
            Nat.min_eq_left (Nat.le_of_lt hj)] at hlen
          omega
        have hpFalse : positiveAssignmentEval P K z p = false := by
          by_cases hqfp : qf = p
          · simpa [hqfp] using hqf
          · have hqfU : qf ∈ U := (mem_targetOthers_iff_ne p qf).2 hqfp
            have hqfRaw : (if K qf then (P qf).all (fun q => z q)
                else (P qf).any (fun q => z q)) = false := hqf
            obtain ⟨u, huP, huz⟩ :=
              exists_false_pred_of_assignmentEval_false P K hne z hqfRaw
            let a : Fin w × Fin w := (u, qf)
            have haM : a ∈ M := by
              dsimp [M]
              rw [List.mem_flatMap]
              exact ⟨qf, hqfU, List.mem_map.mpr ⟨u, huP, rfl⟩⟩
            have hallC := false_of_false_mem_left_of_mem_right z hMCord haM huz
            obtain ⟨e, heC⟩ := List.exists_mem_of_ne_nil C hCne
            have heBlock : e ∈ arcBlock P p := List.mem_of_mem_take heC
            obtain ⟨u', hu'P, rfl⟩ := List.mem_map.mp heBlock
            exact positiveAssignmentEval_and_false_of_exists_false P K z hK
              hu'P (hallC _ heC)
        have hqtp : qt ≠ p := by
          intro h
          rw [h, hpFalse] at hqt
          exact Bool.noConfusion hqt
        have hqtU : qt ∈ U := (mem_targetOthers_iff_ne p qt).2 hqtp
        have hfirst := first_target_true_of_truthOrdered P K hne z U hUne
          hMord ⟨qt, hqtU, hqt⟩
        have hsuccTrue : positiveAssignmentEval P K z (finShift 1 p) = true := by
          rw [← targetOthers_head hw2 p]
          exact hfirst
        have hpredSucc : finPred (finShift 1 p) = p := by
          exact finPred_shift_one p
        have hcandidate : targetCutCandidate K p j = finShift 1 p := by
          simp [targetCutCandidate, hK, hj0]
        rw [hcandidate, hpredSucc]
        exact ⟨hpFalse, hsuccTrue⟩

/-- The target-only cut theorem follows from the local rising-edge leaf. -/
theorem targetCutTracksStart : TargetCutTracksStart w :=
  targetCutTracksStart_of_candidateRises targetCutCandidateRises

/-- Compatibility wrapper used by `GeoWindCore`: every constant-free map has
the degree-one monotone start lift once the local target leaf is available. -/
theorem exists_degree_one_lift_of_constantFreeMap_cut (hw : 0 < w)
    {g : TransMonoid w} (hg : isConstantFreeMap w g)
    {A B : Finset (Config w)}
    (hA : ∀ y ∈ A, IsIntervalConfig y ∧ y ≠ topConfig w)
    (hB : ∀ y ∈ B, IsIntervalConfig y ∧ y ≠ topConfig w)
    (hbij : Set.BijOn (runTrans g) ↑A ↑B) :
    ∃ F : Nat → Nat,
      (∀ x, F (x + w) = F x + w) ∧
      Monotone F ∧
      (∀ z ∈ A, F (startOf hw z).val % w =
        (startOf hw (runTrans g z)).val) :=
  exists_degree_one_lift_of_targetCutTracksStart targetCutTracksStart
    hw hg hA hB hbij

end Internal
end AllenderOQ3
