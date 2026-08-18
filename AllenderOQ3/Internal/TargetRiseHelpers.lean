import AllenderOQ3.Internal.TargetCutSemantics

set_option autoImplicit false

namespace AllenderOQ3
namespace Internal

variable {w : Nat}

def positiveAssignmentEval (P : Fin w → List (Fin w)) (K : Fin w → Bool)
    (z : Config w) : Config w :=
  fun p => if K p then (P p).all (fun q => z q)
    else (P p).any (fun q => z q)

theorem eq_positiveAssignmentEval
    (P : Fin w → List (Fin w)) (K : Fin w → Bool)
    (z y : Config w)
    (hsemAll : ∀ q, K q = true → y q = (P q).all (fun u => z u))
    (hsemAny : ∀ q, K q = false → y q = (P q).any (fun u => z u)) :
    y = positiveAssignmentEval P K z := by
  funext q
  cases hK : K q with
  | false => simpa [positiveAssignmentEval, hK] using hsemAny q hK
  | true => simpa [positiveAssignmentEval, hK] using hsemAll q hK

def TruthBefore (z : Config w) (a b : Fin w × Fin w) : Prop :=
  z a.1 = true ∨ z b.1 = false

theorem pairwise_truthBefore_of_partition (z : Config w)
    {L PT PF : List (Fin w × Fin w)} (hL : L = PT ++ PF)
    (hPT : ∀ e ∈ PT, z e.1 = true)
    (hPF : ∀ e ∈ PF, z e.1 = false) :
    L.Pairwise (TruthBefore z) := by
  rw [hL, List.pairwise_append]
  refine ⟨List.pairwise_of_forall_mem_list (fun a ha b hb => Or.inl (hPT a ha)),
    List.pairwise_of_forall_mem_list (fun a ha b hb => Or.inr (hPF b hb)), ?_⟩
  intro a ha b hb
  exact Or.inl (hPT a ha)

theorem true_of_mem_left_of_true_mem_right (z : Config w)
    {A B : List (Fin w × Fin w)}
    (hord : (A ++ B).Pairwise (TruthBefore z))
    {b : Fin w × Fin w} (hb : b ∈ B) (hbtrue : z b.1 = true) :
    ∀ a ∈ A, z a.1 = true := by
  intro a ha
  have hab := (List.pairwise_append.mp hord).2.2 a ha b hb
  rcases hab with haTrue | hbFalse
  · exact haTrue
  · rw [hbtrue] at hbFalse
    exact Bool.noConfusion hbFalse

theorem false_of_false_mem_left_of_mem_right (z : Config w)
    {A B : List (Fin w × Fin w)}
    (hord : (A ++ B).Pairwise (TruthBefore z))
    {a : Fin w × Fin w} (ha : a ∈ A) (hafalse : z a.1 = false) :
    ∀ b ∈ B, z b.1 = false := by
  intro b hb
  have hab := (List.pairwise_append.mp hord).2.2 a ha b hb
  rcases hab with haTrue | hbFalse
  · rw [hafalse] at haTrue
    exact Bool.noConfusion haTrue
  · exact hbFalse

theorem positiveAssignmentEval_true_of_all_true
    (P : Fin w → List (Fin w)) (K : Fin w → Bool)
    (hne : ∀ p, P p ≠ []) (z : Config w) (p : Fin w)
    (hall : ∀ q ∈ P p, z q = true) :
    positiveAssignmentEval P K z p = true := by
  simp only [positiveAssignmentEval]
  cases hK : K p with
  | false =>
      simp only [Bool.false_eq_true, if_false]
      rw [List.any_eq_true]
      obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil (P p) (hne p)
      exact ⟨q, hq, hall q hq⟩
  | true =>
      simp only [if_true]
      rwa [List.all_eq_true]

theorem positiveAssignmentEval_false_of_all_false
    (P : Fin w → List (Fin w)) (K : Fin w → Bool)
    (hne : ∀ p, P p ≠ []) (z : Config w) (p : Fin w)
    (hall : ∀ q ∈ P p, z q = false) :
    positiveAssignmentEval P K z p = false := by
  simp only [positiveAssignmentEval]
  cases hK : K p with
  | false =>
      simp only [Bool.false_eq_true, if_false]
      apply Bool.eq_false_of_not_eq_true
      rw [List.any_eq_true]
      rintro ⟨q, hq, hqtrue⟩
      rw [hall q hq] at hqtrue
      exact Bool.noConfusion hqtrue
  | true =>
      simp only [if_true]
      obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil (P p) (hne p)
      apply Bool.eq_false_of_not_eq_true
      rw [List.all_eq_true]
      intro htrue
      have := htrue q hq
      rw [hall q hq] at this
      exact Bool.noConfusion this

theorem positiveAssignmentEval_or_true_of_exists_true
    (P : Fin w → List (Fin w)) (K : Fin w → Bool)
    (z : Config w) {p : Fin w} (hK : K p = false)
    {q : Fin w} (hq : q ∈ P p) (hqtrue : z q = true) :
    positiveAssignmentEval P K z p = true := by
  simp only [positiveAssignmentEval, hK, Bool.false_eq_true, if_false]
  rw [List.any_eq_true]
  exact ⟨q, hq, hqtrue⟩

theorem positiveAssignmentEval_and_false_of_exists_false
    (P : Fin w → List (Fin w)) (K : Fin w → Bool)
    (z : Config w) {p : Fin w} (hK : K p = true)
    {q : Fin w} (hq : q ∈ P p) (hqfalse : z q = false) :
    positiveAssignmentEval P K z p = false := by
  simp only [positiveAssignmentEval, hK, if_true]
  apply Bool.eq_false_of_not_eq_true
  rw [List.all_eq_true]
  intro hall
  have := hall q hq
  rw [hqfalse] at this
  exact Bool.noConfusion this

/-- First-target propagation, requiring membership only for the supplied
true witness (so it also applies to the target circle with one block removed). -/
theorem first_target_true_of_truthOrdered
    (P : Fin w → List (Fin w)) (K : Fin w → Bool)
    (hne : ∀ p, P p ≠ []) (z : Config w)
    (T : List (Fin w)) (hT : T ≠ [])
    (hord : (T.flatMap (arcBlock P)).Pairwise (TruthBefore z))
    (hex : ∃ p ∈ T, positiveAssignmentEval P K z p = true) :
    positiveAssignmentEval P K z (T.head hT) = true := by
  cases T with
  | nil => exact (hT rfl).elim
  | cons r T =>
      simp only [List.head_cons]
      obtain ⟨p, hpT, hp⟩ := hex
      by_cases hpr : p = r
      · simpa [hpr] using hp
      · have hpTail : p ∈ T := (List.mem_cons.mp hpT).resolve_left hpr
        have hpraw : (if K p then (P p).all (fun q => z q)
            else (P p).any (fun q => z q)) = true := hp
        obtain ⟨q, hqP, hqtrue⟩ :=
          exists_true_pred_of_assignmentEval_true P K hne z hpraw
        let b : Fin w × Fin w := (q, p)
        have hb : b ∈ T.flatMap (arcBlock P) := by
          rw [List.mem_flatMap]
          refine ⟨p, hpTail, ?_⟩
          exact List.mem_map.mpr ⟨q, hqP, rfl⟩
        have hord' : (arcBlock P r ++ T.flatMap (arcBlock P)).Pairwise
            (TruthBefore z) := by simpa using hord
        apply positiveAssignmentEval_true_of_all_true P K hne z r
        intro q' hq'
        let a : Fin w × Fin w := (q', r)
        have ha : a ∈ arcBlock P r := List.mem_map.mpr ⟨q', hq', rfl⟩
        exact true_of_mem_left_of_true_mem_right z hord' hb hqtrue a ha

theorem last_target_false_of_truthOrdered
    (P : Fin w → List (Fin w)) (K : Fin w → Bool)
    (hne : ∀ p, P p ≠ []) (z : Config w)
    (T : List (Fin w)) (hT : T ≠ [])
    (hord : (T.flatMap (arcBlock P)).Pairwise (TruthBefore z))
    (hex : ∃ p ∈ T, positiveAssignmentEval P K z p = false) :
    positiveAssignmentEval P K z (T.getLast hT) = false := by
  induction T using List.reverseRecOn with
  | nil => exact (hT rfl).elim
  | append_singleton T r ih =>
      rw [show (T ++ [r]).getLast (by simp) = r by simp]
      obtain ⟨p, hpT, hp⟩ := hex
      by_cases hpr : p = r
      · simpa [hpr] using hp
      · have hpInit : p ∈ T := by
          rcases List.mem_append.mp hpT with h | h
          · exact h
          · exact (hpr (List.mem_singleton.mp h)).elim
        have hpraw : (if K p then (P p).all (fun q => z q)
            else (P p).any (fun q => z q)) = false := hp
        obtain ⟨q, hqP, hqfalse⟩ :=
          exists_false_pred_of_assignmentEval_false P K hne z hpraw
        let a : Fin w × Fin w := (q, p)
        have ha : a ∈ T.flatMap (arcBlock P) := by
          rw [List.mem_flatMap]
          refine ⟨p, hpInit, List.mem_map.mpr ⟨q, hqP, rfl⟩⟩
        have hord' : (T.flatMap (arcBlock P) ++ arcBlock P r).Pairwise
            (TruthBefore z) := by simpa using hord
        apply positiveAssignmentEval_false_of_all_false P K hne z r
        intro q' hq'
        let b : Fin w × Fin w := (q', r)
        have hb : b ∈ arcBlock P r := List.mem_map.mpr ⟨q', hq', rfl⟩
        exact false_of_false_mem_left_of_mem_right z hord' ha hqfalse b hb

def targetOthers (p : Fin w) : List (Fin w) :=
  (List.finRange w).drop (p.val + 1) ++ (List.finRange w).take p.val

theorem targetCycle_eq_rotate (p : Fin w) :
    p :: targetOthers p = (List.finRange w).rotate p.val := by
  have hp : p.val < (List.finRange w).length := by simpa using p.isLt
  rw [List.rotate_eq_drop_append_take (Nat.le_of_lt hp),
    List.drop_eq_getElem_cons hp, List.getElem_finRange]
  rfl

theorem targetCycle_eq_map (p : Fin w) :
    p :: targetOthers p =
      (List.finRange w).map (fun k => finShift k.val p) := by
  rw [targetCycle_eq_rotate p, rotate_finRange_eq p]

theorem targetOthers_eq_map_drop_one (hw : 0 < w) (p : Fin w) :
    targetOthers p =
      ((List.finRange w).drop 1).map (fun k => finShift k.val p) := by
  have hzero : (0 : Nat) < (List.finRange w).length := by simpa using hw
  have hcons := List.drop_eq_getElem_cons (l := List.finRange w) hzero
  have hget : (List.finRange w)[0]'hzero = (⟨0, hw⟩ : Fin w) := by simp
  rw [hget] at hcons
  have hfincons : List.finRange w =
      (⟨0, hw⟩ : Fin w) :: (List.finRange w).drop 1 := by
    simpa using hcons
  have hcycle := targetCycle_eq_map p
  rw [hfincons, List.map_cons] at hcycle
  simpa using (List.cons.inj hcycle).2

theorem targetOthers_ne_nil (hw2 : 1 < w) (p : Fin w) :
    targetOthers p ≠ [] := by
  intro hnil
  have hlen := congrArg List.length (targetCycle_eq_rotate p)
  rw [hnil] at hlen
  simp at hlen
  omega

theorem targetOthers_head (hw2 : 1 < w) (p : Fin w) :
    (targetOthers p).head (targetOthers_ne_nil hw2 p) = finShift 1 p := by
  have hw : 0 < w := by omega
  let D := (List.finRange w).drop 1
  have hDne : D ≠ [] := by
    intro hnil
    have hlen := congrArg List.length hnil
    dsimp [D] at hlen
    rw [List.length_drop, List.length_finRange] at hlen
    omega
  have hEq := targetOthers_eq_map_drop_one hw p
  have hmapNe : D.map (fun k => finShift k.val p) ≠ [] := by simpa using hDne
  have hheadEq :
      (targetOthers p).head? =
        (D.map (fun k => finShift k.val p)).head? := congrArg List.head? hEq
  rw [List.head?_eq_head (targetOthers_ne_nil hw2 p),
    List.head?_eq_head hmapNe, List.head_map] at hheadEq
  have hheadD : D.head hDne = (⟨1, hw2⟩ : Fin w) := by
    dsimp [D]
    rw [List.head_drop, List.getElem_finRange]
    rfl
  rw [hheadD] at hheadEq
  exact Option.some.inj hheadEq

theorem targetOthers_getLast (hw2 : 1 < w) (p : Fin w) :
    (targetOthers p).getLast (targetOthers_ne_nil hw2 p) = finPred p := by
  have hw : 0 < w := by omega
  let D := (List.finRange w).drop 1
  have hDne : D ≠ [] := by
    intro hnil
    have hlen := congrArg List.length hnil
    dsimp [D] at hlen
    rw [List.length_drop, List.length_finRange] at hlen
    omega
  have hEq := targetOthers_eq_map_drop_one hw p
  have hmapNe : D.map (fun k => finShift k.val p) ≠ [] := by simpa using hDne
  have hlastEq :
      (targetOthers p).getLast? =
        (D.map (fun k => finShift k.val p)).getLast? := congrArg List.getLast? hEq
  rw [List.getLast?_eq_getLast (targetOthers_ne_nil hw2 p),
    List.getLast?_eq_getLast hmapNe, List.getLast_map] at hlastEq
  have hfinNe : List.finRange w ≠ [] := by simp [Nat.ne_of_gt hw]
  have hlastFin : (List.finRange w).getLast hfinNe =
      (⟨w - 1, by omega⟩ : Fin w) := by
    rw [List.getLast_eq_getElem, List.getElem_finRange]
    apply Fin.ext
    simp
  have hlastD : D.getLast hDne = (⟨w - 1, by omega⟩ : Fin w) := by
    dsimp [D]
    rw [List.getLast_drop, hlastFin]
  rw [hlastD] at hlastEq
  exact Option.some.inj hlastEq

theorem mem_targetOthers_iff_ne (p q : Fin w) :
    q ∈ targetOthers p ↔ q ≠ p := by
  have hcycle := targetCycle_eq_rotate p
  constructor
  · intro hq heq
    subst q
    unfold targetOthers at hq
    rcases List.mem_append.mp hq with hq | hq
    · have := mem_drop_finRange hq
      omega
    · have := mem_take_finRange hq
      omega
  · intro hne
    have hmem : q ∈ (List.finRange w).rotate p.val :=
      List.mem_rotate.mpr (List.mem_finRange q)
    rw [← targetCycle_eq_rotate p, List.mem_cons] at hmem
    exact hmem.resolve_left hne

end Internal
end AllenderOQ3
