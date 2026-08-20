import AllenderOQ3.Base
import AllenderOQ3.Internal.ACCJoin
import AllenderOQ3.Internal.ACCCyclicWord

set_option autoImplicit false

namespace AllenderOQ3.Internal

variable {n m : Nat}

/-- Evaluate a guessed change sequence. -/
def evalGuess {Z : Type} {len K : Nat} (times : Fin K → Fin len) (vals : Fin (K + 1) → Z)
  (i : Fin (len + 1)) : Z :=
  vals ⟨(Finset.univ.filter (fun j : Fin K => (times j : Nat) < (i : Nat))).card, by
    have h1 : (Finset.univ.filter (fun j : Fin K => (times j : Nat) < (i : Nat))).card ≤
      (Finset.univ : Finset (Fin K)).card :=
      Finset.card_filter_le _ _
    rw [Finset.card_univ, Fintype.card_fin] at h1
    exact Nat.lt_succ_of_le h1⟩


lemma z_eq_of_count_eq {Z : Type} {len K : Nat}
    (z : Fin (len + 1) → Z)
    (times : Fin K → Fin len)
    (H_surj : ∀ s : Fin len, z (Fin.castSucc s) ≠ z s.succ → ∃ j : Fin K, times j = s)
    (i i_0 : Fin (len + 1))
    (h_le : (i_0 : Nat) ≤ (i : Nat))
    (h_eq_count : (Finset.univ.filter (fun j : Fin K => (times j : Nat) < (i_0 : Nat))).card =
                  (Finset.univ.filter (fun j : Fin K => (times j : Nat) < (i : Nat))).card) :
    z i_0 = z i := by
  let z' : ℕ → Z := fun n => if h : n < len + 1 then z ⟨n, h⟩ else z 0
  have h_z' : ∀ k (hk : k < len + 1), z' k = z ⟨k, hk⟩ := fun k hk => dif_pos hk
  have h_subset : (Finset.univ.filter (fun j : Fin K => (times j : Nat) < (i_0 : Nat))) ⊆
                  (Finset.univ.filter (fun j : Fin K => (times j : Nat) < (i : Nat))) := by
    intro j hj
    rw [Finset.mem_filter] at hj ⊢
    exact ⟨hj.1, by omega⟩
  have h_eq_set : (Finset.univ.filter (fun j : Fin K => (times j : Nat) < (i_0 : Nat))) =
                  (Finset.univ.filter (fun j : Fin K => (times j : Nat) < (i : Nat))) := by
    exact Finset.eq_of_subset_of_card_le h_subset (by omega)
  have H_no_change : ∀ k : Nat, (i_0 : Nat) ≤ k → k < (i : Nat) → z' k = z' (k + 1) := by
    intro k hk1 hk2
    have H1 : k < len + 1 := by have := i.isLt; omega
    have H2 : k + 1 < len + 1 := by have := i.isLt; omega
    rw [h_z' k H1, h_z' (k + 1) H2]
    by_contra h_neq
    obtain ⟨j, hj_eq⟩ := H_surj ⟨k, by have := i.isLt; omega⟩ h_neq
    have h_in_B : j ∈ Finset.univ.filter (fun j : Fin K => (times j : Nat) < (i : Nat)) := by
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ j, ?_⟩
      have : (times j : Nat) = k := by exact congrArg Fin.val hj_eq
      omega
    have h_in_A : j ∈ Finset.univ.filter (fun j : Fin K => (times j : Nat) < (i_0 : Nat)) := by
      rw [h_eq_set]
      exact h_in_B
    rw [Finset.mem_filter] at h_in_A
    have : (times j : Nat) = k := by exact congrArg Fin.val hj_eq
    omega
  have hz_eq : ∀ d (hd : i_0.val + d ≤ i.val), z' i_0.val = z' (i_0.val + d) := by
    intro d
    induction d with
    | zero =>
      intro hd
      have : i_0.val + 0 = i_0.val := rfl
      rw [this]
    | succ d ih =>
      intro hd
      have hd' : i_0.val + d ≤ i.val := by omega
      have h1 : z' i_0.val = z' (i_0.val + d) := ih hd'
      have h2 : z' (i_0.val + d) = z' (i_0.val + d + 1) := H_no_change (i_0.val + d) (by omega)
        (by omega)
      rw [h1, h2]; congr 1
  have h_final := hz_eq (i.val - i_0.val) (by omega)
  have h_i_eq : i_0.val + (i.val - i_0.val) = i.val := by omega
  rw [h_i_eq] at h_final
  have hi0 : i_0.val < len + 1 := i_0.isLt
  have hi : i.val < len + 1 := i.isLt
  have eq0 : z' i_0.val = z i_0 := by
    have : z i_0 = z ⟨i_0.val, hi0⟩ := rfl
    rw [this, ← h_z' i_0.val hi0]
  have eq1 : z' i.val = z i := by
    have : z i = z ⟨i.val, hi⟩ := rfl
    rw [this, ← h_z' i.val hi]
  rw [eq0, eq1] at h_final
  exact h_final

/-- Any step sequence with at most K changes can be represented as a guess. -/
theorem exists_guess_of_changes_le {Z : Type} [DecidableEq Z] {len K : Nat} (z : Fin (len + 1) → Z)
    (hK : (Finset.univ.filter (fun i : Fin len => z (Fin.castSucc i) ≠ z i.succ)).card ≤ K)
    (h_nonempty : Nonempty (Fin K → Fin len)) :
    ∃ (times : Fin K → Fin len) (vals : Fin (K + 1) → Z), ∀ i, evalGuess times vals i = z i := by
  set S := Finset.univ.filter (fun i : Fin len => z (Fin.castSucc i) ≠ z i.succ)
  set L := S.toList
  have hL_len : L.length = S.card := Finset.length_toList _
  have hL_le : L.length ≤ K := by omega
  let times : Fin K → Fin len := fun j =>
    if h : j.val < L.length then L.get ⟨j.val, h⟩ else (Classical.choice h_nonempty) j
  have H_surj : ∀ s : Fin len, z (Fin.castSucc s) ≠ z s.succ → ∃ j : Fin K, times j = s := by
    intro s h_neq
    have hs : s ∈ S := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ s, h_neq⟩
    have hs_mem : s ∈ L := Finset.mem_toList.mpr hs
    obtain ⟨j, hj_eq⟩ := List.mem_iff_get.mp hs_mem
    have hj_K : j.val < K := by
      have : j.val < L.length := j.isLt
      omega
    use ⟨j.val, hj_K⟩
    dsimp [times]
    rw [dif_pos j.isLt]
    exact hj_eq
  let vals : Fin (K + 1) → Z := fun c =>
    if h : ∃ i : Fin (len + 1),
      (Finset.univ.filter (fun j : Fin K => (times j : Nat) < (i : Nat))).card = c
    then z (Classical.choose h)
    else z 0
  use times, vals
  intro i
  dsimp [evalGuess, vals]
  have h_ex : ∃ i_0 : Fin (len + 1),
    (Finset.univ.filter (fun j : Fin K => (times j : Nat) < (i_0 : Nat))).card =
    (Finset.univ.filter (fun j : Fin K => (times j : Nat) < (i : Nat))).card := ⟨i, rfl⟩
  rw [dif_pos h_ex]
  set i_0 := Classical.choose h_ex
  have h_eq_count :
    (Finset.univ.filter (fun j : Fin K => (times j : Nat) < (i_0 : Nat))).card =
    (Finset.univ.filter (fun j : Fin K => (times j : Nat) < (i : Nat))).card :=
    Classical.choose_spec h_ex
  by_cases h_le : i_0.val ≤ i.val
  · exact z_eq_of_count_eq z times H_surj i i_0 h_le h_eq_count
  · have h_le_2 : i.val ≤ i_0.val := by omega
    exact (z_eq_of_count_eq z times H_surj i_0 i h_le_2 h_eq_count.symm).symm

/-- The bounded-change (aperiodic) layer obligation. -/
theorem cascade_aperiodic_layer {len size_letter size_driver d K : Nat}
    {Z L Y : Type} [Fintype Z] [Fintype L] [Fintype Y] [DecidableEq Z]
    (letter : Fin len → (Fin n → Bool) → L)
    (driver : Fin len → (Fin n → Bool) → Y)
    (step : L → Y → Z → Z)
    (recLetter : Fin len → L → ACCCircuit n m)
    (recDriver : Fin len → Y → ACCCircuit n m)
    (hwfL : ∀ i l, WellFormedACC (recLetter i l))
    (hlayL : ∀ i l q, (recLetter i l).layer q ≤ d)
    (hsizeL : ∀ i l, (recLetter i l).gateCount ≤ size_letter)
    (haccL : ∀ i l x, ACCAccepts (recLetter i l) x ↔ letter i x = l)
    (hwfD : ∀ i y, WellFormedACC (recDriver i y))
    (hlayD : ∀ i y q, (recDriver i y).layer q ≤ d)
    (hsizeD : ∀ i y, (recDriver i y).gateCount ≤ size_driver)
    (haccD : ∀ i y x, ACCAccepts (recDriver i y) x ↔ driver i x = y)
    (z0 : Z)
    (target : Z)
    (z : Fin (len + 1) → (Fin n → Bool) → Z)
    (hz0 : ∀ x, z 0 x = z0)
    (hz_succ : ∀ i x, z i.succ x = step (letter i x) (driver i x) (z (Fin.castSucc i) x))
    (h_changes : ∀ x,
      (Finset.univ.filter (fun i : Fin len => z (Fin.castSucc i) x ≠ z i.succ x)).card ≤ K) :
    ∃ a : ACCCircuit n m,
      WellFormedACC a ∧
      (∀ q, a.layer q ≤ max (d + 2) 1 + 5) ∧
      a.gateCount ≤ Fintype.card (Fin K → Fin len) * Fintype.card (Fin (K + 1) → Z) *
        ((len + 2) * ((Fintype.card L * Fintype.card Y) * (size_letter + size_driver + 1) + 1) + 1)
          + 1 ∧
      (∀ x, ACCAccepts a x ↔ z (Fin.last len) x = target) := by
  have h_rec : ∀ i c1 c2, ∃ c : ACCCircuit n m,
      WellFormedACC c ∧
      (∀ q, c.layer q ≤ d + 2) ∧
      c.gateCount ≤ (Fintype.card L * Fintype.card Y) * (size_letter + size_driver + 1) + 1 ∧
      (∀ x, ACCAccepts c x ↔ step (letter i x) (driver i x) c1 = c2) := by
    intro i c1 c2
    set pairs := (Finset.univ.filter (fun p : L × Y => step p.1 p.2 c1 = c2)).toList with hpairs
    set k' := pairs.length with hk'
    let g (j : Fin k') : Fin 2 → ACCCircuit n m :=
      Fin.cases (recLetter i (pairs.get (hk' ▸ j)).1) (fun _ => recDriver i (pairs.get (hk' ▸ j)).2)
    have hwf : ∀ j idx, WellFormedACC (g j idx) := by
      intro j idx
      refine Fin.cases ?_ ?_ idx
      · exact hwfL i _
      · intro _; exact hwfD i _
    have hlay : ∀ j idx q, (g j idx).layer q ≤ d := by
      intro j idx
      refine Fin.cases ?_ ?_ idx
      · intro q; exact hlayL i _ q
      · intro _ q; exact hlayD i _ q
    refine ⟨accOrAnd g d, wellFormedACC_accOrAnd hwf hlay, accOrAnd_layer_le hlay, ?_, ?_⟩
    · simp only [accOrAnd_gateCount, Fin.sum_univ_two, g]
      have : ∀ j, (g j 0).gateCount + (g j 1).gateCount + 1 ≤ size_letter + size_driver + 1 := by
        intro j
        exact Nat.add_le_add (Nat.add_le_add (hsizeL i _) (hsizeD i _)) (le_refl 1)
      have hsum : (∑ j : Fin k', ((g j 0).gateCount + (g j 1).gateCount + 1)) ≤ k' *
        (size_letter + size_driver + 1) := by
        exact Finset.sum_le_card_nsmul Finset.univ _ _ (fun j _ => this j) |>.trans (by simp)
      calc (∑ j : Fin k', ((g j 0).gateCount + (g j 1).gateCount + 1)) + 1
        ≤ k' * (size_letter + size_driver + 1) + 1 := Nat.add_le_add_right hsum 1
        _ ≤ (Fintype.card L * Fintype.card Y) * (size_letter + size_driver + 1) + 1 := by
          apply Nat.add_le_add_right
          apply Nat.mul_le_mul_right
          have hk_le : k' ≤ (Finset.univ : Finset (L × Y)).card := by
            rw [hk', hpairs, Finset.length_toList]
            apply Finset.card_filter_le
          rwa [Finset.card_univ, Fintype.card_prod] at hk_le
    · intro x
      rw [accAccepts_accOrAnd hwf hlay]
      constructor
      · rintro ⟨j, hj⟩
        have hj0 := hj 0
        have hj1 := hj 1
        change ACCAccepts (recLetter i (pairs.get (hk' ▸ j)).1) x at hj0
        change ACCAccepts (recDriver i (pairs.get (hk' ▸ j)).2) x at hj1
        rw [haccL] at hj0
        rw [haccD] at hj1
        have hmem : pairs.get (hk' ▸ j) ∈ pairs := by
          have hget : pairs.get (hk' ▸ j) = pairs.get (hk' ▸ j) := rfl
          exact List.mem_iff_get.mpr ⟨hk' ▸ j, hget⟩
        have hmem' : pairs.get (hk' ▸ j) ∈
          (Finset.univ.filter (fun p : L × Y => step p.1 p.2 c1 = c2)).toList := hpairs ▸ hmem
        rw [Finset.mem_toList, Finset.mem_filter] at hmem'
        rw [hj0, hj1]
        exact hmem'.2
      · intro hval
        have hmem : (letter i x, driver i x) ∈ pairs := by
          have hmem' : (letter i x, driver i x) ∈
            (Finset.univ.filter (fun p : L × Y => step p.1 p.2 c1 = c2)).toList := by
            rw [Finset.mem_toList, Finset.mem_filter]
            exact ⟨Finset.mem_univ _, hval⟩
          exact hpairs.symm ▸ hmem'
        obtain ⟨j, heq⟩ := List.mem_iff_get.mp hmem
        have hk_j : j.val < k' := by rw [hk']; exact j.isLt
        refine ⟨⟨j.val, hk_j⟩, ?_⟩
        intro idx
        have heq' : pairs.get (hk' ▸ ⟨j.val, hk_j⟩) = (letter i x, driver i x) := by
          have : (hk' ▸ ⟨j.val, hk_j⟩ : Fin pairs.length) = j := Fin.ext rfl
          rw [this]
          exact heq
        have h0 : letter i x = (pairs.get (hk' ▸ ⟨j.val, hk_j⟩)).1 := by rw [heq']
        have h1 : driver i x = (pairs.get (hk' ▸ ⟨j.val, hk_j⟩)).2 := by rw [heq']
        refine Fin.cases ?_ ?_ idx
        · change ACCAccepts (recLetter i (pairs.get (hk' ▸ ⟨j.val, hk_j⟩)).1) x
          rw [haccL]
          exact h0
        · intro _
          change ACCAccepts (recDriver i (pairs.get (hk' ▸ ⟨j.val, hk_j⟩)).2) x
          rw [haccD]
          exact h1
  choose checkStep hcs_wf hcs_lay hcs_size hcs_acc using h_rec
  set Index := (Fin K → Fin len) × (Fin (K + 1) → Z)
  set nIdx := Fintype.card Index
  set idxEquiv := Fintype.equivFin Index
  let outer (i : Fin nIdx) (j : Fin (len + 2)) : ACCCircuit n m :=
    let idx := idxEquiv.symm i
    if hj : j.val = 0 then
      accConst n m (decide (evalGuess idx.1 idx.2 0 = z0))
    else if hj2 : j.val = len + 1 then
      accConst n m (decide (evalGuess idx.1 idx.2 (Fin.last len) = target))
    else
      checkStep ⟨j.val - 1, by omega⟩
        (evalGuess idx.1 idx.2 ⟨j.val - 1, by omega⟩)
        (evalGuess idx.1 idx.2 ⟨j.val, by omega⟩)
  have hwf_out : ∀ i j, WellFormedACC (outer i j) := by
    intro i j
    by_cases hj : j.val = 0
    · have h_eq : outer i j = accConst n m
        (decide (evalGuess (idxEquiv.symm i).1 (idxEquiv.symm i).2 0 = z0)) := by
        dsimp [outer]; rw [dif_pos hj]
      rw [h_eq]; exact wellFormedACC_accConst n m _
    · by_cases hj2 : j.val = len + 1
      · have h_eq : outer i j = accConst n m
          (decide (evalGuess (idxEquiv.symm i).1 (idxEquiv.symm i).2 (Fin.last len) = target)) := by
          dsimp [outer]; rw [dif_neg hj, dif_pos hj2]
        rw [h_eq]; exact wellFormedACC_accConst n m _
      · have h_eq : outer i j = checkStep ⟨j.val - 1, by omega⟩
          (evalGuess (idxEquiv.symm i).1 (idxEquiv.symm i).2 ⟨j.val - 1, by omega⟩)
          (evalGuess (idxEquiv.symm i).1 (idxEquiv.symm i).2 ⟨j.val, by omega⟩) := by
          dsimp [outer]; rw [dif_neg hj, dif_neg hj2]
        rw [h_eq]; exact hcs_wf _ _ _
  have hlay_out : ∀ i j (q : Fin (outer i j).gateCount), (outer i j).layer q ≤ d + 2 := by
    intro i j
    by_cases hj : j.val = 0
    · have h_eq : outer i j = accConst n m
        (decide (evalGuess (idxEquiv.symm i).1 (idxEquiv.symm i).2 0 = z0)) := by
        dsimp [outer]; rw [dif_pos hj]
      rw [h_eq]
      intro q
      rw [accConst_layer]; omega
    · by_cases hj2 : j.val = len + 1
      · have h_eq : outer i j = accConst n m
          (decide (evalGuess (idxEquiv.symm i).1 (idxEquiv.symm i).2 (Fin.last len) = target)) := by
          dsimp [outer]; rw [dif_neg hj, dif_pos hj2]
        rw [h_eq]
        intro q
        rw [accConst_layer]; omega
      · have h_eq : outer i j = checkStep ⟨j.val - 1, by omega⟩
          (evalGuess (idxEquiv.symm i).1 (idxEquiv.symm i).2 ⟨j.val - 1, by omega⟩)
          (evalGuess (idxEquiv.symm i).1 (idxEquiv.symm i).2 ⟨j.val, by omega⟩) := by
          dsimp [outer]; rw [dif_neg hj, dif_neg hj2]
        rw [h_eq]
        intro q
        exact hcs_lay _ _ _ q
  have h_layer_bound : d + 2 + 2 ≤ max (d + 2) 1 + 5 := by omega
  by_cases h_nIdx : nIdx = 0
  · refine ⟨accConst n m (decide (z0 = target)), wellFormedACC_accConst n m _,
      fun q => by rw [accConst_layer]; omega, ?_, ?_⟩
    · rw [accConst_gateCount]; omega
    · intro x; rw [accAccepts_accConst, decide_eq_true_eq]
      have h1 : len = 0 := by
        have h_prod : Fintype.card (Fin K → Fin len) * Fintype.card (Fin (K+1) → Z) = 0 := by
          have hn : nIdx = Fintype.card Index := rfl
          rw [hn, Fintype.card_prod] at h_nIdx
          exact h_nIdx
        have h2 : Fintype.card (Fin (K+1) → Z) > 0 := Fintype.card_pos_iff.mpr ⟨fun _ => z0⟩
        have h3 : Fintype.card (Fin K → Fin len) = 0 := by
          cases Nat.mul_eq_zero.mp h_prod with
          | inl h => exact h
          | inr h => exfalso; omega
        by_contra h_len
        have h4 : len > 0 := by omega
        have h5 : Fintype.card (Fin K → Fin len) > 0 := Fintype.card_pos_iff.mpr ⟨fun _ => ⟨0, h4⟩⟩
        omega
      subst h1
      have h_last : Fin.last 0 = 0 := rfl
      rw [h_last, hz0 x]
  · have h_pos : nIdx > 0 := by omega
    have _diag : Nonempty (Fin nIdx) := ⟨⟨0, h_pos⟩⟩
    refine
      ⟨accOrAnd outer (d + 2), wellFormedACC_accOrAnd hwf_out hlay_out, fun q => le_trans
      (accOrAnd_layer_le hlay_out q) h_layer_bound, ?_, ?_⟩
    · simp only [accOrAnd_gateCount]
      have h_inner : ∀ i, (∑ j : Fin (len + 2), (outer i j).gateCount) + 1 ≤
          (len + 2) * ((Fintype.card L * Fintype.card Y) * (size_letter + size_driver + 1) + 1) + 1
            := by
        intro i
        have h_bound : ∀ j : Fin (len + 2), (outer i j).gateCount ≤
          (Fintype.card L * Fintype.card Y) * (size_letter + size_driver + 1) + 1 := by
          intro j
          by_cases hj : j.val = 0
          · have h_eq : outer i j = accConst n m
              (decide (evalGuess (idxEquiv.symm i).1 (idxEquiv.symm i).2 0 = z0)) := by
              dsimp [outer]; rw [dif_pos hj]
            rw [h_eq]; rw [accConst_gateCount]; omega
          · by_cases hj2 : j.val = len + 1
            · have h_eq : outer i j = accConst n m
                (decide
                (evalGuess (idxEquiv.symm i).1 (idxEquiv.symm i).2 (Fin.last len) = target)) := by
                dsimp [outer]; rw [dif_neg hj, dif_pos hj2]
              rw [h_eq]; rw [accConst_gateCount]; omega
            · have h_eq : outer i j = checkStep ⟨j.val - 1, by omega⟩
                (evalGuess (idxEquiv.symm i).1 (idxEquiv.symm i).2 ⟨j.val - 1, by omega⟩)
                (evalGuess (idxEquiv.symm i).1 (idxEquiv.symm i).2 ⟨j.val, by omega⟩) := by
                dsimp [outer]; rw [dif_neg hj, dif_neg hj2]
              rw [h_eq]; exact hcs_size _ _ _
        have hsum : (∑ j : Fin (len + 2), (outer i j).gateCount) ≤ (len + 2) *
          ((Fintype.card L * Fintype.card Y) * (size_letter + size_driver + 1) + 1) := by
          exact Finset.sum_le_card_nsmul Finset.univ _ _ (fun j _ => h_bound j) |>.trans (by simp)
        exact Nat.add_le_add_right hsum 1
      have hsum_out : (∑ i : Fin nIdx, ((∑ j : Fin (len + 2), (outer i j).gateCount) + 1)) ≤
          nIdx *
            ((len + 2) * ((Fintype.card L * Fintype.card Y) * (size_letter + size_driver + 1) + 1)
            + 1) := by
        exact Finset.sum_le_card_nsmul Finset.univ _ _ (fun i _ => h_inner i) |>.trans (by simp)
      calc (∑ i : Fin nIdx, ((∑ j : Fin (len + 2), (outer i j).gateCount) + 1)) + 1
        ≤ nIdx *
          ((len + 2) * ((Fintype.card L * Fintype.card Y) * (size_letter + size_driver + 1) + 1) +
          1) + 1 := Nat.add_le_add_right hsum_out 1
        _ = Fintype.card (Fin K → Fin len) * Fintype.card (Fin (K + 1) → Z) *
            ((len + 2) * ((Fintype.card L * Fintype.card Y) * (size_letter + size_driver + 1) + 1)
              + 1) + 1 := by
          have hnIdx : nIdx = Fintype.card Index := rfl
          rw [hnIdx, Fintype.card_prod]
    · intro x
      rw [accAccepts_accOrAnd hwf_out hlay_out]
      constructor
      · rintro ⟨i, hi⟩
        set idx := idxEquiv.symm i
        have h0 : evalGuess idx.1 idx.2 0 = z0 := by
          have H := hi ⟨0, by omega⟩
          dsimp [outer] at H
          exact of_decide_eq_true ((accAccepts_accConst n m _ x).mp H)
        have hlen : evalGuess idx.1 idx.2 (Fin.last len) = target := by
          have H := hi ⟨len + 1, by omega⟩
          dsimp [outer] at H
          rw [dif_pos rfl] at H
          exact of_decide_eq_true ((accAccepts_accConst n m _ x).mp H)
        have hstep : ∀ j : Fin len, evalGuess idx.1 idx.2 j.succ = step (letter j x) (driver j x)
          (evalGuess idx.1 idx.2 j.castSucc) := by
          intro j
          have H := hi ⟨j.val + 1, by omega⟩
          dsimp [outer] at H
          have hj_ne2 : j.val + 1 ≠ len + 1 := by omega
          rw [dif_neg hj_ne2] at H
          have H_acc :=
            (hcs_acc j (evalGuess idx.1 idx.2 ⟨j.val, by omega⟩)
            (evalGuess idx.1 idx.2 ⟨j.val + 1, by omega⟩) x).mp H
          have eq1 : (⟨j.val, by omega⟩ : Fin (len + 1)) = j.castSucc := Fin.ext rfl
          have eq2 : (⟨j.val + 1, by omega⟩ : Fin (len + 1)) = j.succ := Fin.ext rfl
          rw [eq1, eq2] at H_acc
          exact H_acc.symm
        have heval : ∀ j, evalGuess idx.1 idx.2 j = z j x := by
          intro j
          induction j using Fin.inductionOn with
          | zero => rw [h0, hz0]
          | succ j ih => rw [hstep j, hz_succ j x, ih]
        rw [← heval (Fin.last len)]
        exact hlen
      · intro htarget
        have h_nonempty : Nonempty (Fin K → Fin len) := Nonempty.map Prod.fst
          (Fintype.card_pos_iff.mp (show 0 < Fintype.card Index from h_pos))
        obtain ⟨times, vals, heval⟩ := exists_guess_of_changes_le (fun j => z j x) (h_changes x)
          h_nonempty
        set idx : Index := ⟨times, vals⟩
        refine ⟨idxEquiv idx, fun j => ?_⟩
        dsimp [outer]
        rw [Equiv.symm_apply_apply]
        by_cases hj : j.val = 0
        · simp only [hj, ↓reduceDIte]
          refine (accAccepts_accConst n m _ x).mpr (decide_eq_true ?_)
          rw [heval 0, hz0]
        · by_cases hj2 : j.val = len + 1
          · simp only [hj2, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceDIte]
            refine (accAccepts_accConst n m _ x).mpr (decide_eq_true ?_)
            rw [heval (Fin.last len)]
            exact htarget
          · simp only [hj, ↓reduceDIte, hj2]
            have h1' : j.val - 1 < len := by omega
            have eq1 : evalGuess idx.1 idx.2 ⟨j.val - 1, by omega⟩ = z
              (Fin.castSucc ⟨j.val - 1, h1'⟩) x := by
              have h_eq : (⟨j.val - 1, by omega⟩ : Fin (len + 1)) = (Fin.castSucc ⟨j.val - 1, h1'⟩)
                := Fin.ext rfl
              rw [h_eq]
              exact heval _
            have eq2 : evalGuess idx.1 idx.2 ⟨j.val, by omega⟩ = z (Fin.succ ⟨j.val - 1, h1'⟩) x :=
              by
              have h_eq : (⟨j.val, by omega⟩ : Fin (len + 1)) = (Fin.succ ⟨j.val - 1, h1'⟩) :=
                Fin.ext (show j.val = j.val - 1 + 1 by omega)
              rw [h_eq]
              exact heval _
            have H_acc : step (letter ⟨j.val - 1, h1'⟩ x) (driver ⟨j.val - 1, h1'⟩ x)
              (evalGuess idx.1 idx.2 ⟨j.val - 1, by omega⟩) = evalGuess idx.1 idx.2
              ⟨j.val, by omega⟩ := by
              rw [eq1, eq2, hz_succ]
            exact (hcs_acc _ _ _ x).mpr H_acc

end AllenderOQ3.Internal
