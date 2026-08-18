import AllenderOQ3.Internal.TransitionMonoid
import AllenderOQ3.Internal.NonCrossingShift

set_option autoImplicit false
set_option maxHeartbeats 800000

open Classical

namespace AllenderOQ3.Internal

variable {w : Nat}

/-- A configuration is identically true. -/
def IsAllTrue (s : Config w) : Prop := ∀ i, s i = true

/-- A configuration is identically false. -/
def IsAllFalse (s : Config w) : Prop := ∀ i, s i = false

/-- The predecessor of a position in the cyclic order. -/
def finPred (j : Fin w) : Fin w := finShift (w - 1) j

/-- A maximal contiguous block of `true`s of length `len` starting at `start`. -/
def IsCyclicInterval (s : Config w) (start : Fin w) (len : Nat) : Prop :=
  0 < len ∧ len ≤ w ∧
  (∀ k, k < len → s (finShift k start) = true) ∧
  (len < w → s (finShift len start) = false) ∧
  (len < w → s (finPred start) = false)

/-- The count of maximal cyclic contiguous blocks of `true`s in a configuration. -/
noncomputable def intervalCount (s : Config w) : Nat :=
  if w = 0 then 0
  else if IsAllTrue s then 1
  else (Finset.univ.filter (fun i : Fin w => s (finPred i) = false ∧ s i = true)).card

/-- `finShift w j = j` since adding `w` is a full cycle in `Fin w`. -/
private theorem finShift_w (hw : 0 < w) (j : Fin w) : finShift w j = j := by
  apply Fin.ext
  simp [finShift, Nat.add_mod_right, Nat.mod_eq_of_lt j.isLt]

/-- `finPred (finShift 1 j) = j`: predecessor of the successor is the identity. -/
private theorem finPred_finShift_one (hw : 0 < w) (j : Fin w) : finPred (finShift 1 j) = j := by
  simp only [finPred]
  rw [finShift_finShift]
  have : 1 + (w - 1) = w := by omega
  rw [this]
  exact finShift_w hw j

/-- `finShift 1 (finPred j) = j`: successor of the predecessor is the identity. -/
private theorem finShift_one_finPred (hw : 0 < w) (j : Fin w) : finShift 1 (finPred j) = j := by
  simp only [finPred]
  rw [finShift_finShift]
  have : w - 1 + 1 = w := by omega
  rw [this]
  exact finShift_w hw j

/-- Every element of `Fin w` is reachable by iterated `finShift`. -/
private theorem finShift_surj (j i : Fin w) :
    ∃ k : Nat, finShift k j = i := by
  use (i.val + w - j.val)
  apply Fin.ext
  simp [finShift]
  have hj := j.isLt
  have hi := i.isLt
  have h1 : j.val + (i.val + w - j.val) = i.val + w := by omega
  rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt hi]

/-- Every element of `Fin w` is reachable from any other by a shift of size `< w`. -/
theorem finShift_surj_lt (j i : Fin w) : ∃ k : Nat, k < w ∧ finShift k j = i := by
  have hj := j.isLt
  have hi := i.isLt
  refine ⟨(i.val + w - j.val) % w, Nat.mod_lt _ (Nat.zero_lt_of_lt hj), ?_⟩
  apply Fin.ext
  simp only [finShift]
  rw [show (j.val + (i.val + w - j.val) % w) % w = (j.val + (i.val + w - j.val)) % w by
        simp [Nat.add_mod]]
  rw [show j.val + (i.val + w - j.val) = i.val + w by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt hi]

/-- **Every configuration with at least one `true` position contains a maximal cyclic block
of `true`s.**  Walk backwards from a `true` position to the first rising edge, then forwards
to the first falling edge. -/
theorem exists_isCyclicInterval (s : Config w) (j0 : Fin w) (h0 : s j0 = true) :
    ∃ (start : Fin w) (len : Nat), IsCyclicInterval s start len := by
  classical
  have hw : 0 < w := Nat.zero_lt_of_lt j0.isLt
  by_cases hall : ∀ i, s i = true
  · exact ⟨j0, w, hw, le_refl w, fun k _ => hall _, fun h => absurd h (lt_irrefl w),
      fun h => absurd h (lt_irrefl w)⟩
  · push_neg at hall
    obtain ⟨jf, hjf⟩ := hall
    have hjf' : s jf = false := by cases hs : s jf <;> simp_all
    -- the first `true` position at or after `jf`
    have hex : ∃ k : Nat, s (finShift k jf) = true := by
      obtain ⟨k, -, hk⟩ := finShift_surj_lt jf j0
      exact ⟨k, by rw [hk]; exact h0⟩
    set k1 := Nat.find hex with hk1
    have hk1spec : s (finShift k1 jf) = true := Nat.find_spec hex
    have hk1pos : 0 < k1 := by
      rcases Nat.eq_zero_or_pos k1 with h | h
      · exfalso
        rw [h, finShift_zero] at hk1spec
        rw [hjf'] at hk1spec
        exact Bool.false_ne_true hk1spec
      · exact h
    set start : Fin w := finShift k1 jf with hstart
    have hstartT : s start = true := hk1spec
    have hpred : s (finPred start) = false := by
      have h1 : finPred start = finShift (k1 - 1) jf := by
        have h2 : finShift k1 jf = finShift 1 (finShift (k1 - 1) jf) := by
          rw [finShift_finShift]
          congr 1
          omega
        rw [hstart, h2, finPred_finShift_one hw]
      rw [h1]
      have hmin := Nat.find_min hex (m := k1 - 1) (by omega)
      cases hs : s (finShift (k1 - 1) jf) with
      | false => rfl
      | true => exact absurd hs hmin
    -- the first `false` position strictly after `start`
    obtain ⟨m0, hm0lt, hm0⟩ := finShift_surj_lt start jf
    have hm0pos : 0 < m0 := by
      rcases Nat.eq_zero_or_pos m0 with h | h
      · exfalso
        rw [h, finShift_zero] at hm0
        rw [hm0, hjf'] at hstartT
        exact Bool.false_ne_true hstartT
      · exact h
    have hQ : ∃ m : Nat, 0 < m ∧ s (finShift m start) = false :=
      ⟨m0, hm0pos, by rw [hm0]; exact hjf'⟩
    set len := Nat.find hQ with hlen
    obtain ⟨hlenpos, hlenfalse⟩ := Nat.find_spec hQ
    have hlenle : len ≤ m0 := Nat.find_le ⟨hm0pos, by rw [hm0]; exact hjf'⟩
    have hlenlt : len < w := lt_of_le_of_lt hlenle hm0lt
    refine ⟨start, len, hlenpos, le_of_lt hlenlt, ?_, fun _ => hlenfalse, fun _ => hpred⟩
    intro k hk
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, finShift_zero]
      exact hstartT
    · have hmin := Nat.find_min hQ (m := k) hk
      push_neg at hmin
      have hmin' := hmin h
      cases hs : s (finShift k start) with
      | false => exact absurd hs hmin'
      | true => rfl

private theorem finShift_succ_eq (k : Nat) (j : Fin w) :
    finShift (k + 1) j = finShift 1 (finShift k j) := by
  rw [finShift_finShift]

/-- `finPred` is an injection on `Fin w`. -/
private theorem finPred_injective (hw : 0 < w) : Function.Injective (finPred (w := w)) := by
  intro a b hab
  have := congrArg (finShift 1) hab
  rwa [finShift_one_finPred hw, finShift_one_finPred hw] at this

/-- If no false→true transitions exist and some position is false, then all are false. -/
private theorem allFalse_of_no_ftransition (s : Config w) (hw : 0 < w)
    (hno : ∀ x : Fin w, s (finPred x) = false → s x = false)
    (j : Fin w) (hj : s j = false) : IsAllFalse s := by
  intro i
  obtain ⟨k, hk⟩ := finShift_surj j i
  rw [← hk]; clear hk i
  induction k with
  | zero => simpa [finShift_zero] using hj
  | succ k ih =>
    rw [finShift_succ_eq]
    apply hno
    rw [finPred_finShift_one hw]
    exact ih

/-- The number of true→false transitions at positions measured by `s ∘ finPred` is the
    same as counting `s(i) = true` positions, because `finPred` is a bijection. -/
private theorem card_filter_finPred_true (s : Config w) (hw : 0 < w) :
    (Finset.univ.filter (fun i : Fin w => s (finPred i) = true)).card =
    (Finset.univ.filter (fun i : Fin w => s i = true)).card := by
  apply Finset.card_bij (fun i _ => finPred i)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hi
  · intro a₁ _ a₂ _ h
    exact finPred_injective hw h
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    exact ⟨finShift 1 b, by rw [finPred_finShift_one hw]; exact hb, finPred_finShift_one hw b⟩

theorem intervalCount_zero_iff (s : Config w) (hw : 0 < w) : intervalCount s = 0 ↔ IsAllFalse s := by
  constructor
  · intro h0
    unfold intervalCount at h0
    simp only [if_neg (show ¬ (w = 0) by omega)] at h0
    by_cases hat : IsAllTrue s
    · simp [hat] at h0
    · simp only [if_neg hat] at h0
      have hno : ∀ x : Fin w, s (finPred x) = false → s x = false := by
        intro x hpx
        by_contra hx
        have hxt : s x = true := by cases (s x) <;> simp_all
        have hmem : x ∈ Finset.univ.filter (fun i : Fin w => s (finPred i) = false ∧ s i = true) := by
          simp [hpx, hxt]
        have hpos := Finset.card_pos.mpr ⟨x, hmem⟩
        omega
      simp only [IsAllTrue, not_forall, Bool.not_eq_true] at hat
      obtain ⟨j, hj⟩ := hat
      exact allFalse_of_no_ftransition s hw hno j hj
  · intro hf
    unfold intervalCount
    simp only [if_neg (show ¬ (w = 0) by omega)]
    have hnat : ¬ IsAllTrue s := by
      intro hat
      have := hat ⟨0, hw⟩
      rw [hf ⟨0, hw⟩] at this
      simp at this
    simp only [if_neg hnat]
    apply Finset.card_eq_zero.mpr
    simp only [Finset.filter_eq_empty_iff, Finset.mem_univ, true_implies, not_and]
    intro x _; rw [hf x]; simp

theorem intervalCount_one_iff_allTrue (s : Config w) (hw : 0 < w) : IsAllTrue s → intervalCount s = 1 := by
  intro h
  simp only [intervalCount]
  rw [if_neg (show ¬(w = 0) by omega)]
  rw [if_pos h]

/-- The number of false→true transitions equals the number of true→false transitions. -/
theorem count_false_true_eq_count_true_false (s : Config w) (hw : 0 < w) :
    (Finset.univ.filter (fun i : Fin w => s (finPred i) = false ∧ s i = true)).card =
    (Finset.univ.filter (fun i : Fin w => s i = true ∧ s (finShift 1 i) = false)).card := by
  classical
  set S₁ := Finset.univ.filter (fun i : Fin w => s (finPred i) = false ∧ s i = true) with hS₁
  set S₂ := Finset.univ.filter (fun i : Fin w => s i = true ∧ s (finShift 1 i) = false) with hS₂
  set T := Finset.univ.filter (fun i : Fin w => s (finPred i) = true ∧ s i = false) with hT
  -- Step A: `|S₂| = |T|` via the bijection `finShift 1 : S₂ → T`.
  have hS₂T : S₂.card = T.card := by
    apply Finset.card_bij (fun i _ => finShift 1 i)
    · intro i hi
      rw [hS₂, Finset.mem_filter] at hi
      obtain ⟨-, hi1, hi2⟩ := hi
      rw [hT, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by rw [finPred_finShift_one hw]; exact hi1, hi2⟩
    · intro a₁ _ a₂ _ h
      have h' := congrArg finPred h
      rwa [finPred_finShift_one hw, finPred_finShift_one hw] at h'
    · intro b hb
      rw [hT, Finset.mem_filter] at hb
      obtain ⟨-, hb1, hb2⟩ := hb
      refine ⟨finPred b, ?_, finShift_one_finPred hw b⟩
      rw [hS₂, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, hb1, ?_⟩
      rw [finShift_one_finPred hw]
      exact hb2
  -- Step B: `|S₁| = |T|`, since both are the complements of the same set `C`
  -- inside two equinumerous sets.
  have hS₁T : S₁.card = T.card := by
    set A := Finset.univ.filter (fun i : Fin w => s i = true) with hA
    set B := Finset.univ.filter (fun i : Fin w => s (finPred i) = true) with hB
    have hAB : B.card = A.card := card_filter_finPred_true s hw
    set C := Finset.univ.filter (fun i : Fin w => s i = true ∧ s (finPred i) = true) with hC
    have hAC : A = C ∪ S₁ := by
      ext i
      simp only [hA, hC, hS₁, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hi
        rcases Bool.eq_false_or_eq_true (s (finPred i)) with hs | hs
        · exact Or.inl ⟨hi, hs⟩
        · exact Or.inr ⟨hs, hi⟩
      · rintro (⟨h1, -⟩ | ⟨-, h2⟩)
        · exact h1
        · exact h2
    have hBC : B = C ∪ T := by
      ext i
      simp only [hB, hC, hT, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hi
        rcases Bool.eq_false_or_eq_true (s i) with hs | hs
        · exact Or.inl ⟨hs, hi⟩
        · exact Or.inr ⟨hi, hs⟩
      · rintro (⟨-, h2⟩ | ⟨h1, -⟩)
        · exact h2
        · exact h1
    have hdisjAC : Disjoint C S₁ := by
      rw [Finset.disjoint_left]
      intro i hi hi'
      rw [hC, Finset.mem_filter] at hi
      rw [hS₁, Finset.mem_filter] at hi'
      rw [hi'.2.1] at hi
      exact Bool.false_ne_true hi.2.2
    have hdisjBC : Disjoint C T := by
      rw [Finset.disjoint_left]
      intro i hi hi'
      rw [hC, Finset.mem_filter] at hi
      rw [hT, Finset.mem_filter] at hi'
      rw [hi'.2.2] at hi
      exact Bool.false_ne_true hi.2.1
    rw [hAC, Finset.card_union_of_disjoint hdisjAC, hBC,
      Finset.card_union_of_disjoint hdisjBC] at hAB
    omega
  rw [hS₁T, ← hS₂T]

end AllenderOQ3.Internal
