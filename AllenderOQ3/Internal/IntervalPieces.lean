import AllenderOQ3.Internal.ConfigInterval

/-!
# Interval pieces of a configuration

A configuration `x : Config w` decomposes into its maximal cyclic blocks of
`true`s.  This file packages each such block as a configuration in its own
right (a *piece*), collects the pieces into a `Finset (Config w)`
(`intervalsOf x`), and proves the two structural facts the localized HMV
analysis needs:

* `mem_intervalsOf_true_iff` — pointwise reconstruction: a coordinate of `x` is
  `true` iff it is `true` in some piece of `x`;
* `isIntervalConfig_of_mem_intervalsOf` — every piece is itself an *interval
  configuration* (`IsIntervalConfig`), i.e. consists of a single maximal block.

The reconstruction is proved by an explicit walk: from a `true` coordinate,
step backwards to the first rising edge and forwards to the first falling edge;
the wrap-around is excluded by comparing both walks with a fixed `false`
coordinate.

Everything here is `sorry`-free.
-/

set_option autoImplicit false

namespace AllenderOQ3
namespace Internal

attribute [local instance] Classical.propDecidable

variable {w : Nat}

/-! ## Shift arithmetic -/

/-- A full turn of the cyclic shift is the identity. -/
theorem finShift_full (j : Fin w) : finShift w j = j := by
  apply Fin.ext
  rw [finShift_val, Nat.add_mod_right, Nat.mod_eq_of_lt j.isLt]

/-- Successor of the predecessor is the identity. -/
theorem finShift_one_pred (j : Fin w) : finShift 1 (finPred j) = j := by
  have hw : 0 < w := j.pos
  simp only [finPred]
  rw [finShift_finShift]
  have h : w - 1 + 1 = w := by omega
  rw [h]
  exact finShift_full j

/-- Predecessor of the successor is the identity. -/
theorem finPred_shift_one (j : Fin w) : finPred (finShift 1 j) = j := by
  have hw : 0 < w := j.pos
  simp only [finPred]
  rw [finShift_finShift]
  have h : 1 + (w - 1) = w := by omega
  rw [h]
  exact finShift_full j

/-- Shift amounts below `w` act freely: equal shifts of the same point have
equal amounts. -/
theorem finShift_amount_inj {a b : Nat} {j : Fin w} (ha : a < w) (hb : b < w)
    (h : finShift a j = finShift b j) : a = b := by
  have hval := congrArg Fin.val h
  rw [finShift_val, finShift_val] at hval
  have hj := j.isLt
  rcases Nat.lt_or_ge (j.val + a) w with h1 | h1
  · rw [Nat.mod_eq_of_lt h1] at hval
    rcases Nat.lt_or_ge (j.val + b) w with h2 | h2
    · rw [Nat.mod_eq_of_lt h2] at hval; omega
    · rw [Nat.mod_eq_sub_mod h2, Nat.mod_eq_of_lt (by omega)] at hval; omega
  · rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)] at hval
    rcases Nat.lt_or_ge (j.val + b) w with h2 | h2
    · rw [Nat.mod_eq_of_lt h2] at hval; omega
    · rw [Nat.mod_eq_sub_mod h2, Nat.mod_eq_of_lt (by omega)] at hval; omega

/-! ## Predecessor iterates -/

/-- One forward step undoes the innermost of `p + 1` backward steps. -/
theorem finShift_one_finPred_iterate (p : Nat) (j : Fin w) :
    finShift 1 (finPred^[p + 1] j) = finPred^[p] j := by
  have h : finPred^[p + 1] j = finPred (finPred^[p] j) :=
    Function.iterate_succ_apply' finPred p j
  rw [h, finShift_one_pred]

/-- A shift by `k ≤ p` undoes `k` of `p` backward steps. -/
theorem finShift_finPred_iterate {p k : Nat} (hkp : k ≤ p) (j : Fin w) :
    finShift k (finPred^[p] j) = finPred^[p - k] j := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk : k ≤ p := by omega
    have h1 : finShift 1 (finShift k (finPred^[p] j)) = finShift (k + 1) (finPred^[p] j) := by
      rw [finShift_finShift]
    rw [← h1, ih hk]
    have h2 : p - k = (p - (k + 1)) + 1 := by omega
    rw [h2]
    exact finShift_one_finPred_iterate _ j

/-- Shifting by `p` undoes `p` backward steps. -/
theorem finShift_finPred_iterate_cancel (p : Nat) (j : Fin w) :
    finShift p (finPred^[p] j) = j := by
  have h := finShift_finPred_iterate (le_refl p) j
  simpa using h

/-- `p` backward steps undo a shift by `p`. -/
theorem finPred_iterate_finShift_cancel (p : Nat) (j : Fin w) :
    finPred^[p] (finShift p j) = j := by
  induction p with
  | zero => simp
  | succ p ih =>
    have h1 : finShift (p + 1) j = finShift 1 (finShift p j) := by
      rw [finShift_finShift]
    rw [h1, Function.iterate_succ_apply, finPred_shift_one]
    exact ih

/-! ## Pieces -/

open Classical in
/-- The configuration whose `true`s are exactly the block of length `len`
starting at `start`. -/
noncomputable def pieceConfig (start : Fin w) (len : Nat) : Config w :=
  fun j => decide (∃ k, k < len ∧ finShift k start = j)

theorem pieceConfig_true_iff {start : Fin w} {len : Nat} {j : Fin w} :
    pieceConfig start len j = true ↔ ∃ k, k < len ∧ finShift k start = j := by
  constructor
  · intro h
    exact of_decide_eq_true h
  · intro h
    exact decide_eq_true h

/-- `y` is the configuration of one maximal block of `x`. -/
def IsIntervalPiece (x y : Config w) : Prop :=
  ∃ (start : Fin w) (len : Nat),
    IsCyclicInterval x start len ∧ y = pieceConfig start len

/-- A configuration consisting of a single maximal block. -/
def IsIntervalConfig (y : Config w) : Prop := IsIntervalPiece y y

open Classical in
/-- The pieces of `x`, as a finite set of configurations. -/
noncomputable def intervalsOf (x : Config w) : Finset (Config w) :=
  Finset.univ.filter (fun y => IsIntervalPiece x y)

theorem mem_intervalsOf {x y : Config w} :
    y ∈ intervalsOf x ↔ IsIntervalPiece x y := by
  simp [intervalsOf]

/-- A piece of `x` is `true` only where `x` is. -/
theorem le_of_isIntervalPiece {x y : Config w} (h : IsIntervalPiece x y) {j : Fin w}
    (hj : y j = true) : x j = true := by
  obtain ⟨start, len, hcyc, rfl⟩ := h
  obtain ⟨k, hk, rfl⟩ := pieceConfig_true_iff.mp hj
  exact hcyc.2.2.1 k hk

/-- **Every piece is an interval configuration.** -/
theorem isIntervalConfig_of_mem_intervalsOf {x y : Config w}
    (h : y ∈ intervalsOf x) : IsIntervalConfig y := by
  obtain ⟨start, len, hcyc, rfl⟩ := mem_intervalsOf.mp h
  obtain ⟨hpos, hlew, htrue, hright, hleft⟩ := hcyc
  refine ⟨start, len, ⟨hpos, hlew, ?_, ?_, ?_⟩, rfl⟩
  · intro k hk
    exact pieceConfig_true_iff.mpr ⟨k, hk, rfl⟩
  · intro hlt
    cases hval : pieceConfig start len (finShift len start) with
    | false => rfl
    | true =>
      obtain ⟨k, hk, hkeq⟩ := pieceConfig_true_iff.mp hval
      have : k = len := finShift_amount_inj (by omega) hlt hkeq
      omega
  · intro hlt
    cases hval : pieceConfig start len (finPred start) with
    | false => rfl
    | true =>
      obtain ⟨k, hk, hkeq⟩ := pieceConfig_true_iff.mp hval
      have hw : 0 < w := start.pos
      have hpred : finPred start = finShift (w - 1) start := rfl
      rw [hpred] at hkeq
      have : k = w - 1 := finShift_amount_inj (by omega) (by omega) hkeq
      omega

/-! ## The block containing a given `true` coordinate -/

/-- **Walk lemma**: every `true` coordinate of `x` lies in some piece of `x`. -/
theorem exists_piece_mem {x : Config w} {j : Fin w} (hj : x j = true) :
    ∃ y ∈ intervalsOf x, y j = true := by
  classical
  have hw : 0 < w := j.pos
  by_cases hall : IsAllTrue x
  · refine ⟨pieceConfig j w, mem_intervalsOf.mpr ⟨j, w, ?_, rfl⟩, ?_⟩
    · exact ⟨hw, le_refl w, fun k _ => hall _,
        fun h => absurd h (lt_irrefl w), fun h => absurd h (lt_irrefl w)⟩
    · refine pieceConfig_true_iff.mpr ⟨0, hw, ?_⟩
      simp
  · -- a `false` coordinate exists
    simp only [IsAllTrue, not_forall] at hall
    obtain ⟨jf, hjf⟩ := hall
    have hxjf : x jf = false := by
      cases hval : x jf with
      | false => rfl
      | true => exact absurd hval hjf
    -- backward walk: first rising edge behind `j`
    obtain ⟨kb, hkblt, hkbeq⟩ := finShift_surj_lt jf j
    have hkbpos : 0 < kb := by
      rcases Nat.eq_zero_or_pos kb with h | h
      · exfalso
        rw [h, finShift_zero] at hkbeq
        rw [hkbeq] at hxjf
        rw [hxjf] at hj
        exact Bool.false_ne_true hj
      · exact h
    have hjfpred : finPred^[kb] j = jf := by
      rw [← hkbeq]
      exact finPred_iterate_finShift_cancel kb jf
    have hb : ∃ p, x (finPred^[p + 1] j) = false := by
      refine ⟨kb - 1, ?_⟩
      rw [show kb - 1 + 1 = kb by omega, hjfpred]
      exact hxjf
    set p0 := Nat.find hb with hp0
    have hp0spec : x (finPred^[p0 + 1] j) = false := Nat.find_spec hb
    have hp0le : p0 ≤ kb - 1 := by
      rw [hp0]
      apply Nat.find_le
      rw [show kb - 1 + 1 = kb by omega, hjfpred]
      exact hxjf
    have hp0w : p0 + 1 < w := by omega
    have hback : ∀ i, i ≤ p0 → x (finPred^[i] j) = true := by
      intro i hi
      cases i with
      | zero => simpa using hj
      | succ p =>
        have hp : p < p0 := by omega
        have hmin := Nat.find_min hb hp
        cases hval : x (finPred^[p + 1] j) with
        | false => exact absurd hval hmin
        | true => rfl
    -- forward walk: first falling edge after `j`
    obtain ⟨kf, -, hkfeq⟩ := finShift_surj_lt j jf
    have hkfpos : 0 < kf := by
      rcases Nat.eq_zero_or_pos kf with h | h
      · exfalso
        rw [h, finShift_zero] at hkfeq
        rw [hkfeq] at hj
        rw [hj] at hxjf
        simp at hxjf
      · exact h
    have hf : ∃ q, x (finShift (q + 1) j) = false := by
      refine ⟨kf - 1, ?_⟩
      rw [show kf - 1 + 1 = kf by omega, hkfeq]
      exact hxjf
    set q0 := Nat.find hf with hq0
    have hq0spec : x (finShift (q0 + 1) j) = false := Nat.find_spec hf
    have hforw : ∀ i, i ≤ q0 → x (finShift i j) = true := by
      intro i hi
      cases i with
      | zero => simpa using hj
      | succ q =>
        have hq : q < q0 := by omega
        have hmin := Nat.find_min hf hq
        cases hval : x (finShift (q + 1) j) with
        | false => exact absurd hval hmin
        | true => rfl
    -- the two walks cannot wrap around each other
    have hcapfalse : x (finShift (w - p0 - 1) j) = false := by
      have hjrec : finShift (p0 + 1) (finPred^[p0 + 1] j) = j :=
        finShift_finPred_iterate_cancel (p0 + 1) j
      have h1 : finShift (w - p0 - 1) j
          = finShift (w - p0 - 1) (finShift (p0 + 1) (finPred^[p0 + 1] j)) := by
        rw [hjrec]
      rw [h1, finShift_finShift, show (p0 + 1) + (w - p0 - 1) = w by omega,
        finShift_full]
      exact hp0spec
    have hq0le : q0 ≤ w - p0 - 2 := by
      rw [hq0]
      apply Nat.find_le
      rw [show w - p0 - 2 + 1 = w - p0 - 1 by omega]
      exact hcapfalse
    -- assemble the block
    set start := finPred^[p0] j with hstart
    set len := p0 + q0 + 1 with hlen
    have hlenw : len < w := by omega
    have hshift_start : ∀ k, k ≤ p0 → finShift k start = finPred^[p0 - k] j := by
      intro k hk
      exact finShift_finPred_iterate hk j
    have hstart_j : finShift p0 start = j := finShift_finPred_iterate_cancel p0 j
    have hshift_forw : ∀ i, finShift (p0 + i) start = finShift i j := by
      intro i
      have h1 : finShift (p0 + i) start = finShift i (finShift p0 start) := by
        rw [finShift_finShift]
      rw [h1, hstart_j]
    have hcyc : IsCyclicInterval x start len := by
      refine ⟨by omega, by omega, ?_, ?_, ?_⟩
      · intro k hk
        rcases Nat.lt_or_ge k (p0 + 1) with h | h
        · rw [hshift_start k (by omega)]
          exact hback _ (by omega)
        · have h2 : k = p0 + (k - p0) := by omega
          rw [h2, hshift_forw]
          exact hforw _ (by omega)
      · intro _
        have h1 : len = p0 + (q0 + 1) := by omega
        rw [h1, hshift_forw]
        exact hq0spec
      · intro _
        have h1 : finPred start = finPred^[p0 + 1] j :=
          (Function.iterate_succ_apply' finPred p0 j).symm
        rw [h1]
        exact hp0spec
    refine ⟨pieceConfig start len, mem_intervalsOf.mpr ⟨start, len, hcyc, rfl⟩, ?_⟩
    exact pieceConfig_true_iff.mpr ⟨p0, by omega, hstart_j⟩

/-- **Pointwise reconstruction**: `x` is `true` at `j` iff some piece of `x`
is. -/
theorem mem_intervalsOf_true_iff {x : Config w} {j : Fin w} :
    x j = true ↔ ∃ y ∈ intervalsOf x, y j = true := by
  constructor
  · exact exists_piece_mem
  · rintro ⟨y, hy, hyj⟩
    exact le_of_isIntervalPiece (mem_intervalsOf.mp hy) hyj

end Internal
end AllenderOQ3
