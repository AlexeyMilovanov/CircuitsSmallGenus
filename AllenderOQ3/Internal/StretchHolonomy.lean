import AllenderOQ3.Internal.StretchTranscript
import AllenderOQ3.Internal.ACCGadgets
import AllenderOQ3.Internal.ACCSumMod
import AllenderOQ3.Internal.ModulusLift
import AllenderOQ3.Internal.WordProblemReduction

/-!
# The holonomy hypothesis, and the reduction of the stretch leaf to it

`StretchPrefixACC w` (see `StretchPrefixReduction`) is the last circuit-shaped
obligation of the cascade.  This file separates its *circuit* content, which is
discharged here, from its *algebraic* content, which is isolated as
`StretchHolonomy w`.

`StretchHolonomy w` says that along an order-isomorphism stretch the restriction
of the running product to the range of the incoming prefix `gin` is
**compressible**: there is a fixed modulus `N`, a family of candidate
restrictions `state gin v` indexed by `v` modulo `N`, and a per-letter exponent
`expo gin g < N`, such that the product of any shape-constant stretch acts on the
range of `gin` as `state gin` at the *sum of the exponents of its letters*.  This
is exactly the cyclic-holonomy input of the Barrington–Thérien cascade for
`NonCrossing w`, and it mentions no circuits at all.

`stretchPrefixACC_of_stretchHolonomy` builds the required `ACC[2N]` circuits from
it.  The construction is guess-free: for a block `[a, c)` the circuit

* computes, for every position `i` of the block, the prefix sum
  `t i = ∑_{a ≤ j < i} expo (letter j)` modulo `N` with `MOD` gates
  (`exists_acc_sumMod`);
* checks, position by position, that the letter at `i` moves `state (t i)` to
  `state (t i + expo (letter i))` on the range of `gin` (a constant-size test of
  the letter value and of `t i`); and
* checks that `state (t c)` composed with `gin` is `gout`.

The checks are *verifications*, not promises, so the circuit is sound on every
input (`mul_blockProd_eq_of_transcript`); `StretchHolonomy` is used only to see
that on a genuine order-isomorphism stretch all the checks succeed.

**Warning.**  `StretchHolonomy w` is *false* for every `0 < w`
(`not_stretchHolonomy_of_pos` in `StretchHolonomyObstruction`): a sum of
per-letter exponents cannot distinguish `g * h` from `h * g`, and out of a
rank-one prefix — a constant map, which lies in `NonCrossing w` — every word is
shape-constant.  The reduction below is therefore vacuous as it stands; it is
kept because the circuit construction it contains (`MOD`-gate prefix sums with
position-wise verification, sound on every input) is what a corrected algebraic
hypothesis, one whose compressed state also records the reached `L`-class, will
have to be plugged into.

Everything here is `sorry`-free.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace AllenderOQ3
namespace Internal

variable {w : Nat}

attribute [local instance] Classical.propDecidable

/-! ## Elementary rewriting of window prefixes -/

/-- A prefix of a window word is the product over the corresponding range. -/
theorem prefixEnd_range'_map {n : Nat} (letter : Nat → (Fin n → Bool) → TransMonoid w)
    (x : Fin n → Bool) (s k j : Nat) (hj : j ≤ k) :
    prefixEnd ((List.range' s k).map (fun i => letter i x)) j
      = ((List.range' s j).map (fun i => letter i x)).prod := by
  rw [prefixEnd, wordEnd, ← List.map_take, List.take_range'_of_length_ge hj]

/-- The product over a range is a block product. -/
theorem range'_map_prod_eq_blockProd {n : Nat} (letter : Nat → (Fin n → Bool) → TransMonoid w)
    (x : Fin n → Bool) (start a k : Nat) :
    ((List.range' (start + a) k).map (fun i => letter i x)).prod
      = blockProd letter start a (a + k) x := by
  simp [blockProd]

/-- The sum of a per-letter exponent over a range. -/
theorem sum_map_expo_range' {n : Nat} (letter : Nat → (Fin n → Bool) → TransMonoid w)
    (x : Fin n → Bool) (expo : TransMonoid w → Nat) (s : Nat) :
    ∀ k : Nat, (((List.range' s k).map (fun i => letter i x)).map expo).sum
      = ∑ j ∈ Finset.range k, expo (letter (s + j) x) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      rw [List.range'_concat]
      simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero]
      rw [ih, Finset.sum_range_succ]
      simp

/-- The window shape is the rank/shape coordinate of the corresponding prefix
product. -/
theorem windowShape_eq_shapeCoord_blockProd {n : Nat}
    (letter : Nat → (Fin n → Bool) → TransMonoid w) (start len : Nat) (x : Fin n → Bool)
    {u : Nat} (hu : u ≤ len) :
    windowShape letter start len x u = shapeCoord (blockProd letter start 0 u x) := by
  rw [windowShape, letterWindowWord, prefixEnd_range'_map letter x start len u hu]
  have := range'_map_prod_eq_blockProd letter x start 0 u
  simp only [Nat.add_zero, Nat.zero_add] at this ⊢
  rw [this]

/-- Step-wise constancy of the window shape propagates along the stretch. -/
theorem windowShape_const_of_steps {n : Nat}
    (letter : Nat → (Fin n → Bool) → TransMonoid w) (start len : Nat) (x : Fin n → Bool)
    {a c : Nat}
    (hstep : ∀ i, a ≤ i → i < c →
      windowShape letter start len x i = windowShape letter start len x (i + 1)) :
    ∀ u, a ≤ u → u ≤ c → windowShape letter start len x u = windowShape letter start len x a := by
  intro u hau huc
  induction u, hau using Nat.le_induction with
  | base => rfl
  | succ u hau ih =>
      have h1 : u ≤ c := by omega
      rw [← hstep u hau (by omega)]
      exact ih h1

/-! ## The holonomy hypothesis -/

/-- **The cyclic-holonomy hypothesis at one incoming prefix `gin`, with modulus
`N`.**

The action on the range of `gin` of any shape-constant stretch of
`NonCrossing w` letters only depends on the sum, modulo `N`, of a per-letter
exponent `expo`.  `state v` is the candidate restriction attached to the residue
`v`; it is periodic in `v`, it is the identity at `v = 0`, and along an
order-isomorphism stretch it computes the true action of the stretch.  This is a
purely algebraic statement: no circuits occur in it. -/
def StretchHolonomyAt (w N : Nat) (gin : TransMonoid w) : Prop :=
  ∃ (state : Nat → Config w → Config w) (expo : TransMonoid w → Nat),
    (∀ g, expo g < N) ∧
    (∀ v, state v = state (v % N)) ∧
    (∀ p ∈ rangeTrans gin, state 0 p = p) ∧
    (∀ word : List (TransMonoid w),
      gin ∈ NonCrossing w →
      (∀ g ∈ word, g ∈ NonCrossing w) →
      (∀ k, k ≤ word.length →
        shapeCoord (gin * prefixEnd word k) = shapeCoord gin) →
      ∀ p ∈ rangeTrans gin,
        runTrans word.prod p = state ((word.map expo).sum) p)

/-- **The cyclic-holonomy hypothesis for `NonCrossing w`**: one modulus `N` that
works (through `StretchHolonomyAt`) for every incoming prefix.

This is *false* for `0 < w`; see `not_stretchHolonomy_of_pos`. -/
def StretchHolonomy (w : Nat) : Prop :=
  ∃ N : Nat, 0 < N ∧ ∀ gin : TransMonoid w, StretchHolonomyAt w N gin

/-! ## From the holonomy hypothesis to the stretch obligation -/

/-- **The cyclic holonomy of order-isomorphism stretches puts the stretch
obligation in `ACC0`.** -/
theorem stretchPrefixACC_of_stretchHolonomy (H : StretchHolonomy w) : StretchPrefixACC w := by
  classical
  obtain ⟨N, hNpos, hol⟩ := H
  simp only [StretchHolonomyAt] at hol
  choose state expo hexpo_lt hstate_per hstate_zero hstate_word using hol
  obtain ⟨M, hMdef⟩ : ∃ M : Nat, M = 2 * N := ⟨_, rfl⟩
  have hMpos : 0 < M := by omega
  have hM2 : 2 ≤ M := by omega
  have hdvdN : N ∣ M := ⟨2, by omega⟩
  have hdvd2 : (2 : Nat) ∣ M := ⟨N, by omega⟩
  obtain ⟨A0, hA0def⟩ : ∃ A0 : Nat, A0 = Fintype.card (TransMonoid w) := ⟨_, rfl⟩
  obtain ⟨K1, hK1def⟩ : ∃ K1 : Nat, K1 = A0 * (M + 2) + 2 * A0 + 1 := ⟨_, rfl⟩
  obtain ⟨K2, hK2def⟩ : ∃ K2 : Nat, K2 = K1 + M + 1 := ⟨_, rfl⟩
  obtain ⟨K3, hK3def⟩ : ∃ K3 : Nat, K3 = M ^ N * ((N + 1) * K2 + 1) + 1 := ⟨_, rfl⟩
  obtain ⟨K4, hK4def⟩ : ∃ K4 : Nat, K4 = N * (K3 + K1 + 1) + 1 := ⟨_, rfl⟩
  obtain ⟨K5, hK5def⟩ : ∃ K5 : Nat, K5 = K4 + 2 := ⟨_, rfl⟩
  refine ⟨M, 15, 3 + K5, hM2, ?_⟩
  intro n letter size hgen hrec start len
  obtain ⟨S1, hS1def⟩ : ∃ S1 : Nat, S1 = A0 * ((M + 2) * size + 2) + 1 := ⟨_, rfl⟩
  obtain ⟨SP, hSPdef⟩ : ∃ SP : Nat, SP = M ^ N * ((N + 1) * (len * S1 + M + 1) + 1) + 1 :=
    ⟨_, rfl⟩
  obtain ⟨SC, hSCdef⟩ : ∃ SC : Nat, SC = N * (SP + S1 + 1) + 1 := ⟨_, rfl⟩
  -- the single letters, recognised at the common modulus `M`
  have hletter : ∀ (i : Nat) (mm : TransMonoid w),
      ∃ b : ACCCircuit n M, WellFormedACC b ∧ (∀ q, b.layer q ≤ 6) ∧
        b.gateCount ≤ (M + 2) * size ∧ (∀ x, ACCAccepts b x ↔ letter i x = mm) := by
    intro i mm
    obtain ⟨b, hbwf, hblay, hbsz, hbacc⟩ := hrec i mm
    refine ⟨accModulusLift b hdvd2, wellFormedACC_accModulusLift b hdvd2 hbwf, ?_, ?_, ?_⟩
    · intro q
      exact accModulusLift_layer_le (c := b) (hM := hdvd2) (d := 2) hblay q
    · exact le_trans (accModulusLift_gateCount_le b hdvd2) (Nat.mul_le_mul_left _ hbsz)
    · intro x
      rw [evalACC_accModulusLift_of_pos hMpos hbwf x]
      exact hbacc x
  choose L hLwf hLlay hLsz hLacc using hletter
  -- position-wise recognisers for the exponent of the letter
  have hexpRec : ∀ (gin : TransMonoid w) (q : Nat) (v : Fin N),
      ∃ b : ACCCircuit n M, WellFormedACC b ∧ (∀ t, b.layer t ≤ 8) ∧
        b.gateCount ≤ S1 ∧
        (∀ x, ACCAccepts b x ↔ expo gin (letter q x) = (v : Nat)) := by
    intro gin q v
    obtain ⟨b, h1, h2, h3, h4⟩ :=
      exists_acc_letterPred (L := L q) (p := letter q)
        (P := fun g => expo gin g = (v : Nat)) (hLwf q) (hLlay q) (hLsz q) (hLacc q)
    exact ⟨b, h1, fun t => le_trans (h2 t) (by omega), by rw [hS1def, hA0def]; exact h3, h4⟩
  choose R hRwf hRlay hRsz hRacc using hexpRec
  -- prefix sums of the exponents, modulo `N`
  have hpsum : ∀ (gin : TransMonoid w) (a k : Nat) (v : Fin N),
      ∃ b : ACCCircuit n M, WellFormedACC b ∧ (∀ t, b.layer t ≤ 11) ∧
        b.gateCount ≤ M ^ N * ((N + 1) * (k * S1 + M + 1) + 1) + 1 ∧
        (∀ x, ACCAccepts b x ↔
          (∑ j ∈ Finset.range k, expo gin (letter (start + a + j) x)) % N = (v : Nat)) := by
    intro gin a k v
    obtain ⟨b, h1, h2, h3, h4⟩ :=
      exists_acc_sumMod (m := M) (N := N) hMpos hdvdN
        (val := fun (j : Fin k) x => expo gin (letter (start + a + (j : Nat)) x))
        (fun j x => hexpo_lt gin _)
        (rec := fun (j : Fin k) (u : Fin N) => R gin (start + a + (j : Nat)) u)
        (fun j u => hRwf _ _ _) (fun j u t => hRlay _ _ _ t) (fun j u => hRsz _ _ _)
        (fun j u x => hRacc gin (start + a + (j : Nat)) u x) ((v : Nat))
    refine ⟨b, h1, fun t => le_trans (h2 t) (by omega), h3, fun x => ?_⟩
    rw [h4 x, Nat.mod_eq_of_lt v.isLt]
    exact Iff.of_eq (congrArg (fun s => s % N = (v : Nat))
      (Fin.sum_univ_eq_sum_range (fun j => expo gin (letter (start + a + j) x)) k))
  choose PS hPSwf hPSlay hPSsz hPSacc using hpsum
  -- the per-position compatibility check
  have hqcheck : ∀ (gin : TransMonoid w) (q : Nat) (v : Fin N),
      ∃ b : ACCCircuit n M, WellFormedACC b ∧ (∀ t, b.layer t ≤ 11) ∧
        b.gateCount ≤ S1 ∧
        (∀ x, ACCAccepts b x ↔
          ∀ p ∈ rangeTrans gin, runTrans (letter q x) (state gin (v : Nat) p)
            = state gin ((v : Nat) + expo gin (letter q x)) p) := by
    intro gin q v
    obtain ⟨b, h1, h2, h3, h4⟩ :=
      exists_acc_letterPred (L := L q) (p := letter q)
        (P := fun g => ∀ p ∈ rangeTrans gin, runTrans g (state gin (v : Nat) p)
          = state gin ((v : Nat) + expo gin g) p) (hLwf q) (hLlay q) (hLsz q) (hLacc q)
    exact ⟨b, h1, fun t => le_trans (h2 t) (by omega), by rw [hS1def, hA0def]; exact h3, h4⟩
  choose QC hQCwf hQClay hQCsz hQCacc using hqcheck
  -- the recogniser for a legitimate block `[a, c)` of the window
  have hmain : ∀ (a c : Nat) (gin gout : TransMonoid w), a ≤ c → c ≤ len →
      ∃ b : ACCCircuit n M, WellFormedACC b ∧ (∀ q, b.layer q ≤ 15) ∧
        b.gateCount ≤ (len + 1) * SC + 2 ∧
        (∀ x, ACCAccepts b x → gin * blockProd letter start a c x = gout) ∧
        (∀ x, (∀ i, a ≤ i → i < c →
            windowShape letter start len x i = windowShape letter start len x (i + 1)) →
          gin = blockProd letter start 0 a x → gout = blockProd letter start 0 c x →
          ACCAccepts b x) := by
    intro a c gin gout hac hcl
    set Tv : Nat → (Fin n → Bool) → Nat := fun k x =>
      (∑ j ∈ Finset.range k, expo gin (letter (start + a + j) x)) % N with hTvdef
    have hTv_lt : ∀ k x, Tv k x < N := fun k x => Nat.mod_lt _ hNpos
    have hTv_zero : ∀ x, Tv 0 x = 0 := by intro x; simp [hTvdef]
    have hTv_succ : ∀ k x, Tv (k + 1) x
        = (Tv k x + expo gin (letter (start + a + k) x)) % N := by
      intro k x
      simp only [hTvdef, Finset.sum_range_succ]
      rw [Nat.mod_add_mod]
    -- the per-position checks
    have hCC : ∀ idx : Fin (c - a + 1), ∃ b : ACCCircuit n M, WellFormedACC b ∧
        (∀ q, b.layer q ≤ 13) ∧ b.gateCount ≤ SC ∧
        (∀ x, ACCAccepts b x ↔ ∃ v : Fin N, Tv idx.val x = (v : Nat) ∧
          (∀ p ∈ rangeTrans gin,
            runTrans (letter (start + (a + idx.val)) x) (state gin (v : Nat) p)
              = state gin ((v : Nat) + expo gin (letter (start + (a + idx.val)) x)) p)) := by
      intro idx
      have hk : idx.val ≤ len := by have := idx.isLt; omega
      have hmono : M ^ N * ((N + 1) * (idx.val * S1 + M + 1) + 1) + 1 ≤ SP := by
        rw [hSPdef]
        have h1 : idx.val * S1 ≤ len * S1 := Nat.mul_le_mul_right _ hk
        have h2 : (N + 1) * (idx.val * S1 + M + 1) ≤ (N + 1) * (len * S1 + M + 1) :=
          Nat.mul_le_mul_left _ (by omega)
        have h3 := Nat.mul_le_mul_left (M ^ N) (Nat.add_le_add_right h2 1)
        omega
      obtain ⟨b, h1, h2, h3, h4⟩ := exists_acc_orPair (K := N) (d := 11)
        (f := fun v : Fin N => PS gin a idx.val v)
        (g := fun v : Fin N => QC gin (start + (a + idx.val)) v)
        (S1 := SP) (S2 := S1)
        (fun v => hPSwf _ _ _ _) (fun v => hQCwf _ _ _)
        (fun v q => hPSlay _ _ _ _ q) (fun v q => hQClay _ _ _ q)
        (fun v => le_trans (hPSsz gin a idx.val v) hmono) (fun v => hQCsz _ _ _)
      refine ⟨b, h1, fun q => le_trans (h2 q) (by omega), ?_, fun x => ?_⟩
      · rw [hSCdef]; exact h3
      · rw [h4 x]
        refine exists_congr fun v => ?_
        rw [hPSacc gin a idx.val v x, hQCacc gin (start + (a + idx.val)) v x]
    choose CC hCCwf hCClay hCCsz hCCacc using hCC
    -- the final check
    have hFF : ∃ b : ACCCircuit n M, WellFormedACC b ∧
        (∀ q, b.layer q ≤ 13) ∧ b.gateCount ≤ SC ∧
        (∀ x, ACCAccepts b x ↔ ∃ v : Fin N, Tv (c - a) x = (v : Nat) ∧
          (∀ y : Config w, state gin (v : Nat) (runTrans gin y) = runTrans gout y)) := by
      have hmono : M ^ N * ((N + 1) * ((c - a) * S1 + M + 1) + 1) + 1 ≤ SP := by
        rw [hSPdef]
        have h1 : (c - a) * S1 ≤ len * S1 := Nat.mul_le_mul_right _ (by omega)
        have h2 : (N + 1) * ((c - a) * S1 + M + 1) ≤ (N + 1) * (len * S1 + M + 1) :=
          Nat.mul_le_mul_left _ (by omega)
        have h3 := Nat.mul_le_mul_left (M ^ N) (Nat.add_le_add_right h2 1)
        omega
      obtain ⟨b, h1, h2, h3, h4⟩ := exists_acc_orPair (K := N) (d := 11)
        (f := fun v : Fin N => PS gin a (c - a) v)
        (g := fun v : Fin N => accConst n M
          (decide (∀ y : Config w, state gin (v : Nat) (runTrans gin y) = runTrans gout y)))
        (S1 := SP) (S2 := 1)
        (fun v => hPSwf _ _ _ _) (fun v => wellFormedACC_accConst n M _)
        (fun v q => hPSlay _ _ _ _ q) (fun v q => by rw [accConst_layer]; omega)
        (fun v => le_trans (hPSsz gin a (c - a) v) hmono) (fun v => le_of_eq rfl)
      refine ⟨b, h1, fun q => le_trans (h2 q) (by omega), ?_, fun x => ?_⟩
      · refine le_trans h3 ?_
        rw [hSCdef]
        have : 1 ≤ S1 := by rw [hS1def]; omega
        have h5 : N * (SP + 1 + 1) ≤ N * (SP + S1 + 1) := Nat.mul_le_mul_left _ (by omega)
        omega
      · rw [h4 x]
        refine exists_congr fun v => ?_
        rw [hPSacc gin a (c - a) v x, accAccepts_accConst]
        exact and_congr Iff.rfl (by simp)
    obtain ⟨FF, hFFwf, hFFlay, hFFsz, hFFacc⟩ := hFF
    -- the conjunction of all the checks
    set fam : Fin (c - a + 1) → ACCCircuit n M := fun idx =>
      if idx.val < c - a then CC idx else FF with hfamdef
    have hfam_lt : ∀ idx : Fin (c - a + 1), idx.val < c - a → fam idx = CC idx := by
      intro idx h; simp only [hfamdef, if_pos h]
    have hfam_last : ∀ idx : Fin (c - a + 1), ¬ idx.val < c - a → fam idx = FF := by
      intro idx h; simp only [hfamdef, if_neg h]
    have hfamwf : ∀ idx, WellFormedACC (fam idx) := by
      intro idx
      by_cases h : idx.val < c - a
      · rw [hfam_lt idx h]; exact hCCwf idx
      · rw [hfam_last idx h]; exact hFFwf
    have hfamlay : ∀ idx q, (fam idx).layer q ≤ 13 := by
      intro idx
      by_cases h : idx.val < c - a
      · rw [hfam_lt idx h]; exact hCClay idx
      · rw [hfam_last idx h]; exact hFFlay
    have hfamsz : ∀ idx, (fam idx).gateCount ≤ SC := by
      intro idx
      by_cases h : idx.val < c - a
      · rw [hfam_lt idx h]; exact hCCsz idx
      · rw [hfam_last idx h]; exact hFFsz
    obtain ⟨E, hEwf, hElay, hEsz, hEacc⟩ := exists_acc_bigAnd fam hfamwf hfamlay hfamsz
    refine ⟨E, hEwf, fun q => le_trans (hElay q) (by omega), ?_, ?_, ?_⟩
    · refine le_trans hEsz ?_
      have : c - a + 1 ≤ len + 1 := by omega
      have h2 : (c - a + 1) * SC ≤ (len + 1) * SC := Nat.mul_le_mul_right _ this
      omega
    · -- soundness
      intro x hx
      rw [hEacc x] at hx
      have hlast : ACCAccepts FF x := by
        have := hx ⟨c - a, by omega⟩
        rwa [hfam_last ⟨c - a, by omega⟩ (by simp)] at this
      have hpos : ∀ i, a ≤ i → i < c → ∃ v : Fin N, Tv (i - a) x = (v : Nat) ∧
          (∀ p ∈ rangeTrans gin, runTrans (letter (start + i) x) (state gin (v : Nat) p)
            = state gin ((v : Nat) + expo gin (letter (start + i) x)) p) := by
        intro i hai hic
        have hidx : (i - a) < c - a := by omega
        have hacc := hx ⟨i - a, by omega⟩
        rw [hfam_lt ⟨i - a, by omega⟩ hidx, hCCacc ⟨i - a, by omega⟩ x] at hacc
        have hpos' : a + (i - a) = i := by omega
        simpa [hpos'] using hacc
      refine mul_blockProd_eq_of_transcript letter start x gin gout
        (fun i => state gin (Tv (i - a) x)) hac ?_ ?_ ?_
      · intro p hp
        change state gin (Tv (a - a) x) p = p
        rw [Nat.sub_self, hTv_zero x]
        exact hstate_zero gin p hp
      · intro i hai hic p hp
        change state gin (Tv (i + 1 - a) x) p
          = runTrans (letter (start + i) x) (state gin (Tv (i - a) x) p)
        obtain ⟨v, hv1, hv2⟩ := hpos i hai hic
        have hstep : i + 1 - a = (i - a) + 1 := by omega
        have hposeq : start + a + (i - a) = start + i := by omega
        rw [hstep, hTv_succ (i - a) x, hposeq, hv1]
        rw [← hstate_per gin ((v : Nat) + expo gin (letter (start + i) x))]
        exact (hv2 p hp).symm
      · intro y
        change state gin (Tv (c - a) x) (runTrans gin y) = runTrans gout y
        obtain ⟨v, hv1, hv2⟩ := (hFFacc x).mp hlast
        rw [hv1]
        exact hv2 y
    · -- completeness
      intro x hshape hgin hgout
      have hwin : ∀ u, a ≤ u → u ≤ c →
          shapeCoord (blockProd letter start 0 u x) = shapeCoord (blockProd letter start 0 a x) := by
        intro u hau huc
        rw [← windowShape_eq_shapeCoord_blockProd letter start len x (by omega),
          ← windowShape_eq_shapeCoord_blockProd letter start len x (show a ≤ len by omega)]
        exact windowShape_const_of_steps letter start len x hshape u hau huc
      have hginmem : gin ∈ NonCrossing w := by
        rw [hgin, blockProd]
        refine Submonoid.list_prod_mem _ ?_
        intro g hg
        rw [List.mem_map] at hg
        obtain ⟨q, -, rfl⟩ := hg
        exact Submonoid.subset_closure (hgen q x)
      have hclaim : ∀ i, a ≤ i → i ≤ c → ∀ p ∈ rangeTrans gin,
          runTrans (blockProd letter start a i x) p = state gin (Tv (i - a) x) p := by
        intro i hai hic p hp
        have hprod : ((List.range' (start + a) (i - a)).map (fun q => letter q x)).prod
            = blockProd letter start a i x := by
          rw [range'_map_prod_eq_blockProd letter x start a (i - a)]
          congr 1
          omega
        have hlenws : ((List.range' (start + a) (i - a)).map (fun q => letter q x)).length
            = i - a := by simp
        have hnc : ∀ g ∈ (List.range' (start + a) (i - a)).map (fun q => letter q x),
            g ∈ NonCrossing w := by
          intro g hg
          rw [List.mem_map] at hg
          obtain ⟨q, -, rfl⟩ := hg
          exact Submonoid.subset_closure (hgen q x)
        have hpromise : ∀ k, k ≤ ((List.range' (start + a) (i - a)).map (fun q => letter q x)).length →
            shapeCoord (gin * prefixEnd ((List.range' (start + a) (i - a)).map (fun q => letter q x)) k)
              = shapeCoord gin := by
          intro k hk
          rw [hlenws] at hk
          have hpe : prefixEnd ((List.range' (start + a) (i - a)).map (fun q => letter q x)) k
              = blockProd letter start a (a + k) x := by
            rw [prefixEnd_range'_map (fun q x => letter q x) x (start + a) (i - a) k hk,
              range'_map_prod_eq_blockProd letter x start a k]
          rw [hpe, hgin, blockProd_concat letter start x (Nat.zero_le a) (Nat.le_add_right a k)]
          exact hwin (a + k) (Nat.le_add_right a k) (by omega)
        have hkey := hstate_word gin ((List.range' (start + a) (i - a)).map (fun q => letter q x))
          hginmem hnc hpromise p hp
        rw [hprod] at hkey
        rw [hkey]
        have hsum : (((List.range' (start + a) (i - a)).map (fun q => letter q x)).map
            (expo gin)).sum = ∑ j ∈ Finset.range (i - a), expo gin (letter (start + a + j) x) :=
          sum_map_expo_range' letter x (expo gin) (start + a) (i - a)
        rw [hsum, hTvdef]
        exact congrFun (hstate_per gin _) p
      rw [hEacc x]
      intro idx
      by_cases hidx : idx.val < c - a
      · rw [hfam_lt idx hidx, hCCacc idx x]
        refine ⟨⟨Tv idx.val x, hTv_lt _ _⟩, rfl, ?_⟩
        intro p hp
        set i := a + idx.val with hidef
        have hai : a ≤ i := by omega
        have hic : i < c := by omega
        have hia : i - a = idx.val := by omega
        have h1 : runTrans (letter (start + i) x) (state gin (Tv idx.val x) p)
            = runTrans (letter (start + i) x) (runTrans (blockProd letter start a i x) p) := by
          rw [← hia, hclaim i hai (by omega) p hp]
        have hnext : blockProd letter start a (i + 1) x
            = blockProd letter start a i x * letter (start + i) x := by
          rw [← blockProd_succ letter start i x]
          exact (blockProd_concat letter start x hai (Nat.le_succ i)).symm
        have h2 : runTrans (letter (start + i) x) (runTrans (blockProd letter start a i x) p)
            = runTrans (blockProd letter start a (i + 1) x) p := by
          rw [hnext, runTrans_mul]
        have h3 : runTrans (blockProd letter start a (i + 1) x) p
            = state gin (Tv (i + 1 - a) x) p := hclaim (i + 1) (by omega) (by omega) p hp
        have h4 : i + 1 - a = idx.val + 1 := by omega
        rw [h1, h2, h3, h4, hTv_succ idx.val x]
        have h5 : start + a + idx.val = start + i := by omega
        rw [h5]
        exact (congrFun (hstate_per gin _) p).symm
      · rw [hfam_last idx hidx, hFFacc x]
        refine ⟨⟨Tv (c - a) x, hTv_lt _ _⟩, rfl, ?_⟩
        intro y
        have hp : runTrans gin y ∈ rangeTrans gin := mem_rangeTrans.mpr ⟨y, rfl⟩
        have := (hclaim c hac (le_refl c) (runTrans gin y) hp).symm
        simp only at this
        rw [this, ← runTrans_mul, hgin,
          blockProd_concat letter start x (Nat.zero_le a) hac, hgout]
  choose Efn hEfnwf hEfnlay hEfnsz hEfnsound hEfncomp using hmain
  -- the size bound
  have harith : (len + 1) * SC + 2 ≤ (size + len + 2) ^ (3 + K5) := by
    obtain ⟨S, hSdef⟩ : ∃ S : Nat, S = size + len + 2 := ⟨_, rfl⟩
    have hS2 : 2 ≤ S := by omega
    have hsizeS : size ≤ S := by omega
    have hlenS : len ≤ S := by omega
    have hSpos : 0 < S := by omega
    have hSS : S ≤ S * S := Nat.le_mul_of_pos_right _ hSpos
    have hSSS : S * S ≤ S * S * S := Nat.le_mul_of_pos_right _ hSpos
    have hone : (1 : Nat) ≤ S * S := by omega
    have e1 : S1 ≤ K1 * S := by
      rw [hS1def, hK1def]
      have h1 : A0 * ((M + 2) * size + 2) + 1 = A0 * (M + 2) * size + (2 * A0 + 1) := by ring
      have h2 : A0 * (M + 2) * size ≤ A0 * (M + 2) * S := Nat.mul_le_mul_left _ hsizeS
      have h3 : 2 * A0 + 1 ≤ (2 * A0 + 1) * S := Nat.le_mul_of_pos_right _ hSpos
      have h4 : (A0 * (M + 2) + 2 * A0 + 1) * S = A0 * (M + 2) * S + (2 * A0 + 1) * S := by ring
      omega
    have e2 : len * S1 + M + 1 ≤ K2 * (S * S) := by
      rw [hK2def]
      have h1 : len * S1 ≤ S * (K1 * S) := Nat.mul_le_mul hlenS e1
      have h2 : M + 1 ≤ (M + 1) * (S * S) := Nat.le_mul_of_pos_right _ (by omega)
      have h3 : (K1 + M + 1) * (S * S) = K1 * (S * S) + (M + 1) * (S * S) := by ring
      have h4 : S * (K1 * S) = K1 * (S * S) := by ring
      omega
    have e3 : SP ≤ K3 * (S * S) := by
      rw [hSPdef, hK3def]
      have h1 : (N + 1) * (len * S1 + M + 1) ≤ (N + 1) * (K2 * (S * S)) :=
        Nat.mul_le_mul_left _ e2
      have h3 : M ^ N * ((N + 1) * (len * S1 + M + 1) + 1)
          ≤ M ^ N * ((N + 1) * (K2 * (S * S)) + S * S) := by
        refine Nat.mul_le_mul_left _ ?_
        omega
      have h4 : M ^ N * ((N + 1) * (K2 * (S * S)) + S * S)
          = (M ^ N * ((N + 1) * K2 + 1)) * (S * S) := by ring
      have h5 : (M ^ N * ((N + 1) * K2 + 1) + 1) * (S * S)
          = (M ^ N * ((N + 1) * K2 + 1)) * (S * S) + S * S := by ring
      omega
    have e4 : SC ≤ K4 * (S * S) := by
      rw [hSCdef, hK4def]
      have h2 : S1 ≤ K1 * (S * S) := le_trans e1 (Nat.mul_le_mul_left _ hSS)
      have h3 : SP + S1 + 1 ≤ K3 * (S * S) + K1 * (S * S) + S * S := by omega
      have h4 : N * (SP + S1 + 1) ≤ N * (K3 * (S * S) + K1 * (S * S) + S * S) :=
        Nat.mul_le_mul_left _ h3
      have h5 : N * (K3 * (S * S) + K1 * (S * S) + S * S) = (N * (K3 + K1 + 1)) * (S * S) := by
        ring
      have h6 : (N * (K3 + K1 + 1) + 1) * (S * S) = (N * (K3 + K1 + 1)) * (S * S) + S * S := by
        ring
      omega
    have e5 : (len + 1) * SC + 2 ≤ K5 * (S * S * S) := by
      rw [hK5def]
      have h1 : len + 1 ≤ S := by omega
      have h2 : (len + 1) * SC ≤ S * (K4 * (S * S)) := Nat.mul_le_mul h1 e4
      have h3 : S * (K4 * (S * S)) = K4 * (S * S * S) := by ring
      have h4 : (2 : Nat) ≤ S * S * S := by omega
      have h5 : (K4 + 2) * (S * S * S) = K4 * (S * S * S) + 2 * (S * S * S) := by ring
      omega
    have e6 : K5 * S ^ 3 ≤ S ^ (3 + K5) := const_mul_pow_le_pow hS2
    have e7 : S ^ 3 = S * S * S := by ring
    have e8 : (size + len + 2) ^ (3 + K5) = S ^ (3 + K5) := by rw [hSdef]
    rw [e7] at e6
    omega
  have hlift : ∀ b1 b2 : ACCCircuit n M, b1 = b2 →
      ((∀ q, b2.layer q ≤ 15) → ∀ q, b1.layer q ≤ 15) := by
    rintro b1 b2 rfl h; exact h
  refine ⟨fun a c gin gout =>
      if h : a ≤ c ∧ c ≤ len then Efn a c gin gout h.1 h.2 else accConst n M false,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro a c gin gout
    by_cases h : a ≤ c ∧ c ≤ len
    · simp only [dif_pos h]; exact hEfnwf a c gin gout h.1 h.2
    · simp only [dif_neg h]; exact wellFormedACC_accConst n M false
  · intro a c gin gout
    by_cases h : a ≤ c ∧ c ≤ len
    · exact hlift _ _ (dif_pos h) (hEfnlay a c gin gout h.1 h.2)
    · refine hlift _ _ (dif_neg h) ?_
      intro q; rw [accConst_layer]; omega
  · intro a c gin gout
    by_cases h : a ≤ c ∧ c ≤ len
    · simp only [dif_pos h]
      exact le_trans (hEfnsz a c gin gout h.1 h.2) harith
    · simp only [dif_neg h, accConst_gateCount]
      have h1 : 1 ≤ (size + len + 2) ^ (3 + K5) := Nat.one_le_pow _ _ (by omega)
      exact h1
  · intro a c gin gout x hac hacc
    by_cases h : a ≤ c ∧ c ≤ len
    · simp only [dif_pos h] at hacc
      exact hEfnsound a c gin gout h.1 h.2 x hacc
    · simp only [dif_neg h] at hacc
      exact absurd ((accAccepts_accConst n M false x).mp hacc) (by simp)
  · intro x a c hac hcl hshape
    have h : a ≤ c ∧ c ≤ len := ⟨hac, hcl⟩
    simp only [dif_pos h]
    exact hEfncomp a c _ _ hac hcl x hshape rfl rfl

end Internal
end AllenderOQ3
