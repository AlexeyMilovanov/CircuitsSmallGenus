import AllenderOQ3.Internal.SourceCutLift

/-!
# The target-side first-true cut lift

For a nonempty AND/OR predecessor assignment, every target block contributes
exactly one unit of target advance while its incoming arcs are traversed:

* an AND block advances after its first arc;
* an OR block advances after its last arc.

Flattening these `0/1` step blocks gives a monotone lift from cuts in the
target-major arc word to target coordinates.  A complete arc-word traversal
advances by exactly `w`.
-/

set_option autoImplicit false

namespace AllenderOQ3
namespace Internal

variable {w : Nat}

/-- A proper interval's canonical start is any witnessed rising edge. -/
theorem startOf_eq_of_rising (hw : 0 < w) {y : Config w}
    (hy : IsIntervalConfig y) (hproper : y ≠ topConfig w) (p : Fin w)
    (hpred : y (finPred p) = false) (hp : y p = true) :
    startOf hw y = p := by
  obtain ⟨hlenpos, hlenle, hypiece⟩ := eq_pieceConfig_canonical hy hw
  have hlenlt : lenOf y < w := by
    rcases eq_or_lt_of_le hlenle with heq | hlt
    · exfalso
      apply hproper
      funext q
      rw [hypiece, topConfig]
      obtain ⟨k, hk, hkq⟩ := finShift_surj_lt (startOf hw y) q
      exact pieceConfig_true_iff.mpr ⟨k, by omega, hkq⟩
    · exact hlt
  have hedge : risingEdges y = {startOf hw y} := by
    calc
      risingEdges y = risingEdges (pieceConfig (startOf hw y) (lenOf y)) :=
        congrArg risingEdges hypiece
      _ = {startOf hw y} := risingEdges_pieceConfig hlenpos hlenlt
  have hpmem : p ∈ risingEdges y := mem_risingEdges.mpr ⟨hpred, hp⟩
  rw [hedge, Finset.mem_singleton] at hpmem
  exact hpmem.symm

/-! ## One target block -/

/-- The increments of the first-true-target coordinate while crossing a
single incoming block.  `K = true` is AND, `K = false` is OR. -/
def targetCutStepBlock {alpha : Type} (K : Bool) : List alpha → List Nat
  | [] => []
  | _ :: qs =>
      if K then 1 :: List.replicate qs.length 0
      else List.replicate qs.length 0 ++ [1]

@[simp] theorem length_targetCutStepBlock {alpha : Type} (K : Bool)
    (Q : List alpha) :
    (targetCutStepBlock K Q).length = Q.length := by
  cases Q with
  | nil => rfl
  | cons q qs =>
      cases K <;> simp [targetCutStepBlock]

theorem sum_targetCutStepBlock {alpha : Type} (K : Bool)
    {Q : List alpha} (hQ : Q ≠ []) :
    (targetCutStepBlock K Q).sum = 1 := by
  cases Q with
  | nil => exact absurd rfl hQ
  | cons q qs =>
      cases K <;> simp [targetCutStepBlock]

/-- Strictly inside a nonempty target block, an AND cut has already advanced
after the first crossed arc, while an OR cut has not yet advanced before its
last arc. -/
theorem sum_take_targetCutStepBlock_lt {alpha : Type} (K : Bool)
    {Q : List alpha} (hQ : Q ≠ []) (j : Nat) (hj : j < Q.length) :
    ((targetCutStepBlock K Q).take j).sum =
      if K then (if j = 0 then 0 else 1) else 0 := by
  cases Q with
  | nil => exact absurd rfl hQ
  | cons q qs =>
      cases K with
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, targetCutStepBlock]
          have hjle : j ≤ qs.length := by simp at hj; omega
          rw [List.take_append_of_le_length (by simpa using hjle)]
          simp
      | true =>
          rcases Nat.eq_zero_or_pos j with rfl | hjpos
          · simp [targetCutStepBlock]
          · obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
            simp [targetCutStepBlock]

/-! ## The target-major step word -/

/-- The `0/1` increments for all targets in target-major order. -/
def targetCutStepWord (P : Fin w → List (Fin w)) (K : Fin w → Bool) :
    List Nat :=
  (List.finRange w).flatMap (fun p => targetCutStepBlock (K p) (P p))

theorem length_targetCutStepWord (P : Fin w → List (Fin w))
    (K : Fin w → Bool) :
    (targetCutStepWord P K).length = (arcPairWord P).length := by
  rw [targetCutStepWord, arcPairWord, List.length_flatMap, List.length_flatMap]
  congr 1
  apply List.map_congr_left
  intro p hp
  rw [length_targetCutStepBlock, arcBlock, List.length_map]

theorem sum_flatMap_targetCutStepBlock (P : Fin w → List (Fin w))
    (K : Fin w → Bool) (hne : ∀ p, P p ≠ []) :
    ∀ L : List (Fin w),
      (L.flatMap (fun p => targetCutStepBlock (K p) (P p))).sum = L.length := by
  intro L
  induction L with
  | nil => simp
  | cons p L ih =>
      rw [List.flatMap_cons, List.sum_append,
        sum_targetCutStepBlock (K p) (hne p), ih]
      exact Nat.add_comm 1 L.length

theorem sum_targetCutStepWord (P : Fin w → List (Fin w))
    (K : Fin w → Bool) (hne : ∀ p, P p ≠ []) :
    (targetCutStepWord P K).sum = w := by
  rw [targetCutStepWord,
    sum_flatMap_targetCutStepBlock P K hne, List.length_finRange]

theorem targetCutStepWord_length_pos (hw : 0 < w)
    (P : Fin w → List (Fin w)) (K : Fin w → Bool)
    (hne : ∀ p, P p ≠ []) :
    0 < (targetCutStepWord P K).length := by
  by_contra h
  have hzero : (targetCutStepWord P K).length = 0 := by omega
  have hnil : targetCutStepWord P K = [] := List.eq_nil_of_length_eq_zero hzero
  have hsum := sum_targetCutStepWord P K hne
  rw [hnil] at hsum
  simp at hsum
  omega

/-! ## Periodic target-cut lift -/

/-- Prefix lift of a finite word of nonnegative cut increments. -/
def wordCutLift {steps : List Nat} (hsteps : 0 < steps.length) : Nat → Nat :=
  periodicPrefix hsteps (fun i => steps.get i)

theorem monotone_wordCutLift {steps : List Nat} (hsteps : 0 < steps.length) :
    Monotone (wordCutLift hsteps) :=
  monotone_periodicPrefix hsteps (fun i => steps.get i)

theorem wordCutLift_add_period {steps : List Nat}
    (hsteps : 0 < steps.length) (x : Nat) :
    wordCutLift hsteps (x + steps.length) =
      wordCutLift hsteps x + steps.sum := by
  rw [wordCutLift, periodicPrefix_add_period,
    periodicPrefix_period_eq_sum]
  rw [← List.sum_ofFn, List.ofFn_get]

/-- Inside the fundamental word window, the prefix lift is the literal sum of
the crossed step entries. -/
theorem wordCutLift_eq_sum_take {steps : List Nat}
    (hsteps : 0 < steps.length) (n : Nat) (hn : n ≤ steps.length) :
    wordCutLift hsteps n = (steps.take n).sum := by
  induction n with
  | zero => simp [wordCutLift]
  | succ n ih =>
      have hnlt : n < steps.length := by omega
      have hfin : (⟨n % steps.length, Nat.mod_lt n hsteps⟩ : Fin steps.length) =
          ⟨n, hnlt⟩ := by
        apply Fin.ext
        exact Nat.mod_eq_of_lt hnlt
      have ih' := ih (by omega)
      rw [wordCutLift] at ih' ⊢
      rw [periodicPrefix_succ, hfin, ih']
      rw [List.sum_take_succ steps n hnlt, List.get_eq_getElem]

/-- The deterministic target-side cut lift attached to `P,K`. -/
noncomputable def targetCutLift (hw : 0 < w)
    (P : Fin w → List (Fin w)) (K : Fin w → Bool)
    (hne : ∀ p, P p ≠ []) : Nat → Nat :=
  wordCutLift (targetCutStepWord_length_pos hw P K hne)

theorem monotone_targetCutLift (hw : 0 < w)
    (P : Fin w → List (Fin w)) (K : Fin w → Bool)
    (hne : ∀ p, P p ≠ []) :
    Monotone (targetCutLift hw P K hne) :=
  monotone_wordCutLift (targetCutStepWord_length_pos hw P K hne)

theorem targetCutLift_add_period (hw : 0 < w)
    (P : Fin w → List (Fin w)) (K : Fin w → Bool)
    (hne : ∀ p, P p ≠ []) (x : Nat) :
    targetCutLift hw P K hne (x + (arcPairWord P).length) =
      targetCutLift hw P K hne x + w := by
  rw [targetCutLift, ← length_targetCutStepWord P K]
  exact (wordCutLift_add_period
    (targetCutStepWord_length_pos hw P K hne) x).trans (by
      rw [sum_targetCutStepWord P K hne])

theorem targetCutLift_add_mul_period (hw : 0 < w)
    (P : Fin w → List (Fin w)) (K : Fin w → Bool)
    (hne : ∀ p, P p ≠ []) (x q : Nat) :
    targetCutLift hw P K hne (x + q * (arcPairWord P).length) =
      targetCutLift hw P K hne x + q * w := by
  induction q with
  | zero => simp
  | succ q ih =>
      have harg : x + (q + 1) * (arcPairWord P).length =
          (x + q * (arcPairWord P).length) + (arcPairWord P).length := by ring
      rw [harg, targetCutLift_add_period, ih]
      ring

/-- Reducing an arc cut modulo the target-major word length does not change
the target coordinate modulo `w`. -/
theorem targetCutLift_mod_wordLength (hw : 0 < w)
    (P : Fin w → List (Fin w)) (K : Fin w → Bool)
    (hne : ∀ p, P p ≠ []) (c : Nat) :
    targetCutLift hw P K hne c % w =
      targetCutLift hw P K hne (c % (arcPairWord P).length) % w := by
  have hNpos : 0 < (arcPairWord P).length := by
    rw [← length_targetCutStepWord P K]
    exact targetCutStepWord_length_pos hw P K hne
  have hdiv := Nat.div_add_mod c (arcPairWord P).length
  have hc : c = c % (arcPairWord P).length +
      (c / (arcPairWord P).length) * (arcPairWord P).length := by
    calc
      c = (arcPairWord P).length * (c / (arcPairWord P).length) +
          c % (arcPairWord P).length := hdiv.symm
      _ = c % (arcPairWord P).length +
          (c / (arcPairWord P).length) * (arcPairWord P).length := by ring
  rw [hc, targetCutLift_add_mul_period]
  simp [Nat.add_mod]

/-! ## Values at target-block cuts -/

/-- Arc-word position of the boundary immediately before target number `r`.
Only `r ≤ w` is used below. -/
def targetBoundary (P : Fin w → List (Fin w)) (r : Nat) : Nat :=
  (((List.finRange w).take r).flatMap (arcBlock P)).length

@[simp] theorem targetBoundary_zero (P : Fin w → List (Fin w)) :
    targetBoundary P 0 = 0 := by simp [targetBoundary]

theorem targetBoundary_succ (P : Fin w → List (Fin w))
    (r : Nat) (hr : r < w) :
    targetBoundary P (r + 1) =
      targetBoundary P r + (P ⟨r, hr⟩).length := by
  have hidx : r < (List.finRange w).length := by simpa using hr
  have htake := List.take_succ_eq_append_getElem
    (l := List.finRange w) (i := r) hidx
  have hget : (List.finRange w)[r]'hidx = (⟨r, hr⟩ : Fin w) := by simp
  rw [targetBoundary, targetBoundary, htake, hget, List.flatMap_append,
    List.flatMap_singleton, List.length_append, arcBlock, List.length_map]

theorem targetBoundary_width (P : Fin w → List (Fin w)) :
    targetBoundary P w = (arcPairWord P).length := by
  rw [targetBoundary, List.take_of_length_le (by simp), arcPairWord]

/-- Every cut strictly inside the target-major word lies in one unique
nonempty target block.  Only existence is needed by the semantic proof. -/
theorem exists_targetBlock_of_cut (hw : 0 < w)
    (P : Fin w → List (Fin w)) (hne : ∀ p, P p ≠ [])
    {r : Nat} (hr : r < (arcPairWord P).length) :
    ∃ (p : Fin w) (j : Nat),
      j < (P p).length ∧ r = targetBoundary P p.val + j := by
  have hex : ∃ n : Nat, r < targetBoundary P (n + 1) := by
    refine ⟨w - 1, ?_⟩
    have hws : w - 1 + 1 = w := by omega
    rw [hws, targetBoundary_width]
    exact hr
  let n := Nat.find hex
  have hnSpec : r < targetBoundary P (n + 1) := Nat.find_spec hex
  have hnle : n ≤ w - 1 := Nat.find_le (by
    have hws : w - 1 + 1 = w := by omega
    rw [hws, targetBoundary_width]
    exact hr)
  have hnlt : n < w := by omega
  have hbefore : targetBoundary P n ≤ r := by
    rcases Nat.eq_zero_or_pos n with hnzero | hnpos
    · rw [hnzero]
      simp
    · have hnot := Nat.find_min hex (m := n - 1) (by omega)
      push_neg at hnot
      have hpred : n - 1 + 1 = n := by omega
      rw [hpred] at hnot
      exact hnot
  let p : Fin w := ⟨n, hnlt⟩
  let j := r - targetBoundary P n
  refine ⟨p, j, ?_, ?_⟩
  · rw [targetBoundary_succ P n hnlt] at hnSpec
    dsimp [p, j]
    omega
  · dsimp [p, j]
    omega

/-- Exact target-major word shape after cutting inside target `p` after `j`
incoming arcs. -/
theorem rotate_arcPairWord_insideBlock (P : Fin w → List (Fin w))
    (p : Fin w) (j : Nat) (hj : j ≤ (P p).length) :
    (arcPairWord P).rotate (targetBoundary P p.val + j) =
      (arcBlock P p).drop j ++
        (((List.finRange w).drop (p.val + 1) ++
          (List.finRange w).take p.val).flatMap (arcBlock P)) ++
      (arcBlock P p).take j := by
  let Lpre := (List.finRange w).take p.val
  let Lpost := (List.finRange w).drop (p.val + 1)
  let A := Lpre.flatMap (arcBlock P)
  let B := arcBlock P p
  let C := Lpost.flatMap (arcBlock P)
  have hpidx : p.val < (List.finRange w).length := by simpa using p.isLt
  have hget : (List.finRange w)[p.val]'hpidx = p := by simp
  have htakeSucc := List.take_succ_eq_append_getElem
    (l := List.finRange w) (i := p.val) hpidx
  have hL : List.finRange w = Lpre ++ [p] ++ Lpost := by
    rw [← List.take_append_drop (p.val + 1) (List.finRange w), htakeSucc, hget]
  have hword : arcPairWord P = A ++ B ++ C := by
    rw [arcPairWord, hL, List.flatMap_append, List.flatMap_append,
      List.flatMap_singleton]
  have hboundary : targetBoundary P p.val = A.length := by rfl
  have hjB : j ≤ B.length := by
    dsimp [B, arcBlock]
    simpa using hj
  have hAB : A.length ≤ (A ++ B ++ C).length := by simp
  calc
    (arcPairWord P).rotate (targetBoundary P p.val + j) =
        ((arcPairWord P).rotate (targetBoundary P p.val)).rotate j := by
      rw [List.rotate_rotate]
    _ = ((A ++ B ++ C).rotate A.length).rotate j := by rw [hword, hboundary]
    _ = (B ++ C ++ A).rotate j := by
      rw [List.rotate_eq_drop_append_take hAB]
      simp only [List.drop_left, List.take_left, List.append_assoc]
    _ = B.drop j ++ (C ++ A) ++ B.take j := by
      have hjall : j ≤ (B ++ C ++ A).length := by simp; omega
      rw [List.rotate_eq_drop_append_take hjall]
      rw [show B ++ C ++ A = B ++ (C ++ A) by simp [List.append_assoc],
        List.drop_append_of_le_length hjB,
        List.take_append_of_le_length hjB]
    _ = (arcBlock P p).drop j ++
        (((List.finRange w).drop (p.val + 1) ++
          (List.finRange w).take p.val).flatMap (arcBlock P)) ++
        (arcBlock P p).take j := by
      dsimp [A, B, C, Lpre, Lpost]
      rw [List.flatMap_append]

/-- The first-true-target lift sends the boundary before target `p` to the
ordinary target coordinate `p`. -/
theorem targetCutLift_targetBoundary (hw : 0 < w)
    (P : Fin w → List (Fin w)) (K : Fin w → Bool)
    (hne : ∀ p, P p ≠ []) (p : Fin w) :
    targetCutLift hw P K hne (targetBoundary P p.val) = p.val := by
  let Lpre := (List.finRange w).take p.val
  let Lpost := (List.finRange w).drop p.val
  let Spre := Lpre.flatMap (fun q => targetCutStepBlock (K q) (P q))
  let Spost := Lpost.flatMap (fun q => targetCutStepBlock (K q) (P q))
  have hL : List.finRange w = Lpre ++ Lpost := by
    dsimp [Lpre, Lpost]
    exact (List.take_append_drop p.val (List.finRange w)).symm
  have hsteps : targetCutStepWord P K = Spre ++ Spost := by
    rw [targetCutStepWord, hL, List.flatMap_append]
  have hboundary : targetBoundary P p.val = Spre.length := by
    rw [targetBoundary, List.length_flatMap]
    dsimp [Spre, Lpre]
    rw [List.length_flatMap]
    congr 1
    apply List.map_congr_left
    intro q hq
    rw [length_targetCutStepBlock, arcBlock, List.length_map]
  have hprele : Spre.length ≤ (targetCutStepWord P K).length := by
    rw [hsteps]
    simp
  have htake : (targetCutStepWord P K).take (targetBoundary P p.val) = Spre := by
    rw [hboundary, hsteps, List.take_left]
  have hboundle : targetBoundary P p.val ≤ (targetCutStepWord P K).length := by
    rw [hboundary]
    exact hprele
  rw [targetCutLift,
    wordCutLift_eq_sum_take
      (targetCutStepWord_length_pos hw P K hne) _ hboundle, htake]
  dsimp [Spre]
  rw [sum_flatMap_targetCutStepBlock P K hne]
  simp [Lpre]

/-- Local formula at an arbitrary cut strictly before an arc of target `p`.
`j=0` is the target boundary; at a strict internal cut, AND advances to
`p+1` and OR stays at `p`. -/
theorem targetCutLift_insideBlock (hw : 0 < w)
    (P : Fin w → List (Fin w)) (K : Fin w → Bool)
    (hne : ∀ p, P p ≠ []) (p : Fin w) (j : Nat) (hj : j < (P p).length) :
    targetCutLift hw P K hne (targetBoundary P p.val + j) =
      p.val + if K p then (if j = 0 then 0 else 1) else 0 := by
  let Lpre := (List.finRange w).take p.val
  let Lpost := (List.finRange w).drop (p.val + 1)
  let block := targetCutStepBlock (K p) (P p)
  let Spre := Lpre.flatMap (fun q => targetCutStepBlock (K q) (P q))
  let Spost := Lpost.flatMap (fun q => targetCutStepBlock (K q) (P q))
  have hpidx : p.val < (List.finRange w).length := by simpa using p.isLt
  have hget : (List.finRange w)[p.val]'hpidx = p := by simp
  have htakeSucc := List.take_succ_eq_append_getElem
    (l := List.finRange w) (i := p.val) hpidx
  have hL : List.finRange w = Lpre ++ [p] ++ Lpost := by
    rw [← List.take_append_drop (p.val + 1) (List.finRange w), htakeSucc, hget]
  have hsteps : targetCutStepWord P K = Spre ++ block ++ Spost := by
    rw [targetCutStepWord, hL, List.flatMap_append, List.flatMap_append,
      List.flatMap_singleton]
  have hsteps' : targetCutStepWord P K = Spre ++ (block ++ Spost) := by
    rw [hsteps, List.append_assoc]
  have hboundary : targetBoundary P p.val = Spre.length := by
    rw [targetBoundary, List.length_flatMap]
    dsimp [Spre, Lpre]
    rw [List.length_flatMap]
    congr 1
    apply List.map_congr_left
    intro q hq
    rw [length_targetCutStepBlock, arcBlock, List.length_map]
  have hjle : j ≤ block.length := by
    dsimp [block]
    rw [length_targetCutStepBlock]
    omega
  have htake : (targetCutStepWord P K).take (targetBoundary P p.val + j) =
      Spre ++ block.take j := by
    rw [hboundary, hsteps', List.take_add, List.take_left, List.drop_left,
      List.take_append_of_le_length hjle]
  have hcutle : targetBoundary P p.val + j ≤ (targetCutStepWord P K).length := by
    rw [hboundary, hsteps, List.length_append, List.length_append]
    omega
  rw [targetCutLift,
    wordCutLift_eq_sum_take
      (targetCutStepWord_length_pos hw P K hne) _ hcutle,
    htake, List.sum_append]
  have hSsum : Spre.sum = p.val := by
    dsimp [Spre]
    rw [sum_flatMap_targetCutStepBlock P K hne]
    simp [Lpre]
  rw [hSsum]
  dsimp [block]
  rw [sum_take_targetCutStepBlock_lt (K p) (hne p) j hj]

/-- Candidate first true target at a cut inside target `p`. -/
noncomputable def targetCutCandidate (K : Fin w → Bool) (p : Fin w)
    (j : Nat) : Fin w :=
  if K p = true ∧ j ≠ 0 then finShift 1 p else p

theorem targetCutLift_insideBlock_mod (hw : 0 < w)
    (P : Fin w → List (Fin w)) (K : Fin w → Bool)
    (hne : ∀ p, P p ≠ []) (p : Fin w) (j : Nat) (hj : j < (P p).length) :
    targetCutLift hw P K hne (targetBoundary P p.val + j) % w =
      (targetCutCandidate K p j).val := by
  rw [targetCutLift_insideBlock hw P K hne p j hj]
  cases hK : K p with
  | false =>
      simp [targetCutCandidate, hK, Nat.mod_eq_of_lt p.isLt]
  | true =>
      rcases Nat.eq_zero_or_pos j with rfl | hjpos
      · simp [targetCutCandidate, hK, Nat.mod_eq_of_lt p.isLt]
      · have hjne : j ≠ 0 := by omega
        simp [targetCutCandidate, hK, hjne, finShift_val]

/-- A nonempty target assignment admits a monotone first-true-target cut lift.
Its domain period is the arc-word length and its codomain increment is the
number `w` of target blocks. -/
theorem exists_targetCutLift (hw : 0 < w)
    (P : Fin w → List (Fin w)) (K : Fin w → Bool)
    (hne : ∀ p, P p ≠ []) :
    ∃ lambda : Nat → Nat,
      Monotone lambda ∧
      (∀ x, lambda (x + (arcPairWord P).length) = lambda x + w) := by
  exact ⟨targetCutLift hw P K hne, monotone_targetCutLift hw P K hne,
    targetCutLift_add_period hw P K hne⟩

/-! ## The remaining target-only semantic leaf -/

/-- **Target-only G3 leaf.**  If a cut of the target-major arc word exposes
exactly the arcs whose sources are true followed by exactly those whose
sources are false, then the target cut lift computes the canonical start of
the proper interval produced by the AND/OR assignment.

There is no circuit, incidence certificate, source sorting, rotation witness,
or input-interval geometry in this statement.  It is a finite list/Boolean
lemma about nonempty target blocks. -/
def TargetCutTracksStart (w : Nat) : Prop :=
  ∀ (hw : 0 < w) (P : Fin w → List (Fin w)) (K : Fin w → Bool)
      (hne : ∀ p, P p ≠ []) (z y : Config w) (c : Nat)
      (PT PF : List (Fin w × Fin w)),
    (arcPairWord P).rotate (c % (arcPairWord P).length) = PT ++ PF →
    (∀ e ∈ PT, z e.1 = true) →
    (∀ e ∈ PF, z e.1 = false) →
    (∀ e ∈ arcPairWord P, z e.1 = true → e ∈ PT) →
    (∀ p, K p = true → y p = (P p).all (fun q => z q)) →
    (∀ p, K p = false → y p = (P p).any (fun q => z q)) →
    IsIntervalConfig y → y ≠ topConfig w →
    targetCutLift hw P K hne c % w = (startOf hw y).val

/-- The irreducible Boolean/list core of `TargetCutTracksStart`: for a cut
already located inside one known target block, the candidate prescribed by
the AND/OR rule is a rising edge of the proper interval output. -/
def TargetCutCandidateRises (w : Nat) : Prop :=
  ∀ (hw : 0 < w) (P : Fin w → List (Fin w)) (K : Fin w → Bool)
      (hne : ∀ p, P p ≠ []) (z y : Config w) (p : Fin w) (j : Nat)
      (hj : j < (P p).length) (PT PF : List (Fin w × Fin w)),
    (arcPairWord P).rotate (targetBoundary P p.val + j) = PT ++ PF →
    (∀ e ∈ PT, z e.1 = true) →
    (∀ e ∈ PF, z e.1 = false) →
    (∀ e ∈ arcPairWord P, z e.1 = true → e ∈ PT) →
    (∀ q, K q = true → y q = (P q).all (fun u => z u)) →
    (∀ q, K q = false → y q = (P q).any (fun u => z u)) →
    IsIntervalConfig y → y ≠ topConfig w →
    y (finPred (targetCutCandidate K p j)) = false ∧
      y (targetCutCandidate K p j) = true

/-- All cut arithmetic and cut-location bookkeeping are discharged here;
proving the local rising-edge statement suffices for the target-only leaf. -/
theorem targetCutTracksStart_of_candidateRises
    (hRise : TargetCutCandidateRises w) : TargetCutTracksStart w := by
  intro hw P K hne z y c PT PF hpart hPT hPF hexact hsemAll hsemAny hy hproper
  have hNpos : 0 < (arcPairWord P).length := by
    rw [← length_targetCutStepWord P K]
    exact targetCutStepWord_length_pos hw P K hne
  let r := c % (arcPairWord P).length
  have hr : r < (arcPairWord P).length := Nat.mod_lt c hNpos
  obtain ⟨p, j, hj, hrEq⟩ := exists_targetBlock_of_cut hw P hne hr
  have hpart' : (arcPairWord P).rotate (targetBoundary P p.val + j) = PT ++ PF := by
    rw [← hrEq]
    exact hpart
  have hrise := hRise hw P K hne z y p j hj PT PF hpart'
    hPT hPF hexact hsemAll hsemAny hy hproper
  have hstart := startOf_eq_of_rising hw hy hproper
    (targetCutCandidate K p j) hrise.1 hrise.2
  calc
    targetCutLift hw P K hne c % w =
        targetCutLift hw P K hne r % w :=
      targetCutLift_mod_wordLength hw P K hne c
    _ = targetCutLift hw P K hne (targetBoundary P p.val + j) % w := by rw [hrEq]
    _ = (targetCutCandidate K p j).val :=
      targetCutLift_insideBlock_mod hw P K hne p j hj
    _ = (startOf hw y).val := congrArg Fin.val hstart.symm

/-- The source-side geometry proved in `SourceCutLift` reduces the complete
pointwise start identity to `TargetCutTracksStart`. -/
theorem sourceTargetCutLift_tracks_start
    (hTarget : TargetCutTracksStart w) (hw : 0 < w)
    (P : Fin w → List (Fin w)) (K : Fin w → Bool)
    (R : List (Fin w × Fin w)) (offset : Nat)
    (hne : ∀ p, P p ≠ [])
    (hRsort : SrcSorted R)
    (hsplit : ∃ A B : List (Fin w × Fin w),
      arcPairWord P = A ++ B ∧ R = B ++ A ∧ offset = A.length)
    {z y : Config w} (hz : IsIntervalConfig z)
    (hy : IsIntervalConfig y) (hyproper : y ≠ topConfig w)
    (hsemAll : ∀ p, K p = true → y p = (P p).all (fun q => z q))
    (hsemAny : ∀ p, K p = false → y p = (P p).any (fun q => z q)) :
    targetCutLift hw P K hne
        (rotatedSourceCutLift hw R offset (startOf hw z).val) % w =
      (startOf hw y).val := by
  obtain ⟨A, B, hAB, hR, hoffset⟩ := hsplit
  obtain ⟨PT, PF, hpart, hPT, hPF, hexact⟩ :=
    exists_trueFalse_rotatedSourceCut_partition hw hAB hR hoffset hRsort hz
  apply hTarget hw P K hne z y
    (rotatedSourceCutLift hw R offset (startOf hw z).val) PT PF
  · simpa [rotatedSourceCutLift] using hpart
  · exact hPT
  · exact hPF
  · exact hexact
  · exact hsemAll
  · exact hsemAny
  · exact hy
  · exact hyproper

/-! ## Composing the source and target lifts -/

/-- The two compatible periodic lifts compose to a degree-one monotone map on
source coordinates.  This is the pure arithmetic assembly needed by G3; the
remaining geometric statement is only that this composite computes the start
of each interval image. -/
theorem compose_source_target_lifts {E : Nat}
    (kappa lambda : Nat → Nat)
    (hkmono : Monotone kappa) (hlmono : Monotone lambda)
    (hkper : ∀ x, kappa (x + w) = kappa x + E)
    (hlper : ∀ x, lambda (x + E) = lambda x + w) :
    ∃ F : Nat → Nat,
      Monotone F ∧
      ∀ x, F (x + w) = F x + w := by
  refine ⟨fun x => lambda (kappa x), hlmono.comp hkmono, ?_⟩
  intro x
  dsimp
  rw [hkper, hlper]

/-- Every constant-free layer carries a fully explicit degree-one monotone
source-to-target cut lift.  All circuit extraction, empty source fibres, and
rotation offsets are discharged here.  To finish G3 it remains only to prove
the pointwise semantic identity saying that this `F` computes the start of
the image interval. -/
theorem exists_constantFreeCutLift (hw : 0 < w) {g : TransMonoid w}
    (hg : isConstantFreeMap w g) :
    ∃ (P : Fin w → List (Fin w)) (K : Fin w → Bool)
        (R : List (Fin w × Fin w)) (offset : Nat)
        (hne : ∀ p, P p ≠ []) (F : Nat → Nat),
      (∀ p, (P p).Nodup) ∧
      (∀ p, (P p).length ≤ 2) ∧
      SrcSorted R ∧
      (∃ A B : List (Fin w × Fin w),
        arcPairWord P = A ++ B ∧ R = B ++ A ∧ offset = A.length) ∧
      F = (fun x => targetCutLift hw P K hne
        (rotatedSourceCutLift hw R offset x)) ∧
      Monotone F ∧
      (∀ x, F (x + w) = F x + w) ∧
      (∀ (z : Config w) (p : Fin w), K p = true →
        runTrans g z p = (P p).all (fun q => z q)) ∧
      (∀ (z : Config w) (p : Fin w), K p = false →
        runTrans g z p = (P p).any (fun q => z q)) := by
  obtain ⟨P, K, R, offset, kappa, hne, hnd, hlen, hRsort, hRlen,
      hrot, hoff, hsplit, hkappa, hkmono, hkper, hsemAll, hsemAny⟩ :=
    exists_constantFreeSourceCutData hw hg
  let lambda := targetCutLift hw P K hne
  have hlmono : Monotone lambda := monotone_targetCutLift hw P K hne
  have hlper : ∀ x, lambda (x + (arcPairWord P).length) = lambda x + w :=
    targetCutLift_add_period hw P K hne
  let F : Nat → Nat := fun x => lambda (kappa x)
  have hFmono : Monotone F := hlmono.comp hkmono
  have hFper : ∀ x, F (x + w) = F x + w := by
    intro x
    dsimp [F]
    rw [hkper, hlper]
  refine ⟨P, K, R, offset, hne, F, hnd, hlen, hRsort, hsplit, ?_,
    hFmono, hFper, hsemAll, hsemAny⟩
  funext x
  dsimp [F, lambda]
  rw [hkappa]

/-- Consequently the former global GEO theorem follows from the single
target-only list lemma `TargetCutTracksStart`. -/
theorem exists_degree_one_lift_of_targetCutTracksStart
    (hTarget : TargetCutTracksStart w) (hw : 0 < w)
    {g : TransMonoid w} (hg : isConstantFreeMap w g)
    {A B : Finset (Config w)}
    (hA : ∀ y ∈ A, IsIntervalConfig y ∧ y ≠ topConfig w)
    (hB : ∀ y ∈ B, IsIntervalConfig y ∧ y ≠ topConfig w)
    (hbij : Set.BijOn (runTrans g) ↑A ↑B) :
    ∃ F : Nat → Nat,
      (∀ x, F (x + w) = F x + w) ∧
      Monotone F ∧
      (∀ x ∈ A,
        F (startOf hw x).val % w = (startOf hw (runTrans g x)).val) := by
  obtain ⟨P, K, R, offset, hne, F, hnd, hlen, hRsort, hsplit,
      hFdef, hFmono, hFper, hsemAll, hsemAny⟩ :=
    exists_constantFreeCutLift hw hg
  refine ⟨F, hFper, hFmono, ?_⟩
  intro x hx
  have hyB : runTrans g x ∈ B := hbij.mapsTo hx
  have htrack := sourceTargetCutLift_tracks_start hTarget hw P K R offset
    hne hRsort hsplit (hA x hx).1 (hB _ hyB).1 (hB _ hyB).2
    (fun p hp => hsemAll x p hp) (fun p hp => hsemAny x p hp)
  have hFx := congrFun hFdef (startOf hw x).val
  rw [hFx]
  exact htrack

end Internal
end AllenderOQ3
