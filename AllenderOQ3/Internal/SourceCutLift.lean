import AllenderOQ3.Internal.LayerExtract
import AllenderOQ3.Internal.IntervalStart
import AllenderOQ3.Internal.ArcWordBlocks

/-!
# Source-cut lifts for the G3 geometry

This module isolates the source-side bookkeeping used by the geometric
winding argument.  It extracts a nonempty predecessor assignment from a
constant-free layer, pads a source-sorted arc word with the empty fibres of
unused source slots, and assigns every source cut an integral position in the
unrolled arc word.
-/

set_option autoImplicit false

namespace AllenderOQ3
namespace Internal

variable {w : Nat}

/-! ## Extracting genuinely constant-free layer data -/

/-- A constant-free certified layer has the usual predecessor semantics, and
every target fibre is nonempty.  The latter fact is recovered from the two
endpoint equations; this lets downstream geometry depend only on `P` and `K`,
without retaining the circuit witness. -/
theorem exists_constantFreeLayerData {g : TransMonoid w}
    (hg : isConstantFreeMap w g) :
    ∃ (P : Fin w → List (Fin w)) (K : Fin w → Bool),
      (∀ p, P p ≠ []) ∧
      (∀ p, (P p).Nodup) ∧
      (∀ p, (P p).length ≤ 2) ∧
      CycSortedSrc (arcPairWord P) ∧
      (∀ (z : Config w) (p : Fin w), K p = true →
        runTrans g z p = (P p).all (fun q => z q)) ∧
      (∀ (z : Config w) (p : Fin w), K p = false →
        runTrans g z p = (P p).any (fun q => z q)) := by
  classical
  obtain ⟨P, K, hnd, hlen, hsort, hsemAll, hsemAny⟩ :=
    exists_layerData (isNonCrossingMap_of_isConstantFreeMap hg)
  have hgmem : g ∈ NonCrossingCF w := Submonoid.subset_closure hg
  have hbot := runTrans_botConfig_of_mem_nonCrossingCF hgmem
  have htop := runTrans_topConfig_of_mem_nonCrossingCF hgmem
  have hne : ∀ p, P p ≠ [] := by
    intro p hp
    cases hK : K p with
    | false =>
        have hsem := hsemAny (topConfig w) p hK
        have hext := congrFun htop p
        rw [hsem, hp] at hext
        simp [topConfig] at hext
    | true =>
        have hsem := hsemAll (botConfig w) p hK
        have hext := congrFun hbot p
        rw [hsem, hp] at hext
        simp [botConfig] at hext
  exact ⟨P, K, hne, hnd, hlen, hsort, hsemAll, hsemAny⟩

/-! ## Empty-padded source fibres -/

/-- The arcs of `W` emitted by the source slot `q`.  This definition exists
for every `q`, so source slots absent from `W` are represented by `[]`. -/
def sourceFiber (W : List (Fin w × Fin w)) (q : Fin w) :
    List (Fin w × Fin w) :=
  W.filter (fun e => decide (e.1 = q))

theorem mem_sourceFiber_iff {W : List (Fin w × Fin w)} {q : Fin w}
    {e : Fin w × Fin w} :
    e ∈ sourceFiber W q ↔ e ∈ W ∧ e.1 = q := by
  simp [sourceFiber]

theorem sourceFiber_eq_nil_of_not_mem {W : List (Fin w × Fin w)}
    {q : Fin w} (h : ∀ e ∈ W, e.1 ≠ q) : sourceFiber W q = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro e he
  exact h e (mem_sourceFiber_iff.mp he).1 (mem_sourceFiber_iff.mp he).2

/-- A source-sorted word is exactly the concatenation of all its source
fibres in coordinate order.  Empty fibres are retained by `finRange`; this is
the padding needed when some source coordinates have no outgoing arcs. -/
theorem flatMap_sourceFiber_eq_of_srcSorted (W : List (Fin w × Fin w))
    (hW : SrcSorted W) :
    (List.finRange w).flatMap (sourceFiber W) = W := by
  have hgroup : GroupedAlong (fun e : Fin w × Fin w => e.1)
      (List.finRange w) W :=
    groupedAlong_of_pairwise_le (fun e : Fin w × Fin w => e.1)
      (List.finRange w) W (List.pairwise_lt_finRange w)
      (fun e _ => List.mem_finRange e.1) hW
  simpa [sourceFiber] using
    (flatMap_filter_of_groupedAlong (fun e : Fin w × Fin w => e.1)
      (List.finRange w) W (List.nodup_finRange w) hgroup)

/-! ## A generic nonnegative periodic prefix sum -/

/-- Prefix sum of a nonnegative weight repeated with period `w`. -/
def periodicPrefix (hw : 0 < w) (mu : Fin w → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => periodicPrefix hw mu n + mu ⟨n % w, Nat.mod_lt n hw⟩

@[simp] theorem periodicPrefix_zero (hw : 0 < w) (mu : Fin w → Nat) :
    periodicPrefix hw mu 0 = 0 := rfl

@[simp] theorem periodicPrefix_succ (hw : 0 < w) (mu : Fin w → Nat)
    (n : Nat) :
    periodicPrefix hw mu (n + 1) =
      periodicPrefix hw mu n + mu ⟨n % w, Nat.mod_lt n hw⟩ := rfl

theorem monotone_periodicPrefix (hw : 0 < w) (mu : Fin w → Nat) :
    Monotone (periodicPrefix hw mu) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [periodicPrefix_succ]
  exact Nat.le_add_right _ _

/-- Advancing one source circumference adds exactly the total weight of one
period. -/
theorem periodicPrefix_add_period (hw : 0 < w) (mu : Fin w → Nat) :
    ∀ x, periodicPrefix hw mu (x + w) =
      periodicPrefix hw mu x + periodicPrefix hw mu w := by
  intro x
  induction x with
  | zero => simp
  | succ x ih =>
      rw [Nat.succ_add, periodicPrefix_succ, ih, periodicPrefix_succ]
      have hmod : (x + w) % w = x % w := Nat.add_mod_right x w
      simp only [hmod]
      omega

/-- Recursive prefix sums agree with the ordinary sum over an initial
segment. -/
theorem periodicPrefix_eq_sum_range (hw : 0 < w) (mu : Fin w → Nat) :
    ∀ n, periodicPrefix hw mu n =
      ∑ i ∈ Finset.range n, mu ⟨i % w, Nat.mod_lt i hw⟩ := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [periodicPrefix_succ, ih, Finset.sum_range_succ]

/-- The weight accumulated over one period is the sum of all `Fin w`
weights. -/
theorem periodicPrefix_period_eq_sum (hw : 0 < w) (mu : Fin w → Nat) :
    periodicPrefix hw mu w = ∑ q : Fin w, mu q := by
  rw [periodicPrefix_eq_sum_range]
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  have hiw : i < w := Finset.mem_range.mp hi
  rw [dif_pos hiw]
  congr 1
  apply Fin.ext
  exact Nat.mod_eq_of_lt hiw

/-! ## Source cuts of a source-sorted arc word -/

/-- Number of arcs in the (possibly empty) fibre of source `q`. -/
def sourceMultiplicity (W : List (Fin w × Fin w)) (q : Fin w) : Nat :=
  (sourceFiber W q).length

/-- Integral position of the cut immediately before source coordinate `x` in
the infinitely unrolled source-major arc word. -/
def sourceCutLift (hw : 0 < w) (W : List (Fin w × Fin w)) (x : Nat) : Nat :=
  periodicPrefix hw (sourceMultiplicity W) x

theorem monotone_sourceCutLift (hw : 0 < w) (W : List (Fin w × Fin w)) :
    Monotone (sourceCutLift hw W) :=
  monotone_periodicPrefix hw (sourceMultiplicity W)

theorem sourceCutLift_add_period (hw : 0 < w)
    (W : List (Fin w × Fin w)) (x : Nat) :
    sourceCutLift hw W (x + w) =
      sourceCutLift hw W x + sourceCutLift hw W w :=
  periodicPrefix_add_period hw (sourceMultiplicity W) x

/-- Passing one source slot advances by the length of that slot's padded
fibre. -/
theorem sourceCutLift_succ_fin (hw : 0 < w)
    (W : List (Fin w × Fin w)) (q : Fin w) :
    sourceCutLift hw W (q.val + 1) =
      sourceCutLift hw W q.val + (sourceFiber W q).length := by
  rw [sourceCutLift, periodicPrefix_succ]
  congr 2
  apply Fin.ext
  exact Nat.mod_eq_of_lt q.isLt

/-- On the fundamental source window, the abstract prefix lift is literally
the length of the concatenated padded fibres before the cut. -/
theorem sourceCutLift_eq_length_take (hw : 0 < w)
    (W : List (Fin w × Fin w)) (n : Nat) (hn : n ≤ w) :
    sourceCutLift hw W n =
      ((List.finRange w).take n |>.flatMap (sourceFiber W)).length := by
  induction n with
  | zero => simp [sourceCutLift]
  | succ n ih =>
      have hnlt : n < w := by omega
      have hfin : (⟨n % w, Nat.mod_lt n hw⟩ : Fin w) = ⟨n, hnlt⟩ := by
        apply Fin.ext
        exact Nat.mod_eq_of_lt hnlt
      have htake := List.take_succ_eq_append_getElem
        (l := List.finRange w) (i := n) (by simpa using hnlt)
      have ih' := ih (by omega)
      rw [sourceCutLift] at ih'
      rw [sourceCutLift, periodicPrefix_succ, hfin,
        ih', htake, List.flatMap_append, List.length_append]
      simp only [List.flatMap_singleton]
      have hidx : n < (List.finRange w).length := by simpa using hnlt
      have hget : (List.finRange w)[n]'hidx = (⟨n, hnlt⟩ : Fin w) := by simp
      rw [hget, sourceMultiplicity]

/-- Rotating a source-sorted word at the prefix cut of `q` is exactly the
empty-padded source-fibre word read from `q` around the circle. -/
theorem rotate_sourceCutLift_eq_flatMap_rotate (hw : 0 < w)
    (W : List (Fin w × Fin w)) (hW : SrcSorted W) (q : Fin w) :
    W.rotate (sourceCutLift hw W q.val) =
      ((List.finRange w).rotate q.val).flatMap (sourceFiber W) := by
  let L := List.finRange w
  let pre := (L.take q.val).flatMap (sourceFiber W)
  let post := (L.drop q.val).flatMap (sourceFiber W)
  have hflat := flatMap_sourceFiber_eq_of_srcSorted W hW
  have hdecomp : W = pre ++ post := by
    dsimp [pre, post, L]
    rw [← List.flatMap_append, List.take_append_drop]
    exact hflat.symm
  have hk : sourceCutLift hw W q.val = pre.length := by
    dsimp [pre, L]
    exact sourceCutLift_eq_length_take hw W q.val q.isLt.le
  have hprele : pre.length ≤ (pre ++ post).length := by simp
  calc
    W.rotate (sourceCutLift hw W q.val) =
        (pre ++ post).rotate (sourceCutLift hw W q.val) :=
      congrArg (fun X => X.rotate (sourceCutLift hw W q.val)) hdecomp
    _ = (pre ++ post).rotate pre.length := by rw [hk]
    _ = post ++ pre := by
      rw [List.rotate_eq_drop_append_take hprele,
        List.drop_left, List.take_left]
    _ = ((List.finRange w).rotate q.val).flatMap (sourceFiber W) := by
      dsimp [pre, post, L]
      rw [List.rotate_eq_drop_append_take
        (by simp : q.val ≤ (List.finRange w).length), List.flatMap_append]

/-- The cut lift points to the leading cut of the arc segment emitted by an
interval configuration.  Rotating the source-sorted word at that cut exposes
all arcs from true sources first and all arcs from false sources afterwards.
The last conjunct records exactness, not just soundness of the two blocks. -/
theorem exists_trueFalse_sourceCut_partition (hw : 0 < w)
    (W : List (Fin w × Fin w)) (hW : SrcSorted W) {z : Config w}
    (hz : IsIntervalConfig z) :
    ∃ PT PF : List (Fin w × Fin w),
      W.rotate (sourceCutLift hw W (startOf hw z).val) = PT ++ PF ∧
      (∀ e ∈ PT, z e.1 = true) ∧
      (∀ e ∈ PF, z e.1 = false) ∧
      (∀ e ∈ W, z e.1 = true → e ∈ PT) := by
  let s := startOf hw z
  let len := lenOf z
  let shift : Fin w → Fin w := fun k => finShift k.val s
  let PT := (((List.finRange w).take len).map shift).flatMap (sourceFiber W)
  let PF := (((List.finRange w).drop len).map shift).flatMap (sourceFiber W)
  obtain ⟨-, hlen, hzpiece⟩ := eq_pieceConfig_canonical hz hw
  have hword : W.rotate (sourceCutLift hw W s.val) = PT ++ PF := by
    rw [rotate_sourceCutLift_eq_flatMap_rotate hw W hW s,
      rotate_finRange_eq, ← List.take_append_drop len (List.finRange w),
      List.map_append, List.flatMap_append]
  have hPT : ∀ e ∈ PT, z e.1 = true := by
    intro e he
    dsimp [PT] at he
    rw [List.mem_flatMap] at he
    obtain ⟨q, hq, heq⟩ := he
    rw [List.mem_map] at hq
    obtain ⟨k, hk, rfl⟩ := hq
    have hks : k.val < len := mem_take_finRange hk
    have hesrc : e.1 = finShift k.val s := (mem_sourceFiber_iff.mp heq).2
    rw [hzpiece, pieceConfig_true_iff]
    exact ⟨k.val, hks, hesrc.symm⟩
  have hPF : ∀ e ∈ PF, z e.1 = false := by
    intro e he
    dsimp [PF] at he
    rw [List.mem_flatMap] at he
    obtain ⟨q, hq, heq⟩ := he
    rw [List.mem_map] at hq
    obtain ⟨k, hk, rfl⟩ := hq
    have hks : len ≤ k.val := mem_drop_finRange hk
    have hesrc : e.1 = finShift k.val s := (mem_sourceFiber_iff.mp heq).2
    cases heval : z e.1 with
    | false => rfl
    | true =>
        exfalso
        rw [hzpiece, pieceConfig_true_iff] at heval
        obtain ⟨j, hj, hjeq⟩ := heval
        have hshift : finShift k.val s = finShift j s := by rw [← hesrc, ← hjeq]
        have hkj := finShift_amount_inj (a := k.val) (b := j)
          k.isLt (lt_of_lt_of_le hj hlen) hshift
        omega
  refine ⟨PT, PF, hword, hPT, hPF, ?_⟩
  intro e heW hez
  have herot : e ∈ W.rotate (sourceCutLift hw W s.val) := List.mem_rotate.mpr heW
  rw [hword, List.mem_append] at herot
  rcases herot with hePT | hePF
  · exact hePT
  · have := hPF e hePF
    rw [hez] at this
    exact Bool.noConfusion this

/-- Exact transport of the preceding partition back across the chosen
`CycSortedSrc` split.  The leading cut in the original target-major word is
`offset + sourceCutLift`; reducing it modulo the word length is harmless
because `List.rotate` is periodic. -/
theorem exists_trueFalse_rotatedSourceCut_partition (hw : 0 < w)
    {W R A B : List (Fin w × Fin w)} {offset : Nat}
    (hWA : W = A ++ B) (hR : R = B ++ A) (hoffset : offset = A.length)
    (hRsort : SrcSorted R) {z : Config w} (hz : IsIntervalConfig z) :
    ∃ PT PF : List (Fin w × Fin w),
      W.rotate ((offset + sourceCutLift hw R (startOf hw z).val) % W.length) =
          PT ++ PF ∧
      (∀ e ∈ PT, z e.1 = true) ∧
      (∀ e ∈ PF, z e.1 = false) ∧
      (∀ e ∈ W, z e.1 = true → e ∈ PT) := by
  obtain ⟨PT, PF, hpart, hPT, hPF, hexact⟩ :=
    exists_trueFalse_sourceCut_partition hw R hRsort hz
  have hoffle : offset ≤ W.length := by
    rw [hoffset, hWA, List.length_append]
    omega
  have hWrot : W.rotate offset = R := by
    calc
      W.rotate offset = (A ++ B).rotate A.length := by rw [hWA, hoffset]
      _ = B ++ A := by
        rw [List.rotate_eq_drop_append_take (by simp),
          List.drop_left, List.take_left]
      _ = R := hR.symm
  refine ⟨PT, PF, ?_, hPT, hPF, ?_⟩
  · rw [List.rotate_mod]
    rw [← List.rotate_rotate W offset
      (sourceCutLift hw R (startOf hw z).val), hWrot]
    exact hpart
  · intro e heW hez
    apply hexact e
    · have hmemrot : e ∈ W.rotate offset := List.mem_rotate.mpr heW
      rwa [hWrot] at hmemrot
    · exact hez

/-- In a source-sorted word, one source circumference advances by the full
arc-word length, including the empty source fibres. -/
theorem sourceCutLift_period_eq_length (hw : 0 < w)
    (W : List (Fin w × Fin w)) (hW : SrcSorted W) :
    sourceCutLift hw W w = W.length := by
  rw [sourceCutLift, periodicPrefix_period_eq_sum]
  have hflat := congrArg List.length (flatMap_sourceFiber_eq_of_srcSorted W hW)
  rw [List.length_flatMap] at hflat
  have hsum : (List.map (fun q => (sourceFiber W q).length)
      (List.finRange w)).sum = ∑ q : Fin w, sourceMultiplicity W q := by
    simp only [sourceMultiplicity]
    rw [← List.sum_toFinset (fun q : Fin w => (sourceFiber W q).length)
      (List.nodup_finRange w)]
    simp
  rw [← hsum]
  exact hflat

/-! ## Rotating a cyclically source-sorted target word -/

/-- Choose a source-sorted rotation of a cyclically source-sorted word.  The
offset is the length of the prefix moved to the back; adding it to a cut in
the sorted rotation gives the corresponding cut in the unrolled original
target-major word. -/
theorem exists_sourceSortedRotation {W : List (Fin w × Fin w)}
    (hW : CycSortedSrc W) :
    ∃ (R : List (Fin w × Fin w)) (offset : Nat),
      SrcSorted R ∧
      R.length = W.length ∧
      CyclicRotation W R ∧
      offset ≤ W.length ∧
      ∃ A B : List (Fin w × Fin w),
        W = A ++ B ∧ R = B ++ A ∧ offset = A.length := by
  obtain ⟨A, B, hAB, hBA⟩ := hW
  refine ⟨B ++ A, A.length, hBA, ?_, ?_, ?_, A, B, hAB, rfl, rfl⟩
  · rw [hAB]
    simp only [List.length_append]
    omega
  · exact ⟨A, B, hAB, rfl⟩
  · rw [hAB]
    simp

/-- The global target-word coordinate of the source cut.  `offset` accounts
for the rotation from the target-major word to its source-sorted reading. -/
def rotatedSourceCutLift (hw : 0 < w)
    (R : List (Fin w × Fin w)) (offset x : Nat) : Nat :=
  offset + sourceCutLift hw R x

theorem monotone_rotatedSourceCutLift (hw : 0 < w)
    (R : List (Fin w × Fin w)) (offset : Nat) :
    Monotone (rotatedSourceCutLift hw R offset) := by
  intro x y hxy
  exact Nat.add_le_add_left (monotone_sourceCutLift hw R hxy) offset

theorem rotatedSourceCutLift_add_period (hw : 0 < w)
    (R : List (Fin w × Fin w)) (offset x : Nat) :
    rotatedSourceCutLift hw R offset (x + w) =
      rotatedSourceCutLift hw R offset x + sourceCutLift hw R w := by
  simp only [rotatedSourceCutLift, sourceCutLift_add_period]
  omega

/-- A cyclically source-sorted word has a canonical *kind* of global
source-cut lift: choose any sorted rotation and add its rotation offset.  The
result is monotone and advances by the exact word length after one traversal
of the source circle. -/
theorem exists_rotatedSourceCutLift (hw : 0 < w)
    {W : List (Fin w × Fin w)} (hW : CycSortedSrc W) :
    ∃ (R : List (Fin w × Fin w)) (offset : Nat) (kappa : Nat → Nat),
      SrcSorted R ∧
      R.length = W.length ∧
      CyclicRotation W R ∧
      offset ≤ W.length ∧
      (∃ A B : List (Fin w × Fin w),
        W = A ++ B ∧ R = B ++ A ∧ offset = A.length) ∧
      kappa = rotatedSourceCutLift hw R offset ∧
      Monotone kappa ∧
      (∀ x, kappa (x + w) = kappa x + W.length) := by
  obtain ⟨R, offset, hsort, hlen, hrot, hoff, hsplit⟩ :=
    exists_sourceSortedRotation hW
  refine ⟨R, offset, rotatedSourceCutLift hw R offset,
    hsort, hlen, hrot, hoff, hsplit, rfl,
    monotone_rotatedSourceCutLift hw R offset, ?_⟩
  intro x
  rw [rotatedSourceCutLift_add_period,
    sourceCutLift_period_eq_length hw R hsort, hlen]

/-- Fully extracted source-cut package for one constant-free layer.  This is
the source-side input expected by the remaining first-true-target argument in
G3. -/
theorem exists_constantFreeSourceCutData (hw : 0 < w) {g : TransMonoid w}
    (hg : isConstantFreeMap w g) :
    ∃ (P : Fin w → List (Fin w)) (K : Fin w → Bool)
        (R : List (Fin w × Fin w)) (offset : Nat) (kappa : Nat → Nat),
      (∀ p, P p ≠ []) ∧
      (∀ p, (P p).Nodup) ∧
      (∀ p, (P p).length ≤ 2) ∧
      SrcSorted R ∧
      R.length = (arcPairWord P).length ∧
      CyclicRotation (arcPairWord P) R ∧
      offset ≤ (arcPairWord P).length ∧
      (∃ A B : List (Fin w × Fin w),
        arcPairWord P = A ++ B ∧ R = B ++ A ∧ offset = A.length) ∧
      kappa = rotatedSourceCutLift hw R offset ∧
      Monotone kappa ∧
      (∀ x, kappa (x + w) = kappa x + (arcPairWord P).length) ∧
      (∀ (z : Config w) (p : Fin w), K p = true →
        runTrans g z p = (P p).all (fun q => z q)) ∧
      (∀ (z : Config w) (p : Fin w), K p = false →
        runTrans g z p = (P p).any (fun q => z q)) := by
  obtain ⟨P, K, hne, hnd, hlen, hsort, hsemAll, hsemAny⟩ :=
    exists_constantFreeLayerData hg
  obtain ⟨R, offset, kappa, hRsort, hRlen, hrot, hoff, hsplit, hkappa,
      hkmono, hkper⟩ := exists_rotatedSourceCutLift hw hsort
  exact ⟨P, K, R, offset, kappa, hne, hnd, hlen, hRsort, hRlen,
    hrot, hoff, hsplit, hkappa, hkmono, hkper, hsemAll, hsemAny⟩

end Internal
end AllenderOQ3
