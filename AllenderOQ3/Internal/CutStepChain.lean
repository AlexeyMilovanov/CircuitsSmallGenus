import AllenderOQ3.Internal.CutChain
import AllenderOQ3.Internal.ACCChain
import AllenderOQ3.Internal.ModulusLift

set_option autoImplicit false

namespace AllenderOQ3.Internal

variable {n w : Nat}

/-!
# From a cut sequence to a flat chain of relations (§6 → §9)

The §6 decomposition produces a `CutSequence`, whose composite `ComposeChain` is
an *inductively* structured composition of one-step relations (at the cut
layers) and gap block relations.  The §9 collapse, on the other hand, consumes a
flat, `Nat`-indexed family of relations composed by `StepChain`.

`cutRel` flattens a cut sequence into such a `Nat`-indexed family — its `k`-th
relation is the `k`-th relation of the sequence — and
`stepChain_cutRel_iff_composeChain` shows the two composites agree, the chain
length being `numRel seq`.
-/

/-- The `Nat`-indexed family of relations of a cut sequence: index `k` is the
`k`-th relation of the sequence (a one-step relation at a cut layer, or a gap
block relation), and `False` beyond the end of the sequence. -/
def cutRel {c : ADRCircuit n} (idx : LayerIndexing c w) (x : Fin n → Bool) {X : Finset Nat} :
    ∀ {i j : Nat}, CutSequence X i j → Nat → State w → State w → Prop
  | _, _, .empty _, _ => fun _ _ => False
  | _, _, .step (i := i) _ _, 0 => OneStep idx x i
  | _, _, .step _ rest, (k + 1) => cutRel idx x rest k
  | _, _, .gap (i := i) (k := k') _ _ _, 0 => Reach idx x i (k' - i)
  | _, _, .gap _ _ rest, (k + 1) => cutRel idx x rest k

theorem cutRel_step_zero {c : ADRCircuit n} (idx : LayerIndexing c w) (x : Fin n → Bool)
    {X : Finset Nat} {i j : Nat} (hX : i ∈ X) (rest : CutSequence X (i + 1) j) :
    cutRel idx x (CutSequence.step hX rest) 0 = OneStep idx x i := rfl

theorem cutRel_step_succ {c : ADRCircuit n} (idx : LayerIndexing c w) (x : Fin n → Bool)
    {X : Finset Nat} {i j : Nat} (hX : i ∈ X) (rest : CutSequence X (i + 1) j) (k : Nat) :
    cutRel idx x (CutSequence.step hX rest) (k + 1) = cutRel idx x rest k := rfl

theorem cutRel_gap_zero {c : ADRCircuit n} (idx : LayerIndexing c w) (x : Fin n → Bool)
    {X : Finset Nat} {i k' j : Nat} (h_lt : i < k')
    (h_not : ∀ l, i < l → l < k' → l ∉ X) (rest : CutSequence X k' j) :
    cutRel idx x (CutSequence.gap h_lt h_not rest) 0 = Reach idx x i (k' - i) := rfl

theorem cutRel_gap_succ {c : ADRCircuit n} (idx : LayerIndexing c w) (x : Fin n → Bool)
    {X : Finset Nat} {i k' j : Nat} (h_lt : i < k')
    (h_not : ∀ l, i < l → l < k' → l ∉ X) (rest : CutSequence X k' j) (k : Nat) :
    cutRel idx x (CutSequence.gap h_lt h_not rest) (k + 1) = cutRel idx x rest k := rfl

/-- **Flattening the §6 decomposition.**  The flat chain of the `numRel seq`
relations of a cut sequence composes to exactly the inductive composite of the
sequence. -/
theorem stepChain_cutRel_iff_composeChain {c : ADRCircuit n} (idx : LayerIndexing c w)
    (x : Fin n → Bool) {X : Finset Nat} :
    ∀ {i j : Nat} (seq : CutSequence X i j) (s t : State w),
      StepChain (cutRel idx x seq) (numRel seq) s t ↔ ComposeChain idx x seq s t := by
  intro i j seq
  induction seq with
  | empty i =>
      intro s t
      constructor
      · rintro rfl
        exact ComposeChain.empty s
      · intro h
        cases h
        rfl
  | @step i j hX rest ih =>
      intro s t
      have hnum : numRel (CutSequence.step hX rest) = 1 + numRel rest := by
        simp [numRel, Nat.add_comm]
      have hshift : ∀ (m : Nat) (a b : State w),
          cutRel idx x (CutSequence.step hX rest) (1 + m) a b ↔ cutRel idx x rest m a b := by
        intro m a b
        rw [Nat.add_comm, cutRel_step_succ]
      rw [hnum, stepChain_add]
      constructor
      · rintro ⟨u, h1, h2⟩
        rw [stepChain_one, cutRel_step_zero] at h1
        refine ComposeChain.step h1 ?_
        exact (ih u t).1 ((stepChain_congr _ (fun m _ a b => hshift m a b) u t).1 h2)
      · intro h
        cases h with
        | @step _ _ _ _ _ u _ h_step h_rest =>
            refine ⟨u, ?_, ?_⟩
            · rw [stepChain_one, cutRel_step_zero]
              exact h_step
            · exact (stepChain_congr _ (fun m _ a b => hshift m a b) u t).2
                ((ih u t).2 h_rest)
  | @gap i k' j h_lt h_not rest ih =>
      intro s t
      have hnum : numRel (CutSequence.gap h_lt h_not rest) = 1 + numRel rest := by
        simp [numRel, Nat.add_comm]
      have hshift : ∀ (m : Nat) (a b : State w),
          cutRel idx x (CutSequence.gap h_lt h_not rest) (1 + m) a b ↔ cutRel idx x rest m a b := by
        intro m a b
        rw [Nat.add_comm, cutRel_gap_succ]
      rw [hnum, stepChain_add]
      constructor
      · rintro ⟨u, h1, h2⟩
        rw [stepChain_one, cutRel_gap_zero] at h1
        refine ComposeChain.gap h1 ?_
        exact (ih u t).1 ((stepChain_congr _ (fun m _ a b => hshift m a b) u t).1 h2)
      · intro h
        cases h with
        | @gap _ _ _ _ _ _ _ u _ h_gap h_rest =>
            refine ⟨u, ?_, ?_⟩
            · rw [stepChain_one, cutRel_gap_zero]
              exact h_gap
            · exact (stepChain_congr _ (fun m _ a b => hshift m a b) u t).2
                ((ih u t).2 h_rest)

/-! ## ACC realizability of the flattened relations -/

/-- `ACCRealizes n M d G Q`: the predicate `Q` on inputs is decided by an `ACC[M]`
circuit of depth `≤ d` and size `≤ G`. -/
def ACCRealizes (n M d G : Nat) (Q : (Fin n → Bool) → Prop) : Prop :=
  ∃ a : ACCCircuit n M, WellFormedACC a ∧ (∀ g, a.layer g ≤ d) ∧ a.gateCount ≤ G ∧
    ∀ x, ACCAccepts a x ↔ Q x

theorem accRealizes_false (M d G : Nat) (hd : 1 ≤ d) (hG : 1 ≤ G) :
    ACCRealizes n M d G (fun _ => False) := by
  refine ⟨accConst n M false, wellFormedACC_accConst n M false, ?_, ?_, ?_⟩
  · intro g; rw [accConst_layer]; exact hd
  · rw [accConst_gateCount]; exact hG
  · intro x; simp [accAccepts_accConst]

theorem accRealizes_congr {M d G : Nat} {Q Q' : (Fin n → Bool) → Prop}
    (h : ∀ x, Q x ↔ Q' x) (hQ : ACCRealizes n M d G Q) : ACCRealizes n M d G Q' := by
  obtain ⟨a, h1, h2, h3, h4⟩ := hQ
  exact ⟨a, h1, h2, h3, fun x => (h4 x).trans (h x)⟩

/-- Lifting the modulus of a realization: an `ACC[m]` realization becomes an
`ACC[M]` realization for any positive multiple `M` of `m`, at the cost of doubling
the depth (plus two) and multiplying the size by `M + 2`. -/
theorem accRealizes_modulusLift {m M d G : Nat} (hdvd : m ∣ M) (hMpos : 0 < M)
    {Q : (Fin n → Bool) → Prop} (h : ACCRealizes n m d G Q) :
    ACCRealizes n M (2 * d + 2) ((M + 2) * G) Q := by
  obtain ⟨a, hwf, hlayer, hsize, hacc⟩ := h
  refine ⟨accModulusLift a hdvd, wellFormedACC_accModulusLift a hdvd hwf,
    accModulusLift_layer_le hlayer,
    le_trans (accModulusLift_gateCount_le a hdvd) (Nat.mul_le_mul_left _ hsize),
    fun x => ?_⟩
  rw [evalACC_accModulusLift_of_pos hMpos hwf x]
  exact hacc x

/-- Every relation of a flattened cut sequence is `ACC`-realizable as soon as the
one-step relations at the cut layers and the gap block relations are. -/
theorem exists_acc_cutRel {c : ADRCircuit n} (idx : LayerIndexing c w) {X : Finset Nat}
    (M d G : Nat) (hd : 1 ≤ d) (hG : 1 ≤ G)
    (hstep : ∀ l, l ∈ X → ∀ s t : State w,
      ACCRealizes n M d G (fun x => OneStep idx x l s t))
    (hgap : ∀ p q, p < q → (∀ l, p < l → l < q → l ∉ X) → ∀ s t : State w,
      ACCRealizes n M d G (fun x => Reach idx x p (q - p) s t)) :
    ∀ {i j : Nat} (seq : CutSequence X i j) (k : Nat) (s t : State w),
      ACCRealizes n M d G (fun x => cutRel idx x seq k s t) := by
  intro i j seq
  induction seq with
  | empty i =>
      intro k s t
      exact accRealizes_false M d G hd hG
  | @step i j hX rest ih =>
      intro k s t
      cases k with
      | zero => exact hstep i hX s t
      | succ k => exact ih k s t
  | @gap i k' j h_lt h_not rest ih =>
      intro k s t
      cases k with
      | zero => exact hgap i k' h_lt h_not s t
      | succ k => exact ih k s t

/-- Every relation of a bracketed chain is `ACC`-realizable as soon as the initial
relation, the output test and the chain's own relations are. -/
theorem exists_acc_bracketRel (M d G m : Nat) (hd : 1 ≤ d) (hG : 1 ≤ G) (z : State w)
    (Init Out : (Fin n → Bool) → State w → Prop)
    (Rel : (Fin n → Bool) → Nat → State w → State w → Prop)
    (hInit : ∀ t : State w, ACCRealizes n M d G (fun x => Init x t))
    (hOut : ∀ s : State w, ACCRealizes n M d G (fun x => Out x s))
    (hRel : ∀ (k : Nat) (s t : State w), ACCRealizes n M d G (fun x => Rel x k s t))
    (k : Nat) (s t : State w) :
    ACCRealizes n M d G (fun x => bracketRel (Init x) (Out x) (Rel x) m z k s t) := by
  classical
  unfold bracketRel
  by_cases hk0 : k = 0
  · refine accRealizes_congr (Q := fun x => Init x t) (fun x => ?_) (hInit t)
    simp [hk0]
  · by_cases hkm : k < m + 1
    · refine accRealizes_congr (Q := fun x => Rel x (k - 1) s t) (fun x => ?_) (hRel (k - 1) s t)
      simp [hk0, hkm]
    · by_cases hz : t = z
      · refine accRealizes_congr (Q := fun x => Out x s) (fun x => ?_) (hOut s)
        simp [hk0, hkm, hz]
      · refine accRealizes_congr (Q := fun _ => False) (fun x => ?_)
          (accRealizes_false M d G hd hG)
        simp [hk0, hkm, hz]

/-- **The §6 chain form of acceptance.**  For any cut sequence spanning the layers
of `c`, acceptance of `c` is exactly connectivity of a base point `z` to itself in
the flat chain of `numRel seq + 2` relations obtained by bracketing the sequence's
relations with the initial-state relation and the output test. -/
theorem adrAccepts_iff_stepChain_bracketRel {c : ADRCircuit n} (hc : WellFormedADR c)
    (idx : LayerIndexing c w) (x : Fin n → Bool)
    (h_out_comp : (c.kind c.output).isComputation = true)
    {X : Finset Nat} (seq : CutSequence X 0 (c.layer c.output)) (z : State w) :
    ADRAccepts c x ↔
      StepChain (bracketRel (InitState idx x) (fun t => t (idx.slot c.output) = true)
        (cutRel idx x seq) (numRel seq) z) (numRel seq + 2) z z := by
  rw [stepChain_bracketRel, adrAccepts_iff_reach hc idx x h_out_comp]
  refine exists_congr fun s => exists_congr fun t => and_congr_right fun _ => ?_
  refine and_congr ?_ Iff.rfl
  rw [stepChain_cutRel_iff_composeChain idx x seq s t,
    composeChain_iff_reach idx x X 0 (c.layer c.output) seq s t, Nat.sub_zero]

/-- **Stream C, assembled at the relational level.**  If the one-step relations at the
cut layers, the `P`-free gap block relations, the initial-state relation and the output
test are all realizable by `ACC[M]` circuits of depth `≤ d` and size `≤ G ≤ (n+1) ^ e₀`,
and the chain is short enough for the §9 round count `k + 1`, then acceptance of the
whole ADR circuit is realized by a single `ACC[M]` circuit of depth `≤ d + 2 * (k + 1)`
and size `≤ (n+1) ^ ((2 * w + 2) * (k + 1) + e₀ + 1)`. -/
theorem exists_acc_adrAccepts {M : Nat} {c : ADRCircuit n} (hc : WellFormedADR c)
    (idx : LayerIndexing c w) (h_out_comp : (c.kind c.output).isComputation = true)
    (P : Finset Nat) (d G e₀ C k : Nat)
    (hd : 1 ≤ d) (hG : 1 ≤ G) (hGpoly : G ≤ (n + 1) ^ e₀) (hn : 1 ≤ n)
    (hB : 2 ≤ Nat.log2 (n + 1)) (hcut : 2 * C ≤ Nat.log2 (n + 1))
    (hlen : 4 * P.card + 3 ≤ C * Nat.log2 (n + 1) ^ k)
    (hstep : ∀ l, l ∈ cutSet P → ∀ s t : State w,
      ACCRealizes n M d G (fun x => OneStep idx x l s t))
    (hgap : ∀ p q, p < q → (∀ l, p < l → l < q → l ∉ cutSet P) → ∀ s t : State w,
      ACCRealizes n M d G (fun x => Reach idx x p (q - p) s t))
    (hinit : ∀ t : State w, ACCRealizes n M d G (fun x => InitState idx x t))
    (hout : ∀ t : State w, ACCRealizes n M d G (fun _ => t (idx.slot c.output) = true)) :
    ∃ a : ACCCircuit n M, WellFormedACC a ∧ (∀ g, a.layer g ≤ d + 2 * (k + 1)) ∧
      a.gateCount ≤ (n + 1) ^ ((2 * w + 2) * (k + 1) + e₀ + 1) ∧
      (∀ x, ACCAccepts a x ↔ ADRAccepts c x) := by
  classical
  obtain ⟨seq, hseq⟩ := exists_cutSequence_cutSet_le P 0 (c.layer c.output) (Nat.zero_le _)
  set z : State w := fun _ => false with hz
  set m := numRel seq with hm
  have hmle : m + 2 ≤ C * Nat.log2 (n + 1) ^ k := by omega
  have hrel : ∀ (i : Nat) (s t : State w),
      ACCRealizes n M d G (fun x =>
        bracketRel (InitState idx x) (fun t => t (idx.slot c.output) = true)
          (cutRel idx x seq) m z i s t) :=
    fun i s t => exists_acc_bracketRel M d G m hd hG z
      (fun x t => InitState idx x t) (fun _ t => t (idx.slot c.output) = true)
      (fun x => cutRel idx x seq) hinit hout
      (exists_acc_cutRel idx M d G hd hG hstep hgap seq) i s t
  obtain ⟨a, hwf, hlayer, hsize, hacc⟩ :=
    exists_acc_stepChain (M := M) (w := w) C k (m + 2) d G e₀ hB hcut hmle hd hG hGpoly hn
      (fun x i s t => bracketRel (InitState idx x) (fun t => t (idx.slot c.output) = true)
        (cutRel idx x seq) m z i s t)
      hrel z z
  refine ⟨a, hwf, hlayer, hsize, fun x => ?_⟩
  rw [hacc x, ← adrAccepts_iff_stepChain_bracketRel hc idx x h_out_comp seq z]

end AllenderOQ3.Internal
