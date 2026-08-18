import AllenderOQ3.Internal.BetaBridge
import AllenderOQ3.Internal.FaninReduce
import AllenderOQ3.Internal.PortSubst
import AllenderOQ3.Internal.PruneReach
import AllenderOQ3.Internal.BridgeArith
import AllenderOQ3.Internal.CutStepChain

set_option autoImplicit false

namespace AllenderOQ3.Internal

open AllenderOQ3

/-!
# §7 The width induction step of the planar bridge

Given the planar bridge at computation width `w - 1` (the induction hypothesis) and
External Facts 2 and 3, this file compiles an arbitrary well-formed rotation-planar
circuit of computation width `≤ w` into a single `ACC[M]` circuit.

The route is the one of `docs/MATHEMATICAL_PROOF.md` §7:

* §7.1 prune to the ancestor cone of the output (`prunedCircuit`), so that every gate
  reaches the output;
* §7.2 extract the cylindrical core through an earliest computation gate `v`
  (`coreWithPorts`); the computation gates outside the core have width `≤ w - 1`;
* §7.3 the induction hypothesis compiles the ancestor cone of every external predecessor,
  hence every *beta port* of the core, into an `ACC[M₁]` circuit;
* §7.4 the N4 refinement (`incidenceRefinement`) turns the core, with its ports adjoined
  as fresh inputs, into an `HMVNormal` incidence-cylindrical circuit of bounded total
  width;
* §7.5 External Fact 3 compiles that into an `ACC[M₂]` *wrapper* over `n + p` inputs, and
  `accPortSubst` substitutes the beta-port circuits for the `p` port inputs (both sides
  lifted to the common modulus `M = 2 * M₁ * M₂`);
* §7.6 the size bookkeeping is `BridgeArith.size_recurrence_absorb`.
-/

variable {n : Nat}

/-- The common modulus of the width-induction step. -/
def bridgeStepModulus (M₁ M₂ : Nat) : Nat := 2 * M₁ * M₂

/-- The depth bound produced by one width-induction step. -/
def bridgeStepDepth (d₁ d₂ : Nat) : Nat := 2 * d₂ + 2 + (2 * (d₁ + 1) + 2) + 2

/-- The gate-count constant of the N4 refinement at fan-in and width `w`. -/
def n4SizeConst (w : Nat) : Nat := (w + 2) * ((w + 1) * w + 1)

/-- The size exponent produced by one width-induction step. -/
def bridgeStepSizeExp (w M e₁ e₂ : Nat) : Nat :=
  max (max (max (1 * (M + 2) + (e₁ + 1 + 1))
      (3 * (M + 2) + (n4SizeConst w + 2) * e₂)) ((M + 2) + 1) + 2) (M + 2)

theorem le_bridgeStepSizeExp_left (w M e₁ e₂ : Nat) :
    max (max (1 * (M + 2) + (e₁ + 1 + 1))
      (3 * (M + 2) + (n4SizeConst w + 2) * e₂)) ((M + 2) + 1) + 2
      ≤ bridgeStepSizeExp w M e₁ e₂ := le_max_left _ _

theorem le_bridgeStepSizeExp_right (w M e₁ e₂ : Nat) :
    M + 2 ≤ bridgeStepSizeExp w M e₁ e₂ := le_max_right _ _

/-- Size of the External-Fact-3 wrapper in terms of the size of the *source* circuit:
the N4 refinement blows the gate count up only by the constant factor `K`. -/
theorem wrapper_size_le {N C A K e : Nat} (hN : 1 ≤ N) (hC : C ≤ K * N)
    (hA : A ≤ (C + 1) ^ e) : A ≤ (N + 1) ^ ((K + 2) * e) := by
  have hT : 2 ≤ N + 1 := by omega
  have h1 : C + 1 ≤ (N + 1) ^ (K + 2) := by
    calc C + 1 ≤ K * N + 1 := Nat.add_le_add_right hC 1
      _ ≤ (K + 1) * (N + 1) := by nlinarith
      _ ≤ (N + 1) ^ (K + 2) := by
          have := const_mul_pow_le hT (K + 1) 1
          simpa using this
  calc A ≤ (C + 1) ^ e := hA
    _ ≤ ((N + 1) ^ (K + 2)) ^ e := Nat.pow_le_pow_left h1 e
    _ = (N + 1) ^ ((K + 2) * e) := (pow_mul _ _ _).symm

/-- The §7.6 size recurrence of one width-induction step, in pure arithmetic form. -/
theorem bridgeStep_size_arith {N Sz GA Sm Mv K e₁ e₂ : Nat} (hN : 1 ≤ N)
    (hGA : GA ≤ (Mv + 2) * (N + 1) ^ ((K + 2) * e₂))
    (hSm : Sm ≤ N * ((Mv + 2) * (N * (N + 1) ^ e₁ + 1)))
    (hS : Sz ≤ 3 * GA + Sm) :
    Sz ≤ (N + 1) ^ (max (max (1 * (Mv + 2) + (e₁ + 1 + 1))
      (3 * (Mv + 2) + (K + 2) * e₂)) ((Mv + 2) + 1) + 2) := by
  refine size_recurrence_absorb hN ?_
  have t1 : N * (N + 1) ^ e₁ ≤ (N + 1) ^ (e₁ + 1) := mul_self_pow_le e₁
  have t2 : (N * (Mv + 2)) * (N * (N + 1) ^ e₁) ≤ (N * (Mv + 2)) * (N + 1) ^ (e₁ + 1) :=
    Nat.mul_le_mul_left _ t1
  have t3 : N * (Mv + 2) ≤ (Mv + 2) * (N + 1) := by nlinarith
  nlinarith [hS, hGA, hSm, t2, t3]

/-- **§7.5 port substitution, packaged.**  A wrapper circuit over `n + p` inputs whose
upper `p` inputs are fed by the port circuits `B` realizes the predicate that the wrapper
realizes on the concatenated input. -/
theorem accPortSubst_realizes {p M dA dB : Nat} (A : ACCCircuit (n + p) M)
    (B : Fin p → ACCCircuit n M) (hAwf : WellFormedACC A) (hBwf : ∀ i, WellFormedACC (B i))
    (hAd : ∀ g, A.layer g ≤ dA) (hBd : ∀ i g, (B i).layer g ≤ dB)
    {Q : (Fin n → Bool) → Prop} {y : (Fin n → Bool) → Fin p → Bool}
    (hBsem : ∀ i x, ACCAccepts (B i) x ↔ y x i = true)
    (hAsem : ∀ x, ACCAccepts A (Fin.addCases x (y x)) ↔ Q x) :
    WellFormedACC (accPortSubst A B) ∧
      (∀ g, (accPortSubst A B).layer g ≤ dA + dB + 2) ∧
      (accPortSubst A B).gateCount ≤ 3 * A.gateCount + ∑ i, (B i).gateCount ∧
      (∀ x, ACCAccepts (accPortSubst A B) x ↔ Q x) := by
  refine ⟨wellFormedACC_accPortSubst A B hAwf hBwf,
    accPortSubst_layer_le hAd hBd, ?_, ?_⟩
  · have := accPortSubst_gateCount_le A B
    omega
  · intro x
    have hx : (fun i => evalACC (B i) (hBwf i) x (B i).output) = y x := by
      funext i
      refine acc_bool_eq_of_iff ?_
      rw [← accAccepts_iff (hBwf i) x]
      exact hBsem i x
    have h := evalACC_accPortSubst hAwf hBwf x
    simp only [hx] at h
    rw [h]
    exact hAsem x

/-- **§7 width-induction step, main case.**  A well-formed rotation-planar circuit of
computation width `≤ w`, all of whose gates reach its output and whose output is a
computation gate, is simulated by a single `ACC[2 * M₁ * M₂]` circuit of constant depth
and polynomial size. -/
theorem acc_of_computation_output (h2 : HansenArcOrderPrinciple)
    {w M₁ d₁ e₁ M₂ d₂ e₂ : Nat} (hM₁ : 2 ≤ M₁) (hM₂ : 2 ≤ M₂)
    (hIH : PlanarBridgeAt (w - 1) M₁ d₁ e₁)
    (hsim : ∀ {N : Nat} (a : ADRCircuit N), HMVNormal a → TotalWidthAtMost a ((w + 1) * w) →
      Nonempty (IncidenceCylinder a) →
      ∃ b : ACCCircuit N M₂, WellFormedACC b ∧ (∀ g, b.layer g ≤ d₂) ∧
        b.gateCount ≤ (a.gateCount + 1) ^ e₂ ∧ (∀ x, ACCAccepts b x ↔ ADRAccepts a x))
    (c : ADRCircuit n) (hc : WellFormedADR c) (hplanar : RotationPlanar c)
    (hw : ADRHasWidthAtMost c w)
    (hreach : ∀ g, EdgeReach c g c.output)
    (hout : (c.kind c.output).isComputation = true) :
    ∃ a : ACCCircuit n (bridgeStepModulus M₁ M₂), WellFormedACC a ∧
      (∀ g, a.layer g ≤ bridgeStepDepth d₁ d₂) ∧
      a.gateCount ≤ (c.gateCount + 1) ^
        (bridgeStepSizeExp w (bridgeStepModulus M₁ M₂) e₁ e₂) ∧
      (∀ x, ACCAccepts a x ↔ ADRAccepts c x) := by
  classical
  -- §7.2: the cylindrical core through an earliest computation gate
  obtain ⟨v, hv_comp, hv_drop⟩ := exists_core_width_lt hc hw hreach ⟨c.output, hout⟩
  have hvmem : v ∈ coreSet c v c.output :=
    mem_coreSet.mpr ⟨hv_comp, edgeReach_refl c v, hreach v⟩
  have homem : c.output ∈ coreSet c v c.output :=
    mem_coreSet.mpr ⟨hout, hreach v, edgeReach_refl c c.output⟩
  have hcore_wf : WellFormedADR (coreWithPorts c v c.output homem) :=
    wellFormedADR_coreWithPorts c v c.output homem hc
  have hcore_tw : TotalWidthAtMost (coreWithPorts c v c.output homem) w :=
    totalWidthAtMost_coreWithPorts_of_widthAtMost c v c.output homem hw
  have hcore_fan : ∀ g, predecessorCount (coreWithPorts c v c.output homem) g ≤ w :=
    predecessorCount_coreWithPorts_le_width homem hc hw
  have hcore_cyl : Nonempty (IncidenceCylinder (coreWithPorts c v c.output homem)) :=
    incidenceCylinder_coreWithPorts h2 homem hvmem hc hplanar
  -- §7.4: the N4 refinement of the core
  obtain ⟨c', emb, hnorm, htw', hsz', hcyl', hout', hsem'⟩ :=
    incidenceRefinement (coreWithPorts c v c.output homem) w w hcore_wf hcore_tw hcore_fan
      hcore_cyl
  -- §7.5: External Fact 3 on the refined core
  obtain ⟨a, hawf, had, hasz, hasem⟩ := hsim c' hnorm htw' hcyl'
  -- §7.3: the beta-port circuits from the induction hypothesis
  choose b hbwf hbd hbsz hbsem using fun g =>
    exists_acc_betaPort_of_widthDrop hc hplanar hIH hv_drop g
  have hdvd₁ : M₁ ∣ bridgeStepModulus M₁ M₂ := ⟨2 * M₂, by rw [bridgeStepModulus]; ring⟩
  have hdvd₂ : M₂ ∣ bridgeStepModulus M₁ M₂ := ⟨2 * M₁, by rw [bridgeStepModulus]; ring⟩
  have hMpos : 0 < bridgeStepModulus M₁ M₂ := by
    rw [bridgeStepModulus]; positivity
  have hc'wf : WellFormedADR c' := hnorm.1
  -- the semantic chain for the wrapper
  have hAsem : ∀ x : Fin n → Bool,
      ACCAccepts (accModulusLift a hdvd₂)
        (Fin.addCases x (betaPort c v c.output (evalADR c hc x))) ↔ ADRAccepts c x := by
    intro x
    rw [evalACC_accModulusLift_of_pos hMpos hawf, hasem]
    have hval : ADRValuation c x (evalADR c hc x) :=
      (adrValuation_iff_eq_evalADR hc).mpr rfl
    have hPA := portAugmentedADRValuation_coreWithPorts c v c.output homem x
      (evalADR c hc x) hval
    have hV' : ADRValuation c' (Fin.addCases x (betaPort c v c.output (evalADR c hc x)))
        (evalADR c' hc'wf (Fin.addCases x (betaPort c v c.output (evalADR c hc x)))) :=
      (adrValuation_iff_eq_evalADR hc'wf).mpr rfl
    have key := hsem' x (betaPort c v c.output (evalADR c hc x))
      (fun g => evalADR c hc x ((coreSet c v c.output).equivFin.symm g)) _ hPA hV'
      (coreWithPorts c v c.output homem).output
    have hsymm : (((coreSet c v c.output).equivFin.symm
        (coreWithPorts c v c.output homem).output : { z // z ∈ coreSet c v c.output })
          : Fin c.gateCount) = c.output := by
      change (((coreSet c v c.output).equivFin.symm
        ((coreSet c v c.output).equivFin ⟨c.output, homem⟩)) : Fin c.gateCount) = c.output
      rw [Equiv.symm_apply_apply]
    rw [adrAccepts_iff hc'wf, hout', key, adrAccepts_iff hc, hsymm]
  -- §7.5: substitute the ports
  obtain ⟨hwf, hd, hsize, hsem⟩ :=
    accPortSubst_realizes (accModulusLift a hdvd₂)
      (fun g => accModulusLift (b g) hdvd₁)
      (wellFormedACC_accModulusLift a hdvd₂ hawf)
      (fun i => wellFormedACC_accModulusLift (b i) hdvd₁ (hbwf i))
      (accModulusLift_layer_le had)
      (fun i => accModulusLift_layer_le (hbd i))
      (y := fun x => betaPort c v c.output (evalADR c hc x))
      (Q := fun x => ADRAccepts c x)
      (fun i x => by
        rw [evalACC_accModulusLift_of_pos hMpos (hbwf i)]
        exact hbsem i x)
      hAsem
  refine ⟨_, hwf, ?_, ?_, hsem⟩
  · intro g
    have := hd g
    rw [bridgeStepDepth]
    omega
  · -- §7.6 size bookkeeping
    simp only [coreWithPorts_gateCount] at hsz'
    have hN : 1 ≤ c.gateCount := c.output.pos
    have hcard : (coreSet c v c.output).card ≤ c.gateCount := by
      simpa using Finset.card_le_univ (coreSet c v c.output)
    have hGA : (accModulusLift a hdvd₂).gateCount
        ≤ (bridgeStepModulus M₁ M₂ + 2)
          * (c.gateCount + 1) ^ ((n4SizeConst w + 2) * e₂) :=
      le_trans (accModulusLift_gateCount_le a hdvd₂)
        (Nat.mul_le_mul_left _
          (wrapper_size_le hN (le_trans hsz' (Nat.mul_le_mul_left _ hcard)) hasz))
    have hBi : ∀ i, (accModulusLift (b i) hdvd₁).gateCount
        ≤ (bridgeStepModulus M₁ M₂ + 2)
          * (c.gateCount * (c.gateCount + 1) ^ e₁ + 1) := fun i =>
      le_trans (accModulusLift_gateCount_le (b i) hdvd₁) (Nat.mul_le_mul_left _ (hbsz i))
    have hsum : (∑ i, (accModulusLift (b i) hdvd₁).gateCount)
        ≤ c.gateCount * ((bridgeStepModulus M₁ M₂ + 2)
          * (c.gateCount * (c.gateCount + 1) ^ e₁ + 1)) := by
      refine le_trans (Finset.sum_le_sum (fun i _ => hBi i)) ?_
      rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_fin]
      exact Nat.mul_le_mul_right _ hcard
    refine le_trans (bridgeStep_size_arith hN hGA hsum hsize)
      (Nat.pow_le_pow_right (by omega) (le_bridgeStepSizeExp_left w _ e₁ e₂))

/-- **§7 width-induction step.**  From the planar bridge at width `w - 1` and External
Facts 2 and 3, the planar bridge at width `w`. -/
theorem bridge_step (h2 : HansenArcOrderPrinciple) (h3 : QuantitativeCylindricalACCPrinciple)
    {w M₁ d₁ e₁ : Nat} (hM₁ : 2 ≤ M₁) (hIH : PlanarBridgeAt (w - 1) M₁ d₁ e₁) :
    ∃ M d e, 2 ≤ M ∧ PlanarBridgeAt w M d e := by
  classical
  obtain ⟨M₂, d₂, e₂, hM₂, hsim⟩ := h3 ((w + 1) * w)
  set M := bridgeStepModulus M₁ M₂ with hM
  set E := bridgeStepSizeExp w M e₁ e₂ with hE
  have hMle : 2 ≤ M := by
    rw [hM, bridgeStepModulus]
    calc 2 = 2 * 1 * 1 := by norm_num
      _ ≤ 2 * M₁ * M₂ := by
          exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 (by omega)) (by omega)
  refine ⟨M, max (bridgeStepDepth d₁ d₂) 2, E, hMle, ?_⟩
  intro n c hc hplanar hw
  have hN : 1 ≤ c.gateCount := c.output.pos
  have hbase : 2 ≤ c.gateCount + 1 := by omega
  by_cases hoc : (c.kind c.output).isComputation = true
  · -- the main case: the output is a computation gate
    have hc₀ : WellFormedADR (prunedCircuit c) := wellFormed_prunedCircuit hc
    have hkind₀ : (prunedCircuit c).kind (prunedCircuit c).output = c.kind c.output := by
      change c.kind ((ancestorEmbedding c).toFun (ancestorOutput c)) = _
      rw [ancestorEmbedding_ancestorOutput]
    obtain ⟨a, hawf, had, hasz, hasem⟩ :=
      acc_of_computation_output h2 hM₁ hM₂ hIH hsim (prunedCircuit c) hc₀
        (rotationPlanar_prunedCircuit hplanar) (width_prunedCircuit hw)
        (edgeReach_output_prunedCircuit c) (by rw [hkind₀]; exact hoc)
    refine ⟨a, hawf, fun g => le_trans (had g) (le_max_left _ _), ?_, ?_⟩
    · refine le_trans hasz (Nat.pow_le_pow_left ?_ _)
      have := gateCount_prunedCircuit_le c
      omega
    · intro x
      exact (hasem x).trans (adrAccepts_prunedCircuit hc x)
  · -- the degenerate case: the output is a literal
    have hlit : ∃ (i : Fin n) (b : Bool), c.kind c.output = ADRGate.literal i b := by
      rcases hkind : c.kind c.output with ⟨i, b⟩ | _ | _
      · exact ⟨i, b, rfl⟩
      · rw [hkind] at hoc; exact absurd rfl hoc
      · rw [hkind] at hoc; exact absurd rfl hoc
    obtain ⟨i, b, hlit⟩ := hlit
    have hdvd : (2 : Nat) ∣ M := by
      rw [hM, bridgeStepModulus]
      exact ⟨M₁ * M₂, by ring⟩
    refine ⟨accModulusLift (literalACC n i b) hdvd,
      wellFormedACC_accModulusLift _ hdvd (wellFormedACC_literalACC i b), ?_, ?_, ?_⟩
    · intro g
      have := accModulusLift_layer_le (c := literalACC n i b) (hM := hdvd) (d := 0)
        (fun g => le_refl 0) g
      omega
    · have h1 : (accModulusLift (literalACC n i b) hdvd).gateCount ≤ (M + 2) * 1 := by
        have := accModulusLift_gateCount_le (literalACC n i b) hdvd
        simpa [literalACC] using this
      have h2' : M + 2 ≤ 2 ^ (M + 2) := le_of_lt Nat.lt_two_pow_self
      have h3' : (2 : Nat) ^ (M + 2) ≤ (c.gateCount + 1) ^ (M + 2) :=
        Nat.pow_le_pow_left hbase _
      have h4' : (c.gateCount + 1) ^ (M + 2) ≤ (c.gateCount + 1) ^ E :=
        Nat.pow_le_pow_right (by omega) (le_bridgeStepSizeExp_right w M e₁ e₂)
      omega
    · intro x
      rw [evalACC_accModulusLift_of_pos (by omega) (wellFormedACC_literalACC i b) x]
      exact acc_of_literal_output hc hlit x

end AllenderOQ3.Internal
