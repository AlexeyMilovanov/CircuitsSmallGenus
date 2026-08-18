import AllenderOQ3.Internal.BetaPorts
import AllenderOQ3.Internal.ACCJoin
import AllenderOQ3.Internal.Semantics

set_option autoImplicit false

namespace AllenderOQ3.Internal

/-!
# §7.3 An ACC circuit for a beta port

Given, for every gate `h` of `c`, an `ACC[M]` circuit `a h` computing the value of `h`
(these come from the width induction hypothesis for external computation gates, and are
trivial one-literal circuits for literal gates), the beta port of a core gate `g` is
computed by a single unbounded AND/OR over the *external* predecessors of `g`.  This adds
one layer and at most `|c|` blocks.
-/

variable {n M : Nat}

open Classical in
/-- The predecessors of `z` that lie outside the core through `v`. -/
noncomputable def externalPreds (c : ADRCircuit n) (v o z : Fin c.gateCount) :
    Finset (Fin c.gateCount) :=
  Finset.univ.filter fun h => h ∉ coreSet c v o ∧ c.edge h z = true

theorem mem_externalPreds {c : ADRCircuit n} {v o z h : Fin c.gateCount} :
    h ∈ externalPreds c v o z ↔ h ∉ coreSet c v o ∧ c.edge h z = true := by
  classical
  simp [externalPreds]

/-- The one-gate `ACC[M]` circuit computing a single literal, at an arbitrary modulus. -/
def literalACCMod (n M : Nat) (i : Fin n) (b : Bool) : ACCCircuit n M where
  gateCount := 1
  output := ⟨0, Nat.zero_lt_one⟩
  kind := fun _ => .literal i b
  layer := fun _ => 0
  edge := fun _ _ => false

theorem wellFormedACC_literalACCMod (i : Fin n) (b : Bool) :
    WellFormedACC (literalACCMod n M i b) :=
  ⟨fun _ _ h => by simp [literalACCMod] at h,
   fun _ => ⟨fun _ => ⟨i, b, rfl⟩, fun _ => rfl⟩,
   fun _ h => by simp [literalACCMod] at h⟩

theorem accAccepts_literalACCMod (i : Fin n) (b : Bool) (x : Fin n → Bool) :
    ACCAccepts (literalACCMod n M i b) x ↔ (if b then !(x i) else x i) = true := by
  constructor
  · rintro ⟨value, hv, hout⟩
    have h0 := hv (literalACCMod n M i b).output
    simp only [literalACCMod] at h0 hout
    rw [h0] at hout
    exact hout
  · intro hb
    refine ⟨fun _ => (if b then !(x i) else x i), ?_, hb⟩
    intro g
    simp only [literalACCMod]

/-- **Literal gates are free.**  A literal gate of `c` is computed by a one-gate `ACC[M]`
circuit, so the beta-port hypothesis of `exists_acc_betaPort` can always be met on the
literal gates of `c`. -/
theorem exists_acc_literal_gate {c : ADRCircuit n} (hc : WellFormedADR c)
    {h : Fin c.gateCount} {i : Fin n} {b : Bool} (hlit : c.kind h = .literal i b) :
    ∀ x, ACCAccepts (literalACCMod n M i b) x ↔ evalADR c hc x h = true := by
  intro x
  have hev : ADRValuation c x (evalADR c hc x) :=
    (adrValuation_iff_eq_evalADR hc).mpr rfl
  have h0 := hev h
  rw [hlit] at h0
  rw [accAccepts_literalACCMod, h0]

/-- **§7.3 beta-port circuit.**  An `ACC[M]` circuit deciding the beta-port value of a core
gate, built as one unbounded AND (resp. OR) over the circuits of the external
predecessors. -/
theorem exists_acc_betaPort {c : ADRCircuit n} (hc : WellFormedADR c)
    {v o : Fin c.gateCount} (g : Fin (coreSet c v o).card) {d G : Nat}
    (a : Fin c.gateCount → ACCCircuit n M)
    (hwf : ∀ h ∈ externalPreds c v o ((coreSet c v o).equivFin.symm g), WellFormedACC (a h))
    (hd : ∀ h ∈ externalPreds c v o ((coreSet c v o).equivFin.symm g),
      ∀ g' : Fin (a h).gateCount, (a h).layer g' ≤ d)
    (hsize : ∀ h ∈ externalPreds c v o ((coreSet c v o).equivFin.symm g),
      (a h).gateCount ≤ G)
    (hsem : ∀ h ∈ externalPreds c v o ((coreSet c v o).equivFin.symm g),
      ∀ x : Fin n → Bool, ACCAccepts (a h) x ↔ evalADR c hc x h = true) :
    ∃ b : ACCCircuit n M, WellFormedACC b ∧ (∀ g', b.layer g' ≤ d + 1) ∧
      b.gateCount ≤ c.gateCount * G + 1 ∧
      (∀ x, ACCAccepts b x ↔ betaPort c v o (evalADR c hc x) g = true) := by
  classical
  set z : Fin c.gateCount := ((coreSet c v o).equivFin.symm g : Fin c.gateCount) with hzdef
  set E : Finset (Fin c.gateCount) := externalPreds c v o z with hEdef
  set f : Fin E.card → ACCCircuit n M := fun i => a (E.equivFin.symm i) with hfdef
  have hext : ∀ i : Fin E.card,
      ((E.equivFin.symm i : Fin c.gateCount)) ∈ externalPreds c v o z :=
    fun i => (E.equivFin.symm i).2
  have hwf_f : ∀ i, WellFormedACC (f i) := fun i => hwf _ (hext i)
  have hd_f : ∀ (i : Fin E.card) (g' : Fin (f i).gateCount), (f i).layer g' ≤ d :=
    fun i g' => hd _ (hext i) _
  have hsize_join : (∑ i, (f i).gateCount) + 1 ≤ c.gateCount * G + 1 := by
    have h1 : (∑ i : Fin E.card, (f i).gateCount) ≤ ∑ _i : Fin E.card, G :=
      Finset.sum_le_sum fun i _ => hsize _ (hext i)
    have h2 : (∑ _i : Fin E.card, G) = E.card * G := by
      simp [Finset.sum_const, Finset.card_univ]
    have h3 : E.card ≤ c.gateCount := by
      have := E.card_le_univ
      simpa using this
    have h4 : E.card * G ≤ c.gateCount * G := Nat.mul_le_mul_right G h3
    omega
  have hcomp : (c.kind z).isComputation = true :=
    (mem_coreSet.mp ((coreSet c v o).equivFin.symm g).2).1
  have hbetadef : ∀ value : Fin c.gateCount → Bool, betaPort c v o value g =
      match c.kind z with
      | .literal _ _ => false
      | .andGate =>
          decide (∀ h, h ∉ coreSet c v o → c.edge h z = true → value h = true)
      | .orGate =>
          decide (∃ h, h ∉ coreSet c v o ∧ c.edge h z = true ∧ value h = true) :=
    fun _ => rfl
  cases hk : c.kind z with
  | literal i b =>
      rw [hk] at hcomp
      simp [ADRGate.isComputation] at hcomp
  | andGate =>
      refine ⟨accJoin f d .andGate,
        wellFormedACC_accJoin hwf_f hd_f (by simp) (by simp),
        accJoin_layer_le hd_f, hsize_join, ?_⟩
      intro x
      rw [accAccepts_accJoin_and hwf_f hd_f x, hbetadef, hk]
      simp only [decide_eq_true_eq]
      have hstep : (∀ i, ACCAccepts (f i) x) ↔
          (∀ i : Fin E.card, evalADR c hc x (E.equivFin.symm i) = true) :=
        forall_congr' fun i => hsem _ (hext i) x
      rw [hstep, forall_equivFin_iff E (fun h => evalADR c hc x h = true)]
      constructor
      · intro H h hnot he
        exact H h (mem_externalPreds.mpr ⟨hnot, he⟩)
      · intro H h hh
        obtain ⟨hnot, he⟩ := mem_externalPreds.mp hh
        exact H h hnot he
  | orGate =>
      refine ⟨accJoin f d .orGate,
        wellFormedACC_accJoin hwf_f hd_f (by simp) (by simp),
        accJoin_layer_le hd_f, hsize_join, ?_⟩
      intro x
      rw [accAccepts_accJoin_or hwf_f hd_f x, hbetadef, hk]
      simp only [decide_eq_true_eq]
      have hstep : (∃ i, ACCAccepts (f i) x) ↔
          (∃ i : Fin E.card, evalADR c hc x (E.equivFin.symm i) = true) :=
        exists_congr fun i => hsem _ (hext i) x
      rw [hstep, exists_equivFin_iff E (fun h => evalADR c hc x h = true)]
      constructor
      · rintro ⟨h, hh, hv⟩
        obtain ⟨hnot, he⟩ := mem_externalPreds.mp hh
        exact ⟨h, hnot, he, hv⟩
      · rintro ⟨h, hnot, he, hv⟩
        exact ⟨h, mem_externalPreds.mpr ⟨hnot, he⟩, hv⟩

end AllenderOQ3.Internal
