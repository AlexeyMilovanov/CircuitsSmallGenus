import AllenderOQ3.Internal.NonCrossingDefs
import AllenderOQ3.Internal.NonCrossingSemantics
import AllenderOQ3.Internal.ACCFewVars
import AllenderOQ3.Internal.ACCJoin

/-!
# The certificate-aligned layer transition as a small `ACC` circuit

`layerTransMap c cert x ell s` is the route-2 (certificate-aligned) transition of
the whole layer `ell + 1`, including the literal ports, which is the reading
matching `TotalWidthAtMost`.  For a *fixed* layer index and fixed source and
target configurations it is a predicate of the input `x` alone, and it depends on
`x` through at most one variable per slot: slots carrying a literal port read a
single (possibly negated) input variable, and every other slot is constant in
`x`.

* `layerTransMap_slot_dichotomy` — the slotwise literal/constant dichotomy;
* `exists_acc_layerTransMap` — a depth-`2` `ACC[m]` circuit of size at most
  `2 * w + 2 ^ w + 1` deciding `layerTransMap c cert x ell s = t`.
-/

set_option autoImplicit false

namespace AllenderOQ3.Internal

variable {n w : Nat} (c : ADRCircuit n) (cert : IncidenceCylinder c)

/-- **Slotwise dichotomy for the certificate-aligned layer transition.**  Each
slot of `layerTransMap c cert x ell s` is, uniformly in `x`, either a single
(possibly negated) input variable — when the slot carries a literal port — or a
constant. -/
theorem layerTransMap_slot_dichotomy (ell : Nat) (s : Config w) (j : Fin w) :
    (∃ (idx : Fin n) (neg : Bool), ∀ x : Fin n → Bool,
        layerTransMap c cert x ell s j = if neg then !(x idx) else x idx) ∨
      (∃ b : Bool, ∀ x : Fin n → Bool, layerTransMap c cert x ell s j = b) := by
  by_cases h : j.val < (cert.layerOrder (ell + 1)).entries.length
  · set v : LayerVertex c (ell + 1) :=
      (FullLayerIndexing c cert (ell + 1)).symm ⟨j.val, h⟩ with hv
    cases hk : c.kind v.val with
    | literal i b =>
        exact Or.inl ⟨i, b, fun x => by
          simp only [layerTransMap, dif_pos h, ← hv, hk]⟩
    | andGate =>
        refine Or.inr ⟨layerTransMap c cert (fun _ => false) ell s j, fun x => ?_⟩
        simp only [layerTransMap, dif_pos h, ← hv, hk]
    | orGate =>
        refine Or.inr ⟨layerTransMap c cert (fun _ => false) ell s j, fun x => ?_⟩
        simp only [layerTransMap, dif_pos h, ← hv, hk]
  · exact Or.inr ⟨false, fun x => by simp only [layerTransMap, dif_neg h]⟩

/-- **One certificate-aligned layer transition is a small constant-depth `ACC`
circuit.**  For fixed configurations `s`, `t` and a fixed layer index, the
predicate `layerTransMap c cert x ell s = t` is decided by an `ACC[m]` circuit of
depth at most `2` whose size depends only on the width `w`. -/
theorem exists_acc_layerTransMap {m : Nat} (ell : Nat) (s t : Config w) :
    ∃ a : ACCCircuit n m, WellFormedACC a ∧ (∀ g, a.layer g ≤ 2) ∧
      a.gateCount ≤ 2 * w + 2 ^ w + 1 ∧
      ∀ x, ACCAccepts a x ↔ layerTransMap c cert x ell s = t :=
  exists_acc_of_slotwise (fun x => layerTransMap c cert x ell s) t
    (layerTransMap_slot_dichotomy c cert ell s)


/-- **A fixed layer letter is recognised by a small constant-depth `ACC` circuit.**
For a fixed layer index `ell` and a fixed element `t` of the width-`w` transition
monoid, the predicate `layerTrans c cert x ell = t` is decided by an `ACC[m]`
circuit of depth at most `3` whose size depends only on the width `w`.  The
circuit is the conjunction, over the `2 ^ w` configurations, of the one-step
circuits of `exists_acc_layerTransMap`. -/
theorem exists_acc_layerTrans_eq {m : Nat} (ell : Nat) (t : TransMonoid w) :
    ∃ a : ACCCircuit n m, WellFormedACC a ∧ (∀ g, a.layer g ≤ 3) ∧
      a.gateCount ≤ 2 ^ w * (2 * w + 2 ^ w + 1) + 1 ∧
      ∀ x, ACCAccepts a x ↔ layerTrans c cert x ell = t := by
  classical
  have hcard : Fintype.card (Config w) = 2 ^ w := by simp [Config]
  set e := Fintype.equivFin (Config w) with he
  choose f hwf hlay hsz hacc using fun i : Fin (Fintype.card (Config w)) =>
    exists_acc_layerTransMap c cert (m := m) ell (e.symm i) (runTrans t (e.symm i))
  have hd : ∀ (i : Fin (Fintype.card (Config w))) (a : Fin (f i).gateCount),
      (f i).layer a ≤ 2 := fun i a => hlay i a
  refine ⟨accJoin f 2 .andGate, wellFormedACC_accJoin hwf hd (by intro i b; simp) (by simp),
    accJoin_layer_le hd, ?_, fun x => ?_⟩
  · have hsum : ∑ i : Fin (Fintype.card (Config w)), (f i).gateCount
        ≤ ∑ _i : Fin (Fintype.card (Config w)), (2 * w + 2 ^ w + 1) :=
      Finset.sum_le_sum fun i _ => hsz i
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, hcard] at hsum
    have hgc : (accJoin f 2 (ACCGate.andGate : ACCGate n m)).gateCount
        = (∑ i : Fin (Fintype.card (Config w)), (f i).gateCount) + 1 := rfl
    omega
  · rw [accAccepts_accJoin_and hwf hd x]
    rw [layerTrans, transMonoid_ext_iff]
    constructor
    · intro h s
      simpa using (hacc (e s) x).mp (h (e s))
    · intro h i
      exact (hacc i x).mpr (h (e.symm i))


/-- **Slotwise dichotomy for the input configuration.**  Each slot of
`initConfig c cert x w` is either a single (possibly negated) input variable —
when the slot carries a layer-`0` literal port — or a constant. -/
theorem initConfig_slot_dichotomy (j : Fin w) :
    (∃ (idx : Fin n) (neg : Bool), ∀ x : Fin n → Bool,
        initConfig c cert x w j = if neg then !(x idx) else x idx) ∨
      (∃ b : Bool, ∀ x : Fin n → Bool, initConfig c cert x w j = b) := by
  by_cases h : j.val < (cert.layerOrder 0).entries.length
  · set v : LayerVertex c 0 := (FullLayerIndexing c cert 0).symm ⟨j.val, h⟩ with hv
    cases hk : c.kind v.val with
    | literal i b =>
        exact Or.inl ⟨i, b, fun x => by simp only [initConfig, dif_pos h, ← hv, hk]⟩
    | andGate =>
        exact Or.inr ⟨true, fun x => by simp only [initConfig, dif_pos h, ← hv, hk]⟩
    | orGate =>
        exact Or.inr ⟨false, fun x => by simp only [initConfig, dif_pos h, ← hv, hk]⟩
  · exact Or.inr ⟨false, fun x => by simp only [initConfig, dif_neg h]⟩

/-- **The input configuration is recognised by a small constant-depth `ACC`
circuit.**  For a fixed configuration `s`, the predicate `initConfig c cert x w = s`
is decided by an `ACC[m]` circuit of depth at most `2` and size at most
`2 * w + 2 ^ w + 1`. -/
theorem exists_acc_initConfig {m : Nat} (s : Config w) :
    ∃ a : ACCCircuit n m, WellFormedACC a ∧ (∀ g, a.layer g ≤ 2) ∧
      a.gateCount ≤ 2 * w + 2 ^ w + 1 ∧
      ∀ x, ACCAccepts a x ↔ initConfig c cert x w = s :=
  exists_acc_of_slotwise (fun x => initConfig c cert x w) s
    (initConfig_slot_dichotomy c cert)

end AllenderOQ3.Internal
