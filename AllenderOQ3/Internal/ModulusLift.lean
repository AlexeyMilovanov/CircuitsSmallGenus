import AllenderOQ3.Internal.ACCBuild

set_option autoImplicit false
namespace AllenderOQ3.Internal

variable {n m M : Nat}

/-!
# Common-modulus lifting

Given a `MOD_m` circuit `c` and a multiple `M` of `m`, we build a `MOD_M` circuit on the
same inputs.  Writing `k = M / m` (clamped to be at least `1`), every gate `g` of `c` is
replaced by `k` copies: the *principal* copy `(g, 0)`, which carries the kind of `g`, and
`k - 1` *duplicate* copies `(g, t)` (`t ≠ 0`), each a one-input `orGate` fed by the
principal copy, hence carrying the same value.

A `MOD_m` gate of `c` becomes a `MOD_M` gate fed by **all** `k` copies of each of its
inputs, so the number of true inputs is multiplied by `k`; since `M = m * k`, the residue
condition `k * N ≡ 0 (mod m * k)` is equivalent to `N ≡ 0 (mod m)` when `k > 0`.
All other gates are fed only by principal copies.

Layers are doubled: the principal copy of `g` sits on layer `2 * c.layer g` and its
duplicates on layer `2 * c.layer g + 1`, which keeps literals on layer `0` and leaves
room for the duplication cascade.
-/

/-- The number of copies of each gate used by the modulus lift (at least one). -/
def modulusCopies (m M : Nat) : Nat := max (M / m) 1

theorem modulusCopies_pos (m M : Nat) : 0 < modulusCopies m M := by
  simp [modulusCopies]

theorem modulusCopies_le (m M : Nat) : modulusCopies m M ≤ M + 2 := by
  have := Nat.div_le_self M m
  simp only [modulusCopies]
  omega

/-- The index of the principal copy of a gate. -/
def modZero (m M : Nat) : Fin (modulusCopies m M) := ⟨0, modulusCopies_pos m M⟩

/-- Reinterpret a gate over modulus `m` as the corresponding gate over modulus `M`. -/
def liftGate (g : ACCGate n m) : ACCGate n M :=
  match g with
  | .literal j b => .literal j b
  | .andGate => .andGate
  | .orGate => .orGate
  | .notGate => .notGate
  | .modGate => .modGate

theorem liftGate_eq_literal_iff {g : ACCGate n m} {j : Fin n} {b : Bool} :
    (liftGate g : ACCGate n M) = .literal j b ↔ g = .literal j b := by
  cases g <;> simp [liftGate]

theorem liftGate_eq_notGate_iff {g : ACCGate n m} :
    (liftGate g : ACCGate n M) = .notGate ↔ g = .notGate := by
  cases g <;> simp [liftGate]

theorem liftGate_eq_modGate_iff {g : ACCGate n m} :
    (liftGate g : ACCGate n M) = .modGate ↔ g = .modGate := by
  cases g <;> simp [liftGate]

theorem liftGate_orGate_ne_notGate : (ACCGate.orGate : ACCGate n M) ≠ .notGate := by simp

/-- The edge relation of the modulus lift, in terms of gate/copy pairs. -/
def modLiftEdge (c : ACCCircuit n m) (u v : Fin c.gateCount)
    (s t : Fin (modulusCopies m M)) : Bool :=
  if t = modZero m M then
    (match c.kind v with
      | .modGate => c.edge u v
      | _ => c.edge u v && decide (s = modZero m M))
  else decide (u = v) && decide (s = modZero m M)

theorem modLiftEdge_eq_true_iff (c : ACCCircuit n m) (u v : Fin c.gateCount)
    (s t : Fin (modulusCopies m M)) :
    modLiftEdge c u v s t = true ↔
      (t = modZero m M ∧ c.edge u v = true ∧ (c.kind v = .modGate ∨ s = modZero m M)) ∨
        (t ≠ modZero m M ∧ u = v ∧ s = modZero m M) := by
  unfold modLiftEdge
  by_cases ht : t = modZero m M
  · subst ht
    simp only [ne_eq, not_true_eq_false, false_and, or_false, true_and]
    cases c.kind v <;> simp
  · simp [ht]

/-- Common-modulus lifting: converts a `MOD_m` circuit to a `MOD_M` circuit where `M` is a
multiple of `m`. -/
-- The divisibility hypothesis `_hM` is part of the intended interface of the
-- lift, but the data of the lifted circuit does not depend on it.
def accModulusLift (c : ACCCircuit n m) (_hM : m ∣ M) : ACCCircuit n M where
  gateCount := c.gateCount * modulusCopies m M
  output := finProdFinEquiv (c.output, modZero m M)
  kind := fun G =>
    if (finProdFinEquiv.symm G).2 = modZero m M then
      liftGate (c.kind (finProdFinEquiv.symm G).1)
    else .orGate
  layer := fun G =>
    2 * c.layer (finProdFinEquiv.symm G).1 +
      (if (finProdFinEquiv.symm G).2 = modZero m M then 0 else 1)
  edge := fun U V =>
    modLiftEdge c (finProdFinEquiv.symm U).1 (finProdFinEquiv.symm V).1
      (finProdFinEquiv.symm U).2 (finProdFinEquiv.symm V).2

@[simp] theorem accModulusLift_gateCount (c : ACCCircuit n m) (hM : m ∣ M) :
    (accModulusLift c hM).gateCount = c.gateCount * modulusCopies m M := rfl

@[simp] theorem accModulusLift_output (c : ACCCircuit n m) (hM : m ∣ M) :
    (accModulusLift c hM).output = finProdFinEquiv (c.output, modZero m M) := rfl

@[simp] theorem accModulusLift_kind (c : ACCCircuit n m) (hM : m ∣ M)
    (g : Fin c.gateCount) (t : Fin (modulusCopies m M)) :
    (accModulusLift c hM).kind (finProdFinEquiv (g, t)) =
      if t = modZero m M then liftGate (c.kind g) else .orGate := by
  simp only [accModulusLift, Equiv.symm_apply_apply]

@[simp] theorem accModulusLift_layer (c : ACCCircuit n m) (hM : m ∣ M)
    (g : Fin c.gateCount) (t : Fin (modulusCopies m M)) :
    (accModulusLift c hM).layer (finProdFinEquiv (g, t)) =
      2 * c.layer g + (if t = modZero m M then 0 else 1) := by
  simp only [accModulusLift, Equiv.symm_apply_apply]

@[simp] theorem accModulusLift_edge (c : ACCCircuit n m) (hM : m ∣ M)
    (u v : Fin c.gateCount) (s t : Fin (modulusCopies m M)) :
    (accModulusLift c hM).edge (finProdFinEquiv (u, s)) (finProdFinEquiv (v, t)) =
      modLiftEdge c u v s t := by
  simp only [accModulusLift, Equiv.symm_apply_apply]

/-- Every gate index of the lifted circuit is a gate/copy pair. -/
theorem exists_prod_repr (c : ACCCircuit n m) (hM : m ∣ M)
    (G : Fin (accModulusLift c hM).gateCount) :
    ∃ (g : Fin c.gateCount) (t : Fin (modulusCopies m M)), G = finProdFinEquiv (g, t) :=
  ⟨(finProdFinEquiv.symm G).1, (finProdFinEquiv.symm G).2, by
    rw [Prod.mk.eta, Equiv.apply_symm_apply]⟩

/-- The lifted circuit preserves well-formedness. -/
theorem wellFormedACC_accModulusLift (c : ACCCircuit n m) (hM : m ∣ M)
    (hc : WellFormedACC c) : WellFormedACC (accModulusLift c hM) := by
  obtain ⟨hc1, hc2, hc3⟩ := hc
  refine ⟨?_, ?_, ?_⟩
  · intro U V hUV
    obtain ⟨u, s, rfl⟩ := exists_prod_repr c hM U
    obtain ⟨v, t, rfl⟩ := exists_prod_repr c hM V
    rw [accModulusLift_edge, modLiftEdge_eq_true_iff] at hUV
    rw [accModulusLift_layer, accModulusLift_layer]
    rcases hUV with ⟨ht, he, _⟩ | ⟨ht, rfl, hs⟩
    · have := hc1 u v he
      rw [if_pos ht]
      split <;> omega
    · rw [if_pos hs, if_neg ht]
      omega
  · intro G
    obtain ⟨g, t, rfl⟩ := exists_prod_repr c hM G
    rw [accModulusLift_layer, accModulusLift_kind]
    by_cases ht : t = modZero m M
    · rw [if_pos ht, if_pos ht]
      constructor
      · intro h0
        obtain ⟨j, b, hj⟩ := (hc2 g).mp (by omega)
        exact ⟨j, b, by rw [hj]; rfl⟩
      · rintro ⟨j, b, hj⟩
        have := (hc2 g).mpr ⟨j, b, liftGate_eq_literal_iff.mp hj⟩
        omega
    · rw [if_neg ht, if_neg ht]
      constructor
      · intro h0; omega
      · rintro ⟨j, b, hj⟩
        exact absurd hj (by simp)
  · intro G hG
    obtain ⟨g, t, rfl⟩ := exists_prod_repr c hM G
    rw [accModulusLift_kind] at hG
    by_cases ht : t = modZero m M
    · rw [if_pos ht] at hG
      have hkg : c.kind g = .notGate := liftGate_eq_notGate_iff.mp hG
      obtain ⟨h, hh, huniq⟩ := hc3 g hkg
      refine ⟨finProdFinEquiv (h, modZero m M), ?_, ?_⟩
      · have he : (accModulusLift c hM).edge (finProdFinEquiv (h, modZero m M))
            (finProdFinEquiv (g, t)) = true := by
          rw [accModulusLift_edge, modLiftEdge_eq_true_iff]
          exact Or.inl ⟨ht, hh, Or.inr rfl⟩
        exact he
      · intro U hU
        obtain ⟨u, s, rfl⟩ := exists_prod_repr c hM U
        have hU' : (accModulusLift c hM).edge (finProdFinEquiv (u, s))
            (finProdFinEquiv (g, t)) = true := hU
        rw [accModulusLift_edge, modLiftEdge_eq_true_iff] at hU'
        rcases hU' with ⟨_, he, hmod⟩ | ⟨ht', _, _⟩
        · have hs : s = modZero m M := by
            rcases hmod with hmod | hs
            · rw [hkg] at hmod; exact absurd hmod (by simp)
            · exact hs
          rw [huniq u he, hs]
        · exact absurd ht ht'
    · rw [if_neg ht] at hG
      exact absurd hG (by simp)

/-- Layer doubling keeps the strict ACC layering constraints while providing space for the
multiplicity gadgets and OR cascades. Literals stay at layer 0. -/
theorem accModulusLift_layer_le {c : ACCCircuit n m} {hM : m ∣ M} {d : Nat}
    (hc : ∀ g, c.layer g ≤ d) : ∀ g, (accModulusLift c hM).layer g ≤ 2 * d + 2 := by
  intro G
  obtain ⟨g, t, rfl⟩ := exists_prod_repr c hM G
  rw [accModulusLift_layer]
  have := hc g
  split <;> omega

/-- The size of the lifted circuit is bounded by a constant factor depending only on M. -/
theorem accModulusLift_gateCount_le (c : ACCCircuit n m) (hM : m ∣ M) :
    (accModulusLift c hM).gateCount ≤ (M + 2) * c.gateCount := by
  rw [accModulusLift_gateCount, Nat.mul_comm (M + 2) c.gateCount]
  exact Nat.mul_le_mul_left _ (modulusCopies_le m M)

/-- For a positive modulus the number of copies is exactly `M / m`, so `m * k = M`. -/
theorem modulusCopies_mul (hM : m ∣ M) (hMpos : 0 < M) : m * modulusCopies m M = M := by
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · rw [Nat.zero_dvd] at hM; omega
    · exact h
  have hle : m ≤ M := Nat.le_of_dvd hMpos hM
  have h1 : 1 ≤ M / m := (Nat.one_le_div_iff hm).mpr hle
  have hk : modulusCopies m M = M / m := by simp only [modulusCopies]; omega
  rw [hk, Nat.mul_div_cancel' hM]

/-- Multiplying a count by the number of copies turns divisibility by `M` into
divisibility by `m`. -/
theorem card_mul_copies_mod_iff (hM : m ∣ M) (hMpos : 0 < M) (N : Nat) :
    N * modulusCopies m M % M = 0 ↔ N % m = 0 := by
  have hk : 0 < modulusCopies m M := modulusCopies_pos m M
  have hMk : m * modulusCopies m M = M := modulusCopies_mul hM hMpos
  have h1 : N * modulusCopies m M % (m * modulusCopies m M) = N % m * modulusCopies m M :=
    Nat.mul_mod_mul_right _ _ _
  rw [hMk] at h1
  rw [h1]
  simp [hk.ne']

/-- The value carried by the copies of a gate: every copy carries the value of the gate. -/
def modLiftValue (c : ACCCircuit n m) (hM : m ∣ M) (vc : Fin c.gateCount → Bool) :
    Fin (accModulusLift c hM).gateCount → Bool :=
  fun G => vc (finProdFinEquiv.symm G).1

@[simp] theorem modLiftValue_apply (c : ACCCircuit n m) (hM : m ∣ M)
    (vc : Fin c.gateCount → Bool) (g : Fin c.gateCount) (t : Fin (modulusCopies m M)) :
    modLiftValue c hM vc (finProdFinEquiv (g, t)) = vc g := by
  simp only [modLiftValue, Equiv.symm_apply_apply]

/-- A `MOD_M` gate of the lift sees each true input of the original `MOD_m` gate exactly
`modulusCopies m M` times. -/
theorem accModulusLift_card_modGate {c : ACCCircuit n m} (hM : m ∣ M)
    {v : Fin c.gateCount} (hkv : c.kind v = .modGate) (vc : Fin c.gateCount → Bool) :
    (Finset.univ.filter (fun H : Fin (accModulusLift c hM).gateCount =>
        (accModulusLift c hM).edge H (finProdFinEquiv (v, modZero m M)) = true ∧
          modLiftValue c hM vc H = true)).card
      = (Finset.univ.filter (fun h : Fin c.gateCount =>
          c.edge h v = true ∧ vc h = true)).card * modulusCopies m M := by
  classical
  have hprod : ((Finset.univ.filter (fun h : Fin c.gateCount => c.edge h v = true ∧ vc h = true))
      ×ˢ (Finset.univ : Finset (Fin (modulusCopies m M)))).card
      = (Finset.univ.filter (fun h : Fin c.gateCount => c.edge h v = true ∧ vc h = true)).card
        * modulusCopies m M := by
    rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
  rw [← hprod]
  refine (Finset.card_bij (fun q _ => finProdFinEquiv q) ?_ ?_ ?_).symm
  · rintro ⟨u, s⟩ hq
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    refine ⟨?_, ?_⟩
    · rw [accModulusLift_edge, modLiftEdge_eq_true_iff]
      exact Or.inl ⟨rfl, hq.1.1, Or.inl hkv⟩
    · rw [modLiftValue_apply]
      exact hq.1.2
  · rintro ⟨u₁, s₁⟩ _ ⟨u₂, s₂⟩ _ hEq
    exact finProdFinEquiv.injective hEq
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    obtain ⟨u, s, rfl⟩ := exists_prod_repr c hM y
    rw [accModulusLift_edge, modLiftEdge_eq_true_iff] at hy
    rw [modLiftValue_apply] at hy
    rcases hy.1 with ⟨_, he, _⟩ | ⟨ht, _, _⟩
    · refine ⟨(u, s), ?_, rfl⟩
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
      exact ⟨he, hy.2⟩
    · exact absurd rfl ht

/-- Gluing: the copied valuation is a valuation of the lifted circuit, provided the new
modulus is positive (so that `m * modulusCopies m M = M`). -/
theorem accValuation_accModulusLift {c : ACCCircuit n m} (hM : m ∣ M) (hMpos : 0 < M)
    {x : Fin n → Bool} {vc : Fin c.gateCount → Bool} (hvc : ACCValuation c x vc) :
    ACCValuation (accModulusLift c hM) x (modLiftValue c hM vc) := by
  intro G
  obtain ⟨g, t, rfl⟩ := exists_prod_repr c hM G
  rw [accModulusLift_kind]
  by_cases ht : t = modZero m M
  · subst ht
    have hg := hvc g
    rw [if_pos rfl]
    cases hk : c.kind g with
    | literal j b =>
        simp only [hk] at hg
        simp only [liftGate, modLiftValue_apply]
        exact hg
    | andGate =>
        simp only [hk] at hg
        simp only [liftGate, modLiftValue_apply]
        rw [hg]
        constructor
        · intro H U hU
          obtain ⟨u, s, rfl⟩ := exists_prod_repr c hM U
          rw [accModulusLift_edge, modLiftEdge_eq_true_iff] at hU
          rcases hU with ⟨_, he, _⟩ | ⟨ht', _, _⟩
          · rw [modLiftValue_apply]; exact H u he
          · exact absurd rfl ht'
        · intro H u he
          have := H (finProdFinEquiv (u, modZero m M)) (by
            rw [accModulusLift_edge, modLiftEdge_eq_true_iff]
            exact Or.inl ⟨rfl, he, Or.inr rfl⟩)
          rwa [modLiftValue_apply] at this
    | orGate =>
        simp only [hk] at hg
        simp only [liftGate, modLiftValue_apply]
        rw [hg]
        constructor
        · rintro ⟨u, he, hv⟩
          refine ⟨finProdFinEquiv (u, modZero m M), ?_, ?_⟩
          · rw [accModulusLift_edge, modLiftEdge_eq_true_iff]
            exact Or.inl ⟨rfl, he, Or.inr rfl⟩
          · rwa [modLiftValue_apply]
        · rintro ⟨U, hU, hUv⟩
          obtain ⟨u, s, rfl⟩ := exists_prod_repr c hM U
          rw [accModulusLift_edge, modLiftEdge_eq_true_iff] at hU
          rcases hU with ⟨_, he, _⟩ | ⟨ht', _, _⟩
          · exact ⟨u, he, by rwa [modLiftValue_apply] at hUv⟩
          · exact absurd rfl ht'
    | notGate =>
        simp only [hk] at hg
        simp only [liftGate, modLiftValue_apply]
        rw [hg]
        constructor
        · rintro ⟨u, he, hv⟩
          refine ⟨finProdFinEquiv (u, modZero m M), ?_, ?_⟩
          · rw [accModulusLift_edge, modLiftEdge_eq_true_iff]
            exact Or.inl ⟨rfl, he, Or.inr rfl⟩
          · rwa [modLiftValue_apply]
        · rintro ⟨U, hU, hUv⟩
          obtain ⟨u, s, rfl⟩ := exists_prod_repr c hM U
          rw [accModulusLift_edge, modLiftEdge_eq_true_iff] at hU
          rcases hU with ⟨_, he, _⟩ | ⟨ht', _, _⟩
          · exact ⟨u, he, by rwa [modLiftValue_apply] at hUv⟩
          · exact absurd rfl ht'
    | modGate =>
        simp only [hk] at hg
        simp only [liftGate, modLiftValue_apply]
        rw [hg, accModulusLift_card_modGate hM hk vc, card_mul_copies_mod_iff hM hMpos]
  · rw [if_neg ht]
    simp only [modLiftValue_apply]
    constructor
    · intro hv
      refine ⟨finProdFinEquiv (g, modZero m M), ?_, ?_⟩
      · rw [accModulusLift_edge, modLiftEdge_eq_true_iff]
        exact Or.inr ⟨ht, rfl, rfl⟩
      · rw [modLiftValue_apply]; exact hv
    · rintro ⟨U, hU, hUv⟩
      obtain ⟨u, s, rfl⟩ := exists_prod_repr c hM U
      rw [accModulusLift_edge, modLiftEdge_eq_true_iff] at hU
      rcases hU with ⟨ht', _, _⟩ | ⟨_, rfl, _⟩
      · exact absurd ht' ht
      · rwa [modLiftValue_apply] at hUv

/-- Semantics of modulus lifting for a positive target modulus: the lifted circuit accepts
exactly the same inputs as the original one. -/
theorem evalACC_accModulusLift_of_pos {c : ACCCircuit n m} {hM : m ∣ M} (hMpos : 0 < M)
    (hc : WellFormedACC c) (x : Fin n → Bool) :
    ACCAccepts (accModulusLift c hM) x ↔ ACCAccepts c x := by
  have hvc : ACCValuation c x (evalACC c hc x) := (accValuation_iff_eq_evalACC hc).mpr rfl
  have hV := accValuation_accModulusLift hM hMpos hvc
  constructor
  · rintro ⟨w, hw, hout⟩
    have hwe := accValuation_unique (wellFormedACC_accModulusLift c hM hc) hw hV
    rw [hwe, accModulusLift_output, modLiftValue_apply] at hout
    exact ⟨_, hvc, hout⟩
  · rintro ⟨w, hw, hout⟩
    have hwe : w = evalACC c hc x := (accValuation_iff_eq_evalACC hc).mp hw
    refine ⟨_, hV, ?_⟩
    rw [accModulusLift_output, modLiftValue_apply, ← hwe]
    exact hout

/-!
### The unrestricted statement is false

The lemma originally stated here,

```text
theorem evalACC_accModulusLift {c : ACCCircuit n m} {hM : m ∣ M} (hc : WellFormedACC c)
    (x : Fin n → Bool) :
    ACCAccepts (accModulusLift c hM) x ↔ ACCAccepts c x
```

is **false**, and is therefore commented out below instead of being carried as an
open obligation.  The hypothesis `m ∣ M` also admits the degenerate target modulus
`M = 0`; then `modulusCopies m 0 = 1`, so the lift is the original circuit with each
`MOD_m` gate reinterpreted as a `MOD_0` gate, i.e. as a `NOR` gate.  For `m = 2` and a
`MOD_2` gate with two true inputs the two circuits disagree.  This is made precise by
`accModulusLift_counterexample` below.

The usable form of the statement, with the hypothesis `0 < M` that the construction
actually needs, is `evalACC_accModulusLift_of_pos` above, and it is fully proved.  The
false version was never used anywhere in this development.

```text
/-- Semantics of modulus lifting: the valuation of the lifted circuit computes exactly the
same output as the original circuit. -/
theorem evalACC_accModulusLift {c : ACCCircuit n m} {hM : m ∣ M} (hc : WellFormedACC c)
    (x : Fin n → Bool) :
    ACCAccepts (accModulusLift c hM) x ↔ ACCAccepts c x := ...
```
-/

/-- Deciding one clause of `ACCValuation`. -/
def accValuationDecidable {n m : Nat} (c : ACCCircuit n m) (x : Fin n → Bool)
    (value : Fin c.gateCount → Bool) : Decidable (ACCValuation c x value) := by
  unfold ACCValuation
  have hp : DecidablePred (fun g : Fin c.gateCount => match c.kind g with
      | .literal i negated => value g = if negated then !(x i) else x i
      | .andGate => (value g = true ↔ ∀ h, c.edge h g = true → value h = true)
      | .orGate => (value g = true ↔ ∃ h, c.edge h g = true ∧ value h = true)
      | .notGate => (value g = true ↔ ∃ h, c.edge h g = true ∧ value h = false)
      | .modGate => (value g = true ↔
          (Finset.univ.filter (fun h => c.edge h g = true ∧ value h = true)).card % m = 0)) := by
    intro g
    dsimp only
    cases c.kind g <;> exact inferInstance
  exact @Fintype.decidableForallFintype _ _ hp _

attribute [local instance] accValuationDecidable

/-- Acceptance of a concrete ACC circuit is decidable. -/
def accAcceptsDecidable {n m : Nat} (c : ACCCircuit n m) (x : Fin n → Bool) :
    Decidable (ACCAccepts c x) := by
  unfold ACCAccepts
  exact Fintype.decidableExistsFintype

attribute [local instance] accAcceptsDecidable

/-- A three-gate `MOD_2` circuit on one input: two copies of the literal `x 0` feeding a
`MOD_2` gate.  On the all-true input the `MOD_2` gate sees two true inputs, so it fires. -/
def modLiftCounterexampleCircuit : ACCCircuit 1 2 where
  gateCount := 3
  output := 2
  kind := fun g => if g.val = 2 then .modGate else .literal 0 false
  layer := fun g => if g.val = 2 then 1 else 0
  edge := fun u v => decide (v.val = 2 ∧ u.val ≠ 2)

theorem wellFormedACC_modLiftCounterexampleCircuit :
    WellFormedACC modLiftCounterexampleCircuit := by
  refine ⟨by decide, by decide, ?_⟩
  intro g hg
  fin_cases g <;> simp [modLiftCounterexampleCircuit] at hg

/-- The modulus lift does **not** preserve acceptance for the degenerate modulus `M = 0`:
the displayed circuit accepts the all-true input, while its lift to modulus `0` rejects it.
This is why `evalACC_accModulusLift_of_pos` carries the hypothesis `0 < M`. -/
theorem accModulusLift_counterexample :
    ¬ (∀ (n m M : Nat) (c : ACCCircuit n m) (hM : m ∣ M), WellFormedACC c →
        ∀ x : Fin n → Bool, ACCAccepts (accModulusLift c hM) x ↔ ACCAccepts c x) := by
  intro h
  have hacc : ACCAccepts modLiftCounterexampleCircuit (fun _ => true) := by decide
  have hlift := (h 1 2 0 modLiftCounterexampleCircuit ⟨0, rfl⟩
    wellFormedACC_modLiftCounterexampleCircuit (fun _ => true)).mpr hacc
  revert hlift
  decide

end AllenderOQ3.Internal
