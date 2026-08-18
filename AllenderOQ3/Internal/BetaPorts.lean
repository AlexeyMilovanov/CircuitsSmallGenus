import AllenderOQ3.Internal.CorePorts2
import AllenderOQ3.Internal.FaninReduce

set_option autoImplicit false

namespace AllenderOQ3.Internal

/-!
# §7.3 Beta ports for the cylindrical core

For a gate `g` of the extracted core `coreWithPorts c v o ho`, the predecessors of `g`
in the source circuit `c` split into those lying inside the core (these are exactly the
predecessors that the core circuit retains) and the *external* ones (computation gates
outside the core, and literal gates).  The **beta port** value `betaPort` of `g` is the
gate's own operation applied to the external predecessor values only.

The main result `portAugmentedADRValuation_coreWithPorts` says that any valuation of `c`
restricts to a *port-augmented* valuation of the core with these port values.  This is
exactly the semantic input consumed by the N4 refinement
(`FaninReduce.incidenceRefinement`).
-/

variable {n : Nat}

open Classical in
/-- The beta-port value of a core gate: its own operation applied to the values of its
predecessors *outside* the core. -/
noncomputable def betaPort (c : ADRCircuit n) (v o : Fin c.gateCount)
    (value : Fin c.gateCount → Bool) (g : Fin (coreSet c v o).card) : Bool :=
  match c.kind ((coreSet c v o).equivFin.symm g) with
  | .literal _ _ => false
  | .andGate =>
      decide (∀ h, h ∉ coreSet c v o → c.edge h ((coreSet c v o).equivFin.symm g) = true →
        value h = true)
  | .orGate =>
      decide (∃ h, h ∉ coreSet c v o ∧ c.edge h ((coreSet c v o).equivFin.symm g) = true ∧
        value h = true)

/-- Splitting the predecessors of a core gate into internal and external ones (AND case). -/
theorem forall_pred_split {c : ADRCircuit n} {v o : Fin c.gateCount}
    (value : Fin c.gateCount → Bool) (z : Fin c.gateCount) :
    (∀ h, c.edge h z = true → value h = true) ↔
      ((∀ h ∈ coreSet c v o, c.edge h z = true → value h = true) ∧
        (∀ h, h ∉ coreSet c v o → c.edge h z = true → value h = true)) := by
  constructor
  · intro H
    exact ⟨fun h _ he => H h he, fun h _ he => H h he⟩
  · rintro ⟨H1, H2⟩ h he
    by_cases hm : h ∈ coreSet c v o
    · exact H1 h hm he
    · exact H2 h hm he

/-- Splitting the predecessors of a core gate into internal and external ones (OR case). -/
theorem exists_pred_split {c : ADRCircuit n} {v o : Fin c.gateCount}
    (value : Fin c.gateCount → Bool) (z : Fin c.gateCount) :
    (∃ h, c.edge h z = true ∧ value h = true) ↔
      ((∃ h ∈ coreSet c v o, c.edge h z = true ∧ value h = true) ∨
        (∃ h, h ∉ coreSet c v o ∧ c.edge h z = true ∧ value h = true)) := by
  constructor
  · rintro ⟨h, he, hv⟩
    by_cases hm : h ∈ coreSet c v o
    · exact Or.inl ⟨h, hm, he, hv⟩
    · exact Or.inr ⟨h, hm, he, hv⟩
  · rintro (⟨h, -, he, hv⟩ | ⟨h, -, he, hv⟩) <;> exact ⟨h, he, hv⟩

/-- Quantifying over `Fin s.card` through `Finset.equivFin` is quantifying over `s`. -/
theorem forall_equivFin_iff {alpha : Type} (s : Finset alpha) (P : alpha → Prop) :
    (∀ i : Fin s.card, P (s.equivFin.symm i)) ↔ (∀ h ∈ s, P h) := by
  constructor
  · intro H h hh
    have := H (s.equivFin ⟨h, hh⟩)
    rwa [Equiv.symm_apply_apply] at this
  · intro H i
    exact H _ (s.equivFin.symm i).2

theorem exists_equivFin_iff {alpha : Type} (s : Finset alpha) (P : alpha → Prop) :
    (∃ i : Fin s.card, P (s.equivFin.symm i)) ↔ (∃ h ∈ s, P h) := by
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨_, (s.equivFin.symm i).2, hi⟩
  · rintro ⟨h, hh, hP⟩
    refine ⟨s.equivFin ⟨h, hh⟩, ?_⟩
    rwa [Equiv.symm_apply_apply]

/-- **§7.3 beta ports.**  Any valuation of `c` restricts, along the core embedding, to a
port-augmented valuation of the extracted core, the ports carrying the beta values. -/
theorem portAugmentedADRValuation_coreWithPorts (c : ADRCircuit n) (v o : Fin c.gateCount)
    (ho : o ∈ coreSet c v o) (x : Fin n → Bool) (value : Fin c.gateCount → Bool)
    (hval : ADRValuation c x value) :
    PortAugmentedADRValuation (coreWithPorts c v o ho) x
      (betaPort c v o value) (fun g => value ((coreSet c v o).equivFin.symm g)) := by
  classical
  intro g
  have hkind : (coreWithPorts c v o ho).kind g =
      c.kind (((coreSet c v o).equivFin.symm g) : Fin c.gateCount) := rfl
  have hbeta : betaPort c v o value g =
      match c.kind (((coreSet c v o).equivFin.symm g) : Fin c.gateCount) with
      | .literal _ _ => false
      | .andGate =>
          decide (∀ h, h ∉ coreSet c v o →
            c.edge h (((coreSet c v o).equivFin.symm g) : Fin c.gateCount) = true →
            value h = true)
      | .orGate =>
          decide (∃ h, h ∉ coreSet c v o ∧
            c.edge h (((coreSet c v o).equivFin.symm g) : Fin c.gateCount) = true ∧
            value h = true) := rfl
  have hedge : ∀ h : Fin (coreSet c v o).card,
      (coreWithPorts c v o ho).edge h g =
        c.edge (((coreSet c v o).equivFin.symm h) : Fin c.gateCount)
          (((coreSet c v o).equivFin.symm g) : Fin c.gateCount) :=
    fun h => coreWithPorts_edge c v o ho h g
  have hval_z := hval (((coreSet c v o).equivFin.symm g) : Fin c.gateCount)
  cases hk : (coreWithPorts c v o ho).kind g with
  | literal i b =>
      have hkz : c.kind (((coreSet c v o).equivFin.symm g) : Fin c.gateCount) =
          .literal i b := hkind.symm.trans hk
      rw [hkz] at hval_z
      exact hval_z
  | andGate =>
      have hkz : c.kind (((coreSet c v o).equivFin.symm g) : Fin c.gateCount) =
          .andGate := hkind.symm.trans hk
      simp only [hkz] at hval_z
      simp only [hbeta, hkz, decide_eq_true_eq]
      rw [hval_z, forall_pred_split (v := v) (o := o) value]
      constructor
      · rintro ⟨H1, H2⟩
        refine ⟨?_, H2⟩
        intro h hh
        rw [hedge h] at hh
        exact H1 _ ((coreSet c v o).equivFin.symm h).2 hh
      · rintro ⟨H1, H2⟩
        refine ⟨?_, H2⟩
        intro h hh he
        have := H1 ((coreSet c v o).equivFin ⟨h, hh⟩)
        rw [hedge, Equiv.symm_apply_apply] at this
        exact this he
  | orGate =>
      have hkz : c.kind (((coreSet c v o).equivFin.symm g) : Fin c.gateCount) =
          .orGate := hkind.symm.trans hk
      simp only [hkz] at hval_z
      simp only [hbeta, hkz, decide_eq_true_eq]
      rw [hval_z, exists_pred_split (v := v) (o := o) value]
      constructor
      · rintro (⟨h, hh, he, hv⟩ | H2)
        · refine Or.inl ⟨(coreSet c v o).equivFin ⟨h, hh⟩, ?_⟩
          rw [hedge, Equiv.symm_apply_apply]
          exact ⟨he, hv⟩
        · exact Or.inr H2
      · rintro (⟨h, he, hv⟩ | H2)
        · rw [hedge h] at he
          exact Or.inl ⟨_, ((coreSet c v o).equivFin.symm h).2, he, hv⟩
        · exact Or.inr H2

end AllenderOQ3.Internal
