import AllenderOQ3.Internal.ACCLayerTrans
import AllenderOQ3.Internal.ACCLocal

/-!
# Assembling the `ACC` simulation from a word-product recogniser

The route-2 semantics of `NonCrossingSemantics` expresses acceptance of a
bounded-width ADR circuit as one slot of the product of its layer letters,
applied to the input configuration.  The input configuration is recognised by a
small constant-depth `ACC` circuit (`exists_acc_initConfig`).  This file
performs the remaining, purely mechanical assembly step: *if* for each element
of the width-`w` transition monoid the predicate "the word product of the layer
letters equals that element" is recognised by an `ACC[m]` circuit of depth `D`
and size `S`, *then* `ADRAccepts c` itself is recognised by an `ACC[m]` circuit
of depth `max D 2 + 2` and size `K * (S + (2 * w + 2 ^ w + 1) + 2) + 1`, where
`K` is the number of (configuration, transition) pairs — a constant depending
only on `w`.

This isolates exactly what is still missing for the quantitative cylindrical
`ACC` principle: a small constant-depth recogniser for the word problem of the
transition monoid, which is where the incidence (non-crossing) hypothesis and
the Barrington--Thérien argument have to be used.
-/

set_option autoImplicit false

namespace AllenderOQ3.Internal

variable {n w : Nat} (c : ADRCircuit n) (cert : IncidenceCylinder c)

/-- The word of layer letters read off the input `x`, up to the output layer. -/
noncomputable def outputWord (x : Fin n → Bool) (w : Nat) : TransMonoid w :=
  wordEnd ((List.range (c.layer c.output)).map (fun i => layerTrans c cert x i))

/-- **Assembly of the `ACC` simulation from a word-product recogniser.** -/
theorem exists_acc_adrAccepts_of_word {m D S : Nat} (hc : WellFormedADR c)
    (hW : TotalWidthAtMost c w)
    (hword : ∀ g : TransMonoid w, ∃ a : ACCCircuit n m, WellFormedACC a ∧
      (∀ q, a.layer q ≤ D) ∧ a.gateCount ≤ S ∧
      (∀ x, ACCAccepts a x ↔ outputWord c cert x w = g)) :
    ∃ a : ACCCircuit n m, WellFormedACC a ∧
      (∀ q, a.layer q ≤ max D 2 + 2) ∧
      a.gateCount ≤
        Fintype.card (Config w × TransMonoid w) * (S + (2 * w + 2 ^ w + 1) + 2) + 1 ∧
      ∀ x, ACCAccepts a x ↔ ADRAccepts c x := by
  classical
  -- the slot of the output gate inside its own layer
  set jslot : Fin w := ⟨(FullLayerIndexing c cert (c.layer c.output) ⟨c.output, rfl⟩).val,
    fullIndex_lt c cert hW (c.layer c.output) ⟨c.output, rfl⟩⟩ with hjslot
  have hj : (FullLayerIndexing c cert (c.layer c.output) ⟨c.output, rfl⟩).val = jslot.val := rfl
  set K := Fintype.card (Config w × TransMonoid w) with hK
  set e := Fintype.equivFin (Config w × TransMonoid w) with he
  set d := max D 2 with hd
  choose A hAwf hAlay hAsz hAacc using fun i : Fin K =>
    exists_acc_initConfig c cert (m := m) (e.symm i).1
  choose B hBwf hBlay hBsz hBacc using fun i : Fin K => hword (e.symm i).2
  -- the three conjuncts attached to a (configuration, transition) pair
  set blocks : (i : Fin K) → Fin 3 → ACCCircuit n m := fun i j =>
    if j.val = 0 then A i
    else if j.val = 1 then B i
    else accConst n m (runTrans (e.symm i).2 (e.symm i).1 jslot) with hblocks
  have hb0 : ∀ i, blocks i 0 = A i := by intro i; rw [hblocks]; simp
  have hb1 : ∀ i, blocks i 1 = B i := by intro i; rw [hblocks]; simp
  have hb2 : ∀ i, blocks i 2
      = accConst n m (runTrans (e.symm i).2 (e.symm i).1 jslot) := by
    intro i; rw [hblocks]; simp
  have hjcases : ∀ j : Fin 3, j = 0 ∨ j = 1 ∨ j = 2 := by
    intro j
    rcases (show j.val = 0 ∨ j.val = 1 ∨ j.val = 2 from by omega) with h | h | h
    · exact Or.inl (Fin.ext (by simp [h]))
    · exact Or.inr (Or.inl (Fin.ext (by simp [h])))
    · exact Or.inr (Or.inr (Fin.ext (by simp [h])))
  have hbwf : ∀ i j, WellFormedACC (blocks i j) := by
    intro i j
    rcases hjcases j with h | h | h <;> subst h
    · rw [hb0 i]; exact hAwf i
    · rw [hb1 i]; exact hBwf i
    · rw [hb2 i]; exact wellFormedACC_accConst n m _
  have hblay : ∀ i j (q : Fin (blocks i j).gateCount), (blocks i j).layer q ≤ d := by
    intro i j
    rcases hjcases j with h | h | h <;> subst h
    · rw [hb0 i]; exact fun q => le_trans (hAlay i q) (by omega)
    · rw [hb1 i]; exact fun q => le_trans (hBlay i q) (by omega)
    · rw [hb2 i]; intro q; rw [accConst_layer]; omega
  refine ⟨accOrAnd blocks d, wellFormedACC_accOrAnd hbwf hblay,
    accOrAnd_layer_le hblay, ?_, fun x => ?_⟩
  · -- size bound
    have hb : ∀ i : Fin K, (∑ j, (blocks i j).gateCount) + 1
        ≤ S + (2 * w + 2 ^ w + 1) + 2 := by
      intro i
      have h0 : (blocks i 0).gateCount ≤ 2 * w + 2 ^ w + 1 := by rw [hb0 i]; exact hAsz i
      have h1 : (blocks i 1).gateCount ≤ S := by rw [hb1 i]; exact hBsz i
      have h2 : (blocks i 2).gateCount = 1 := by rw [hb2 i]; exact accConst_gateCount n m _
      have hsum : ∑ j, (blocks i j).gateCount
          = (blocks i 0).gateCount + (blocks i 1).gateCount + (blocks i 2).gateCount := by
        simp [Fin.sum_univ_three]
      omega
    have hsum : ∑ i : Fin K, ((∑ j, (blocks i j).gateCount) + 1)
        ≤ ∑ _i : Fin K, (S + (2 * w + 2 ^ w + 1) + 2) :=
      Finset.sum_le_sum fun i _ => hb i
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
    have hgc : (accOrAnd blocks d).gateCount
        = (∑ i : Fin K, ((∑ j, (blocks i j).gateCount) + 1)) + 1 := rfl
    omega
  · -- semantics
    rw [accAccepts_accOrAnd hbwf hblay x,
      adrAccepts_iff_runTrans_word c cert hc hW x jslot hj]
    constructor
    · rintro ⟨i, hi⟩
      have h0 := (hAacc i x).mp (by rw [← hb0 i]; exact hi 0)
      have h1 := (hBacc i x).mp (by rw [← hb1 i]; exact hi 1)
      have h2 := (accAccepts_accConst n m _ x).mp (by rw [← hb2 i]; exact hi 2)
      rw [outputWord] at h1
      rw [h1, h0]
      exact h2
    · intro haccept
      refine ⟨e (initConfig c cert x w, outputWord c cert x w), fun j => ?_⟩
      have hsymm : e.symm (e (initConfig c cert x w, outputWord c cert x w))
          = (initConfig c cert x w, outputWord c cert x w) := e.symm_apply_apply _
      rcases hjcases j with h | h | h <;> subst h
      · rw [hb0 _]
        exact (hAacc _ x).mpr (by rw [hsymm])
      · rw [hb1 _]
        exact (hBacc _ x).mpr (by rw [hsymm])
      · rw [hb2 _]
        refine (accAccepts_accConst n m _ x).mpr ?_
        rw [hsymm]
        exact haccept

end AllenderOQ3.Internal
