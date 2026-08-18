import AllenderOQ3.Internal.ACCJoin
import AllenderOQ3.Internal.StateRelation
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi

/-!
# Two-relation ACC composition (B3a, the `B = 2` case of the §9 round)

`accComposeTwo R R' d` composes two `State`-indexed families of `ACC[M]`
relations into a single family via the depth-two `OR`-of-`AND` operator
`AllenderOQ3.Internal.accOrAnd`: it ORs over the `q = 2 ^ w` middle states `t`
of the `AND` of the two entry circuits.  Its acceptance is exactly the
one-intermediate-state composition `∃ t, R s t ∧ R' t u`, it adds depth `2`, and
the modulus is unchanged.

This is the `B = 2` special case of the §9 blocking round.  The full §9 round
that matches `polylogCompose_collapse` (round map `m ↦ ⌈m / B⌉`, `k + 1` rounds,
constant added depth) composes `B` relations at once inside one `accOrAnd` over
`(B - 1)`-tuples of intermediate states; see `accComposeMany` below for that
`B`-ary generalisation.
-/

set_option autoImplicit false

namespace AllenderOQ3.Internal

variable {n M : Nat} {w : Nat}

instance : Fintype (State w) :=
  show Fintype (Fin w → Bool) by infer_instance

/-- Compose two `State`-indexed `ACC[M]` relation families into one, over the
`q = 2 ^ w` middle states, with the depth-two `OR`-of-`AND` operator. -/
noncomputable def accComposeTwo
    (R R' : State w → State w → ACCCircuit n M) (d : Nat)
    (s u : State w) : ACCCircuit n M :=
  accOrAnd (fun (i : Fin (Fintype.card (State w))) =>
    ![R s ((Fintype.equivFin (State w)).symm i),
      R' ((Fintype.equivFin (State w)).symm i) u]) d

theorem wellFormedACC_accComposeTwo
    (R R' : State w → State w → ACCCircuit n M) (d : Nat)
    (hR : ∀ s t, WellFormedACC (R s t)) (hR' : ∀ t u, WellFormedACC (R' t u))
    (hdR : ∀ s t g, (R s t).layer g ≤ d) (hdR' : ∀ t u g, (R' t u).layer g ≤ d)
    (s u : State w) :
    WellFormedACC (accComposeTwo R R' d s u) := by
  apply wellFormedACC_accOrAnd
  · intro i j
    fin_cases j
    · exact hR s _
    · exact hR' _ u
  · intro i j
    fin_cases j
    · exact hdR s _
    · exact hdR' _ u

theorem accComposeTwo_layer_le
    (R R' : State w → State w → ACCCircuit n M) (d : Nat)
    (hdR : ∀ s t g, (R s t).layer g ≤ d) (hdR' : ∀ t u g, (R' t u).layer g ≤ d)
    (s u : State w) (g : Fin (accComposeTwo R R' d s u).gateCount) :
    (accComposeTwo R R' d s u).layer g ≤ d + 2 := by
  apply accOrAnd_layer_le
  intro i j
  fin_cases j
  · exact hdR s _
  · exact hdR' _ u

theorem accAccepts_accComposeTwo
    (R R' : State w → State w → ACCCircuit n M) (d : Nat)
    (hR : ∀ s t, WellFormedACC (R s t)) (hR' : ∀ t u, WellFormedACC (R' t u))
    (hdR : ∀ s t g, (R s t).layer g ≤ d) (hdR' : ∀ t u g, (R' t u).layer g ≤ d)
    (s u : State w) (x : Fin n → Bool) :
    ACCAccepts (accComposeTwo R R' d s u) x ↔
      ∃ t, ACCAccepts (R s t) x ∧ ACCAccepts (R' t u) x := by
  rw [accComposeTwo, accAccepts_accOrAnd]
  · constructor
    · rintro ⟨i, hi⟩
      exact ⟨(Fintype.equivFin (State w)).symm i, hi 0, hi 1⟩
    · rintro ⟨t, ht, ht'⟩
      refine ⟨Fintype.equivFin (State w) t, fun j => ?_⟩
      fin_cases j
      · simpa [Equiv.symm_apply_apply] using ht
      · simpa [Equiv.symm_apply_apply] using ht'
  · intro i j
    fin_cases j
    · exact hR s _
    · exact hR' _ u
  · intro i j
    fin_cases j
    · exact hdR s _
    · exact hdR' _ u

/-- The exact gate count of the two-relation composition: one middle gate per
state, an `AND` root per state, and one final `OR` root. -/
theorem accComposeTwo_gateCount
    (R R' : State w → State w → ACCCircuit n M) (d : Nat)
    (s u : State w) :
    (accComposeTwo R R' d s u).gateCount =
      (∑ i : Fin (Fintype.card (State w)),
        ((R s ((Fintype.equivFin (State w)).symm i)).gateCount +
          (R' ((Fintype.equivFin (State w)).symm i) u).gateCount + 1)) + 1 := by
  rw [accComposeTwo, accOrAnd_gateCount]
  refine congrArg (· + 1) (Finset.sum_congr rfl (fun i _ => ?_))
  refine congrArg (· + 1) ?_
  rw [Fin.sum_univ_two]
  simp

/-! ## The `B`-ary §9 round -/

section Many

variable {B : Nat}

instance : DecidableEq (State w) :=
  show DecidableEq (Fin w → Bool) by infer_instance

/-- Normalise a candidate path `q : Fin (B+1) → State w` so that it starts at
`s` and ends at `u`.  ORing over all `q` of the conjunction of the `B` steps of
`accComposePath` is therefore exactly an OR over all `s`-to-`u` paths. -/
def accComposePath (B : Nat) (s u : State w) (q : Fin (B + 1) → State w) :
    Fin (B + 1) → State w :=
  fun j => if j = 0 then s else if j = Fin.last B then u else q j

@[simp] theorem accComposePath_zero (B : Nat) (s u : State w)
    (q : Fin (B + 1) → State w) : accComposePath B s u q 0 = s := by
  simp [accComposePath]

theorem accComposePath_last (hB : 1 ≤ B) (s u : State w)
    (q : Fin (B + 1) → State w) : accComposePath B s u q (Fin.last B) = u := by
  have h : (Fin.last B : Fin (B + 1)) ≠ 0 := by
    simp only [ne_eq, Fin.ext_iff, Fin.val_last, Fin.val_zero]
    omega
  simp [accComposePath, h]

/-- A path that already starts at `s` and ends at `u` is a fixed point of the
normalisation. -/
theorem accComposePath_eq_self (B : Nat) (s u : State w)
    {p : Fin (B + 1) → State w} (h0 : p 0 = s) (hl : p (Fin.last B) = u) :
    accComposePath B s u p = p := by
  funext j
  unfold accComposePath
  split_ifs with h1 h2
  · rw [h1, h0]
  · rw [h2, hl]
  · rfl

/-- The `B`-ary §9 composition round: one depth-two `OR`-of-`AND` over all
candidate intermediate-state paths, whose `j`-th conjunct is the `j`-th
relation applied to the `j`-th step of the (normalised) path. -/
noncomputable def accComposeMany (B : Nat)
    (R : Fin B → State w → State w → ACCCircuit n M) (d : Nat)
    (s u : State w) : ACCCircuit n M :=
  accOrAnd (fun (i : Fin (Fintype.card (Fin (B + 1) → State w))) (j : Fin B) =>
    R j (accComposePath B s u ((Fintype.equivFin (Fin (B + 1) → State w)).symm i) j.castSucc)
      (accComposePath B s u ((Fintype.equivFin (Fin (B + 1) → State w)).symm i) j.succ)) d

theorem wellFormedACC_accComposeMany (B : Nat)
    (R : Fin B → State w → State w → ACCCircuit n M) (d : Nat)
    (hR : ∀ j s t, WellFormedACC (R j s t))
    (hdR : ∀ j s t g, (R j s t).layer g ≤ d) (s u : State w) :
    WellFormedACC (accComposeMany B R d s u) :=
  wellFormedACC_accOrAnd (fun _ j => hR j _ _) (fun _ j => hdR j _ _)

theorem accComposeMany_layer_le (B : Nat)
    (R : Fin B → State w → State w → ACCCircuit n M) (d : Nat)
    (hdR : ∀ j s t g, (R j s t).layer g ≤ d) (s u : State w)
    (g : Fin (accComposeMany B R d s u).gateCount) :
    (accComposeMany B R d s u).layer g ≤ d + 2 :=
  accOrAnd_layer_le (fun _ j => hdR j _ _) g

/-- Acceptance of the `B`-ary round is exactly the existence of an `s`-to-`u`
path of intermediate states all of whose `B` steps are accepted. -/
theorem accAccepts_accComposeMany (B : Nat) (hB : 2 ≤ B)
    (R : Fin B → State w → State w → ACCCircuit n M) (d : Nat)
    (hR : ∀ j s t, WellFormedACC (R j s t))
    (hdR : ∀ j s t g, (R j s t).layer g ≤ d)
    (s u : State w) (x : Fin n → Bool) :
    ACCAccepts (accComposeMany B R d s u) x ↔
      ∃ p : Fin (B + 1) → State w, p 0 = s ∧ p (Fin.last B) = u ∧
        ∀ j : Fin B, ACCAccepts (R j (p j.castSucc) (p j.succ)) x := by
  have hB1 : 1 ≤ B := le_trans (by norm_num) hB
  rw [accComposeMany, accAccepts_accOrAnd (fun _ j => hR j _ _) (fun _ j => hdR j _ _)]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨accComposePath B s u ((Fintype.equivFin (Fin (B + 1) → State w)).symm i),
      accComposePath_zero B s u _, accComposePath_last hB1 s u _, hi⟩
  · rintro ⟨p, h0, hl, hp⟩
    refine ⟨Fintype.equivFin (Fin (B + 1) → State w) p, fun j => ?_⟩
    rw [Equiv.symm_apply_apply, accComposePath_eq_self B s u h0 hl]
    exact hp j

/-- The exact gate count of the `B`-ary round: the `B` step circuits plus one
`AND` root per candidate path, plus one final `OR` root. -/
theorem accComposeMany_gateCount (B : Nat)
    (R : Fin B → State w → State w → ACCCircuit n M) (d : Nat)
    (s u : State w) :
    (accComposeMany B R d s u).gateCount =
      (∑ i : Fin (Fintype.card (Fin (B + 1) → State w)),
        ((∑ j : Fin B,
          (R j (accComposePath B s u ((Fintype.equivFin (Fin (B + 1) → State w)).symm i)
              j.castSucc)
            (accComposePath B s u ((Fintype.equivFin (Fin (B + 1) → State w)).symm i)
              j.succ)).gateCount) + 1)) + 1 := by
  rw [accComposeMany, accOrAnd_gateCount]

/-- The number of candidate intermediate-state paths of a `B`-ary round is
`(2 ^ w) ^ (B + 1)`. -/
theorem card_statePath (B w : Nat) :
    Fintype.card (Fin (B + 1) → State w) = (2 ^ w) ^ (B + 1) := by
  have hcard : Fintype.card (State w) = 2 ^ w := by
    change Fintype.card (Fin w → Bool) = 2 ^ w
    simp
  rw [Fintype.card_fun, hcard, Fintype.card_fin]

/-- Size of one `B`-ary round: if every step circuit has at most `G` gates, the
round has at most `(number of candidate paths) * (B * G + 1) + 1` gates. -/
theorem accComposeMany_gateCount_le (B : Nat)
    (R : Fin B → State w → State w → ACCCircuit n M) (d G : Nat)
    (hG : ∀ j s t, (R j s t).gateCount ≤ G) (s u : State w) :
    (accComposeMany B R d s u).gateCount
      ≤ Fintype.card (Fin (B + 1) → State w) * (B * G + 1) + 1 := by
  rw [accComposeMany_gateCount]
  refine Nat.add_le_add_right ?_ 1
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin (Fintype.card (Fin (B + 1) → State w)))),
      ((∑ j : Fin B,
        (R j (accComposePath B s u ((Fintype.equivFin (Fin (B + 1) → State w)).symm i)
            j.castSucc)
          (accComposePath B s u ((Fintype.equivFin (Fin (B + 1) → State w)).symm i)
            j.succ)).gateCount) + 1) ≤ B * G + 1 := by
    intro i _
    refine Nat.add_le_add_right ?_ 1
    calc (∑ j : Fin B,
            (R j (accComposePath B s u ((Fintype.equivFin (Fin (B + 1) → State w)).symm i)
                j.castSucc)
              (accComposePath B s u ((Fintype.equivFin (Fin (B + 1) → State w)).symm i)
                j.succ)).gateCount)
          ≤ ∑ _j : Fin B, G := Finset.sum_le_sum (fun j _ => hG j _ _)
      _ = B * G := by simp [Finset.sum_const, Finset.card_univ]
  calc (∑ i : Fin (Fintype.card (Fin (B + 1) → State w)),
          ((∑ j : Fin B,
            (R j (accComposePath B s u ((Fintype.equivFin (Fin (B + 1) → State w)).symm i)
                j.castSucc)
              (accComposePath B s u ((Fintype.equivFin (Fin (B + 1) → State w)).symm i)
                j.succ)).gateCount) + 1))
        ≤ ∑ _i : Fin (Fintype.card (Fin (B + 1) → State w)), (B * G + 1) :=
          Finset.sum_le_sum hterm
    _ = Fintype.card (Fin (B + 1) → State w) * (B * G + 1) := by
        simp [Finset.sum_const, Finset.card_univ]

end Many

end AllenderOQ3.Internal
