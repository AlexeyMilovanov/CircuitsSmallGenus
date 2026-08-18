import AllenderOQ3.Internal.LocalDivisorCompression

/-!
# The local-divisor induction (S4, proved)

The Krohn–Rhodes-free replacement for Barrington–Thérien, specialized to
monoids with abelian subgroups:

> if every subgroup of the finite monoid `M` is abelian
> (`LocalUnitsCommute M`), then `MonoidWordACCGen M`.

Proof recipe (`docs/LOCAL_DIVISOR_PLAN.md` §5) — strong induction on
`Nat.card M` in the form `∀ k, ∀ M [Monoid M] [Finite M], Nat.card M ≤ k → …`:

1. Choose a generating `Finset` `A` (e.g. the finite `Finset.univ` works) of
   MINIMAL CARDINALITY with `Submonoid.closure ↑A = ⊤` (Nat well-ordering).
   Minimality gives `∀ c ∈ A, (c : M) ∉ Submonoid.closure ↑(A.erase c)` —
   otherwise `A.erase c` still generates, contradicting minimality.
2. If every member of `A` is a unit, every element of `M` is a unit
   (`Submonoid.closure_induction` with `IsUnit.mul`, `isUnit_one`), so
   `mul_comm_of_localUnitsCommute_units` applies; install
   `letI : CommMonoid M := { ‹Monoid M› with mul_comm := … }` and finish with
   `monoidWordACCGen_of_comm`.
3. Otherwise pick a nonunit `c ∈ A` and set `N := Submonoid.closure
   ↑(A.erase c)`.  Then `Nat.card ↥N < Nat.card M` (the subtype misses `c`;
   `Fintype.card_subtype_lt`) and `Nat.card (LocalDivisor c) < Nat.card M`
   (`card_localDivisor_lt`).  Both inherit the hypothesis
   (`localUnitsCommute_submonoid`, `localUnitsCommute_localDivisor`), so the
   induction gives `MonoidWordACCGen` for both.  Apply
   `monoidWordACCGen_compression c ↑(A.erase c)`, then
   `monoidWordACCGen_of_genOn` with the alphabet
   `insert c (Submonoid.closure ↑(A.erase c))` (it contains `1` and
   generates, since `A ⊆ insert c ↑N`).

This recipe is carried out below: `monoidWordACCGen_of_localUnitsCommute` is
`sorry`-free, and so are the circuit leaves S2 and S3 of
`LocalDivisorCompression.lean` that it rests on.
-/

set_option autoImplicit false

namespace AllenderOQ3
namespace Internal

/-- Strong-induction form of S4: the statement for all monoids of cardinality
at most `k`, proved by induction on `k`. -/
theorem monoidWordACCGen_of_localUnitsCommute_aux :
    ∀ (k : Nat) (M : Type) [Monoid M] [Finite M],
      Nat.card M ≤ k → LocalUnitsCommute M → MonoidWordACCGen M := by
  intro k
  induction k with
  | zero =>
    intro M _ _ hcard _
    have hpos : 0 < Nat.card M := Nat.card_pos
    omega
  | succ k ih =>
    intro M _ _ hcard h
    classical
    haveI : Fintype M := Fintype.ofFinite M
    -- a generating finset of minimal cardinality
    have hexA : ∃ n, ∃ A : Finset M, A.card = n ∧ Submonoid.closure (↑A : Set M) = ⊤ :=
      ⟨_, Finset.univ, rfl, by simp⟩
    obtain ⟨A, hAcard, hAgen⟩ := Nat.find_spec hexA
    have hAmin : ∀ A' : Finset M, Submonoid.closure (↑A' : Set M) = ⊤ →
        Nat.find hexA ≤ A'.card := fun A' hA' => Nat.find_le ⟨A', rfl, hA'⟩
    by_cases hunits : ∀ c ∈ A, IsUnit c
    · -- base case: every generator, hence every element, is a unit
      have hall : ∀ m : M, IsUnit m := by
        intro m
        have hm : m ∈ Submonoid.closure (↑A : Set M) := by rw [hAgen]; trivial
        induction hm using Submonoid.closure_induction with
        | mem x hx => exact hunits x (by simpa using hx)
        | one => exact isUnit_one
        | mul x y _ _ hx hy => exact hx.mul hy
      letI : CommMonoid M :=
        { (inferInstance : Monoid M) with
          mul_comm := mul_comm_of_localUnitsCommute_units h hall }
      exact monoidWordACCGen_of_comm M
    · -- inductive step at a nonunit generator `c`
      push_neg at hunits
      obtain ⟨c, hcA, hc⟩ := hunits
      set B : Set M := (↑(A.erase c) : Set M) with hB
      have hcnot : c ∉ Submonoid.closure B := by
        intro hmem
        have hsub : (↑A : Set M) ⊆ (Submonoid.closure B : Set M) := by
          intro a ha
          by_cases hac : a = c
          · exact hac ▸ hmem
          · exact Submonoid.subset_closure (by simp [hB, hac, Finset.mem_coe.mp ha])
        have htop : Submonoid.closure B = ⊤ := by
          have hmono : Submonoid.closure (↑A : Set M) ≤ Submonoid.closure B :=
            Submonoid.closure_le.mpr hsub
          rw [hAgen] at hmono
          exact top_le_iff.mp hmono
        have h1 := hAmin (A.erase c) (by rw [← hB]; exact htop)
        have h2 : (A.erase c).card < A.card := Finset.card_erase_lt_of_mem hcA
        omega
      have hNcard : Nat.card (Submonoid.closure B) < Nat.card M := by
        have h1 : Nat.card (Submonoid.closure B)
            = Fintype.card {x : M // x ∈ Submonoid.closure B} := Nat.card_eq_fintype_card
        rw [h1, Nat.card_eq_fintype_card]
        exact Fintype.card_subtype_lt (p := fun x : M => x ∈ Submonoid.closure B)
          (x := c) hcnot
      have hDcard : Nat.card (LocalDivisor c) < Nat.card M :=
        LocalDivisor.card_localDivisor_lt hc
      have hN : MonoidWordACCGen (Submonoid.closure B) :=
        ih _ (by omega) (localUnitsCommute_submonoid _ h)
      have hD : MonoidWordACCGen (LocalDivisor c) :=
        ih _ (by omega) (localUnitsCommute_localDivisor h)
      refine monoidWordACCGen_of_genOn ?_ ?_ (monoidWordACCGen_compression c B hN hD)
      · exact Set.mem_insert_of_mem _ (Submonoid.one_mem _)
      · have hsub : (↑A : Set M) ⊆ insert c (↑(Submonoid.closure B) : Set M) := by
          intro a ha
          by_cases hac : a = c
          · exact hac ▸ Set.mem_insert _ _
          · exact Set.mem_insert_of_mem _ (Submonoid.subset_closure
              (by simp [hB, hac, Finset.mem_coe.mp ha]))
        have hmono := Submonoid.closure_mono hsub
        rw [hAgen] at hmono
        exact top_le_iff.mp hmono

/-- **S4: the local-divisor induction.** -/
theorem monoidWordACCGen_of_localUnitsCommute (M : Type) [Monoid M] [Finite M]
    (h : LocalUnitsCommute M) : MonoidWordACCGen M :=
  monoidWordACCGen_of_localUnitsCommute_aux (Nat.card M) M le_rfl h

end Internal
end AllenderOQ3
