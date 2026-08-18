import AllenderOQ3.Internal.LocalPredicate

set_option autoImplicit false

namespace AllenderOQ3.Internal

/-!
# Packaging a large-input ACC family into `InNonuniformACC0`

The final assembly produces `ACC[M]` circuits only for inputs above a fixed
threshold (the point where the polylog-genus bound becomes usable).  Below the
threshold there are only finitely many input lengths, and each of them is
handled by the depth-two truth-table circuit `accTruthTable`.

`inNonuniformACC0_of_large_inputs` performs exactly this splice: from circuits
for all `n ≥ threshold`, of one modulus, one depth bound and one size exponent,
it builds a full family and proves the four `InNonuniformACC0` clauses, using
`accTruthTable_layer_le` and `accTruthTable_gateCount_le_pow` for the finitely
many small lengths.
-/

/-- Splice a family defined above a threshold with truth-table circuits below it. -/
theorem inNonuniformACC0_of_large_inputs (L : BinaryLanguage) (M threshold depth e : Nat)
    (hM : 2 ≤ M)
    (h : ∀ n, threshold ≤ n → ∃ a : ACCCircuit n M, WellFormedACC a ∧
      (∀ g, a.layer g ≤ depth) ∧ a.gateCount ≤ (n + 1) ^ e ∧
      (∀ x, ACCAccepts a x ↔ L n x)) :
    InNonuniformACC0 L := by
  classical
  obtain ⟨eT, hT⟩ := accTruthTable_gateCount_le_pow threshold
  have key : ∀ n : Nat, ∃ a : ACCCircuit n M, WellFormedACC a ∧
      (∀ g, a.layer g ≤ max depth 2) ∧ a.gateCount ≤ (n + 1) ^ (max e eT) ∧
      (∀ x, ACCAccepts a x ↔ L n x) := by
    intro n
    have hbase : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
    by_cases hn : threshold ≤ n
    · obtain ⟨a, ha1, ha2, ha3, ha4⟩ := h n hn
      exact ⟨a, ha1, fun g => le_trans (ha2 g) (le_max_left _ _),
        le_trans ha3 (Nat.pow_le_pow_right hbase (le_max_left _ _)), ha4⟩
    · refine ⟨accTruthTable n M (L n) (fun x => Classical.propDecidable (L n x)),
        wellFormedACC_accTruthTable n M (L n) _,
        fun g => le_trans (accTruthTable_layer_le (m := M) n (L n) _ g) (le_max_right _ _),
        le_trans (hT n (by omega) M (L n) _)
          (Nat.pow_le_pow_right hbase (le_max_right _ _)),
        fun x => accAccepts_accTruthTable n M (L n) _ x⟩
  exact ⟨M, max depth 2, max e eT, fun n => Classical.choose (key n), hM,
    fun n => (Classical.choose_spec (key n)).1,
    fun n g => (Classical.choose_spec (key n)).2.1 g,
    fun n => (Classical.choose_spec (key n)).2.2.1,
    fun n x => (Classical.choose_spec (key n)).2.2.2 x⟩

end AllenderOQ3.Internal
