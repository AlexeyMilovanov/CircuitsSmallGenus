import AllenderOQ3.Internal.WordProblemReduction
import AllenderOQ3.Internal.ACCMulPair
import AllenderOQ3.Internal.NonCrossing
import AllenderOQ3.Internal.ACCCyclicWord
import AllenderOQ3.Internal.ModulusLift

/-!
# The unit case of the abstract word obligation

`LetterWordACC w` (see `ShortWordProblem`) asks for an `ACC0` recogniser of the
value of a window product of `NonCrossing w`-valued letters.  This file settles
the case in which every letter is a **unit** of `NonCrossing w`.

The unit group `(NonCrossing w)ˣ` is cyclic (`nonCrossing_units_cyclic`), so the
letters are powers `g₀ ^ k i x` of one fixed element `g₀` of finite order `N`,
and the value of the product only depends on `∑ i, k i x` modulo `N`.  That is
exactly the situation handled by `exists_acc_powWord` (a `MOD` count per residue
followed by a finite `OR`), once the depth-two `ACC[2]` letter recognisers have
been lifted to the common modulus `2 * N` by `accModulusLift`.
-/

set_option autoImplicit false

namespace AllenderOQ3.Internal

/-- **The unit case of `LetterWordACC`.**  If every letter takes its values in
the unit group of `NonCrossing w`, the value of a window product is recognised
by an `ACC[2N]` circuit of constant depth and of size polynomial in
`size + len`. -/
theorem letterWordACC_units (w : Nat) :
    ∃ modulus depth exponent : Nat,
      2 ≤ modulus ∧
        ∀ {n : Nat} (letter : Nat → (Fin n → Bool) → TransMonoid w) (size : Nat),
          (∀ i x, ∃ u : (NonCrossing w)ˣ, (u.val.val : TransMonoid w) = letter i x) →
          (∀ (i : Nat) (mm : TransMonoid w),
            ∃ a : ACCCircuit n 2,
              WellFormedACC a ∧
              (∀ q, a.layer q ≤ 2) ∧
              a.gateCount ≤ size ∧
              (∀ x, ACCAccepts a x ↔ letter i x = mm)) →
          ∀ (start len : Nat) (h : TransMonoid w),
            ∃ a : ACCCircuit n modulus,
              WellFormedACC a ∧
              (∀ q, a.layer q ≤ depth) ∧
              a.gateCount ≤ (size + len + 2) ^ exponent ∧
              (∀ x, ACCAccepts a x ↔
                wordEnd ((List.range' start len).map (fun i => letter i x)) = h) := by
  classical
  -- a generator of the (cyclic) unit group, and its image in the transition monoid
  obtain ⟨g, hg⟩ := nonCrossing_units_isCyclic w
  set g0 : TransMonoid w := (g.val.val : TransMonoid w) with hg0def
  have hcoe_inj :
      Function.Injective (fun u : (NonCrossing w)ˣ => (u.val.val : TransMonoid w)) := by
    intro a b hab
    exact Units.ext (Subtype.ext hab)
  haveI : Finite ((NonCrossing w)ˣ) := Finite.of_injective _ hcoe_inj
  have hcoe_pow : ∀ j : Nat, (((g ^ j).val.val : TransMonoid w)) = g0 ^ j := by
    intro j
    rw [hg0def]
    push_cast
    rfl
  set N := orderOf g with hNdef
  have hNpos : 0 < N := orderOf_pos g
  have hgN : g ^ N = 1 := pow_orderOf_eq_one g
  have hg0N : g0 ^ N = 1 := by
    have hcp := hcoe_pow N
    rw [hgN] at hcp
    simpa using hcp.symm
  -- every unit is a power of `g` with exponent below `N`
  have hpowers : ∀ u : (NonCrossing w)ˣ,
      ∃ j : Nat, j < N ∧ (u.val.val : TransMonoid w) = g0 ^ j := by
    intro u
    obtain ⟨k, hk⟩ := hg u
    have hNz : (0 : ℤ) < (N : ℤ) := by exact_mod_cast hNpos
    have hr0 : 0 ≤ k % (N : ℤ) := Int.emod_nonneg _ (by omega)
    have hrlt : k % (N : ℤ) < (N : ℤ) := Int.emod_lt_of_pos _ hNz
    refine ⟨(k % (N : ℤ)).toNat, by omega, ?_⟩
    have hsplit : k = (N : ℤ) * (k / (N : ℤ)) + k % (N : ℤ) := by
      have hem := Int.emod_add_mul_ediv k (N : ℤ)
      omega
    have hzp : g ^ k = g ^ (k % (N : ℤ)) := by
      conv_lhs => rw [hsplit]
      rw [zpow_add, zpow_mul, zpow_natCast, hgN, one_zpow, one_mul]
    have hnat : g ^ (k % (N : ℤ)) = g ^ ((k % (N : ℤ)).toNat) := by
      rw [← zpow_natCast g ((k % (N : ℤ)).toNat), Int.toNat_of_nonneg hr0]
    rw [hk, hzp, hnat, hcoe_pow]
  -- the common modulus
  set m := 2 * N with hmdef
  have hmpos : 0 < m := by omega
  have hm2 : (2 : Nat) ∣ m := ⟨N, rfl⟩
  have hNm : N ∣ m := ⟨2, by omega⟩
  set P := m ^ N with hPdef
  set C2 := N * (P * ((N + 1) * (2 * m + 3) + 1) + 4) + 1 with hC2def
  refine ⟨m, 11, 2 + C2, by omega, ?_⟩
  intro n letter size hunits hrec start len h
  -- the exponent of each letter
  have hex : ∀ i x, ∃ v : Nat, v < N ∧ letter i x = g0 ^ v := by
    intro i x
    obtain ⟨u, hu⟩ := hunits i x
    obtain ⟨j, hjN, hj⟩ := hpowers u
    exact ⟨j, hjN, by rw [← hu, hj]⟩
  choose kk hkkN hkkeq using hex
  -- the exponent is uniquely determined
  have hkk_unique : ∀ i x (v : Nat), v < N → letter i x = g0 ^ v → kk i x = v := by
    intro i x v hv hval
    have hpe : g0 ^ (kk i x) = g0 ^ v := by rw [← hkkeq i x, hval]
    have hgp : g ^ (kk i x) = g ^ v := by
      apply hcoe_inj
      simp only [hcoe_pow]
      exact hpe
    have hmod : kk i x ≡ v [MOD orderOf g] := (pow_eq_pow_iff_modEq).mp hgp
    have hmod' := hmod
    rw [Nat.ModEq, ← hNdef, Nat.mod_eq_of_lt (hkkN i x), Nat.mod_eq_of_lt hv] at hmod'
    exact hmod'
  -- the per-position, per-residue recognisers, lifted to the modulus `m`
  have hrecm : ∀ (i : Fin len) (v : Fin N),
      ∃ a : ACCCircuit n m,
        WellFormedACC a ∧
        (∀ q, a.layer q ≤ 6) ∧
        a.gateCount ≤ (m + 2) * size ∧
        (∀ x, ACCAccepts a x ↔ kk (start + (i : Nat)) x = (v : Nat)) := by
    intro i v
    obtain ⟨b, hbwf, hblay, hbsz, hbacc⟩ := hrec (start + (i : Nat)) (g0 ^ (v : Nat))
    refine ⟨accModulusLift b hm2, wellFormedACC_accModulusLift b hm2 hbwf,
      ?_, ?_, ?_⟩
    · have := accModulusLift_layer_le (c := b) (hM := hm2) (d := 2) hblay
      intro q
      exact le_trans (this q) (by omega)
    · exact le_trans (accModulusLift_gateCount_le b hm2) (Nat.mul_le_mul_left _ hbsz)
    · intro x
      rw [evalACC_accModulusLift_of_pos hmpos hbwf x, hbacc x]
      constructor
      · intro hval
        exact hkk_unique _ x _ v.isLt hval
      · intro hval
        rw [hkkeq (start + (i : Nat)) x, hval]
  choose rec hrwf hrlay hrsz hracc using hrecm
  obtain ⟨a, hawf, halay, hasz, haacc⟩ :=
    exists_acc_powWord (n := n) (m := m) (N := N) hmpos hNm (G := TransMonoid w) g0 hg0N
      (len := len) (size := (m + 2) * size) (d := 6)
      (fun i x => kk (start + (i : Nat)) x) (fun i x => hkkN _ x)
      rec hrwf hrlay hrsz hracc h
  refine ⟨a, hawf, ?_, ?_, ?_⟩
  · intro q
    exact le_trans (halay q) (by omega)
  · -- size bound
    set S := size + len + 2 with hSdef
    have hS2 : 2 ≤ S := by omega
    set T := S * S with hTdef
    have hT1 : 1 ≤ T := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hlenS : len ≤ S := by omega
    have hsizeS : size ≤ S := by omega
    set X := len * ((m + 2) * size) + m + 1 with hXdef
    have hX : X ≤ (2 * m + 3) * T := by
      have h1 : len * ((m + 2) * size) ≤ (m + 2) * T := by
        calc len * ((m + 2) * size) = (m + 2) * (len * size) := by ring
          _ ≤ (m + 2) * (S * S) := Nat.mul_le_mul_left _ (Nat.mul_le_mul hlenS hsizeS)
          _ = (m + 2) * T := by rw [hTdef]
      have h2 : m + 1 ≤ (m + 1) * T := Nat.le_mul_of_pos_right _ (by omega)
      calc X = len * ((m + 2) * size) + (m + 1) := by rw [hXdef]; ring
        _ ≤ (m + 2) * T + (m + 1) * T := Nat.add_le_add h1 h2
        _ = (2 * m + 3) * T := by ring
    have hstep1 : (N + 1) * X + 1 ≤ ((N + 1) * (2 * m + 3) + 1) * T := by
      have h1 : (N + 1) * X ≤ (N + 1) * ((2 * m + 3) * T) := Nat.mul_le_mul_left _ hX
      calc (N + 1) * X + 1 ≤ (N + 1) * ((2 * m + 3) * T) + 1 * T :=
            Nat.add_le_add h1 (by omega)
        _ = ((N + 1) * (2 * m + 3) + 1) * T := by ring
    have hstep2 : P * ((N + 1) * X + 1) + 4 ≤ (P * ((N + 1) * (2 * m + 3) + 1) + 4) * T := by
      have h1 : P * ((N + 1) * X + 1) ≤ P * (((N + 1) * (2 * m + 3) + 1) * T) :=
        Nat.mul_le_mul_left _ hstep1
      calc P * ((N + 1) * X + 1) + 4 ≤ P * (((N + 1) * (2 * m + 3) + 1) * T) + 4 * T :=
            Nat.add_le_add h1 (by omega)
        _ = (P * ((N + 1) * (2 * m + 3) + 1) + 4) * T := by ring
    have hstep3 : N * (P * ((N + 1) * X + 1) + 4) + 1 ≤ C2 * T := by
      have h1 : N * (P * ((N + 1) * X + 1) + 4)
          ≤ N * ((P * ((N + 1) * (2 * m + 3) + 1) + 4) * T) := Nat.mul_le_mul_left _ hstep2
      calc N * (P * ((N + 1) * X + 1) + 4) + 1
          ≤ N * ((P * ((N + 1) * (2 * m + 3) + 1) + 4) * T) + 1 * T :=
            Nat.add_le_add h1 (by omega)
        _ = C2 * T := by rw [hC2def]; ring
    have hfinal : C2 * T ≤ S ^ (2 + C2) := by
      have : C2 * S ^ 2 ≤ S ^ (2 + C2) := const_mul_pow_le_pow hS2
      calc C2 * T = C2 * S ^ 2 := by rw [hTdef, pow_two]
        _ ≤ S ^ (2 + C2) := this
    exact le_trans hasz (le_trans hstep3 hfinal)
  · -- semantics
    intro x
    have hlist : (List.ofFn fun i : Fin len => g0 ^ kk (start + (i : Nat)) x)
        = (List.range' start len).map (fun i => letter i x) := by
      apply List.ext_getElem
      · simp
      · intro i hi hi'
        simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range']
        rw [← hkkeq, one_mul]
    have hprod : (List.ofFn fun i : Fin len => g0 ^ kk (start + (i : Nat)) x).prod
        = wordEnd ((List.range' start len).map (fun i => letter i x)) := by
      rw [hlist]
      rfl
    rw [haacc x, hprod]

end AllenderOQ3.Internal
