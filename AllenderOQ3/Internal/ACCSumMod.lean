import AllenderOQ3.Internal.ACCMod

/-!
# `ACC` circuits add modulo `N`

The counting engine needed by the word problem of a monoid whose subgroups are
cyclic: if each of `len` positions carries a value in `{0, …, N-1}` that is
recognised by a small `ACC[m]` circuit, then the residue modulo `N` of the sum
of the values is recognised by an `ACC[m]` circuit of depth three more than the
recognisers and of size a constant multiple of `len` times theirs, provided
`N ∣ m`.

The construction is the standard one: guess, for every value `v < N`, the
residue modulo `m` of the number of positions carrying `v` (a constant `m ^ N`
many guesses), check each guess with one `MOD_m` gate (`accCountEq`), and check
the resulting arithmetic identity `∑ v * count v ≡ r (mod N)` by a constant.
-/

set_option autoImplicit false

namespace AllenderOQ3.Internal


/-- Summing a bounded function by fibres. -/
theorem sum_eq_sum_mul_count {len N : Nat} (f : Fin len → Nat) (hf : ∀ i, f i < N) :
    ∑ i, f i
      = ∑ v : Fin N, (v : Nat) * (Finset.univ.filter fun i => f i = (v : Nat)).card := by
  classical
  have hmaps : ∀ i ∈ (Finset.univ : Finset (Fin len)),
      (⟨f i, hf i⟩ : Fin N) ∈ (Finset.univ : Finset (Fin N)) := by
    intro i _; exact Finset.mem_univ _
  have hfib := Finset.sum_fiberwise_of_maps_to (g := fun i : Fin len => (⟨f i, hf i⟩ : Fin N))
    (f := f) hmaps
  rw [← hfib]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hfilter : (Finset.univ.filter fun i : Fin len => (⟨f i, hf i⟩ : Fin N) = v)
      = Finset.univ.filter fun i : Fin len => f i = (v : Nat) := by
    ext i
    simp [Fin.ext_iff]
  rw [hfilter]
  rw [Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.mp hi).2)]
  simp [Nat.mul_comm]

/-- A sum of pointwise congruent terms is congruent. -/
theorem sum_modEq_sum {N : Nat} {ι : Type} (s : Finset ι) (f g : ι → Nat)
    (h : ∀ i ∈ s, f i ≡ g i [MOD N]) : (∑ i ∈ s, f i) ≡ (∑ i ∈ s, g i) [MOD N] := by
  classical
  unfold Nat.ModEq
  rw [Finset.sum_nat_mod, Finset.sum_nat_mod (s := s) (f := g)]
  exact congrArg (· % N) (Finset.sum_congr rfl fun i hi => h i hi)

/-- **`ACC` circuits compute sums modulo `N`.**  Each of the `len` positions
carries a value below `N`, recognised value by value by a circuit of depth `d`
and size `size`; the predicate "the values sum to `r` modulo `N`" is then
recognised in depth `max d 1 + 3` and size `m ^ N * ((N+1) * (len*size+m+1) + 1) + 1`. -/
theorem exists_acc_sumMod {n m N : Nat} (hm : 0 < m) (hNm : N ∣ m)
    {len size d : Nat}
    (val : Fin len → (Fin n → Bool) → Nat)
    (hval : ∀ i x, val i x < N)
    (rec : Fin len → Fin N → ACCCircuit n m)
    (hwf : ∀ i v, WellFormedACC (rec i v))
    (hlay : ∀ i v q, (rec i v).layer q ≤ d)
    (hsize : ∀ i v, (rec i v).gateCount ≤ size)
    (hacc : ∀ i v x, ACCAccepts (rec i v) x ↔ val i x = (v : Nat))
    (r : Nat) :
    ∃ a : ACCCircuit n m,
      WellFormedACC a ∧
      (∀ q, a.layer q ≤ max d 1 + 3) ∧
      a.gateCount ≤ m ^ N * ((N + 1) * (len * size + m + 1) + 1) + 1 ∧
      (∀ x, ACCAccepts a x ↔ (∑ i, val i x) % N = r % N) := by
  classical
  set K := Fintype.card (Fin N → Fin m) with hK
  set ee := Fintype.equivFin (Fin N → Fin m) with hee
  -- the counting circuit for the value `v` and the guessed residue `t`
  set count : Fin N → Nat → ACCCircuit n m := fun v t =>
    accCountEq (fun p : Fin len => rec p v) d t with hcount
  set blocks : (i : Fin K) → Fin (N + 1) → ACCCircuit n m := fun i j =>
    if h : (j : Nat) < N then count ⟨(j : Nat), h⟩ (((ee.symm i) ⟨(j : Nat), h⟩ : Fin m) : Nat)
    else accConst n m
      (decide ((∑ v : Fin N, (v : Nat) * (((ee.symm i) v : Fin m) : Nat)) % N = r % N))
    with hblocks
  have hbLt : ∀ (i : Fin K) (j : Fin (N + 1)) (h : (j : Nat) < N),
      blocks i j = count ⟨(j : Nat), h⟩ (((ee.symm i) ⟨(j : Nat), h⟩ : Fin m) : Nat) := by
    intro i j h; rw [hblocks]; exact dif_pos h
  have hbTop : ∀ (i : Fin K) (j : Fin (N + 1)), ¬ (j : Nat) < N →
      blocks i j = accConst n m
        (decide ((∑ v : Fin N, (v : Nat) * (((ee.symm i) v : Fin m) : Nat)) % N = r % N)) := by
    intro i j h; rw [hblocks]; exact dif_neg h
  -- well-formedness and depth of the blocks
  have hcwf : ∀ (v : Fin N) (t : Nat), WellFormedACC (count v t) := by
    intro v t
    exact wellFormedACC_accCountEq (fun p => hwf p v) (fun p q => hlay p v q)
  have hclay : ∀ (v : Fin N) (t : Nat) (q : Fin (count v t).gateCount),
      (count v t).layer q ≤ max d 1 + 1 := by
    intro v t q
    exact accCountEq_layer_le (fun p q' => hlay p v q') q
  have hbwf : ∀ i j, WellFormedACC (blocks i j) := by
    intro i j
    by_cases h : (j : Nat) < N
    · rw [hbLt i j h]; exact hcwf _ _
    · rw [hbTop i j h]; exact wellFormedACC_accConst n m _
  have hblay : ∀ i j (q : Fin (blocks i j).gateCount),
      (blocks i j).layer q ≤ max d 1 + 1 := by
    intro i j
    by_cases h : (j : Nat) < N
    · rw [hbLt i j h]; exact fun q => hclay _ _ q
    · rw [hbTop i j h]; intro q; rw [accConst_layer]; omega
  refine ⟨accOrAnd blocks (max d 1 + 1), wellFormedACC_accOrAnd hbwf hblay,
    accOrAnd_layer_le hblay, ?_, fun x => ?_⟩
  · -- size bound
    have hcsize : ∀ (v : Fin N) (t : Nat), (count v t).gateCount ≤ len * size + m + 1 := by
      intro v t
      have hgc : (count v t).gateCount
          = (∑ p : Fin len, (rec p v).gateCount) + ((m - (t % m)) % m) + 1 :=
        accCountEq_gateCount
      have h1 : (∑ p : Fin len, (rec p v).gateCount) ≤ len * size := by
        have := Finset.sum_le_sum (fun p (_ : p ∈ (Finset.univ : Finset (Fin len))) => hsize p v)
        simpa [Finset.sum_const, Finset.card_univ, mul_comm] using this
      have h2 : (m - (t % m)) % m ≤ m := le_of_lt (Nat.mod_lt _ hm)
      omega
    have hbsize : ∀ i j, (blocks i j).gateCount ≤ len * size + m + 1 := by
      intro i j
      by_cases h : (j : Nat) < N
      · rw [hbLt i j h]; exact hcsize _ _
      · rw [hbTop i j h, accConst_gateCount]; omega
    have hrow : ∀ i : Fin K, (∑ j, (blocks i j).gateCount) + 1
        ≤ (N + 1) * (len * size + m + 1) + 1 := by
      intro i
      have := Finset.sum_le_sum
        (fun j (_ : j ∈ (Finset.univ : Finset (Fin (N + 1)))) => hbsize i j)
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at this
      omega
    have hsum : ∑ i : Fin K, ((∑ j, (blocks i j).gateCount) + 1)
        ≤ ∑ _i : Fin K, ((N + 1) * (len * size + m + 1) + 1) :=
      Finset.sum_le_sum fun i _ => hrow i
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
    have hgc : (accOrAnd blocks (max d 1 + 1)).gateCount
        = (∑ i : Fin K, ((∑ j, (blocks i j).gateCount) + 1)) + 1 := rfl
    have hKval : K = m ^ N := by
      rw [hK, Fintype.card_fun]
      simp
    rw [hgc, ← hKval]
    exact Nat.add_le_add_right hsum 1
  · -- semantics
    set cnt : Fin N → Nat := fun v =>
      (Finset.univ.filter fun p : Fin len => val p x = (v : Nat)).card with hcnt
    have hsumid : ∑ i, val i x = ∑ v : Fin N, (v : Nat) * cnt v :=
      sum_eq_sum_mul_count (fun i => val i x) (fun i => hval i x)
    have hcountacc : ∀ (v : Fin N) (t : Nat),
        ACCAccepts (count v t) x ↔ cnt v % m = t % m := by
      intro v t
      rw [hcount]
      rw [accAccepts_accCountEq hm (fun p => hwf p v) (fun p q => hlay p v q) x]
      have hfil : (Finset.univ.filter fun p : Fin len => ACCAccepts (rec p v) x)
          = Finset.univ.filter fun p : Fin len => val p x = (v : Nat) := by
        ext p
        simp [hacc p v x]
      rw [hfil]
    -- the arithmetic step: guessed residues determine the sum modulo `N`
    have harith : ∀ c : Fin N → Fin m, (∀ v, cnt v % m = ((c v : Fin m) : Nat) % m) →
        ((∑ i, val i x) % N = r % N ↔
          (∑ v : Fin N, (v : Nat) * ((c v : Fin m) : Nat)) % N = r % N) := by
      intro c hc
      have hmod : ∀ v : Fin N, (v : Nat) * cnt v ≡ (v : Nat) * ((c v : Fin m) : Nat) [MOD N] := by
        intro v
        exact Nat.ModEq.mul_left _ (Nat.ModEq.of_dvd hNm (hc v))
      have hsumeq : (∑ v : Fin N, (v : Nat) * cnt v)
          ≡ (∑ v : Fin N, (v : Nat) * ((c v : Fin m) : Nat)) [MOD N] :=
        sum_modEq_sum _ _ _ fun v _ => hmod v
      rw [hsumid]
      exact ⟨fun h => hsumeq.symm.trans h, fun h => hsumeq.trans h⟩
    rw [accAccepts_accOrAnd hbwf hblay x]
    constructor
    · rintro ⟨i, hi⟩
      set c := ee.symm i with hc
      have hcv : ∀ v : Fin N, cnt v % m = ((c v : Fin m) : Nat) % m := by
        intro v
        have hj : ((⟨(v : Nat), Nat.lt_succ_of_lt v.isLt⟩ : Fin (N + 1)) : Nat) < N := v.isLt
        have := hi ⟨(v : Nat), Nat.lt_succ_of_lt v.isLt⟩
        rw [hbLt i _ hj] at this
        have hv : (⟨(v : Nat), hj⟩ : Fin N) = v := Fin.ext rfl
        rw [hv] at this
        exact (hcountacc v _).mp this
      have htop := hi ⟨N, Nat.lt_succ_self N⟩
      rw [hbTop i _ (by simp)] at htop
      have htop' := (accAccepts_accConst n m _ x).mp htop
      exact (harith c hcv).mpr (of_decide_eq_true htop')
    · intro hx
      refine ⟨ee (fun v => ⟨cnt v % m, Nat.mod_lt _ hm⟩), fun j => ?_⟩
      set c : Fin N → Fin m := fun v => ⟨cnt v % m, Nat.mod_lt _ hm⟩ with hcdef
      have hsymm : ee.symm (ee c) = c := ee.symm_apply_apply c
      have hcv : ∀ v : Fin N, cnt v % m = ((c v : Fin m) : Nat) % m := by
        intro v
        simp [hcdef]
      by_cases h : (j : Nat) < N
      · rw [hbLt _ j h, hsymm]
        exact (hcountacc _ _).mpr (hcv ⟨(j : Nat), h⟩)
      · rw [hbTop _ j h, hsymm]
        refine (accAccepts_accConst n m _ x).mpr ?_
        exact decide_eq_true ((harith c hcv).mp hx)

end AllenderOQ3.Internal
