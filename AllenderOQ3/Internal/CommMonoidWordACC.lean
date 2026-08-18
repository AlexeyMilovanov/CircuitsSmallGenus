import AllenderOQ3.Internal.MonoidWordACC
import AllenderOQ3.Internal.ACCThreshold
import AllenderOQ3.Internal.ACCSumMod
import AllenderOQ3.Internal.ModulusLift
import AllenderOQ3.Internal.PowerBounds

/-!
# The word problem of a finite commutative monoid is in `ACC`

This is the base case of the Barrington–Thérien analysis, and in particular it
covers the cyclic groups that the holonomy of the cylindrical cascade produces.

In a commutative monoid the product of a block depends only on how many times
each letter occurs in it, and, the monoid being finite, only on that count
*truncated at the index* `I` and *modulo the period* `P` of the monoid
(`pow_eq_pow_of_index_period`).  Both data are `ACC`-computable: the truncated
count by the constant threshold gadgets of `ACCThreshold`, and the residue by the
`MOD` gates of `ACCSumMod`.  Guessing the (constantly many) profiles and checking
them turns this into a constant-depth polynomial-size recogniser.

The main results are `exists_acc_prod_comm` (a single block value is
recognisable) and `monoidWordACC_of_comm` (the full `MonoidWordACC` interface,
with all the quantitative bookkeeping), together with the sanity witness
`monoidWordACC_multiplicative_zmod`, which shows that the interface is met by
monoids that are not subsingletons.

Everything here is `sorry`-free.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace AllenderOQ3
namespace Internal

attribute [local instance] Classical.propDecidable

/-! ## Eventual periodicity of the powers of a finite monoid -/

/-- Iterating a period. -/
theorem pow_add_mul_period {M : Type} [Monoid M] {g : M} {I p : Nat}
    (h : ∀ k, I ≤ k → g ^ (k + p) = g ^ k) :
    ∀ (t k : Nat), I ≤ k → g ^ (k + t * p) = g ^ k := by
  intro t
  induction t with
  | zero => intro k _; simp
  | succ s ih =>
      intro k hk
      have hrw : k + (s + 1) * p = (k + s * p) + p := by ring
      rw [hrw, h (k + s * p) (by omega), ih k hk]

/-- **The powers of an element of a finite monoid are eventually periodic.** -/
theorem exists_period {M : Type} [Monoid M] [Finite M] (g : M) :
    ∃ I p : Nat, 0 < p ∧ ∀ k, I ≤ k → g ^ (k + p) = g ^ k := by
  classical
  haveI := Fintype.ofFinite M
  have hni : ¬ Function.Injective (fun i : Fin (Fintype.card M + 1) => g ^ (i : Nat)) := by
    intro hinj
    have hle := Fintype.card_le_of_injective _ hinj
    simp at hle
  rw [Function.not_injective_iff] at hni
  obtain ⟨i, j, hij, hne⟩ := hni
  -- order the two exponents
  rcases Nat.lt_or_ge (i : Nat) (j : Nat) with hlt | hge
  · refine ⟨(i : Nat), (j : Nat) - (i : Nat), by omega, fun k hk => ?_⟩
    have hk' : k + ((j : Nat) - (i : Nat)) = (k - (i : Nat)) + (j : Nat) := by omega
    have hk'' : k = (k - (i : Nat)) + (i : Nat) := by omega
    rw [hk', pow_add, ← hij, ← pow_add, ← hk'']
  · have hlt : (j : Nat) < (i : Nat) := by
      rcases Nat.lt_or_ge (j : Nat) (i : Nat) with h | h
      · exact h
      · exact absurd (Fin.ext (by omega)) hne
    refine ⟨(j : Nat), (i : Nat) - (j : Nat), by omega, fun k hk => ?_⟩
    have hk' : k + ((i : Nat) - (j : Nat)) = (k - (j : Nat)) + (i : Nat) := by omega
    have hk'' : k = (k - (j : Nat)) + (j : Nat) := by omega
    rw [hk', pow_add, hij, ← pow_add, ← hk'']

/-- **A finite monoid has a uniform index and period**: past the index, powers
depend only on the exponent modulo the period. -/
theorem exists_index_period (M : Type) [Monoid M] [Finite M] :
    ∃ I P : Nat, 0 < P ∧ ∀ (g : M) (k : Nat), I ≤ k → g ^ (k + P) = g ^ k := by
  classical
  haveI := Fintype.ofFinite M
  choose Ifun pfun hppos hpow using fun g : M => exists_period g
  refine ⟨Finset.univ.sup Ifun, ∏ g : M, pfun g,
    Finset.prod_pos (fun g _ => hppos g), ?_⟩
  intro g k hk
  have hIg : Ifun g ≤ k :=
    le_trans (Finset.le_sup (f := Ifun) (Finset.mem_univ g)) hk
  obtain ⟨t, ht⟩ : pfun g ∣ ∏ h : M, pfun h := Finset.dvd_prod_of_mem _ (Finset.mem_univ g)
  rw [ht, Nat.mul_comm]
  exact pow_add_mul_period (hpow g) t k hIg

/-- Past the index, equal residues modulo the period give equal powers. -/
theorem pow_eq_pow_of_index_period {M : Type} [Monoid M] {I P : Nat}
    (h : ∀ (g : M) (k : Nat), I ≤ k → g ^ (k + P) = g ^ k) (g : M) {k k' : Nat}
    (hk : I ≤ k) (hk' : I ≤ k') (hmod : k % P = k' % P) : g ^ k = g ^ k' := by
  -- it suffices to treat `k ≤ k'`
  have main : ∀ u v : Nat, I ≤ u → u ≤ v → u % P = v % P → g ^ u = g ^ v := by
    intro u v hu huv hmuv
    have hdvd : P ∣ v - u := (Nat.modEq_iff_dvd' huv).mp hmuv
    obtain ⟨t, ht⟩ := hdvd
    rw [Nat.mul_comm] at ht
    have hv : v = u + t * P := by omega
    rw [hv, pow_add_mul_period (fun k hk => h g k hk) t u hu]
  rcases Nat.le_total k k' with hle | hle
  · exact main k k' hk hle hmod
  · exact (main k' k hk' hle hmod.symm).symm

/-! ## Count specifications -/

/-- The condition a letter count `cnt` has to satisfy for the profile value `v`:
below the index the count is pinned exactly, above it only its residue modulo the
period matters. -/
def CountSpec (I P v cnt : Nat) : Prop :=
  if v < I then cnt = v else I ≤ cnt ∧ cnt % P = v % P

/-- A count satisfying the specification for `v` has the same power as `v`. -/
theorem pow_eq_pow_of_countSpec {M : Type} [Monoid M] {I P : Nat}
    (h : ∀ (g : M) (k : Nat), I ≤ k → g ^ (k + P) = g ^ k) (g : M) {v cnt : Nat}
    (hspec : CountSpec I P v cnt) : g ^ cnt = g ^ v := by
  unfold CountSpec at hspec
  by_cases hv : v < I
  · rw [if_pos hv] at hspec
    rw [hspec]
  · rw [if_neg hv] at hspec
    exact pow_eq_pow_of_index_period h g hspec.1 (by omega) hspec.2

/-- The profile value of a count: the count itself below the index, and the
index plus the residue of the excess above it. -/
def profOf (I P cnt : Nat) : Nat :=
  if cnt < I then cnt else I + (cnt - I) % P

theorem profOf_lt {I P cnt : Nat} (hP : 0 < P) : profOf I P cnt < I + P := by
  unfold profOf
  by_cases h : cnt < I
  · rw [if_pos h]; omega
  · rw [if_neg h]
    have := Nat.mod_lt (cnt - I) hP
    omega

theorem countSpec_profOf {I P cnt : Nat} (hP : 0 < P) :
    CountSpec I P (profOf I P cnt) cnt := by
  unfold CountSpec profOf
  by_cases h : cnt < I
  · rw [if_pos h, if_pos h]
  · have hmod := Nat.mod_lt (cnt - I) hP
    rw [if_neg h, if_neg (by omega : ¬ I + (cnt - I) % P < I)]
    refine ⟨by omega, ?_⟩
    have h1 : (cnt - I) % P ≡ (cnt - I) [MOD P] := Nat.mod_modEq _ _
    have h2 : I + (cnt - I) % P ≡ I + (cnt - I) [MOD P] := Nat.ModEq.add_left I h1
    have h3 : I + (cnt - I) = cnt := by omega
    rw [h3] at h2
    exact h2.symm

/-! ## The product of a block by letter counts -/

/-- A range of positions, read as a tuple. -/
theorem map_range'_eq_ofFn {M : Type} (f : Nat → M) : ∀ (bl s : Nat),
    ((List.range' s bl).map f) = List.ofFn (fun p : Fin bl => f (s + p)) := by
  intro bl
  induction bl with
  | zero => intro s; simp
  | succ k ih =>
      intro s
      rw [List.range'_succ, List.map_cons, ih (s + 1), List.ofFn_succ]
      simp [Nat.add_comm, Nat.add_left_comm]

/-- **In a commutative monoid a product is determined by the letter counts.** -/
theorem prod_eq_prod_pow_card {M : Type} [CommMonoid M] [Fintype M] {bl : Nat}
    (idx : Fin bl → M) :
    ∏ p, idx p = ∏ g : M, g ^ (Finset.univ.filter fun p => idx p = g).card := by
  classical
  rw [← Finset.prod_fiberwise_of_maps_to (g := idx) (fun p _ => Finset.mem_univ (idx p))]
  refine Finset.prod_congr rfl fun g _ => ?_
  rw [Finset.prod_congr rfl (fun p hp => (Finset.mem_filter.mp hp).2), Finset.prod_const]

/-- The product of a block of a commutative monoid word, by letter counts. -/
theorem blockProd_eq_prod_pow_card {M : Type} [CommMonoid M] [Fintype M] {n : Nat}
    (letter : Nat → (Fin n → Bool) → M) (start a b : Nat) (x : Fin n → Bool) :
    blockProd letter start a b x
      = ∏ g : M, g ^ (Finset.univ.filter
          fun p : Fin (b - a) => letter (start + a + p) x = g).card := by
  classical
  rw [blockProd, map_range'_eq_ofFn (fun i => letter i x) (b - a) (start + a), List.prod_ofFn]
  exact prod_eq_prod_pow_card _

/-! ## Recognising a count specification -/

/-- **The residue modulo `P` of the number of accepting positions is
`ACC`-computable**, by a single `MOD P` gate fed with the indicator circuits. -/
theorem exists_acc_countMod {n m : Nat} (hmpos : 0 < m) {P : Nat} (hP2 : 2 ≤ P) (hPm : P ∣ m)
    {bl d Sz : Nat} (fam : Fin bl → ACCCircuit n m)
    (hwf : ∀ p, WellFormedACC (fam p)) (hlay : ∀ p q, (fam p).layer q ≤ d)
    (hsz : ∀ p, (fam p).gateCount ≤ Sz) (r : Nat) :
    ∃ a : ACCCircuit n m,
      WellFormedACC a ∧ (∀ q, a.layer q ≤ max d 1 + 4) ∧
      a.gateCount ≤ m ^ P * ((P + 1) * (bl * (Sz + 1) + m + 1) + 1) + 1 ∧
      (∀ x, ACCAccepts a x ↔
        (Finset.univ.filter fun p : Fin bl => ACCAccepts (fam p) x).card % P = r % P) := by
  classical
  set val : Fin bl → (Fin n → Bool) → Nat :=
    fun p x => if ACCAccepts (fam p) x then 1 else 0 with hvaldef
  have hval01 : ∀ p x, val p x = 0 ∨ val p x = 1 := by
    intro p x
    by_cases h : ACCAccepts (fam p) x
    · right; simp [hvaldef, h]
    · left; simp [hvaldef, h]
  have hval : ∀ p x, val p x < P := by
    intro p x
    have := hval01 p x
    omega
  set rec : Fin bl → Fin P → ACCCircuit n m := fun p w =>
    if (w : Nat) = 1 then fam p
    else if (w : Nat) = 0 then accNot (fam p) d else accConst n m false with hrecdef
  have hrec1 : ∀ (p : Fin bl) (w : Fin P), (w : Nat) = 1 → rec p w = fam p := by
    intro p w hw; simp only [hrecdef, if_pos hw]
  have hrec0 : ∀ (p : Fin bl) (w : Fin P), (w : Nat) = 0 → rec p w = accNot (fam p) d := by
    intro p w hw
    simp only [hrecdef, if_neg (by omega : ¬ (w : Nat) = 1), if_pos hw]
  have hrec2 : ∀ (p : Fin bl) (w : Fin P), 2 ≤ (w : Nat) → rec p w = accConst n m false := by
    intro p w hw
    simp only [hrecdef, if_neg (by omega : ¬ (w : Nat) = 1), if_neg (by omega : ¬ (w : Nat) = 0)]
  have hcases : ∀ w : Fin P, (w : Nat) = 0 ∨ (w : Nat) = 1 ∨ 2 ≤ (w : Nat) := by
    intro w; omega
  have hrwf : ∀ p w, WellFormedACC (rec p w) := by
    intro p w
    rcases hcases w with hw | hw | hw
    · rw [hrec0 p w hw]; exact wellFormedACC_accNot (hwf p) (hlay p)
    · rw [hrec1 p w hw]; exact hwf p
    · rw [hrec2 p w hw]; exact wellFormedACC_accConst n m false
  have hrlay : ∀ p w q, (rec p w).layer q ≤ d + 1 := by
    intro p w
    rcases hcases w with hw | hw | hw
    · rw [hrec0 p w hw]; exact accNot_layer_le (hlay p)
    · rw [hrec1 p w hw]; exact fun q => le_trans (hlay p q) (by omega)
    · rw [hrec2 p w hw]; intro q; rw [accConst_layer]; omega
  have hrsz : ∀ p w, (rec p w).gateCount ≤ Sz + 1 := by
    intro p w
    rcases hcases w with hw | hw | hw
    · rw [hrec0 p w hw, accNot_gateCount]; have := hsz p; omega
    · rw [hrec1 p w hw]; have := hsz p; omega
    · rw [hrec2 p w hw, accConst_gateCount]; omega
  have hracc : ∀ p w x, ACCAccepts (rec p w) x ↔ val p x = (w : Nat) := by
    intro p w x
    rcases hcases w with hw | hw | hw
    · rw [hrec0 p w hw, accAccepts_accNot (hwf p) (hlay p) x, hw, hvaldef]
      by_cases h : ACCAccepts (fam p) x
      · simp [h]
      · simp [h]
    · rw [hrec1 p w hw, hw, hvaldef]
      by_cases h : ACCAccepts (fam p) x
      · simp [h]
      · simp [h]
    · rw [hrec2 p w hw, accAccepts_accConst]
      constructor
      · intro h; exact absurd h (by simp)
      · intro h; exact absurd h (by have := hval01 p x; omega)
  obtain ⟨a, hawf, halay, hasz, haacc⟩ :=
    exists_acc_sumMod (n := n) (m := m) (N := P) hmpos hPm (d := d + 1) (size := Sz + 1)
      val hval rec hrwf hrlay hrsz hracc r
  refine ⟨a, hawf, fun q => le_trans (halay q) (by omega), hasz, ?_⟩
  intro x
  rw [haacc x]
  have hsum : (∑ p, val p x)
      = (Finset.univ.filter fun p : Fin bl => ACCAccepts (fam p) x).card := by
    rw [Finset.card_filter]
  rw [hsum]

/-- **A count specification is `ACC`-recognisable.**  Below the index the count
is pinned exactly by the threshold gadgets; above it, the threshold "at least
`I`" is combined with a `MOD P` gate. -/
theorem exists_acc_countSpec {n m : Nat} (hmpos : 0 < m) {I P : Nat} (hP2 : 2 ≤ P) (hPm : P ∣ m)
    {bl d Sz S s : Nat} (hS : 2 ≤ S) (hblS : bl ≤ S) (hSzS : Sz ≤ S ^ s)
    (fam : Fin bl → ACCCircuit n m)
    (hwf : ∀ p, WellFormedACC (fam p)) (hlay : ∀ p q, (fam p).layer q ≤ d)
    (hsz : ∀ p, (fam p).gateCount ≤ Sz) {v : Nat} (hv : v < I + P) :
    ∃ a : ACCCircuit n m,
      WellFormedACC a ∧ (∀ q, a.layer q ≤ max d 1 + 10) ∧
      a.gateCount ≤ S ^ (4 * (I + P) + 2 * s + m * P + m + P + 30) ∧
      (∀ x, ACCAccepts a x ↔ CountSpec I P v
        (Finset.univ.filter fun p : Fin bl => ACCAccepts (fam p) x).card) := by
  classical
  by_cases hvI : v < I
  · obtain ⟨a, hawf, halay, hasz, haacc⟩ :=
      exists_acc_countEq (j := v) fam hwf hlay hsz
    refine ⟨a, hawf, fun q => le_trans (halay q) (by omega), ?_, ?_⟩
    · have hbl : ∀ e, bl ^ e ≤ S ^ e := fun e => Nat.pow_le_pow_left hblS e
      have h1 : bl ^ (v + 1) * ((v + 1) * Sz + 4) ≤ S ^ (2 * (I + P) + s + 6) := by
        refine le_trans (pow_bnd_mul (a := I + P) (b := (I + P) + s + 4 + 1)
          (le_trans (hbl (v + 1)) (pow_bnd_mono hS (by omega)))
          (pow_bnd_add hS (pow_bnd_mul (le_trans (pow_bnd_const hS (v + 1))
            (pow_bnd_mono hS (by omega))) hSzS) (pow_bnd_const hS 4))) ?_
        exact pow_bnd_mono hS (by omega)
      have h2 : bl ^ v * (v * Sz + 4) ≤ S ^ (2 * (I + P) + s + 6) := by
        refine le_trans (pow_bnd_mul (a := I + P) (b := (I + P) + s + 4 + 1)
          (le_trans (hbl v) (pow_bnd_mono hS (by omega)))
          (pow_bnd_add hS (pow_bnd_mul (le_trans (pow_bnd_const hS v)
            (pow_bnd_mono hS (by omega))) hSzS) (pow_bnd_const hS 4))) ?_
        exact pow_bnd_mono hS (by omega)
      refine le_trans hasz ?_
      have hsum1 : bl ^ (v + 1) * ((v + 1) * Sz + 4) + bl ^ v * (v * Sz + 4)
          ≤ S ^ (4 * (I + P) + 2 * s + 13) :=
        le_trans (pow_bnd_add hS h1 h2) (pow_bnd_mono hS (by omega))
      have hsum2 : bl ^ (v + 1) * ((v + 1) * Sz + 4) + bl ^ v * (v * Sz + 4) + 2
          ≤ S ^ (4 * (I + P) + 2 * s + 16) :=
        le_trans (pow_bnd_add hS hsum1 (pow_bnd_const hS 2)) (pow_bnd_mono hS (by omega))
      have hsum3 : 2 * (bl ^ (v + 1) * ((v + 1) * Sz + 4) + bl ^ v * (v * Sz + 4) + 2)
          ≤ S ^ (4 * (I + P) + 2 * s + 18) :=
        le_trans (pow_bnd_mul (pow_bnd_const hS 2) hsum2) (pow_bnd_mono hS (by omega))
      exact le_trans (pow_bnd_add hS hsum3 (pow_bnd_const hS 2)) (pow_bnd_mono hS (by omega))
    · intro x
      rw [haacc x]
      unfold CountSpec
      rw [if_pos hvI]
  · obtain ⟨a₁, h1wf, h1lay, h1sz, h1acc⟩ := exists_acc_countGe (j := I) fam hwf hlay hsz
    obtain ⟨a₂, h2wf, h2lay, h2sz, h2acc⟩ :=
      exists_acc_countMod hmpos hP2 hPm fam hwf hlay hsz v
    have hb1 : a₁.gateCount ≤ S ^ (2 * (I + P) + s + 8) := by
      have hbl : bl ^ I ≤ S ^ I := Nat.pow_le_pow_left hblS I
      have hx : bl ^ I * (I * Sz + 4) ≤ S ^ (2 * (I + P) + s + 6) := by
        refine le_trans (pow_bnd_mul (a := I + P) (b := (I + P) + s + 4 + 1)
          (le_trans hbl (pow_bnd_mono hS (by omega)))
          (pow_bnd_add hS (pow_bnd_mul (le_trans (pow_bnd_const hS I)
            (pow_bnd_mono hS (by omega))) hSzS) (pow_bnd_const hS 4))) ?_
        exact pow_bnd_mono hS (by omega)
      exact le_trans h1sz
        (le_trans (pow_bnd_add hS hx (pow_bnd_const hS 1)) (pow_bnd_mono hS (by omega)))
    have hb2 : a₂.gateCount ≤ S ^ (m * P + m + P + s + 20) := by
      have hSz1 : Sz + 1 ≤ S ^ (s + 2) :=
        le_trans (pow_bnd_add hS hSzS (pow_bnd_const hS 1)) (pow_bnd_mono hS (by omega))
      have hblpow : bl ≤ S ^ 1 := by simpa using hblS
      have hi1 : bl * (Sz + 1) ≤ S ^ (s + 3) :=
        le_trans (pow_bnd_mul hblpow hSz1) (pow_bnd_mono hS (by omega))
      have hi2 : bl * (Sz + 1) + m + 1 ≤ S ^ (s + m + 8) := by
        have ha := pow_bnd_add hS hi1 (pow_bnd_const hS m)
        have hb := pow_bnd_add hS ha (pow_bnd_const hS 1)
        exact le_trans hb (pow_bnd_mono hS (by omega))
      have hi3 : (P + 1) * (bl * (Sz + 1) + m + 1) ≤ S ^ (P + s + m + 10) :=
        le_trans (pow_bnd_mul (pow_bnd_const hS (P + 1)) hi2) (pow_bnd_mono hS (by omega))
      have hi4 : (P + 1) * (bl * (Sz + 1) + m + 1) + 1 ≤ S ^ (P + s + m + 13) :=
        le_trans (pow_bnd_add hS hi3 (pow_bnd_const hS 1)) (pow_bnd_mono hS (by omega))
      have hi5 : m ^ P * ((P + 1) * (bl * (Sz + 1) + m + 1) + 1)
          ≤ S ^ (m * P + P + s + m + 15) := by
        have hmP : m ^ P ≤ S ^ (m * P) := pow_bnd_pow (pow_bnd_const hS m)
        exact le_trans (pow_bnd_mul hmP hi4) (pow_bnd_mono hS (by omega))
      exact le_trans h2sz
        (le_trans (pow_bnd_add hS hi5 (pow_bnd_const hS 1)) (pow_bnd_mono hS (by omega)))
    set pair : Fin 2 → ACCCircuit n m := fun i => if (i : Nat) = 0 then a₁ else a₂ with hpair
    have hp0 : pair 0 = a₁ := by simp [hpair]
    have hp1 : pair 1 = a₂ := by simp [hpair]
    have hicases : ∀ i : Fin 2, i = 0 ∨ i = 1 := by
      intro i
      rcases (show (i : Nat) = 0 ∨ (i : Nat) = 1 from by omega) with hi | hi
      · exact Or.inl (Fin.ext (by simp [hi]))
      · exact Or.inr (Fin.ext (by simp [hi]))
    have hpwf : ∀ i, WellFormedACC (pair i) := by
      intro i; rcases hicases i with rfl | rfl
      · rw [hp0]; exact h1wf
      · rw [hp1]; exact h2wf
    have hplay : ∀ i q, (pair i).layer q ≤ max d 1 + 8 := by
      intro i; rcases hicases i with rfl | rfl
      · rw [hp0]; exact fun q => le_trans (h1lay q) (by omega)
      · rw [hp1]; exact fun q => le_trans (h2lay q) (by omega)
    have hpsz : ∀ i, (pair i).gateCount ≤ S ^ (4 * (I + P) + 2 * s + m * P + m + P + 24) := by
      intro i; rcases hicases i with rfl | rfl
      · rw [hp0]; exact le_trans hb1 (pow_bnd_mono hS (by omega))
      · rw [hp1]; exact le_trans hb2 (pow_bnd_mono hS (by omega))
    obtain ⟨a, hawf, halay, hasz, haacc⟩ := exists_acc_bigAnd pair hpwf hplay hpsz
    refine ⟨a, hawf, fun q => le_trans (halay q) (by omega), ?_, ?_⟩
    · refine le_trans hasz ?_
      have hmul : 2 * S ^ (4 * (I + P) + 2 * s + m * P + m + P + 24)
          ≤ S ^ (4 * (I + P) + 2 * s + m * P + m + P + 26) :=
        le_trans (pow_bnd_mul (pow_bnd_const hS 2) (le_refl _)) (pow_bnd_mono hS (by omega))
      exact le_trans (pow_bnd_add hS hmul (pow_bnd_const hS 2)) (pow_bnd_mono hS (by omega))
    · intro x
      rw [haacc x]
      unfold CountSpec
      rw [if_neg hvI]
      constructor
      · intro h
        have hA := (h1acc x).mp (by have := h 0; rwa [hp0] at this)
        have hB := (h2acc x).mp (by have := h 1; rwa [hp1] at this)
        exact ⟨hA, hB⟩
      · rintro ⟨hA, hB⟩ i
        rcases hicases i with rfl | rfl
        · rw [hp0]; exact (h1acc x).mpr hA
        · rw [hp1]; exact (h2acc x).mpr hB

/-- The profile value is determined by the count it specifies. -/
theorem profOf_eq_of_countSpec {I P v cnt : Nat} (hv : v < I + P)
    (h : CountSpec I P v cnt) : profOf I P cnt = v := by
  unfold CountSpec at h
  unfold profOf
  by_cases hvI : v < I
  · rw [if_pos hvI] at h
    rw [h, if_pos hvI]
  · rw [if_neg hvI] at h
    obtain ⟨hIc, hmod⟩ := h
    rw [if_neg (by omega : ¬ cnt < I)]
    have hmodeq : (cnt - I) % P = (v - I) % P := by
      have h1 : cnt - I + I = cnt := by omega
      have h2 : v - I + I = v := by omega
      have : (cnt - I + I) % P = (v - I + I) % P := by rw [h1, h2]; exact hmod
      exact Nat.ModEq.add_right_cancel' I this
    rw [hmodeq, Nat.mod_eq_of_lt (by omega : v - I < P)]
    omega

/-- The product of a block of a commutative monoid word, as a product over a
finite index type. -/
theorem blockProd_eq_prod {M : Type} [CommMonoid M] {n : Nat}
    (letter : Nat → (Fin n → Bool) → M) (start a b : Nat) (x : Fin n → Bool) :
    blockProd letter start a b x = ∏ p : Fin (b - a), letter (start + a + p) x := by
  rw [blockProd, map_range'_eq_ofFn (fun i => letter i x) (b - a) (start + a), List.prod_ofFn]

/-! ## The value of a commutative block -/

/-- **The value of a block of a commutative monoid word is `ACC`-recognisable.**
The circuit guesses the profile of the block — for every letter, its number of
occurrences truncated at the index and taken modulo the period — checks it with
the count gadgets, and accepts if the resulting product is the target value. -/
theorem exists_acc_prod_comm {M : Type} [CommMonoid M] [Fintype M] {n Mod : Nat}
    (hModpos : 0 < Mod) {I P : Nat} (hP2 : 2 ≤ P) (hPMod : P ∣ Mod)
    (hpow : ∀ (g : M) (k : Nat), I ≤ k → g ^ (k + P) = g ^ k)
    {d Sz S s bl : Nat} (hS : 2 ≤ S) (hblS : bl ≤ S) (hSzS : Sz ≤ S ^ s)
    (pos : Fin bl → Nat) (letter : Nat → (Fin n → Bool) → M)
    (L : Nat → M → ACCCircuit n Mod)
    (hLwf : ∀ i g, WellFormedACC (L i g))
    (hLlay : ∀ i g q, (L i g).layer q ≤ d)
    (hLsz : ∀ i g, (L i g).gateCount ≤ Sz)
    (hLacc : ∀ i g x, ACCAccepts (L i g) x ↔ letter i x = g)
    (target : M) :
    ∃ c : ACCCircuit n Mod,
      WellFormedACC c ∧ (∀ q, c.layer q ≤ max d 1 + 14) ∧
      c.gateCount ≤ S ^ ((I + P) ^ Fintype.card M +
        (Fintype.card M + (4 * (I + P) + 2 * s + Mod * P + Mod + P + 30) + 3) + 5) ∧
      (∀ x, ACCAccepts c x ↔ (∏ p : Fin bl, letter (pos p) x) = target) := by
  classical
  have hPpos : 0 < P := by omega
  set E1 := 4 * (I + P) + 2 * s + Mod * P + Mod + P + 30 with hE1
  set cnt : M → (Fin n → Bool) → Nat := fun g x =>
    (Finset.univ.filter fun p : Fin bl => ACCAccepts (L (pos p) g) x).card with hcntdef
  -- the profile determines the product of the block
  have hkey : ∀ x, (∏ g : M, g ^ profOf I P (cnt g x)) = ∏ p : Fin bl, letter (pos p) x := by
    intro x
    rw [prod_eq_prod_pow_card (fun p : Fin bl => letter (pos p) x)]
    refine Finset.prod_congr rfl fun g _ => ?_
    have hfil : (Finset.univ.filter fun p : Fin bl => letter (pos p) x = g)
        = (Finset.univ.filter fun p : Fin bl => ACCAccepts (L (pos p) g) x) := by
      refine Finset.filter_congr ?_
      intro p _
      simp [hLacc (pos p) g x]
    rw [hfil]
    exact (pow_eq_pow_of_countSpec hpow g (countSpec_profOf hPpos)).symm
  -- the profile of an input
  set prof : (Fin n → Bool) → (M → Fin (I + P)) := fun x g =>
    ⟨profOf I P (cnt g x), profOf_lt hPpos⟩ with hprofdef
  -- one count specification, for one letter
  have hspec : ∀ (pr : M → Fin (I + P)) (g : M), ∃ c : ACCCircuit n Mod,
      WellFormedACC c ∧ (∀ q, c.layer q ≤ max d 1 + 10) ∧ c.gateCount ≤ S ^ E1 ∧
      (∀ x, ACCAccepts c x ↔ CountSpec I P ((pr g : Nat)) (cnt g x)) := by
    intro pr g
    exact exists_acc_countSpec hModpos hP2 hPMod hS hblS hSzS (fun p => L (pos p) g)
      (fun p => hLwf _ _) (fun p q => hLlay _ _ q) (fun p => hLsz _ _) (pr g).isLt
  choose C hCwf hClay hCsz hCacc using hspec
  -- the full profile check
  set ee := Fintype.equivFin M with heedef
  have hprofrec : ∀ pr : M → Fin (I + P), ∃ c : ACCCircuit n Mod,
      WellFormedACC c ∧ (∀ q, c.layer q ≤ max d 1 + 12) ∧
      c.gateCount ≤ S ^ (Fintype.card M + E1 + 3) ∧
      (∀ x, ACCAccepts c x ↔ prof x = pr) := by
    intro pr
    obtain ⟨c, hcwf, hclay, hcsz, hcacc⟩ :=
      exists_acc_bigAnd (fun i : Fin (Fintype.card M) => C pr (ee.symm i))
        (fun i => hCwf _ _) (fun i => hClay _ _) (fun i => hCsz _ _)
    refine ⟨c, hcwf, fun q => le_trans (hclay q) (by omega), ?_, ?_⟩
    · refine le_trans hcsz ?_
      have h1 : Fintype.card M * S ^ E1 ≤ S ^ (Fintype.card M + E1) :=
        pow_bnd_mul (pow_bnd_const hS _) (le_refl _)
      exact le_trans (pow_bnd_add hS h1 (pow_bnd_const hS 2)) (pow_bnd_mono hS (by omega))
    · intro x
      rw [hcacc x]
      constructor
      · intro h
        funext g
        have hg := (hCacc pr g x).mp (by simpa using h (ee g))
        have := profOf_eq_of_countSpec (pr g).isLt hg
        exact Fin.ext (by simpa [hprofdef] using this)
      · intro h i
        refine (hCacc pr (ee.symm i) x).mpr ?_
        have hval : (pr (ee.symm i) : Nat) = profOf I P (cnt (ee.symm i) x) := by
          rw [← h]
        rw [hval]
        exact countSpec_profOf hPpos
  choose Bp hBpwf hBplay hBpsz hBpacc using hprofrec
  -- guess the profile
  obtain ⟨c, hcwf, hclay, hcsz, hcacc⟩ :=
    exists_acc_letterPred (G := M → Fin (I + P)) (d := max d 1 + 12)
      (Sz := S ^ (Fintype.card M + E1 + 3)) Bp prof
      (fun pr => (∏ g : M, g ^ (pr g : Nat)) = target)
      hBpwf hBplay hBpsz hBpacc
  refine ⟨c, hcwf, fun q => le_trans (hclay q) (by omega), ?_, ?_⟩
  · refine le_trans hcsz ?_
    have hcard : Fintype.card (M → Fin (I + P)) = (I + P) ^ Fintype.card M := by
      simp
    rw [hcard]
    have h1 : S ^ (Fintype.card M + E1 + 3) + 2 ≤ S ^ (Fintype.card M + E1 + 3 + 3) :=
      le_trans (pow_bnd_add hS (le_refl _) (pow_bnd_const hS 2)) (pow_bnd_mono hS (by omega))
    have h2 : (I + P) ^ Fintype.card M * (S ^ (Fintype.card M + E1 + 3) + 2)
        ≤ S ^ ((I + P) ^ Fintype.card M + (Fintype.card M + E1 + 3 + 3)) :=
      pow_bnd_mul (pow_bnd_const hS _) h1
    exact le_trans (pow_bnd_add hS h2 (pow_bnd_const hS 1)) (pow_bnd_mono hS (by omega))
  · intro x
    rw [hcacc x]
    constructor
    · intro h
      rw [← hkey x, ← h]
    · intro h
      rw [← h, ← hkey x]

/-! ## The word problem of a finite commutative monoid -/

/-- The size exponent produced by the commutative construction, for a monoid
with `cM` elements, index `I` and period `P`. -/
def commWordExponent (cM I P : Nat) : Nat :=
  (I + P) ^ cM + (cM + (4 * (I + P) + 2 * (2 * P + 3) + 2 * P * P + 2 * P + P + 30) + 3) + 5

/-- **The word problem of a finite commutative monoid is in `ACC⁰`.** -/
theorem monoidWordACC_of_comm (M : Type) [CommMonoid M] [Finite M] : MonoidWordACC M := by
  classical
  haveI : Fintype M := Fintype.ofFinite M
  obtain ⟨I, P0, hP0, hpow0⟩ := exists_index_period M
  have hP2 : 2 ≤ 2 * P0 := by omega
  have hpow : ∀ (g : M) (k : Nat), I ≤ k → g ^ (k + 2 * P0) = g ^ k :=
    fun g k hk => pow_add_mul_period (hpow0 g) 2 k hk
  refine ⟨2 * (2 * P0), 20, commWordExponent (Fintype.card M) I (2 * P0), by omega, ?_⟩
  intro n letter size hrec start len
  have hModpos : 0 < 2 * (2 * P0) := by omega
  have hdvd2 : (2 : Nat) ∣ 2 * (2 * P0) := ⟨2 * P0, rfl⟩
  have hPMod : 2 * P0 ∣ 2 * (2 * P0) := ⟨2, by ring⟩
  -- the letter recognisers, lifted to the modulus of the construction
  have hletter : ∀ (i : Nat) (g : M), ∃ a : ACCCircuit n (2 * (2 * P0)),
      WellFormedACC a ∧ (∀ q, a.layer q ≤ 6) ∧
      a.gateCount ≤ (2 * (2 * P0) + 2) * size ∧
      (∀ x, ACCAccepts a x ↔ letter i x = g) := by
    intro i g
    obtain ⟨b, hbwf, hblay, hbsz, hbacc⟩ := hrec i g
    refine ⟨accModulusLift b hdvd2, wellFormedACC_accModulusLift b hdvd2 hbwf, ?_, ?_, ?_⟩
    · intro q
      exact le_trans (accModulusLift_layer_le (c := b) (hM := hdvd2) (d := 2) hblay q) (by omega)
    · exact le_trans (accModulusLift_gateCount_le b hdvd2) (Nat.mul_le_mul_left _ hbsz)
    · intro x
      rw [evalACC_accModulusLift_of_pos hModpos hbwf x]
      exact hbacc x
  choose L hLwf hLlay hLsz hLacc using hletter
  have hS : 2 ≤ size + len + 2 := by omega
  have hsize1 : size ≤ (size + len + 2) ^ 1 := by rw [pow_one]; omega
  have hSzS : (2 * (2 * P0) + 2) * size ≤ (size + len + 2) ^ (2 * (2 * P0) + 3) :=
    le_trans (pow_bnd_mul (pow_bnd_const hS (2 * (2 * P0) + 2)) hsize1)
      (pow_bnd_mono hS (by omega))
  have main : ∀ (a b : Nat) (g : M), ∃ c : ACCCircuit n (2 * (2 * P0)),
      WellFormedACC c ∧ (∀ q, c.layer q ≤ 20) ∧
      c.gateCount ≤ (size + len + 2) ^ commWordExponent (Fintype.card M) I (2 * P0) ∧
      (∀ x, ACCAccepts c x → blockProd letter start a b x = g) ∧
      (b - a ≤ len → ∀ x, ACCAccepts c x ↔ blockProd letter start a b x = g) := by
    intro a b g
    by_cases hbl : b - a ≤ len
    · obtain ⟨c, hcwf, hclay, hcsz, hcacc⟩ :=
        exists_acc_prod_comm (M := M) (Mod := 2 * (2 * P0)) hModpos hP2 hPMod hpow
          (d := 6) (Sz := (2 * (2 * P0) + 2) * size) (S := size + len + 2)
          (s := 2 * (2 * P0) + 3) (bl := b - a) hS (by omega) hSzS
          (fun p => start + a + p) letter L hLwf hLlay hLsz hLacc g
      refine ⟨c, hcwf, fun q => le_trans (hclay q) (by omega), hcsz, ?_, ?_⟩
      · intro x hx
        rw [blockProd_eq_prod]
        exact (hcacc x).mp hx
      · intro _ x
        rw [blockProd_eq_prod]
        exact hcacc x
    · refine ⟨accConst n (2 * (2 * P0)) false,
        wellFormedACC_accConst n (2 * (2 * P0)) false, ?_, ?_, ?_, ?_⟩
      · intro q; rw [accConst_layer]; omega
      · rw [accConst_gateCount]; exact Nat.one_le_pow _ _ (by omega)
      · intro x hx
        exact absurd ((accAccepts_accConst n (2 * (2 * P0)) false x).mp hx) (by simp)
      · intro h; exact absurd h hbl
  choose B hBwf hBlay hBsz hBsound hBcomp using main
  refine ⟨B, hBwf, hBlay, hBsz, hBsound, ?_⟩
  intro x a b hab hbl
  exact (hBcomp a b _ (by omega) x).mpr rfl

/-- **Sanity witness.**  The interface `MonoidWordACC` is met by a nontrivial
monoid: the cyclic group of order `k`, written multiplicatively. -/
theorem monoidWordACC_multiplicative_zmod (k : Nat) [NeZero k] :
    MonoidWordACC (Multiplicative (ZMod k)) :=
  monoidWordACC_of_comm _

end Internal
end AllenderOQ3
