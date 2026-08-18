import AllenderOQ3.Internal.LocalDivisorMarked
import AllenderOQ3.Internal.PredCirc
import AllenderOQ3.Internal.MonoidWordACCGen

/-!
# The marked local-divisor compression lemma

`MonoidWordACCGenOn M A` is the generalized word-problem interface restricted
to words whose letters provably lie in `A`.  S2 and S3 of
`docs/LOCAL_DIVISOR_PLAN.md` are the circuit half of the local-divisor
induction; both are proved below:

* **S2 `monoidWordACCGen_compression`** (proved) — from `MonoidWordACCGen` for the
  submonoid `⟨B⟩` and for the local divisor `M_c`, conclude the generalized
  property for words over `⟨B⟩ ∪ {c}`.  The construction is block-local: for a
  requested block, the positions of `c` inside the block are guessed, gaps are
  evaluated by the recursive `⟨B⟩` circuits (mapping `c ↦ 1`, with a
  no-`c`-between conjunction), and the sequence of derived letters
  `c * (gap) * c : LocalDivisor c` is evaluated by the recursive `M_c`
  circuits.  A derived word must be built separately for every requested
  block: a `c` beyond the right endpoint changes the answer (Rees-quotient
  counterexample, `docs/LOCAL_DIVISOR_PLAN.md` §3).  Soundness must hold for
  every `(a, b)`; completeness only on the promised window; out-of-window
  blocks use the constantly-false circuit as in `RTrivialWordACC`.
* **S3 `monoidWordACCGen_of_genOn`** (proved) — the representation-expansion
  wrapper:
  if `A` contains `1` and generates `M`, the alphabet-restricted property
  yields the full one (replace each letter by a fixed padded generator word;
  recognizers of expanded letters are ORs of the original ones).

The algebraic factorization behind S2 is proved in `localDivisor_telescope`
here and in `LocalDivisorMarked.lean`, and the circuit bookkeeping it uses is
the `HasPredCirc` layer of `PredCirc.lean`.  Everything here is `sorry`-free.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace AllenderOQ3
namespace Internal

/-- The generalized interface restricted to letters from `A`. -/
def MonoidWordACCGenOn (M : Type) [Monoid M] [Finite M] (A : Set M) : Prop :=
  ∀ m_in d_in : Nat, 2 ≤ m_in → 2 ≤ d_in →
  ∃ m_out d_out exponent : Nat,
    2 ≤ m_out ∧ m_in ∣ m_out ∧
      ∀ {n : Nat} (letter : Nat → (Fin n → Bool) → M) (size : Nat),
        (∀ (i : Nat) (x : Fin n → Bool), letter i x ∈ A) →
        (∀ (i : Nat) (mm : M),
          ∃ a : ACCCircuit n m_in,
            WellFormedACC a ∧
            (∀ q, a.layer q ≤ d_in) ∧
            a.gateCount ≤ size ∧
            (∀ x, ACCAccepts a x ↔ letter i x = mm)) →
        ∀ start len : Nat,
          ∃ B : Nat → Nat → M → ACCCircuit n m_out,
            (∀ a b g, WellFormedACC (B a b g)) ∧
            (∀ a b g q, (B a b g).layer q ≤ d_out) ∧
            (∀ a b g, (B a b g).gateCount ≤ (size + len + 2) ^ exponent) ∧
            (∀ (a b : Nat) (g : M) (x : Fin n → Bool),
              ACCAccepts (B a b g) x → blockProd letter start a b x = g) ∧
            (∀ (x : Fin n → Bool) (a b : Nat), a ≤ b → b ≤ len →
              ACCAccepts (B a b (blockProd letter start a b x)) x)

/-- The unrestricted interface gives the restricted one for any alphabet. -/
theorem monoidWordACCGenOn_of_gen {M : Type} [Monoid M] [Finite M]
    (H : MonoidWordACCGen M) (A : Set M) : MonoidWordACCGenOn M A := by
  intro m_in d_in hm hd
  obtain ⟨m_out, d_out, e, hm2, hdiv, hcore⟩ := H m_in d_in hm hd
  exact ⟨m_out, d_out, e, hm2, hdiv, fun letter size _ hrec start len =>
    hcore letter size hrec start len⟩

/-- The restricted interface on the full alphabet gives the unrestricted
one. -/
theorem monoidWordACCGen_of_genOn_univ {M : Type} [Monoid M] [Finite M]
    (H : MonoidWordACCGenOn M Set.univ) : MonoidWordACCGen M := by
  intro m_in d_in hm hd
  obtain ⟨m_out, d_out, e, hm2, hdiv, hcore⟩ := H m_in d_in hm hd
  exact ⟨m_out, d_out, e, hm2, hdiv, fun letter size hrec start len =>
    hcore letter size (fun _ _ => Set.mem_univ _) hrec start len⟩

/-! ## The algebraic factorization -/

/-- **Telescoping of local-divisor letters**: multiplying elements of
`LocalDivisor c` multiplies out to the underlying `M`-product with single
`c`-separators.  `(c*u₁*c) ∘ (c*u₂*c) ∘ … = c*u₁*c*u₂*c*…*c`. -/
theorem localDivisor_telescope {M : Type} [Monoid M] {c : M}
    (p q : LocalDivisor c) {y : M} (hy : q.val = c * y) :
    (p * q).val = p.val * y :=
  LocalDivisor.mul_val' hy

set_option maxHeartbeats 2000000 in
/-- **S2: the marked compression lemma.**  For a requested block `[a, b)` the
circuit guesses the first and the last mark `p'`, `q'` of the block, the two
mark-free end gaps (evaluated in `⟨B⟩` by the recursive circuits `BN` of the
mark-free word `unmarkedLetter`), and the value of the derived word
`derivLetter c lett b` between the two marks (evaluated in `LocalDivisor c` by
the recursive circuits `BD`, one family per right endpoint `b`).  Soundness
and completeness are exactly `blockProd_marked_split` and
`blockProd_unmarkedLetter` of `LocalDivisorMarked.lean`; the quantitative
discipline (`(size + len + 2) ^ exponent`, constant depth, soundness
everywhere / completeness on the window) is tracked through the `HasPredCirc`
combinators and the `pow_bnd_*` lemmas. -/
theorem monoidWordACCGen_compression {M : Type} [Monoid M] [Finite M] (c : M)
    (B : Set M)
    (hN : MonoidWordACCGen (Submonoid.closure B))
    (hMc : MonoidWordACCGen (LocalDivisor c)) :
    MonoidWordACCGenOn M (insert c (Submonoid.closure B : Set M)) := by
  classical
  haveI : Fintype M := Fintype.ofFinite M
  haveI : Fintype (LocalDivisor c) := Fintype.ofFinite _
  haveI : Fintype (Submonoid.closure B : Submonoid M) := Fintype.ofFinite _
  intro m_in d_in hm hd
  set NN : Submonoid M := Submonoid.closure B with hNNdef
  set d1 : Nat := max d_in 1 + 2 with hd1def
  set d2 : Nat := d1 + 2 with hd2def
  obtain ⟨m_N, d_N, e_N, hm_N, hdvd_N, hcoreN⟩ := hN m_in d1 hm (by omega)
  set dd : Nat := max (2 * d2 + 2) d_N with hdddef
  obtain ⟨m_D, d_D, e_D, hm_D, hdvd_D, hcoreD⟩ := hMc m_N (dd + 6) hm_N (by omega)
  set dfin : Nat := max (2 * d2 + 2) (max (2 * d_N + 2) (max d_D 1)) with hdfindef
  set p1 : Nat := Fintype.card M + 2 with hp1def
  set p2 : Nat := p1 + 3 with hp2def
  set pN : Nat := (p1 + 2) * e_N with hpNdef
  set p3 : Nat := m_N + 2 + p2 + pN + 1 with hp3def
  set p4 : Nat := Fintype.card NN + p3 + 11 with hp4def
  set pD : Nat := (p4 + 2) * e_D with hpDdef
  set p5 : Nat := m_D + 2 + p2 + pN + pD with hp5def
  set pG : Nat := 3 * Fintype.card NN + Fintype.card (LocalDivisor c) + 3 with hpGdef
  refine ⟨m_D, dfin + 8, pG + p5 + 10, hm_D, dvd_trans hdvd_N hdvd_D, ?_⟩
  intro n letter size hA hrec start len
  set S : Nat := size + len + 2 with hSdef
  have hS2 : 2 ≤ S := by omega
  have hpow2 : ∀ k : Nat, 2 ^ k ≤ S ^ k := fun k => Nat.pow_le_pow_left hS2 k
  have hSp : ∀ k : Nat, 1 ≤ S ^ k := fun k => Nat.one_le_pow _ _ (by omega)
  have hone : (1 : Nat) ≤ S ^ 0 := by simp
  have hlenS : len + 1 ≤ S ^ 1 := by rw [pow_one]; omega
  have hlen2S : len + 2 ≤ S ^ 1 := by rw [pow_one]; omega
  have hsizeS : size + 2 ≤ S ^ 1 := by rw [pow_one]; omega
  -- relative coordinates
  set lett : Nat → (Fin n → Bool) → M := fun i x => letter (start + i) x with hlettdef
  have hlettA : ∀ (i : Nat) (x : Fin n → Bool), lett i x = c ∨ lett i x ∈ NN := by
    intro i x
    rcases Set.mem_insert_iff.mp (hA (start + i) x) with h | h
    · exact Or.inl h
    · exact Or.inr h
  -- letter recognisers, and arbitrary predicates of a letter value
  choose Lc hLwf hLlay hLsz hLacc using hrec
  have hSz1 : Fintype.card M * (size + 2) + 1 ≤ S ^ p1 := by
    have h1 : Fintype.card M ≤ S ^ Fintype.card M := pow_bnd_const hS2 _
    have h2 := pow_bnd_mul h1 hsizeS
    have h4 := pow_bnd_add hS2 h2 hone
    exact le_trans h4 (pow_bnd_mono hS2 (by omega))
  have hpred : ∀ (i : Nat) (P : M → Prop),
      HasPredCirc n m_in d1 (S ^ p1) (fun x => P (lett i x)) := by
    intro i P
    have h := hasPredCirc_ofLetter (n := n) (m := m_in) (G := M) (fun x => lett i x)
      (Lc (start + i))
      (fun g => ⟨hLwf (start + i) g, hLlay (start + i) g, hLsz (start + i) g,
        fun x => hLacc (start + i) g x⟩) P
    exact h.mono (by omega) hSz1 (fun x => Iff.rfl)
  -- mark-free ranges
  have hSz2 : (len + 1) * S ^ p1 + 2 ≤ S ^ p2 := by
    have h1 := pow_bnd_mul hlenS (le_refl (S ^ p1))
    have h2 : (2 : Nat) ≤ S ^ 1 := by rw [pow_one]; omega
    have h3 := pow_bnd_add hS2 h1 h2
    exact le_trans h3 (pow_bnd_mono hS2 (by omega))
  have hfree : ∀ s t : Nat, t ≤ len + 1 →
      HasPredCirc n m_in d2 (S ^ p2) (fun x => ∀ i, s ≤ i → i < t → lett i x ≠ c) := by
    intro s t ht
    have hcomp : ∀ j : Fin (len + 1),
        HasPredCirc n m_in d1 (S ^ p1)
          (fun x => s ≤ (j : Nat) → (j : Nat) < t → lett (j : Nat) x ≠ c) :=
      fun j => hpred (j : Nat) (fun g => s ≤ (j : Nat) → (j : Nat) < t → g ≠ c)
    refine (hasPredCirc_bigAnd hcomp).mono (by omega) hSz2 ?_
    intro x
    constructor
    · intro hx i hsi hit
      exact hx ⟨i, by omega⟩ hsi hit
    · intro hx j hsj hjt
      exact hx _ hsj hjt
  -- the mark-free word inside `NN`, and its block circuits
  set uw : Nat → (Fin n → Bool) → NN := unmarkedLetter c NN lett with huwdef
  have hrecUW : ∀ (i : Nat) (v : NN), ∃ a : ACCCircuit n m_in,
      WellFormedACC a ∧ (∀ q, a.layer q ≤ d1) ∧ a.gateCount ≤ S ^ p1 ∧
      (∀ x, ACCAccepts a x ↔ uw i x = v) := by
    intro i v
    obtain ⟨a, ha⟩ := hpred i (fun g => unmarkedVal c NN g = v)
    exact ⟨a, ha.wf, ha.lay, ha.sz, fun x => ha.acc x⟩
  obtain ⟨BN, hBNwf, hBNlay, hBNsz, hBNsound, hBNcomp⟩ :=
    hcoreN (n := n) uw (S ^ p1) hrecUW 0 len
  have hBNszS : ∀ (a b : Nat) (v : NN), (BN a b v).gateCount ≤ S ^ pN := by
    intro a b v
    refine le_trans (hBNsz a b v) ?_
    have h1 : S ^ p1 + len + 2 ≤ S ^ (p1 + 2) := by
      have h2 := pow_bnd_add hS2 (le_refl (S ^ p1)) hlen2S
      exact le_trans (by omega) (le_trans h2 (pow_bnd_mono hS2 (by omega)))
    exact pow_bnd_pow h1
  have hBNpred : ∀ (a b : Nat) (v : NN), a ≤ b → b ≤ len →
      HasPredCirc n m_N d_N (S ^ pN) (fun x => blockProd uw 0 a b x = v) := by
    intro a b v hab hbl
    refine ⟨BN a b v, ⟨hBNwf a b v, hBNlay a b v, hBNszS a b v, ?_⟩⟩
    intro x
    constructor
    · intro hx; exact hBNsound a b v x hx
    · intro hx; rw [← hx]; exact hBNcomp x a b hab hbl
  -- the three component families at modulus `m_N`
  have hliftN : ∀ (dq Szq : Nat) (P : (Fin n → Bool) → Prop),
      HasPredCirc n m_in dq Szq P → 2 * dq + 2 ≤ dd → (m_N + 2) * Szq ≤ S ^ p3 →
      HasPredCirc n m_N dd (S ^ p3) P := by
    intro dq Szq P h hdq hsq
    exact (h.lift hdvd_N (by omega)).mono hdq hsq (fun x => Iff.rfl)
  have hmulN1 : (m_N + 2) * S ^ p1 ≤ S ^ p3 := by
    have h1 : m_N + 2 ≤ S ^ (m_N + 2) := pow_bnd_const hS2 _
    exact le_trans (pow_bnd_mul h1 (le_refl (S ^ p1))) (pow_bnd_mono hS2 (by omega))
  have hmulN2 : (m_N + 2) * S ^ p2 ≤ S ^ p3 := by
    have h1 : m_N + 2 ≤ S ^ (m_N + 2) := pow_bnd_const hS2 _
    exact le_trans (pow_bnd_mul h1 (le_refl (S ^ p2))) (pow_bnd_mono hS2 (by omega))
  have hMkN : ∀ k : Nat, HasPredCirc n m_N dd (S ^ p3) (fun x => lett k x = c) := by
    intro k
    exact hliftN d1 (S ^ p1) _ (hpred k (fun g => g = c)) (by omega) hmulN1
  have hNotMkN : ∀ k : Nat, HasPredCirc n m_N dd (S ^ p3) (fun x => lett k x ≠ c) := by
    intro k
    exact hliftN d1 (S ^ p1) _ (hpred k (fun g => g ≠ c)) (by omega) hmulN1
  have hFreeN : ∀ s t : Nat, t ≤ len + 1 →
      HasPredCirc n m_N dd (S ^ p3) (fun x => ∀ i, s ≤ i → i < t → lett i x ≠ c) := by
    intro s t ht
    exact hliftN d2 (S ^ p2) _ (hfree s t ht) (by omega) hmulN2
  have hBNN : ∀ (p q : Nat) (v : NN), p ≤ q → q ≤ len →
      HasPredCirc n m_N dd (S ^ p3) (fun x => blockProd uw 0 p q x = v) := by
    intro p q v h1 h2
    exact (hBNpred p q v h1 h2).mono (by omega) (pow_bnd_mono hS2 (by omega)) (fun x => Iff.rfl)
  -- the derived-letter recognisers of the window `[·, b)`
  have hderiv : ∀ b : Nat, b ≤ len → ∀ (i : Nat) (v : LocalDivisor c),
      HasPredCirc n m_N (dd + 6) (S ^ p4) (fun x => derivLetter c lett b i x = v) := by
    intro b hb i v
    have hguess : ∀ u : (Fin (len + 1) × NN) ⊕ Bool,
        HasPredCirc n m_N (dd + 4) (S ^ (p3 + 6))
          (fun x => match u with
            | Sum.inl ju =>
                (i < (ju.1 : Nat) ∧ (ju.1 : Nat) < b ∧
                    LocalDivisor.gap c ((ju.2 : NN) : M) = v) ∧
                  ((lett i x = c ∧ lett (ju.1 : Nat) x = c) ∧
                    ((∀ t, i + 1 ≤ t → t < (ju.1 : Nat) → lett t x ≠ c) ∧
                      blockProd uw 0 (i + 1) (ju.1 : Nat) x = ju.2))
            | Sum.inr false =>
                v = 1 ∧ (lett i x = c ∧ ∀ t, i + 1 ≤ t → t < b → lett t x ≠ c)
            | Sum.inr true => v = 1 ∧ lett i x ≠ c) := by
      intro u
      have hbig : 2 * (2 * S ^ p3 + 2) + 2 ≤ S ^ (p3 + 6) := by
        have h4 : (4 : Nat) ≤ S ^ 2 := le_trans (by norm_num) (hpow2 2)
        have h6 : (6 : Nat) ≤ S ^ 3 := le_trans (by norm_num) (hpow2 3)
        have h1 := pow_bnd_mul h4 (le_refl (S ^ p3))
        have h2 := pow_bnd_add hS2 h1 h6
        have h3 : 2 * (2 * S ^ p3 + 2) + 2 = 4 * S ^ p3 + 6 := by ring
        rw [h3]
        exact le_trans h2 (pow_bnd_mono hS2 (by omega))
      have hsmall : 2 * S ^ p3 + 2 ≤ S ^ (p3 + 6) := by
        have := hSp p3
        omega
      have hsmall0 : S ^ p3 ≤ S ^ (p3 + 6) := pow_bnd_mono hS2 (by omega)
      rcases u with ⟨j, uu⟩ | bb
      · show HasPredCirc n m_N (dd + 4) (S ^ (p3 + 6))
          (fun x => (i < (j : Nat) ∧ (j : Nat) < b ∧ LocalDivisor.gap c ((uu : NN) : M) = v) ∧
            ((lett i x = c ∧ lett (j : Nat) x = c) ∧
              ((∀ t, i + 1 ≤ t → t < (j : Nat) → lett t x ≠ c) ∧
                blockProd uw 0 (i + 1) (j : Nat) x = uu)))
        by_cases hcond : i < (j : Nat) ∧ (j : Nat) < b ∧ LocalDivisor.gap c ((uu : NN) : M) = v
        · have hjlen : (j : Nat) ≤ len := by omega
          have hA1 := hasPredCirc_and (hMkN i) (hMkN (j : Nat))
          have hA2 := hasPredCirc_and (hFreeN (i + 1) (j : Nat) (by omega))
            (hBNN (i + 1) (j : Nat) uu (by omega) hjlen)
          have hA3 := hasPredCirc_and hA1 hA2
          refine hA3.mono (by omega) hbig ?_
          intro x
          exact ⟨fun h => ⟨hcond, h⟩, fun h => h.2⟩
        · refine hasPredCirc_false.mono (by omega) (hSp _) ?_
          intro x
          exact ⟨fun h => h.elim, fun h => hcond h.1⟩
      · rcases bb with _ | _
        · show HasPredCirc n m_N (dd + 4) (S ^ (p3 + 6))
            (fun x => v = 1 ∧ (lett i x = c ∧ ∀ t, i + 1 ≤ t → t < b → lett t x ≠ c))
          by_cases hv : v = (1 : LocalDivisor c)
          · have hA1 := hasPredCirc_and (hMkN i) (hFreeN (i + 1) b (by omega))
            refine hA1.mono (by omega) hsmall ?_
            intro x
            exact ⟨fun h => ⟨hv, h⟩, fun h => h.2⟩
          · refine hasPredCirc_false.mono (by omega) (hSp _) ?_
            intro x
            exact ⟨fun h => h.elim, fun h => hv h.1⟩
        · show HasPredCirc n m_N (dd + 4) (S ^ (p3 + 6)) (fun x => v = 1 ∧ lett i x ≠ c)
          by_cases hv : v = (1 : LocalDivisor c)
          · refine (hNotMkN i).mono (by omega) hsmall0 ?_
            intro x
            exact ⟨fun h => ⟨hv, h⟩, fun h => h.2⟩
          · refine hasPredCirc_false.mono (by omega) (hSp _) ?_
            intro x
            exact ⟨fun h => h.elim, fun h => hv h.1⟩
    have hex := hasPredCirc_exists hguess
    have hcard : Fintype.card ((Fin (len + 1) × NN) ⊕ Bool) = (len + 1) * Fintype.card NN + 2 := by
      simp
    have hsize : Fintype.card ((Fin (len + 1) × NN) ⊕ Bool) * (S ^ (p3 + 6) + 1) + 1 ≤ S ^ p4 := by
      rw [hcard]
      have hc1 : (len + 1) * Fintype.card NN + 2 ≤ S ^ (Fintype.card NN + 3) := by
        have h1 : Fintype.card NN ≤ S ^ Fintype.card NN := pow_bnd_const hS2 _
        have h2 := pow_bnd_mul hlenS h1
        have h3 : (2 : Nat) ≤ S ^ 1 := by rw [pow_one]; omega
        have h4 := pow_bnd_add hS2 h2 h3
        exact le_trans h4 (pow_bnd_mono hS2 (by omega))
      have hc2 : S ^ (p3 + 6) + 1 ≤ S ^ (p3 + 7) := by
        have h1 := pow_bnd_add hS2 (le_refl (S ^ (p3 + 6))) hone
        exact le_trans h1 (pow_bnd_mono hS2 (by omega))
      have h5 := pow_bnd_mul hc1 hc2
      have h6 := pow_bnd_add hS2 h5 hone
      exact le_trans h6 (pow_bnd_mono hS2 (by omega))
    refine hex.mono (by omega) hsize ?_
    intro x
    constructor
    · rintro ⟨u, hu⟩
      rcases u with ⟨j, uu⟩ | bb
      · obtain ⟨⟨hij0, hjb0, hgap0⟩, ⟨hmi, hmj0⟩, hfr0, hprod0⟩ := hu
        have hij : i < (j : Nat) := hij0
        have hjb : (j : Nat) < b := hjb0
        have hgap : LocalDivisor.gap c ((uu : NN) : M) = v := hgap0
        have hmj : lett (j : Nat) x = c := hmj0
        have hfr : ∀ t, i + 1 ≤ t → t < (j : Nat) → lett t x ≠ c := hfr0
        have hprod : blockProd uw 0 (i + 1) (j : Nat) x = uu := hprod0
        have hex' : ∃ t, i < t ∧ t < b ∧ lett t x = c := ⟨(j : Nat), hij, hjb, hmj⟩
        obtain ⟨hr1, hr2, hr3, hr4⟩ := nextMarkPos_spec c lett x hex'
        have hrle := nextMarkPos_le c lett x hij hjb hmj
        have hrj : nextMarkPos c lett x b i = (j : Nat) := by
          by_contra hne
          exact hfr (nextMarkPos c lett x b i) (by omega) (by omega) hr3
        have hval : blockProd lett 0 (i + 1) (j : Nat) x = ((uu : NN) : M) := by
          rw [← hprod]
          exact (blockProd_unmarkedLetter c NN lett x (fun t => hlettA t x)
            (fun t ht1 ht2 => hfr t ht1 ht2)).symm
        rw [derivLetter_of_mark c lett b i x hmi hex', hrj, hval]
        exact hgap
      · rcases bb with _ | _
        · obtain ⟨hv, hmi, hfr⟩ := hu
          have hno : ¬ ∃ t, i < t ∧ t < b ∧ lett t x = c := by
            rintro ⟨t, ht1, ht2, ht3⟩
            exact hfr t (by omega) ht2 ht3
          rw [derivLetter_of_no_next c lett b i x hno]
          exact hv.symm
        · obtain ⟨hv, hmi⟩ := hu
          rw [derivLetter_of_not_mark c lett b i x hmi]
          exact hv.symm
    · intro hval
      by_cases hmi : lett i x = c
      · by_cases hnext : ∃ t, i < t ∧ t < b ∧ lett t x = c
        · obtain ⟨hr1, hr2, hr3, hr4⟩ := nextMarkPos_spec c lett x hnext
          refine ⟨Sum.inl (⟨nextMarkPos c lett x b i, by omega⟩,
            blockProd uw 0 (i + 1) (nextMarkPos c lett x b i) x), ?_⟩
          refine ⟨⟨hr1, hr2, ?_⟩, ⟨hmi, hr3⟩, ?_, rfl⟩
          · have hfrr : ∀ t, i + 1 ≤ t → t < nextMarkPos c lett x b i → lett t x ≠ c :=
              fun t ht1 ht2 => hr4 t (by omega) ht2
            have hvv : ((blockProd uw 0 (i + 1) (nextMarkPos c lett x b i) x : NN) : M)
                = blockProd lett 0 (i + 1) (nextMarkPos c lett x b i) x :=
              blockProd_unmarkedLetter c NN lett x (fun t => hlettA t x) hfrr
            rw [hvv, ← derivLetter_of_mark c lett b i x hmi hnext]
            exact hval
          · exact fun t ht1 ht2 => hr4 t (by omega) ht2
        · refine ⟨Sum.inr false, ?_, hmi, ?_⟩
          · rw [← hval, derivLetter_of_no_next c lett b i x hnext]
          · intro t ht1 ht2 ht3
            exact hnext ⟨t, by omega, ht2, ht3⟩
      · refine ⟨Sum.inr true, ?_, hmi⟩
        rw [← hval, derivLetter_of_not_mark c lett b i x hmi]
  -- the block circuits of the derived word, one family per right endpoint
  have hBDex : ∀ b : Nat, ∃ BD : Nat → Nat → LocalDivisor c → ACCCircuit n m_D,
      (∀ p q g, WellFormedACC (BD p q g)) ∧
      (∀ p q g r, (BD p q g).layer r ≤ max d_D 1) ∧
      (∀ p q g, (BD p q g).gateCount ≤ S ^ pD) ∧
      (∀ (p q : Nat) (g : LocalDivisor c) (x : Fin n → Bool), ACCAccepts (BD p q g) x →
        blockProd (derivLetter c lett b) 0 p q x = g) ∧
      (b ≤ len → ∀ (x : Fin n → Bool) (p q : Nat), p ≤ q → q ≤ len →
        ACCAccepts (BD p q (blockProd (derivLetter c lett b) 0 p q x)) x) := by
    intro b
    by_cases hb : b ≤ len
    · obtain ⟨BD, h1, h2, h3, h4, h5⟩ :=
        hcoreD (n := n) (derivLetter c lett b) (S ^ p4)
          (fun i v => (hderiv b hb i v).imp (fun a ha => ⟨ha.wf, ha.lay, ha.sz, ha.acc⟩)) 0 len
      refine ⟨BD, h1, fun p q g r => le_trans (h2 p q g r) (by omega), ?_, h4, fun _ => h5⟩
      intro p q g
      refine le_trans (h3 p q g) ?_
      have hstep : S ^ p4 + len + 2 ≤ S ^ (p4 + 2) := by
        have h6 := pow_bnd_add hS2 (le_refl (S ^ p4)) hlen2S
        exact le_trans (by omega) (le_trans h6 (pow_bnd_mono hS2 (by omega)))
      exact pow_bnd_pow hstep
    · refine ⟨fun _ _ _ => accConst n m_D false, fun _ _ _ => wellFormedACC_accConst n m_D false,
        ?_, ?_, ?_, ?_⟩
      · intro p q g r; rw [accConst_layer]; omega
      · intro p q g; rw [accConst_gateCount]; exact hSp _
      · intro p q g x hx
        exact absurd ((accAccepts_accConst n m_D false x).mp hx) (by simp)
      · intro hcon; exact absurd hcon hb
  choose BD hBDwf hBDlay hBDsz hBDsound hBDcomp using hBDex
  -- the component families at the final modulus `m_D`
  have hliftD : ∀ (dq Szq : Nat) (P : (Fin n → Bool) → Prop),
      HasPredCirc n m_in dq Szq P → 2 * dq + 2 ≤ dfin → (m_D + 2) * Szq ≤ S ^ p5 →
      HasPredCirc n m_D dfin (S ^ p5) P := by
    intro dq Szq P h hdq hsq
    exact (h.lift (dvd_trans hdvd_N hdvd_D) (by omega)).mono hdq hsq (fun x => Iff.rfl)
  have hmulD1 : (m_D + 2) * S ^ p1 ≤ S ^ p5 := by
    have h1 : m_D + 2 ≤ S ^ (m_D + 2) := pow_bnd_const hS2 _
    exact le_trans (pow_bnd_mul h1 (le_refl (S ^ p1))) (pow_bnd_mono hS2 (by omega))
  have hmulD2 : (m_D + 2) * S ^ p2 ≤ S ^ p5 := by
    have h1 : m_D + 2 ≤ S ^ (m_D + 2) := pow_bnd_const hS2 _
    exact le_trans (pow_bnd_mul h1 (le_refl (S ^ p2))) (pow_bnd_mono hS2 (by omega))
  have hMkD : ∀ k : Nat, HasPredCirc n m_D dfin (S ^ p5) (fun x => lett k x = c) := by
    intro k
    exact hliftD d1 (S ^ p1) _ (hpred k (fun g => g = c)) (by omega) hmulD1
  have hFreeD : ∀ s t : Nat, t ≤ len + 1 →
      HasPredCirc n m_D dfin (S ^ p5) (fun x => ∀ i, s ≤ i → i < t → lett i x ≠ c) := by
    intro s t ht
    exact hliftD d2 (S ^ p2) _ (hfree s t ht) (by omega) hmulD2
  have hBND : ∀ (p q : Nat) (v : NN), p ≤ q → q ≤ len →
      HasPredCirc n m_D dfin (S ^ p5) (fun x => blockProd uw 0 p q x = v) := by
    intro p q v h1 h2
    have hlift := (hBNpred p q v h1 h2).lift hdvd_D (by omega)
    refine hlift.mono (by omega) ?_ (fun x => Iff.rfl)
    have h3 : m_D + 2 ≤ S ^ (m_D + 2) := pow_bnd_const hS2 _
    exact le_trans (pow_bnd_mul h3 (le_refl (S ^ pN))) (pow_bnd_mono hS2 (by omega))
  have hBDD : ∀ (b p q : Nat) (gm : LocalDivisor c), b ≤ len → p ≤ q → q ≤ len →
      HasPredCirc n m_D dfin (S ^ p5)
        (fun x => blockProd (derivLetter c lett b) 0 p q x = gm) := by
    intro b p q gm hb hpq hql
    refine ⟨BD b p q gm, ⟨hBDwf b p q gm, fun r => le_trans (hBDlay b p q gm r) (by omega),
      le_trans (hBDsz b p q gm) (pow_bnd_mono hS2 (by omega)), ?_⟩⟩
    intro x
    constructor
    · intro hx; exact hBDsound b p q gm x hx
    · intro hx; rw [← hx]; exact hBDcomp b hb x p q hpq hql
  -- the final block circuits
  have key : ∀ (a b : Nat) (g : M), ∃ circ : ACCCircuit n m_D,
      WellFormedACC circ ∧ (∀ q, circ.layer q ≤ dfin + 8) ∧
      circ.gateCount ≤ S ^ (pG + p5 + 10) ∧
      (∀ x, ACCAccepts circ x → blockProd lett 0 a b x = g) ∧
      (a ≤ b → b ≤ len → ∀ x, blockProd lett 0 a b x = g → ACCAccepts circ x) := by
    intro a b g
    by_cases hab : a ≤ b ∧ b ≤ len
    · obtain ⟨hab1, hab2⟩ := hab
      have hguess : ∀ u : ((Fin (len + 1) × Fin (len + 1)) × (NN × NN) × LocalDivisor c) ⊕ NN,
          HasPredCirc n m_D (dfin + 6) (S ^ (p5 + 8))
            (fun x => match u with
              | Sum.inl w =>
                  (a ≤ (w.1.1 : Nat) ∧ (w.1.1 : Nat) ≤ (w.1.2 : Nat) ∧ (w.1.2 : Nat) < b ∧
                      ((w.2.1.1 : NN) : M) * (w.2.2).val * ((w.2.1.2 : NN) : M) = g) ∧
                    (((lett (w.1.1 : Nat) x = c ∧ lett (w.1.2 : Nat) x = c) ∧
                        ((∀ t, a ≤ t → t < (w.1.1 : Nat) → lett t x ≠ c) ∧
                          (∀ t, (w.1.2 : Nat) + 1 ≤ t → t < b → lett t x ≠ c))) ∧
                      ((blockProd uw 0 a (w.1.1 : Nat) x = w.2.1.1 ∧
                          blockProd uw 0 ((w.1.2 : Nat) + 1) b x = w.2.1.2) ∧
                        blockProd (derivLetter c lett b) 0 (w.1.1 : Nat) (w.1.2 : Nat) x = w.2.2))
              | Sum.inr u0 =>
                  ((u0 : NN) : M) = g ∧
                    ((∀ t, a ≤ t → t < b → lett t x ≠ c) ∧ blockProd uw 0 a b x = u0)) := by
        intro u
        have hbig0 : (8 : Nat) * S ^ p5 + 14 ≤ S ^ (p5 + 8) := by
          have h8 : (8 : Nat) ≤ S ^ 3 := le_trans (by norm_num) (hpow2 3)
          have h14 : (14 : Nat) ≤ S ^ 4 := le_trans (by norm_num) (hpow2 4)
          have h1 := pow_bnd_mul h8 (le_refl (S ^ p5))
          have h2 := pow_bnd_add hS2 h1 h14
          exact le_trans h2 (pow_bnd_mono hS2 (by omega))
        have hbig : 2 * (2 * (2 * S ^ p5 + 2) + 2) + 2 ≤ S ^ (p5 + 8) := by
          have h3 : 2 * (2 * (2 * S ^ p5 + 2) + 2) + 2 = 8 * S ^ p5 + 14 := by ring
          rw [h3]
          exact hbig0
        have hsmall : 2 * S ^ p5 + 2 ≤ S ^ (p5 + 8) := by
          have h1 : 2 * S ^ p5 + 2 ≤ 8 * S ^ p5 + 14 := by
            have := hSp p5; omega
          exact le_trans h1 hbig0
        rcases u with ⟨⟨p', q'⟩, ⟨u0, uk⟩, gm⟩ | u0
        · show HasPredCirc n m_D (dfin + 6) (S ^ (p5 + 8))
            (fun x => (a ≤ (p' : Nat) ∧ (p' : Nat) ≤ (q' : Nat) ∧ (q' : Nat) < b ∧
                ((u0 : NN) : M) * gm.val * ((uk : NN) : M) = g) ∧
              (((lett (p' : Nat) x = c ∧ lett (q' : Nat) x = c) ∧
                  ((∀ t, a ≤ t → t < (p' : Nat) → lett t x ≠ c) ∧
                    (∀ t, (q' : Nat) + 1 ≤ t → t < b → lett t x ≠ c))) ∧
                ((blockProd uw 0 a (p' : Nat) x = u0 ∧
                    blockProd uw 0 ((q' : Nat) + 1) b x = uk) ∧
                  blockProd (derivLetter c lett b) 0 (p' : Nat) (q' : Nat) x = gm)))
          by_cases hcond : a ≤ (p' : Nat) ∧ (p' : Nat) ≤ (q' : Nat) ∧ (q' : Nat) < b ∧
              ((u0 : NN) : M) * gm.val * ((uk : NN) : M) = g
          · obtain ⟨hc1, hc2, hc3, hc4⟩ := hcond
            have hA1 := hasPredCirc_and (hMkD (p' : Nat)) (hMkD (q' : Nat))
            have hA2 := hasPredCirc_and (hFreeD a (p' : Nat) (by omega))
              (hFreeD ((q' : Nat) + 1) b (by omega))
            have hA3 := hasPredCirc_and (hBND a (p' : Nat) u0 (by omega) (by omega))
              (hBND ((q' : Nat) + 1) b uk (by omega) (by omega))
            have hA4 : HasPredCirc n m_D (dfin + 2) (2 * S ^ p5 + 2)
                (fun x => blockProd (derivLetter c lett b) 0 (p' : Nat) (q' : Nat) x = gm) :=
              (hBDD b (p' : Nat) (q' : Nat) gm hab2 hc2 (by omega)).mono
                (by omega) (by have := hSp p5; omega) (fun x => Iff.rfl)
            have hB1 := hasPredCirc_and hA1 hA2
            have hB2 := hasPredCirc_and hA3 hA4
            have hC := hasPredCirc_and hB1 hB2
            refine hC.mono (by omega) hbig ?_
            intro x
            exact ⟨fun h => ⟨⟨hc1, hc2, hc3, hc4⟩, h⟩, fun h => h.2⟩
          · refine hasPredCirc_false.mono (by omega) (hSp _) ?_
            intro x
            exact ⟨fun h => h.elim, fun h => hcond h.1⟩
        · show HasPredCirc n m_D (dfin + 6) (S ^ (p5 + 8))
            (fun x => ((u0 : NN) : M) = g ∧
              ((∀ t, a ≤ t → t < b → lett t x ≠ c) ∧ blockProd uw 0 a b x = u0))
          by_cases hcond : ((u0 : NN) : M) = g
          · have hA1 := hasPredCirc_and (hFreeD a b (by omega)) (hBND a b u0 hab1 hab2)
            refine hA1.mono (by omega) hsmall ?_
            intro x
            exact ⟨fun h => ⟨hcond, h⟩, fun h => h.2⟩
          · refine hasPredCirc_false.mono (by omega) (hSp _) ?_
            intro x
            exact ⟨fun h => h.elim, fun h => hcond h.1⟩
      have hex := hasPredCirc_exists hguess
      have hcard : Fintype.card (((Fin (len + 1) × Fin (len + 1)) × (NN × NN) × LocalDivisor c)
            ⊕ NN)
          = (len + 1) * (len + 1) * (Fintype.card NN * Fintype.card NN *
              Fintype.card (LocalDivisor c)) + Fintype.card NN := by
        simp [Fintype.card_sum, Fintype.card_prod, mul_assoc]
      have hsizefin : Fintype.card (((Fin (len + 1) × Fin (len + 1)) × (NN × NN) ×
            LocalDivisor c) ⊕ NN) * (S ^ (p5 + 8) + 1) + 1 ≤ S ^ (pG + p5 + 10) := by
        rw [hcard]
        have hcN : Fintype.card NN ≤ S ^ Fintype.card NN := pow_bnd_const hS2 _
        have hcD : Fintype.card (LocalDivisor c) ≤ S ^ Fintype.card (LocalDivisor c) :=
          pow_bnd_const hS2 _
        have h1 := pow_bnd_mul hlenS hlenS
        have h2 := pow_bnd_mul (pow_bnd_mul hcN hcN) hcD
        have h3 := pow_bnd_mul h1 h2
        have h4 := pow_bnd_add hS2 h3 hcN
        have h5 : (len + 1) * (len + 1) * (Fintype.card NN * Fintype.card NN *
            Fintype.card (LocalDivisor c)) + Fintype.card NN ≤ S ^ pG :=
          le_trans h4 (pow_bnd_mono hS2 (by omega))
        have h6 : S ^ (p5 + 8) + 1 ≤ S ^ (p5 + 9) := by
          have h7 := pow_bnd_add hS2 (le_refl (S ^ (p5 + 8))) hone
          exact le_trans h7 (pow_bnd_mono hS2 (by omega))
        have h8 := pow_bnd_mul h5 h6
        have h9 := pow_bnd_add hS2 h8 hone
        exact le_trans h9 (pow_bnd_mono hS2 (by omega))
      obtain ⟨circ, hcirc⟩ := hex.mono (le_refl (dfin + 8)) hsizefin (fun x => Iff.rfl)
      refine ⟨circ, hcirc.wf, hcirc.lay, hcirc.sz, ?_, ?_⟩
      · intro x hx
        obtain ⟨u, hu⟩ := (hcirc.acc x).mp hx
        rcases u with ⟨⟨p', q'⟩, ⟨u0, uk⟩, gm⟩ | u0
        · obtain ⟨⟨hc1', hc2', hc3', hc4'⟩, ⟨⟨hmp', hmq'⟩, hf1', hf2'⟩, ⟨hb1', hb2'⟩, hbd'⟩ := hu
          have hc1 : a ≤ (p' : Nat) := hc1'
          have hc2 : (p' : Nat) ≤ (q' : Nat) := hc2'
          have hc3 : (q' : Nat) < b := hc3'
          have hc4 : ((u0 : NN) : M) * gm.val * ((uk : NN) : M) = g := hc4'
          have hmp : lett (p' : Nat) x = c := hmp'
          have hmq : lett (q' : Nat) x = c := hmq'
          have hf1 : ∀ t, a ≤ t → t < (p' : Nat) → lett t x ≠ c := hf1'
          have hf2 : ∀ t, (q' : Nat) + 1 ≤ t → t < b → lett t x ≠ c := hf2'
          have hb1 : blockProd uw 0 a (p' : Nat) x = u0 := hb1'
          have hb2 : blockProd uw 0 ((q' : Nat) + 1) b x = uk := hb2'
          have hbd : blockProd (derivLetter c lett b) 0 (p' : Nat) (q' : Nat) x = gm := hbd'
          have hsplit := blockProd_marked_split c NN lett x (fun t => hlettA t x)
            hc1 hc2 hc3 hmp hmq (fun t ht1 ht2 => hf1 t ht1 ht2)
            (fun t ht1 ht2 => hf2 t (by omega) ht2)
          rw [hsplit, hb1, hb2, hbd]
          exact hc4
        · obtain ⟨hc1, hf, hb1'⟩ := hu
          have hb1 : blockProd uw 0 a b x = u0 := hb1'
          have hval := blockProd_unmarkedLetter c NN lett x (fun t => hlettA t x)
            (fun t ht1 ht2 => hf t ht1 ht2)
          rw [← hval, hb1]
          exact hc1
      · intro _ _ x hgx
        refine (hcirc.acc x).mpr ?_
        by_cases hmark : ∃ t, a ≤ t ∧ t < b ∧ lett t x = c
        · classical
          set F : Finset Nat := (Finset.range b).filter (fun t => a ≤ t ∧ lett t x = c) with hFdef
          have hFne : F.Nonempty := by
            obtain ⟨t, ht1, ht2, ht3⟩ := hmark
            exact ⟨t, by simp [hFdef, Finset.mem_filter, Finset.mem_range, ht1, ht2, ht3]⟩
          set p0 : Nat := F.min' hFne with hp0def
          set q0 : Nat := F.max' hFne with hq0def
          have hp0mem : p0 ∈ F := F.min'_mem hFne
          have hq0mem : q0 ∈ F := F.max'_mem hFne
          have hp0 : a ≤ p0 ∧ p0 < b ∧ lett p0 x = c := by
            have := Finset.mem_filter.mp hp0mem
            exact ⟨this.2.1, Finset.mem_range.mp this.1, this.2.2⟩
          have hq0 : a ≤ q0 ∧ q0 < b ∧ lett q0 x = c := by
            have := Finset.mem_filter.mp hq0mem
            exact ⟨this.2.1, Finset.mem_range.mp this.1, this.2.2⟩
          have hpq : p0 ≤ q0 := F.min'_le q0 hq0mem
          have hfr1 : ∀ t, a ≤ t → t < p0 → lett t x ≠ c := by
            intro t ht1 ht2 ht3
            have : t ∈ F := by
              simp [hFdef, Finset.mem_filter, Finset.mem_range, ht1, ht3]
              omega
            have := F.min'_le t this
            omega
          have hfr2 : ∀ t, q0 + 1 ≤ t → t < b → lett t x ≠ c := by
            intro t ht1 ht2 ht3
            have : t ∈ F := by
              simp [hFdef, Finset.mem_filter, Finset.mem_range, ht2, ht3]
              omega
            have := F.le_max' t this
            omega
          refine ⟨Sum.inl ((⟨p0, by omega⟩, ⟨q0, by omega⟩),
            (blockProd uw 0 a p0 x, blockProd uw 0 (q0 + 1) b x),
            blockProd (derivLetter c lett b) 0 p0 q0 x), ?_⟩
          refine ⟨⟨hp0.1, hpq, hq0.2.1, ?_⟩, ⟨⟨hp0.2.2, hq0.2.2⟩, hfr1, hfr2⟩, ⟨rfl, rfl⟩, rfl⟩
          have hsplit := blockProd_marked_split c NN lett x (fun t => hlettA t x)
            hp0.1 hpq hq0.2.1 hp0.2.2 hq0.2.2 hfr1 (fun t ht1 ht2 => hfr2 t (by omega) ht2)
          rw [← hsplit]
          exact hgx
        · refine ⟨Sum.inr (blockProd uw 0 a b x), ?_, ?_, rfl⟩
          · have hval := blockProd_unmarkedLetter c NN lett x (fun t => hlettA t x)
              (fun t ht1 ht2 ht3 => hmark ⟨t, ht1, ht2, ht3⟩)
            rw [hval]
            exact hgx
          · intro t ht1 ht2 ht3
            exact hmark ⟨t, ht1, ht2, ht3⟩
    · refine ⟨accConst n m_D false, wellFormedACC_accConst n m_D false, ?_, ?_, ?_, ?_⟩
      · intro q; rw [accConst_layer]; omega
      · rw [accConst_gateCount]; exact hSp _
      · intro x hx
        exact absurd ((accAccepts_accConst n m_D false x).mp hx) (by simp)
      · intro h1 h2
        exact absurd ⟨h1, h2⟩ hab
  choose Bc hBcwf hBclay hBcsz hBcsound hBccomp using key
  refine ⟨Bc, hBcwf, hBclay, hBcsz, ?_, ?_⟩
  · intro a b g x hx
    rw [blockProd_start_shift]
    exact hBcsound a b g x hx
  · intro x a b hab hbl
    exact hBccomp a b _ hab hbl x (blockProd_start_shift letter x start a b).symm

/-! ## List bookkeeping for the representation expansion (S3) -/

/-- Reindexing a `List.range'` product to start at `0`. -/
theorem prod_range'_shift {G : Type} [Monoid G] :
    ∀ (k s : Nat) (F H : Nat → G), (∀ r, r < k → F (s + r) = H r) →
      ((List.range' s k).map F).prod = ((List.range' 0 k).map H).prod := by
  intro k
  induction k with
  | zero => intro s F H _; simp
  | succ k ih =>
    intro s F H hFH
    have h0 : F s = H 0 := by simpa using hFH 0 (Nat.succ_pos k)
    have e1 : ((List.range' s (k+1)).map F).prod = F s * ((List.range' (s+1) k).map F).prod := by
      simp [List.range'_succ]
    have e2 : ((List.range' 0 (k+1)).map H).prod = H 0 * ((List.range' 1 k).map H).prod := by
      simp [List.range'_succ]
    have e3 : ((List.range' (s+1) k).map F).prod
        = ((List.range' 0 k).map (fun r => H (r+1))).prod := by
      refine ih (s+1) F (fun r => H (r+1)) ?_
      intro r hr
      have hstep := hFH (r+1) (by omega)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hstep
    have e4 : ((List.range' 1 k).map H).prod
        = ((List.range' 0 k).map (fun r => H (r+1))).prod := by
      refine ih 1 H (fun r => H (r+1)) ?_
      intro r _
      rw [Nat.add_comm]
    rw [e1, e2, e3, e4, h0]

/-- A word padded on the right with `1`s up to a fixed length `R` has the same
product. -/
theorem prod_getD_range' {G : Type} [Monoid G] :
    ∀ (l : List G) (R : Nat), l.length ≤ R →
      ((List.range' 0 R).map (fun r => l.getD r 1)).prod = l.prod := by
  intro l
  induction l with
  | nil => intro R _; simp
  | cons a t ih =>
    intro R hR
    obtain ⟨R', rfl⟩ : ∃ R', R = R' + 1 := ⟨R - 1, by simp at hR; omega⟩
    have hlen : t.length ≤ R' := by simp at hR; omega
    have e1 : ((List.range' 0 (R'+1)).map (fun r => (a :: t).getD r 1)).prod
        = (a :: t).getD 0 1 * ((List.range' 1 R').map (fun r => (a :: t).getD r 1)).prod := by
      simp [List.range'_succ]
    have e2 : ((List.range' 1 R').map (fun r => (a :: t).getD r 1)).prod
        = ((List.range' 0 R').map (fun r => t.getD r 1)).prod := by
      refine prod_range'_shift R' 1 (fun r => (a :: t).getD r 1) (fun r => t.getD r 1) ?_
      intro r _
      change (a :: t).getD (1 + r) 1 = t.getD r 1
      rw [Nat.add_comm]
      exact List.getD_cons_succ
    rw [e1, e2, ih R' hlen]
    simp

/-- **S3: representation expansion.**  Fix a generator word
`rep m` (letters in `A`) for every `m` with `List.prod (rep m) = m`
(`Submonoid.exists_list_of_mem_closure` on `hgen`), pad on the right with
`1 ∈ A` to the maximal length `R`; the expanded word has letters in `A`,
length `R * len`, blocks `[R*a, R*b)`, and the `j`-th expanded letter is
recognized by an OR of the original letter recognizers over the constantly
many `m` whose representation has the required `j % R`-th symbol. -/
theorem monoidWordACCGen_of_genOn {M : Type} [Monoid M] [Finite M] {A : Set M}
    (h1 : (1 : M) ∈ A) (hgen : Submonoid.closure A = ⊤)
    (H : MonoidWordACCGenOn M A) : MonoidWordACCGen M := by
  classical
  haveI : Fintype M := Fintype.ofFinite M
  -- a generator word for every element, of uniformly bounded length
  have hrepex : ∀ m : M, ∃ l : List M, (∀ y ∈ l, y ∈ A) ∧ l.prod = m := by
    intro m
    exact Submonoid.exists_list_of_mem_closure (by rw [hgen]; trivial)
  choose rep hrepA hrepprod using hrepex
  set R : Nat := (Finset.univ.sup fun m : M => (rep m).length) + 1 with hRdef
  have hRpos : 0 < R := by omega
  have hRlen : ∀ m : M, (rep m).length ≤ R := by
    intro m
    have h : (rep m).length ≤ Finset.univ.sup (fun m : M => (rep m).length) :=
      Finset.le_sup (f := fun m : M => (rep m).length) (Finset.mem_univ m)
    rw [hRdef]
    omega
  -- the padded representation, as a function of the position
  set word : M → Nat → M := fun m j => (rep m).getD j 1 with hworddef
  have hwordA : ∀ m j, word m j ∈ A := by
    intro m j
    rcases lt_or_ge j (rep m).length with hj | hj
    · have hmem : (rep m).getD j 1 ∈ rep m := by
        rw [List.getD_eq_getElem _ _ hj]
        exact List.getElem_mem hj
      exact hrepA m _ hmem
    · have hw : word m j = 1 := by
        simp only [hworddef]
        rw [List.getD_eq_default _ _ hj]
      rw [hw]; exact h1
  have hwordprod : ∀ m : M, ((List.range' 0 R).map (word m)).prod = m := by
    intro m
    have hp := prod_getD_range' (rep m) R (hRlen m)
    simpa [hworddef, hrepprod m] using hp
  intro m_in d_in hm hd
  obtain ⟨m_out, d_out, e', hm2, hdiv, hcore⟩ := H m_in (max d_in 1 + 2) hm (by omega)
  refine ⟨m_out, d_out, (Fintype.card M + R + 11) * e', hm2, hdiv, ?_⟩
  intro n letter size hrec start len
  -- the expanded word: position `j` carries the `j % R`-th symbol of the
  -- representation of the `j / R`-th original letter
  set letter' : Nat → (Fin n → Bool) → M := fun j x => word (letter (j / R) x) (j % R)
    with hletter'def
  have hletter'A : ∀ (j : Nat) (x : Fin n → Bool), letter' j x ∈ A := fun j x => hwordA _ _
  have hrec' : ∀ (j : Nat) (mm : M), ∃ a : ACCCircuit n m_in,
      WellFormedACC a ∧ (∀ q, a.layer q ≤ max d_in 1 + 2) ∧
      a.gateCount ≤ Fintype.card M * (size + 2) + 1 ∧
      (∀ x, ACCAccepts a x ↔ letter' j x = mm) := by
    intro j mm
    choose L hLwf hLlay hLsz hLacc using hrec (j / R)
    obtain ⟨a, hawf, halay, hasz, haacc⟩ :=
      exists_acc_letterPred L (letter (j / R)) (fun g => word g (j % R) = mm)
        hLwf hLlay hLsz (fun g x => hLacc g x)
    exact ⟨a, hawf, halay, hasz, fun x => haacc x⟩
  obtain ⟨B', hB'wf, hB'lay, hB'sz, hB'sound, hB'comp⟩ :=
    hcore letter' (Fintype.card M * (size + 2) + 1) hletter'A hrec' (R * start) (R * len)
  -- one original letter is the product of its `R` expanded positions
  have hstep : ∀ (x : Fin n → Bool) (b : Nat),
      blockProd letter' (R * start) (R * b) (R * (b + 1)) x = letter (start + b) x := by
    intro x b
    have hr : R * (b + 1) - R * b = R := by
      have hrr : R * (b+1) = R * b + R := by ring
      omega
    have hs : R * start + R * b = R * (start + b) := by ring
    have hshift := prod_range'_shift R (R * (start + b)) (fun i => letter' i x)
      (fun r => word (letter (start + b) x) r) ?_
    · change ((List.range' (R * start + R * b) (R * (b+1) - R * b)).map
        (fun i => letter' i x)).prod = letter (start + b) x
      rw [hr, hs, hshift, hwordprod]
    · intro r hr'
      have hdiv2 : (R * (start + b) + r) / R = start + b := by
        rw [Nat.add_comm, Nat.add_mul_div_left _ _ hRpos, Nat.div_eq_of_lt hr']
        omega
      have hmod2 : (R * (start + b) + r) % R = r := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr']
      change letter' (R * (start + b) + r) x = word (letter (start + b) x) r
      rw [hletter'def]
      simp only [hdiv2, hmod2]
  -- hence the expanded blocks compute the original blocks
  have halign : ∀ (x : Fin n → Bool) (a b : Nat),
      blockProd letter' (R * start) (R * a) (R * b) x = blockProd letter start a b x := by
    intro x a b
    by_cases hab : a ≤ b
    · induction b, hab using Nat.le_induction with
      | base => simp [blockProd]
      | succ b hb ih =>
        have hc1 : blockProd letter start a b x * blockProd letter start b (b+1) x
            = blockProd letter start a (b+1) x := blockProd_concat letter start x hb (by omega)
        have hc2 : blockProd letter' (R * start) (R * a) (R * b) x
              * blockProd letter' (R * start) (R * b) (R * (b+1)) x
            = blockProd letter' (R * start) (R * a) (R * (b+1)) x :=
          blockProd_concat letter' (R * start) x (Nat.mul_le_mul_left R hb)
            (Nat.mul_le_mul_left R (by omega))
        have hc3 : blockProd letter start b (b+1) x = letter (start + b) x := by
          simp [blockProd]
        rw [← hc1, ← hc2, ih, hstep, hc3]
    · have e1 : b - a = 0 := by omega
      have e2 : R * b - R * a = 0 := by
        have hle : R * b ≤ R * a := Nat.mul_le_mul_left R (by omega)
        omega
      simp [blockProd, e1, e2]
  refine ⟨fun a b g => B' (R * a) (R * b) g, fun a b g => hB'wf _ _ _,
    fun a b g q => hB'lay _ _ _ q, ?_, ?_, ?_⟩
  · -- the size bookkeeping
    intro a b g
    refine le_trans (hB'sz (R * a) (R * b) g) ?_
    set S := size + len + 2 with hSdef
    have hS : 2 ≤ S := by omega
    have hsize : size ≤ S ^ 1 := by rw [pow_one]; omega
    have hlenb : len ≤ S ^ 1 := by rw [pow_one]; omega
    have h2 : (2 : Nat) ≤ S ^ 2 := pow_bnd_const hS 2
    have hsize2 : size + 2 ≤ S ^ 4 := by
      have hb := pow_bnd_add hS hsize h2
      exact le_trans hb (pow_bnd_mono hS (by omega))
    have hcard : Fintype.card M ≤ S ^ Fintype.card M := pow_bnd_const hS _
    have hmul : Fintype.card M * (size + 2) ≤ S ^ (Fintype.card M + 4) := pow_bnd_mul hcard hsize2
    have hone : (1 : Nat) ≤ S ^ 1 := pow_bnd_const hS 1
    have hsize' : Fintype.card M * (size + 2) + 1 ≤ S ^ (Fintype.card M + 6) := by
      have hb := pow_bnd_add hS hmul hone
      exact le_trans hb (pow_bnd_mono hS (by omega))
    have hRb : R ≤ S ^ R := pow_bnd_const hS R
    have hRlenb : R * len ≤ S ^ (R + 1) := pow_bnd_mul hRb hlenb
    have hsum : Fintype.card M * (size + 2) + 1 + R * len
        ≤ S ^ (Fintype.card M + R + 8) := by
      have hb := pow_bnd_add hS hsize' hRlenb
      exact le_trans hb (pow_bnd_mono hS (by omega))
    have htot : Fintype.card M * (size + 2) + 1 + R * len + 2
        ≤ S ^ (Fintype.card M + R + 11) := by
      have hb := pow_bnd_add hS hsum h2
      exact le_trans hb (pow_bnd_mono hS (by omega))
    exact pow_bnd_pow htot
  · -- soundness
    intro a b g x hacc
    have hsnd := hB'sound (R * a) (R * b) g x hacc
    rw [halign] at hsnd
    exact hsnd
  · -- completeness on the promised window
    intro x a b hab hblen
    have hcomp := hB'comp x (R * a) (R * b) (Nat.mul_le_mul_left R hab)
      (Nat.mul_le_mul_left R hblen)
    rw [halign] at hcomp
    exact hcomp

end Internal
end AllenderOQ3
