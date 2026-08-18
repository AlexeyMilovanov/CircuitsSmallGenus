import AllenderOQ3.Internal.BlockAssembly
import AllenderOQ3.Internal.EpochBlocks
import AllenderOQ3.Internal.ShortWordProblem
import AllenderOQ3.Internal.CascadeCoordinate

/-!
# Reduction of the letter word problem to the per-epoch problem

The prefix products of a window of `NonCrossing w` letters change their
rank/shape coordinate at most `epochBound w` times, however long the window is
(`card_shapeCoord_changes_le_nonCrossing`).  By `exists_constant_blocks_fin` the
window therefore splits into at most `epochBound w + 1` blocks on each of which
the coordinate is constant up to the last letter — the *epochs*.  Feeding
per-epoch recognisers to the guess-and-verify gadget `exists_acc_blockAssembly`
turns them into a recogniser for the whole window, of constant depth and of size
polynomial in `size + len`.

Hence `LetterWordACCGen w` follows from `EpochWordACC w`: the obligation to
recognise the product of a *single shape-constant block*.  That is the
remaining mathematical content of the cascade (the holonomy of an epoch lives in
a cyclic group, whose contribution is counted by `MOD` gates); the combinatorial
assembly around it is discharged here.

Everything here is `sorry`-free.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace AllenderOQ3
namespace Internal

variable {w : Nat}

/-- The word of letters filling the window `[start, start + len)`. -/
noncomputable def letterWindowWord {n : Nat} (letter : Nat → (Fin n → Bool) → TransMonoid w)
    (start len : Nat) (x : Fin n → Bool) : List (TransMonoid w) :=
  (List.range' start len).map (fun i => letter i x)

/-- The rank/shape coordinate of the prefix of the window word. -/
noncomputable def windowShape {n : Nat} (letter : Nat → (Fin n → Bool) → TransMonoid w)
    (start len : Nat) (x : Fin n → Bool) (u : Nat) :
    Fin (2 ^ w + 1) × Fin (2 ^ w * 2 ^ w + 1) :=
  shapeCoord (prefixEnd (letterWindowWord letter start len x) u)

/-- The number of rank/shape changes along a word of `NonCrossing w` letters,
hence one less than the number of epochs the window splits into. -/
def epochBound (w : Nat) : Nat := 2 ^ w * (2 ^ w * 2 ^ w + 1) + 2 ^ w * 2 ^ w

/-- **The per-epoch recognition obligation.**  For every window of letters there
are recognisers `B a b g` of constant depth and polynomial size which

* never accept unless the product of the letters of the block `[start + a, start + b)`
  is `g` (soundness), and
* do accept the true product on every block on which the rank/shape coordinate of
  the prefix products is constant up to the last letter (completeness on epochs).

The letters are the certified layer maps of `LetterWordACCGen`, and each single
letter test is available as a depth-two `ACC[2]` circuit of size at most `size`. -/
def EpochWordACC (w : Nat) : Prop :=
  ∃ modulus depth exponent : Nat,
    2 ≤ modulus ∧
      ∀ {n : Nat} (letter : Nat → (Fin n → Bool) → TransMonoid w) (size : Nat),
        (∀ i x, isNonCrossingMap w (letter i x)) →
        (∀ (i : Nat) (mm : TransMonoid w),
          ∃ a : ACCCircuit n 2,
            WellFormedACC a ∧
            (∀ q, a.layer q ≤ 2) ∧
            a.gateCount ≤ size ∧
            (∀ x, ACCAccepts a x ↔ letter i x = mm)) →
        ∀ start len : Nat,
          ∃ B : Nat → Nat → TransMonoid w → ACCCircuit n modulus,
            (∀ a b g, WellFormedACC (B a b g)) ∧
            (∀ a b g q, (B a b g).layer q ≤ depth) ∧
            (∀ a b g, (B a b g).gateCount ≤ (size + len + 2) ^ exponent) ∧
            (∀ (a b : Nat) (g : TransMonoid w) (x : Fin n → Bool), a ≤ b →
              ACCAccepts (B a b g) x → blockProd letter start a b x = g) ∧
            (∀ (x : Fin n → Bool) (a b : Nat), a ≤ b → b ≤ len →
              (∀ i, a ≤ i → i + 1 < b →
                windowShape letter start len x i = windowShape letter start len x (i + 1)) →
              ACCAccepts (B a b (blockProd letter start a b x)) x)

/-- The rank/shape coordinate of the prefixes of a window of non-crossing letters
changes at most `epochBound w` times. -/
theorem card_changeSet_windowShape_le {n : Nat}
    (letter : Nat → (Fin n → Bool) → TransMonoid w)
    (hgen : ∀ i x, isNonCrossingMap w (letter i x))
    (start len : Nat) (x : Fin n → Bool) :
    (changeSet (windowShape letter start len x) 0 len).card ≤ epochBound w := by
  classical
  set word := letterWindowWord letter start len x with hword
  have hmem : ∀ g ∈ word, g ∈ NonCrossing w := by
    intro g hg
    rw [hword, letterWindowWord, List.mem_map] at hg
    obtain ⟨i, -, rfl⟩ := hg
    exact Submonoid.subset_closure (hgen i x)
  have hkey := card_shapeCoord_changes_le_nonCrossing hmem len
  have hcard :
      (changeSet (windowShape letter start len x) 0 len).card
        = (Finset.univ.filter (fun i : Fin len =>
            shapeCoord (prefixEnd word i.castSucc.val)
              ≠ shapeCoord (prefixEnd word i.succ.val))).card := by
    refine (Finset.card_bij (fun (i : Fin len) _ => i.val) ?_ ?_ ?_).symm
    · intro i hi
      rw [Finset.mem_filter] at hi
      refine (mem_changeSet _ 0 len i.val).mpr ⟨i.isLt, ?_⟩
      simpa [windowShape, hword, Fin.val_castSucc, Fin.val_succ] using hi.2
    · intro i _ j _ hij
      exact Fin.ext hij
    · intro k hk
      rw [mem_changeSet] at hk
      refine ⟨⟨k, hk.1⟩, ?_, rfl⟩
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      simpa [windowShape, hword, Fin.val_castSucc, Fin.val_succ] using hk.2
  rw [hcard]
  exact hkey

/-- **A sanity check on the shape of the obligation**: for the degenerate width
`w = 0` the transition monoid is trivial, so the constant circuit is a per-epoch
recogniser, and `EpochWordACC 0` holds.  In particular the hypothesis of
`letterWordACCGen_of_epochWordACC` is satisfiable. -/
theorem epochWordACC_zero : EpochWordACC 0 := by
  have hsub : Subsingleton (TransMonoid 0) := by
    constructor
    intro a b
    apply MulOpposite.unop_injective
    funext s j
    exact j.elim0
  refine ⟨2, 1, 1, le_refl 2, ?_⟩
  intro n letter size _ _ start len
  refine ⟨fun _ _ _ => accConst n 2 true, fun a b g => wellFormedACC_accConst n 2 true,
    ?_, ?_, ?_, ?_⟩
  · intro a b g q
    exact le_of_eq (accConst_layer n 2 true q)
  · intro a b g
    rw [accConst_gateCount, pow_one]
    omega
  · intro a b g x _ _
    exact hsub.allEq _ _
  · intro x a b _ _ _
    exact (accAccepts_accConst n 2 true x).mpr rfl

/-- **The letter word problem reduces to the per-epoch problem.** -/
theorem letterWordACCGen_of_epochWordACC (H : EpochWordACC w) : LetterWordACCGen w := by
  classical
  obtain ⟨M, D, e, hM, hcore⟩ := H
  -- the number of blocks
  set K := epochBound w + 1 with hK
  refine ⟨M, max D 1 + 2,
    K + 1 + e + Fintype.card (Fin K → TransMonoid w) * (2 * K + 3) + 1, hM, ?_⟩
  intro n letter size hgen hrec start len h
  obtain ⟨B, hBwf, hBlay, hBsz, hBsound, hBcomp⟩ := hcore letter size hgen hrec start len
  have hcomplete : ∀ x : Fin n → Bool, ∃ t : Fin (K + 1) → Fin (len + 1),
      (t 0).val = 0 ∧ (t (Fin.last K)).val = len ∧
      (∀ j : Fin K, (t j.castSucc).val ≤ (t j.succ).val) ∧
      (∀ j : Fin K, ACCAccepts
          (B (t j.castSucc).val (t j.succ).val
            (blockProd letter start (t j.castSucc).val (t j.succ).val x)) x) := by
    intro x
    obtain ⟨t, ht0, htlast, htmono, htblocks⟩ :=
      exists_constant_blocks_fin (windowShape letter start len x) (epochBound w) 0 len
        (card_changeSet_windowShape_le letter hgen start len x)
    refine ⟨t, ht0, htlast, htmono, ?_⟩
    intro j
    refine hBcomp x _ _ (htmono j) ?_ ?_
    · exact Nat.lt_succ_iff.mp (t j.succ).isLt
    · intro i hi hi'
      have hb := htblocks j i hi hi'
      simpa using hb
  obtain ⟨a, hawf, halay, hasz, haacc⟩ :=
    exists_acc_blockAssembly (G := TransMonoid w) (K := K) (len := len)
      (d := D) (Sz := (size + len + 2) ^ e) letter start B hBwf hBlay hBsz hBsound hcomplete h
  refine ⟨a, hawf, halay, ?_, ?_⟩
  · -- size bound
    set S := size + len + 2 with hS
    have hS2 : 2 ≤ S := by omega
    have hSe : 1 ≤ S ^ e := Nat.one_le_pow _ _ (by omega)
    have hcard1 : Fintype.card (Fin (K + 1) → Fin (len + 1)) ≤ S ^ (K + 1) := by
      have : Fintype.card (Fin (K + 1) → Fin (len + 1)) = (len + 1) ^ (K + 1) := by
        simp
      rw [this]
      exact Nat.pow_le_pow_left (by omega) _
    have hfactor : (K + 1) * (S ^ e + 1) + 1 ≤ (2 * K + 3) * S ^ e := by
      have h2 : (K + 2) ≤ (K + 2) * S ^ e := Nat.le_mul_of_pos_right _ (by omega)
      calc (K + 1) * (S ^ e + 1) + 1 = (K + 1) * S ^ e + (K + 2) := by ring
        _ ≤ (K + 1) * S ^ e + (K + 2) * S ^ e := Nat.add_le_add_left h2 _
        _ = (2 * K + 3) * S ^ e := by ring
    have hstep : Fintype.card (Fin (K + 1) → Fin (len + 1))
        * Fintype.card (Fin K → TransMonoid w)
        * ((K + 1) * (S ^ e + 1) + 1)
        ≤ Fintype.card (Fin K → TransMonoid w) * (2 * K + 3) * S ^ (K + 1 + e) := by
      calc Fintype.card (Fin (K + 1) → Fin (len + 1)) * Fintype.card (Fin K → TransMonoid w)
            * ((K + 1) * (S ^ e + 1) + 1)
          ≤ (S ^ (K + 1) * Fintype.card (Fin K → TransMonoid w)) * ((2 * K + 3) * S ^ e) :=
            Nat.mul_le_mul (Nat.mul_le_mul_right _ hcard1) hfactor
        _ = (Fintype.card (Fin K → TransMonoid w) * (2 * K + 3)) * (S ^ (K + 1) * S ^ e) := by
            ring
        _ = Fintype.card (Fin K → TransMonoid w) * (2 * K + 3) * S ^ (K + 1 + e) := by
            rw [← pow_add]
    have hpow : Fintype.card (Fin K → TransMonoid w) * (2 * K + 3) * S ^ (K + 1 + e)
        ≤ S ^ (K + 1 + e + Fintype.card (Fin K → TransMonoid w) * (2 * K + 3)) :=
      const_mul_pow_le_pow hS2
    have hlast : S ^ (K + 1 + e + Fintype.card (Fin K → TransMonoid w) * (2 * K + 3)) + 1
        ≤ S ^ (K + 1 + e + Fintype.card (Fin K → TransMonoid w) * (2 * K + 3) + 1) := by
      set E := K + 1 + e + Fintype.card (Fin K → TransMonoid w) * (2 * K + 3) with hE
      have h1 : 1 ≤ S ^ E := Nat.one_le_pow _ _ (by omega)
      have h2 : 2 * S ^ E ≤ S * S ^ E := Nat.mul_le_mul_right _ hS2
      have h3 : S * S ^ E = S ^ (E + 1) := by ring
      omega
    calc a.gateCount
        ≤ Fintype.card (Fin (K + 1) → Fin (len + 1)) * Fintype.card (Fin K → TransMonoid w)
            * ((K + 1) * (S ^ e + 1) + 1) + 1 := hasz
      _ ≤ Fintype.card (Fin K → TransMonoid w) * (2 * K + 3) * S ^ (K + 1 + e) + 1 :=
          Nat.add_le_add_right hstep 1
      _ ≤ S ^ (K + 1 + e + Fintype.card (Fin K → TransMonoid w) * (2 * K + 3)) + 1 :=
          Nat.add_le_add_right hpow 1
      _ ≤ S ^ (K + 1 + e + Fintype.card (Fin K → TransMonoid w) * (2 * K + 3) + 1) := hlast
  · -- semantics
    intro x
    rw [haacc x]
    have : blockProd letter start 0 len x
        = wordEnd ((List.range' start len).map (fun i => letter i x)) := by
      simp [blockProd, wordEnd]
    rw [this]


/-! ## The finer reduction: peeling the last letter off each epoch -/

/-- The product of a one-letter block is that letter. -/
theorem blockProd_succ {n : Nat} {G : Type} [Monoid G] (f : Nat → (Fin n → Bool) → G)
    (start a : Nat) (x : Fin n → Bool) : blockProd f start a (a + 1) x = f (start + a) x := by
  simp [blockProd]

/-- **The per-stretch recognition obligation.**  Like `EpochWordACC`, but the
blocks that have to be recognised are the *order-isomorphism stretches*: those
along which the rank/shape coordinate of the prefix products is constant at every
step, the shape-dropping last letter of an epoch having been peeled off.  This is
the leaf on which the holonomy argument acts: on such a stretch the letters are
order isomorphisms between the reachable sets
(`orderIso_blockEnd_of_shapeCoord_const`). -/
def StretchWordACC (w : Nat) : Prop :=
  ∃ modulus depth exponent : Nat,
    2 ≤ modulus ∧
      ∀ {n : Nat} (letter : Nat → (Fin n → Bool) → TransMonoid w) (size : Nat),
        (∀ i x, isNonCrossingMap w (letter i x)) →
        (∀ (i : Nat) (mm : TransMonoid w),
          ∃ a : ACCCircuit n 2,
            WellFormedACC a ∧
            (∀ q, a.layer q ≤ 2) ∧
            a.gateCount ≤ size ∧
            (∀ x, ACCAccepts a x ↔ letter i x = mm)) →
        ∀ start len : Nat,
          ∃ E : Nat → Nat → TransMonoid w → ACCCircuit n modulus,
            (∀ a c g, WellFormedACC (E a c g)) ∧
            (∀ a c g q, (E a c g).layer q ≤ depth) ∧
            (∀ a c g, (E a c g).gateCount ≤ (size + len + 2) ^ exponent) ∧
            (∀ (a c : Nat) (g : TransMonoid w) (x : Fin n → Bool), a ≤ c →
              ACCAccepts (E a c g) x → blockProd letter start a c x = g) ∧
            (∀ (x : Fin n → Bool) (a c : Nat), a ≤ c → c ≤ len →
              (∀ i, a ≤ i → i < c →
                windowShape letter start len x i = windowShape letter start len x (i + 1)) →
              ACCAccepts (E a c (blockProd letter start a c x)) x)

/-- **The letter word problem reduces to the per-stretch problem.**  Each of the
at most `epochBound w + 1` epochs of the window is split into an
order-isomorphism stretch followed by the single letter that drops the shape, so
the window is covered by `2 * (epochBound w + 1)` blocks, each recognised either
by the given single-letter recogniser or by the per-stretch recogniser; the
guess-and-verify gadget assembles them. -/
theorem letterWordACCGen_of_stretchWordACC (H : StretchWordACC w) : LetterWordACCGen w := by
  classical
  obtain ⟨Ms, Ds, es, hMs, hcore⟩ := H
  set M := 2 * Ms with hMdef
  have hMpos : 0 < M := by omega
  have hdvdS : Ms ∣ M := ⟨2, by omega⟩
  have hdvd2 : 2 ∣ M := ⟨Ms, rfl⟩
  set K := epochBound w + 1 with hKdef
  set KK := 2 * K with hKKdef
  set C1 := 2 * (M + 2) with hC1def
  set C2 := (KK + 1) * C1 + KK + 2 with hC2def
  set A := Fintype.card (Fin KK → TransMonoid w) with hAdef
  refine ⟨M, max (2 * Ds + 6) 1 + 2, KK + es + 3 + A * C2, by omega, ?_⟩
  intro n letter size hgen hrec start len h
  obtain ⟨E, hEwf, hElay, hEsz, hEsound, hEcomp⟩ := hcore letter size hgen hrec start len
  -- single letters, recognised at the common modulus `M`
  have hletter : ∀ (i : Nat) (mm : TransMonoid w),
      ∃ a : ACCCircuit n M,
        WellFormedACC a ∧ (∀ q, a.layer q ≤ 6) ∧ a.gateCount ≤ (M + 2) * size ∧
        (∀ x, ACCAccepts a x ↔ letter i x = mm) := by
    intro i mm
    obtain ⟨b, hbwf, hblay, hbsz, hbacc⟩ := hrec i mm
    refine ⟨accModulusLift b hdvd2, wellFormedACC_accModulusLift b hdvd2 hbwf, ?_, ?_, ?_⟩
    · intro q
      exact le_trans (accModulusLift_layer_le (c := b) (hM := hdvd2) (d := 2) hblay q) (by omega)
    · exact le_trans (accModulusLift_gateCount_le b hdvd2) (Nat.mul_le_mul_left _ hbsz)
    · intro x
      rw [evalACC_accModulusLift_of_pos hMpos hbwf x]
      exact hbacc x
  choose L hLwf hLlay hLsz hLacc using hletter
  -- the block recognisers: a single letter, or a stretch lifted to the modulus `M`
  set Bf : Nat → Nat → TransMonoid w → ACCCircuit n M := fun a b g =>
    if b = a + 1 then L (start + a) g else accModulusLift (E a b g) hdvdS with hBfdef
  have hBf_letter : ∀ a b g, b = a + 1 → Bf a b g = L (start + a) g := by
    intro a b g hb
    simp only [hBfdef, if_pos hb]
  have hBf_stretch : ∀ a b g, ¬ b = a + 1 → Bf a b g = accModulusLift (E a b g) hdvdS := by
    intro a b g hb
    simp only [hBfdef, if_neg hb]
  have hBwf : ∀ a b g, WellFormedACC (Bf a b g) := by
    intro a b g
    by_cases hb : b = a + 1
    · rw [hBf_letter a b g hb]; exact hLwf _ _
    · rw [hBf_stretch a b g hb]
      exact wellFormedACC_accModulusLift _ hdvdS (hEwf _ _ _)
  have hBlay : ∀ a b g q, (Bf a b g).layer q ≤ 2 * Ds + 6 := by
    intro a b g
    by_cases hb : b = a + 1
    · rw [hBf_letter a b g hb]
      exact fun q => le_trans (hLlay _ _ q) (by omega)
    · rw [hBf_stretch a b g hb]
      exact fun q =>
        le_trans (accModulusLift_layer_le (c := E a b g) (hM := hdvdS) (d := Ds)
          (hElay a b g) q) (by omega)
  have hBsz : ∀ a b g, (Bf a b g).gateCount ≤ (M + 2) * ((size + len + 2) ^ es + size) := by
    intro a b g
    by_cases hb : b = a + 1
    · rw [hBf_letter a b g hb]
      exact le_trans (hLsz _ _) (Nat.mul_le_mul_left _ (by omega))
    · rw [hBf_stretch a b g hb]
      refine le_trans (accModulusLift_gateCount_le _ hdvdS) ?_
      exact Nat.mul_le_mul_left _ (le_trans (hEsz a b g) (by omega))
  have hBsound : ∀ (a b : Nat) (g : TransMonoid w) (x : Fin n → Bool), a ≤ b →
      ACCAccepts (Bf a b g) x → blockProd letter start a b x = g := by
    intro a b g x hab hacc
    by_cases hb : b = a + 1
    · rw [hBf_letter a b g hb] at hacc
      subst hb
      rw [blockProd_succ]
      exact (hLacc _ _ x).mp hacc
    · rw [hBf_stretch a b g hb] at hacc
      rw [evalACC_accModulusLift_of_pos hMpos (hEwf a b g) x] at hacc
      exact hEsound a b g x hab hacc
  -- the decomposition of every input into `2 * K` blocks
  have hcomplete : ∀ x : Fin n → Bool, ∃ tf : Fin (KK + 1) → Fin (len + 1),
      (tf 0).val = 0 ∧ (tf (Fin.last KK)).val = len ∧
      (∀ j : Fin KK, (tf j.castSucc).val ≤ (tf j.succ).val) ∧
      (∀ j : Fin KK, ACCAccepts
          (Bf (tf j.castSucc).val (tf j.succ).val
            (blockProd letter start (tf j.castSucc).val (tf j.succ).val x)) x) := by
    intro x
    obtain ⟨t, ht0, htmono, htle, htlast, htblocks⟩ :=
      exists_constant_blocks (windowShape letter start len x) (epochBound w) 0 len
        (card_changeSet_windowShape_le letter hgen start len x)
    set t2 : Nat → Nat := fun k =>
      if k % 2 = 0 then t (k / 2) else max (t (k / 2)) (t (k / 2 + 1) - 1) with ht2def
    have ht2_even : ∀ i, t2 (2 * i) = t i := by
      intro i
      have h1 : (2 * i) % 2 = 0 := by omega
      have h2 : (2 * i) / 2 = i := by omega
      simp only [ht2def, h1, h2, if_pos]
    have ht2_odd : ∀ i, t2 (2 * i + 1) = max (t i) (t (i + 1) - 1) := by
      intro i
      have h1 : ¬ (2 * i + 1) % 2 = 0 := by omega
      have h2 : (2 * i + 1) / 2 = i := by omega
      simp only [ht2def, h1, h2, if_false]
    have ht2_le : ∀ k, t2 k ≤ len := by
      intro k
      rcases Nat.even_or_odd k with he | ho
      · obtain ⟨i, hi⟩ := he
        have : k = 2 * i := by omega
        rw [this, ht2_even]
        exact htle i
      · obtain ⟨i, hi⟩ := ho
        have : k = 2 * i + 1 := by omega
        rw [this, ht2_odd]
        have h1 := htle i
        have h2 := htle (i + 1)
        omega
    have ht2_mono : ∀ k, t2 k ≤ t2 (k + 1) := by
      intro k
      rcases Nat.even_or_odd k with he | ho
      · obtain ⟨i, hi⟩ := he
        have hk : k = 2 * i := by omega
        subst hk
        rw [ht2_even, ht2_odd]
        omega
      · obtain ⟨i, hi⟩ := ho
        have hk : k = 2 * i + 1 := by omega
        subst hk
        have hnext : 2 * i + 1 + 1 = 2 * (i + 1) := by omega
        rw [ht2_odd, hnext, ht2_even]
        have := htmono i
        omega
    -- every block is accepted
    have hblock : ∀ k, k < KK →
        ACCAccepts (Bf (t2 k) (t2 (k + 1)) (blockProd letter start (t2 k) (t2 (k + 1)) x)) x := by
      have hsingle : ∀ a : Nat,
          ACCAccepts (Bf a (a + 1) (blockProd letter start a (a + 1) x)) x := by
        intro a
        rw [hBf_letter a (a + 1) _ rfl, blockProd_succ]
        exact (hLacc _ _ x).mpr rfl
      have hstretch : ∀ a c : Nat, a ≤ c → c ≤ len → ¬ c = a + 1 →
          (∀ i, a ≤ i → i < c →
            windowShape letter start len x i = windowShape letter start len x (i + 1)) →
          ACCAccepts (Bf a c (blockProd letter start a c x)) x := by
        intro a c hac hcl hne hcond
        rw [hBf_stretch a c _ hne,
          evalACC_accModulusLift_of_pos hMpos (hEwf a c _) x]
        exact hEcomp x a c hac hcl hcond
      intro k hk
      rcases Nat.even_or_odd k with he | ho
      · obtain ⟨i, hi⟩ := he
        have hk2 : k = 2 * i := by omega
        subst hk2
        have hnext : 2 * i + 1 = 2 * i + 1 := rfl
        rw [ht2_even, ht2_odd]
        by_cases hb : max (t i) (t (i + 1) - 1) = t i + 1
        · rw [hb]; exact hsingle (t i)
        · refine hstretch _ _ (le_max_left _ _) ?_ hb ?_
          · have h1 := htle i
            have h2 := htle (i + 1)
            omega
          · intro i' hi1 hi2
            have hmi := htmono i
            have hlt : i' + 1 < t (i + 1) := by
              rcases Nat.eq_or_lt_of_le hmi with heq | hlt
              · omega
              · omega
            have hb2 := htblocks i i' hi1 hlt
            simpa using hb2
      · obtain ⟨i, hi⟩ := ho
        have hk2 : k = 2 * i + 1 := by omega
        subst hk2
        have hnext : 2 * i + 1 + 1 = 2 * (i + 1) := by omega
        rw [ht2_odd, hnext, ht2_even]
        have hmi := htmono i
        rcases Nat.eq_or_lt_of_le hmi with heq | hlt
        · -- an empty epoch: the two sub-blocks are empty
          have hmax : max (t i) (t (i + 1) - 1) = t (i + 1) := by omega
          rw [hmax]
          refine hstretch _ _ (le_refl _) (htle (i + 1)) (by omega) ?_
          intro i' hi1 hi2
          omega
        · have hmax : max (t i) (t (i + 1) - 1) = t (i + 1) - 1 := by omega
          rw [hmax]
          have hsucc : t (i + 1) = (t (i + 1) - 1) + 1 := by omega
          rw [hsucc]
          exact hsingle _
    refine ⟨fun j => ⟨t2 j.val, by have := ht2_le j.val; omega⟩, ?_, ?_, ?_, ?_⟩
    · have h0 : t2 0 = 0 := by
        have := ht2_even 0
        simpa [ht0] using this
      simpa using h0
    · have hlast : t2 (2 * K) = len := by
        rw [ht2_even]
        exact htlast
      simpa [Fin.val_last, hKKdef] using hlast
    · intro j
      simpa [Fin.val_castSucc, Fin.val_succ] using ht2_mono j.val
    · intro j
      have := hblock j.val j.isLt
      simpa [Fin.val_castSucc, Fin.val_succ] using this
  obtain ⟨a, hawf, halay, hasz, haacc⟩ :=
    exists_acc_blockAssembly (G := TransMonoid w) (K := KK) (len := len)
      (d := 2 * Ds + 6) (Sz := (M + 2) * ((size + len + 2) ^ es + size))
      letter start Bf hBwf hBlay hBsz hBsound hcomplete h
  refine ⟨a, hawf, halay, ?_, ?_⟩
  · -- size bound
    set S := size + len + 2 with hS
    have hS2 : 2 ≤ S := by omega
    have hSe : 1 ≤ S ^ (es + 1) := Nat.one_le_pow _ _ (by omega)
    have hcard1 : Fintype.card (Fin (KK + 1) → Fin (len + 1)) ≤ S ^ (KK + 1) := by
      have hc : Fintype.card (Fin (KK + 1) → Fin (len + 1)) = (len + 1) ^ (KK + 1) := by
        simp
      rw [hc]
      exact Nat.pow_le_pow_left (by omega) _
    have hSz : (M + 2) * (S ^ es + size) ≤ C1 * S ^ (es + 1) := by
      have h1 : S ^ es ≤ S ^ (es + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      have h2 : size ≤ S ^ (es + 1) := by
        have : S ≤ S ^ (es + 1) := by
          calc S = S ^ 1 := (pow_one S).symm
            _ ≤ S ^ (es + 1) := Nat.pow_le_pow_right (by omega) (by omega)
        omega
      calc (M + 2) * (S ^ es + size) ≤ (M + 2) * (S ^ (es + 1) + S ^ (es + 1)) :=
            Nat.mul_le_mul_left _ (Nat.add_le_add h1 h2)
        _ = C1 * S ^ (es + 1) := by rw [hC1def]; ring
    have hfactor : (KK + 1) * ((M + 2) * (S ^ es + size) + 1) + 1 ≤ C2 * S ^ (es + 1) := by
      have h1 : (KK + 1) * ((M + 2) * (S ^ es + size) + 1) + 1
          ≤ (KK + 1) * (C1 * S ^ (es + 1)) + (KK + 2) := by
        have hexp : (KK + 1) * ((M + 2) * (S ^ es + size) + 1)
            = (KK + 1) * ((M + 2) * (S ^ es + size)) + (KK + 1) := by
          rw [Nat.mul_add, Nat.mul_one]
        have := Nat.mul_le_mul_left (KK + 1) hSz
        omega
      have h2 : (KK + 2) ≤ (KK + 2) * S ^ (es + 1) := Nat.le_mul_of_pos_right _ (by omega)
      have h3 : (KK + 1) * (C1 * S ^ (es + 1)) + (KK + 2) * S ^ (es + 1) = C2 * S ^ (es + 1) := by
        rw [hC2def]; ring
      omega
    have hstep : Fintype.card (Fin (KK + 1) → Fin (len + 1)) * A
        * ((KK + 1) * ((M + 2) * (S ^ es + size) + 1) + 1)
        ≤ (A * C2) * S ^ (KK + 1 + (es + 1)) := by
      calc Fintype.card (Fin (KK + 1) → Fin (len + 1)) * A
            * ((KK + 1) * ((M + 2) * (S ^ es + size) + 1) + 1)
          ≤ (S ^ (KK + 1) * A) * (C2 * S ^ (es + 1)) :=
            Nat.mul_le_mul (Nat.mul_le_mul_right _ hcard1) hfactor
        _ = (A * C2) * (S ^ (KK + 1) * S ^ (es + 1)) := by ring
        _ = (A * C2) * S ^ (KK + 1 + (es + 1)) := by rw [← pow_add]
    have hpow : (A * C2) * S ^ (KK + 1 + (es + 1)) ≤ S ^ (KK + 1 + (es + 1) + A * C2) :=
      const_mul_pow_le_pow hS2
    have hlast : S ^ (KK + 1 + (es + 1) + A * C2) + 1 ≤ S ^ (KK + es + 3 + A * C2) := by
      set F := KK + 1 + (es + 1) + A * C2 with hF
      have h1 : 1 ≤ S ^ F := Nat.one_le_pow _ _ (by omega)
      have h2 : 2 * S ^ F ≤ S * S ^ F := Nat.mul_le_mul_right _ hS2
      have h3 : S * S ^ F = S ^ (F + 1) := by ring
      have h4 : F + 1 = KK + es + 3 + A * C2 := by rw [hF]; ring
      rw [← h4]
      omega
    calc a.gateCount
        ≤ Fintype.card (Fin (KK + 1) → Fin (len + 1)) * Fintype.card (Fin KK → TransMonoid w)
            * ((KK + 1) * ((M + 2) * (S ^ es + size) + 1) + 1) + 1 := hasz
      _ ≤ (A * C2) * S ^ (KK + 1 + (es + 1)) + 1 := Nat.add_le_add_right hstep 1
      _ ≤ S ^ (KK + 1 + (es + 1) + A * C2) + 1 := Nat.add_le_add_right hpow 1
      _ ≤ S ^ (KK + es + 3 + A * C2) := hlast
  · -- semantics
    intro x
    rw [haacc x]
    have hprod : blockProd letter start 0 len x
        = wordEnd ((List.range' start len).map (fun i => letter i x)) := by
      simp [blockProd, wordEnd]
    rw [hprod]

end Internal
end AllenderOQ3
