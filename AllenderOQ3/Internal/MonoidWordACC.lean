import AllenderOQ3.Internal.EpochReduction
import AllenderOQ3.Internal.ACCGadgets

/-!
# The word problem of a fixed finite monoid in `ACC`

The last circuit-shaped obligation of the cylindrical simulation
(`EpochWordACC`, and through it `LetterWordACCGen`, `WindowWordACC`,
`ShortWordProblemACC`) is, after all the combinatorial assembly of
`EpochReduction`/`BlockAssembly` has been discharged, an instance of a single
completely standard question:

> given a *fixed finite monoid* `M`, a window of letters of `M` each of which is
> recognised by a depth-two circuit of size `size`, is the value of the product
> of a sub-block of the window recognised by a constant-depth circuit of size
> polynomial in `size + len`?

This file isolates that question as `MonoidWordACC M`, a statement that mentions
no cylinders, no epochs and no rank/shape coordinate, only the monoid `M`.

* `monoidWordACC_of_subsingleton` shows the interface is satisfiable (a sanity
  check that the definition is not vacuous or unsatisfiable by shape).
* `monoidWordACC_submonoid` and `monoidWordACC_of_surjective` are the two
  closure properties that make the notion behave like the usual "the word
  problem of `M` is in `ACC⁰`": it passes to submonoids and to quotients, hence
  to *divisors* of `M` (`monoidWordACC_of_divides`).
* `epochWordACC_of_monoidWordACC` reduces the remaining cylindrical obligation
  `EpochWordACC w` to `MonoidWordACC (NonCrossing w)`, i.e. to the word problem
  of the incidence-constrained submonoid alone.  The reduction is `sorry`-free:
  the epoch hypothesis is simply not needed once the word problem of the whole
  monoid is available (indeed it cannot help — out of a rank-one prefix every
  continuation is shape-constant, see the discussion in
  `StretchHolonomyObstruction`).

What remains open is exactly `monoidWordACC_nonCrossing`, the Barrington–Thérien
statement for `NonCrossing w`.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace AllenderOQ3
namespace Internal

attribute [local instance] Classical.propDecidable

/-- **The word problem of the finite monoid `M` is in `ACC⁰`**, in the
quantitative form needed by the cylindrical simulation.

There are a modulus `≥ 2`, a depth and an exponent, all depending on `M` only,
such that: whenever the letters `letter i x` of a window are individually
recognised by depth-two `ACC[2]` circuits of size at most `size` (one for each
position `i` and each candidate value), every block `[start + a, start + b)` of
the window has a family of circuits `B a b g` of that constant depth and of size
polynomial in `size + len`, which never accept unless the product of the letters
of the block is `g`, and do accept the true product of every block *inside the
window* `[start, start + len)`.

Completeness has to be restricted to blocks inside the window: a block of length
far beyond `len` carries more positions than the allowed size, so no bound
polynomial in `size + len` could hold for a recogniser of it.  Soundness, on the
other hand, is required on every block and every input. -/
def MonoidWordACC (M : Type) [Monoid M] [Finite M] : Prop :=
  ∃ modulus depth exponent : Nat,
    2 ≤ modulus ∧
      ∀ {n : Nat} (letter : Nat → (Fin n → Bool) → M) (size : Nat),
        (∀ (i : Nat) (mm : M),
          ∃ a : ACCCircuit n 2,
            WellFormedACC a ∧
            (∀ q, a.layer q ≤ 2) ∧
            a.gateCount ≤ size ∧
            (∀ x, ACCAccepts a x ↔ letter i x = mm)) →
        ∀ start len : Nat,
          ∃ B : Nat → Nat → M → ACCCircuit n modulus,
            (∀ a b g, WellFormedACC (B a b g)) ∧
            (∀ a b g q, (B a b g).layer q ≤ depth) ∧
            (∀ a b g, (B a b g).gateCount ≤ (size + len + 2) ^ exponent) ∧
            (∀ (a b : Nat) (g : M) (x : Fin n → Bool),
              ACCAccepts (B a b g) x → blockProd letter start a b x = g) ∧
            (∀ (x : Fin n → Bool) (a b : Nat), a ≤ b → b ≤ len →
              ACCAccepts (B a b (blockProd letter start a b x)) x)

/-! ## The interface is satisfiable -/

/-- **Sanity check.**  For a trivial monoid the constant circuit works, so
`MonoidWordACC` is not unsatisfiable by shape. -/
theorem monoidWordACC_of_subsingleton (M : Type) [Monoid M] [Finite M] [Subsingleton M] :
    MonoidWordACC M := by
  refine ⟨2, 1, 0, le_refl 2, ?_⟩
  intro n letter size _ start len
  refine ⟨fun _ _ _ => accConst n 2 true, fun _ _ _ => wellFormedACC_accConst n 2 true,
    ?_, ?_, ?_, ?_⟩
  · intro a b g q
    exact le_of_eq (accConst_layer n 2 true q)
  · intro a b g
    rw [accConst_gateCount, pow_zero]
  · intro a b g x _
    exact Subsingleton.elim _ _
  · intro x a b _ _
    exact (accAccepts_accConst n 2 true x).mpr rfl

/-! ## Blocks of a submonoid-valued word -/

/-- The product of a block of letters of a submonoid, read in the ambient
monoid. -/
theorem coe_blockProd {N : Type} [Monoid N] {S : Submonoid N} {n : Nat}
    (f : Nat → (Fin n → Bool) → S) (start a b : Nat) (x : Fin n → Bool) :
    ((blockProd f start a b x : S) : N)
      = blockProd (fun i y => ((f i y : S) : N)) start a b x := by
  simp [blockProd, List.map_map, Function.comp_def]

/-! ## Closure properties -/

/-- **The word problem passes to submonoids.** -/
theorem monoidWordACC_submonoid {N : Type} [Monoid N] [Finite N]
    (H : MonoidWordACC N) (S : Submonoid N) : MonoidWordACC S := by
  classical
  obtain ⟨M, D, e, hM, hcore⟩ := H
  refine ⟨M, max D 1, e, hM, ?_⟩
  intro n letter size hrec start len
  -- the same word, read in the ambient monoid
  set letterN : Nat → (Fin n → Bool) → N := fun i x => ((letter i x : S) : N) with hletterN
  have hrecN : ∀ (i : Nat) (mm : N),
      ∃ a : ACCCircuit n 2,
        WellFormedACC a ∧ (∀ q, a.layer q ≤ 2) ∧ a.gateCount ≤ size ∧
        (∀ x, ACCAccepts a x ↔ letterN i x = mm) := by
    intro i mm
    by_cases hmm : mm ∈ S
    · obtain ⟨a, h1, h2, h3, h4⟩ := hrec i ⟨mm, hmm⟩
      refine ⟨a, h1, h2, h3, fun x => ?_⟩
      rw [h4 x, hletterN]
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    · refine ⟨accConst n 2 false, wellFormedACC_accConst n 2 false, ?_, ?_, ?_⟩
      · intro q
        rw [accConst_layer]; omega
      · rw [accConst_gateCount]
        by_contra hc
        -- with `size = 0` even the given recognisers are impossible, so anything follows
        obtain ⟨a, _, _, h3, _⟩ := hrec i 1
        have := a.output.isLt
        omega
      · intro x
        rw [accAccepts_accConst]
        constructor
        · intro h; exact absurd h (by simp)
        · intro h
          exact absurd (h ▸ (letter i x).2) hmm
  obtain ⟨B, hwf, hlay, hsz, hsound, hcomp⟩ := hcore letterN size hrecN start len
  have hblock : ∀ (a b : Nat) (x : Fin n → Bool),
      blockProd letterN start a b x = ((blockProd letter start a b x : S) : N) := by
    intro a b x
    rw [hletterN]
    exact (coe_blockProd letter start a b x).symm
  refine ⟨fun a b g => B a b ((g : S) : N), fun a b g => hwf _ _ _, ?_, ?_, ?_, ?_⟩
  · intro a b g q
    exact le_trans (hlay _ _ _ q) (le_max_left _ _)
  · intro a b g
    exact hsz _ _ _
  · intro a b g x hx
    have h := hsound a b ((g : S) : N) x hx
    rw [hblock a b x] at h
    exact Subtype.ext h
  · intro x a b hab hbl
    have h := hcomp x a b hab hbl
    rw [hblock a b x] at h
    exact h

/-- The image of a block product under a monoid homomorphism. -/
theorem map_blockProd {N M' : Type} [Monoid N] [Monoid M'] {n : Nat} (phi : N →* M')
    (f : Nat → (Fin n → Bool) → N) (start a b : Nat) (x : Fin n → Bool) :
    phi (blockProd f start a b x) = blockProd (fun i y => phi (f i y)) start a b x := by
  simp [blockProd, map_list_prod, List.map_map, Function.comp_def]

/-- **The word problem passes to quotients**, i.e. along a surjective monoid
homomorphism: a letter of the quotient is lifted through a set-theoretic section,
and the value of the lifted block product is guessed among the (constantly many)
preimages of the target. -/
theorem monoidWordACC_of_surjective {N M' : Type} [Monoid N] [Finite N] [Monoid M'] [Finite M']
    (H : MonoidWordACC N) (phi : N →* M') (hphi : Function.Surjective phi) :
    MonoidWordACC M' := by
  classical
  haveI : Fintype N := Fintype.ofFinite N
  obtain ⟨Mo, D, e, hMo, hcore⟩ := H
  -- a set-theoretic section of `phi`
  choose sec hsec using hphi
  have hsecinj : Function.Injective sec := Function.LeftInverse.injective hsec
  refine ⟨Mo, max D 1 + 2, e + (Fintype.card N * 3 + 1), hMo, ?_⟩
  intro n letter size hrec start len
  set letterN : Nat → (Fin n → Bool) → N := fun i x => sec (letter i x) with hletterN
  have hsize_pos : 1 ≤ size := by
    obtain ⟨a, _, _, h3, _⟩ := hrec 0 1
    have := a.output.isLt
    omega
  have hrecN : ∀ (i : Nat) (mm : N),
      ∃ a : ACCCircuit n 2,
        WellFormedACC a ∧ (∀ q, a.layer q ≤ 2) ∧ a.gateCount ≤ size ∧
        (∀ x, ACCAccepts a x ↔ letterN i x = mm) := by
    intro i mm
    by_cases hmm : sec (phi mm) = mm
    · obtain ⟨a, h1, h2, h3, h4⟩ := hrec i (phi mm)
      refine ⟨a, h1, h2, h3, fun x => ?_⟩
      rw [h4 x, hletterN]
      change letter i x = phi mm ↔ sec (letter i x) = mm
      constructor
      · intro h
        rw [h]
        exact hmm
      · intro h
        exact hsecinj (h.trans hmm.symm)
    · refine ⟨accConst n 2 false, wellFormedACC_accConst n 2 false, ?_, ?_, ?_⟩
      · intro q
        rw [accConst_layer]; omega
      · rw [accConst_gateCount]; omega
      · intro x
        rw [accAccepts_accConst]
        constructor
        · intro h; exact absurd h (by simp)
        · intro h
          refine absurd ?_ hmm
          rw [← h, hletterN, hsec]
  obtain ⟨B, hwf, hlay, hsz, hsound, hcomp⟩ := hcore letterN size hrecN start len
  have hmapblock : ∀ (a b : Nat) (x : Fin n → Bool),
      phi (blockProd letterN start a b x) = blockProd letter start a b x := by
    intro a b x
    rw [map_blockProd phi letterN start a b x, hletterN]
    simp [hsec]
  have hkey : ∀ (a b : Nat) (g : M'),
      ∃ c : ACCCircuit n Mo,
        WellFormedACC c ∧ (∀ q, c.layer q ≤ max D 1 + 2) ∧
        c.gateCount ≤ (size + len + 2) ^ (e + (Fintype.card N * 3 + 1)) ∧
        (∀ x, ACCAccepts c x → blockProd letter start a b x = g) ∧
        (a ≤ b → b ≤ len → ∀ x, blockProd letter start a b x = g → ACCAccepts c x) := by
    intro a b g
    set ee := Fintype.equivFin N with hee
    set fam : Fin (Fintype.card N) → ACCCircuit n Mo := fun i =>
      if phi (ee.symm i) = g then B a b (ee.symm i) else accConst n Mo false with hfam
    have hfam_pos : ∀ i, phi (ee.symm i) = g → fam i = B a b (ee.symm i) := by
      intro i hi
      simp only [hfam, if_pos hi]
    have hfam_neg : ∀ i, ¬ phi (ee.symm i) = g → fam i = accConst n Mo false := by
      intro i hi
      simp only [hfam, if_neg hi]
    have hfam_wf : ∀ i, WellFormedACC (fam i) := by
      intro i
      by_cases hi : phi (ee.symm i) = g
      · rw [hfam_pos i hi]; exact hwf _ _ _
      · rw [hfam_neg i hi]; exact wellFormedACC_accConst n Mo false
    have hfam_lay : ∀ i q, (fam i).layer q ≤ max D 1 := by
      intro i
      by_cases hi : phi (ee.symm i) = g
      · rw [hfam_pos i hi]
        exact fun q => le_trans (hlay _ _ _ q) (le_max_left _ _)
      · rw [hfam_neg i hi]
        intro q
        rw [accConst_layer]
        exact le_max_right _ _
    have hfam_sz : ∀ i, (fam i).gateCount ≤ (size + len + 2) ^ e := by
      intro i
      by_cases hi : phi (ee.symm i) = g
      · rw [hfam_pos i hi]; exact hsz _ _ _
      · rw [hfam_neg i hi, accConst_gateCount]
        exact Nat.one_le_pow _ _ (by omega)
    obtain ⟨c, hcwf, hclay, hcsz, hcacc⟩ :=
      exists_acc_orPair (n := n) (m := Mo) (K := Fintype.card N) (d := max D 1)
        (S1 := (size + len + 2) ^ e) (S2 := 1)
        fam (fun _ => accConst n Mo true) hfam_wf
        (fun _ => wellFormedACC_accConst n Mo true) hfam_lay
        (fun _ q => by rw [accConst_layer]; exact le_max_right _ _)
        hfam_sz (fun _ => le_of_eq (accConst_gateCount n Mo true))
    have hconst : ∀ y : Fin n → Bool, ACCAccepts (accConst n Mo true) y :=
      fun y => (accAccepts_accConst n Mo true y).mpr rfl
    refine ⟨c, hcwf, hclay, ?_, ?_, ?_⟩
    · -- size bound
      have hP : 2 ≤ size + len + 2 := by omega
      have hS : 1 ≤ (size + len + 2) ^ e := Nat.one_le_pow _ _ (by omega)
      have h1 : Fintype.card N * ((size + len + 2) ^ e + 1 + 1) + 1
          ≤ (Fintype.card N * 3 + 1) * (size + len + 2) ^ e :=
        assemble_size_bound (K := Fintype.card N) (A := 0) hS
      exact le_trans hcsz (le_trans h1 (const_mul_pow_le_pow hP))
    · -- soundness
      intro x hx
      rw [hcacc x] at hx
      obtain ⟨i, hi, -⟩ := hx
      by_cases hphii : phi (ee.symm i) = g
      · rw [hfam_pos i hphii] at hi
        have hval := hsound a b (ee.symm i) x hi
        rw [← hmapblock a b x, hval]
        exact hphii
      · rw [hfam_neg i hphii, accAccepts_accConst] at hi
        exact absurd hi (by simp)
    · -- completeness inside the window
      intro hab hbl x hg
      rw [hcacc x]
      have hval : phi (blockProd letterN start a b x) = g := by
        rw [hmapblock a b x]; exact hg
      refine ⟨ee (blockProd letterN start a b x), ?_, hconst x⟩
      have hsymm : ee.symm (ee (blockProd letterN start a b x))
          = blockProd letterN start a b x := ee.symm_apply_apply _
      have hcond : phi (ee.symm (ee (blockProd letterN start a b x))) = g := by
        rw [hsymm]; exact hval
      rw [hfam_pos _ hcond, hsymm]
      exact hcomp x a b hab hbl
  choose B' hB'wf hB'lay hB'sz hB'sound hB'comp using hkey
  refine ⟨B', hB'wf, hB'lay, hB'sz, hB'sound, ?_⟩
  intro x a b hab hbl
  exact hB'comp a b _ hab hbl x rfl

/-- **The word problem passes to divisors**: a quotient of a submonoid of `N`. -/
theorem monoidWordACC_of_divides {N M' : Type} [Monoid N] [Finite N] [Monoid M'] [Finite M']
    (H : MonoidWordACC N) (S : Submonoid N) (phi : S →* M') (hphi : Function.Surjective phi) :
    MonoidWordACC M' :=
  monoidWordACC_of_surjective (monoidWordACC_submonoid H S) phi hphi

/-! ## The reduction of the cylindrical obligation -/

/- The former Barrington–Thérien leaf `monoidWordACC_nonCrossing` now lives in
`LocalDivisorRoute.lean`, derived from the local-divisor induction
(`LocalDivisorInduction.lean`) and the abelianness of the local groups of
`NonCrossing w`.  See `docs/LOCAL_DIVISOR_PLAN.md`. -/

/-- **The per-epoch obligation follows from the word problem of `NonCrossing w`.**

Every letter of the window is a cylindrical layer map, hence an element of
`NonCrossing w`; the product of a block is therefore the image of a block product
of the corresponding word over the submonoid, and the recognisers supplied by
`MonoidWordACC (NonCrossing w)` decide it.  This is more than `EpochWordACC`
asks for: the recognisers are complete on all blocks of the window, epoch or
not. -/
theorem epochWordACC_of_monoidWordACC {w : Nat} (H : MonoidWordACC (NonCrossing w)) :
    EpochWordACC w := by
  classical
  obtain ⟨M, D, e, hM, hcore⟩ := H
  refine ⟨M, max D 1, e, hM, ?_⟩
  intro n letter size hgen hrec start len
  set letterS : Nat → (Fin n → Bool) → NonCrossing w :=
    fun i x => ⟨letter i x, Submonoid.subset_closure (hgen i x)⟩ with hletterS
  have hcoe : ∀ (a b : Nat) (x : Fin n → Bool),
      ((blockProd letterS start a b x : NonCrossing w) : TransMonoid w)
        = blockProd letter start a b x := by
    intro a b x
    rw [coe_blockProd letterS start a b x]
  have hrecS : ∀ (i : Nat) (mm : NonCrossing w),
      ∃ a : ACCCircuit n 2,
        WellFormedACC a ∧ (∀ q, a.layer q ≤ 2) ∧ a.gateCount ≤ size ∧
        (∀ x, ACCAccepts a x ↔ letterS i x = mm) := by
    intro i mm
    obtain ⟨a, h1, h2, h3, h4⟩ := hrec i (mm : TransMonoid w)
    refine ⟨a, h1, h2, h3, fun x => ?_⟩
    rw [h4 x, hletterS]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  obtain ⟨B, hwf, hlay, hsz, hsound, hcomp⟩ := hcore letterS size hrecS start len
  set Bt : Nat → Nat → TransMonoid w → ACCCircuit n M := fun a b g =>
    if h : g ∈ NonCrossing w then B a b ⟨g, h⟩ else accConst n M false with hBt
  have hBt_pos : ∀ (a b : Nat) (g : TransMonoid w) (h : g ∈ NonCrossing w),
      Bt a b g = B a b ⟨g, h⟩ := by
    intro a b g h
    simp only [hBt, dif_pos h]
  have hBt_neg : ∀ (a b : Nat) (g : TransMonoid w), g ∉ NonCrossing w →
      Bt a b g = accConst n M false := by
    intro a b g h
    simp only [hBt, dif_neg h]
  refine ⟨Bt, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b g
    by_cases h : g ∈ NonCrossing w
    · rw [hBt_pos a b g h]; exact hwf _ _ _
    · rw [hBt_neg a b g h]; exact wellFormedACC_accConst n M false
  · intro a b g q
    revert q
    by_cases h : g ∈ NonCrossing w
    · rw [hBt_pos a b g h]
      exact fun q => le_trans (hlay _ _ _ q) (le_max_left _ _)
    · rw [hBt_neg a b g h]
      intro q
      rw [accConst_layer]
      exact le_max_right _ _
  · intro a b g
    by_cases h : g ∈ NonCrossing w
    · rw [hBt_pos a b g h]; exact hsz _ _ _
    · rw [hBt_neg a b g h, accConst_gateCount]
      exact Nat.one_le_pow _ _ (by omega)
  · -- soundness
    intro a b g x _ haccept
    by_cases h : g ∈ NonCrossing w
    · rw [hBt_pos a b g h] at haccept
      have hval := hsound a b ⟨g, h⟩ x haccept
      rw [← hcoe a b x, hval]
    · rw [hBt_neg a b g h] at haccept
      rw [accAccepts_accConst] at haccept
      exact absurd haccept (by simp)
  · -- completeness
    intro x a b hab hbl _
    have hmem : blockProd letter start a b x ∈ NonCrossing w := by
      rw [← hcoe a b x]
      exact (blockProd letterS start a b x).2
    rw [hBt_pos a b _ hmem]
    have h := hcomp x a b hab hbl
    have heq : blockProd letterS start a b x
        = ⟨blockProd letter start a b x, hmem⟩ := Subtype.ext (hcoe a b x)
    rwa [heq] at h

end Internal
end AllenderOQ3
