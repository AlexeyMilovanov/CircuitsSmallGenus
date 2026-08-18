import AllenderOQ3.Internal.WordCompress
import AllenderOQ3.Internal.WordProblemReduction
import AllenderOQ3.Internal.ACCLetter
import AllenderOQ3.Internal.LetterWordUnits
import AllenderOQ3.Internal.CascadeAperiodic
import AllenderOQ3.Internal.CascadeCyclic
import AllenderOQ3.Internal.CascadeCoordinate

/-!
# The word problem only has to be solved for short words

`WordProblemACC w` asks for an `ACC` recogniser of the predicate "the product of
*all* layer letters below the output layer equals `g`".  The number of layers is
not bounded by the size of the circuit, so as stated the obligation involves
words of unbounded length.

`WordCompress` removes that slack: the word factors as a degenerate prefix
(`1` or the constant-`false` transition `zeroTrans w`) times a suffix of length
at most `c.gateCount`, and both the split point and the prefix depend only on
the circuit and its certificate, not on the input.  This file records the
resulting weaker obligation

* `ShortWordProblemACC w` — recognise `pre * (product of the layer letters over a
  window `List.range' start len` of length `len ≤ c.gateCount`) = g`,

and proves

* `wordProblemACC_of_short : ShortWordProblemACC w → WordProblemACC w`,
* `quantitativeCylindricalACC_of_shortWordProblem` — the frozen principle follows
  from the short-word obligation alone.
-/

set_option autoImplicit false

namespace AllenderOQ3.Internal

/-- The layer word of a circuit, restricted to a window of layer indices. -/
noncomputable def windowWord {n : Nat} (c : ADRCircuit n) (cert : IncidenceCylinder c)
    (x : Fin n → Bool) (w start len : Nat) : TransMonoid w :=
  wordEnd ((List.range' start len).map (fun i => layerTrans c cert x i))

/-- A word over a window splits at any interior point. -/
theorem wordEnd_range'_split {W : Nat} (letter : Nat → TransMonoid W)
    (start len₁ len₂ : Nat) :
    wordEnd ((List.range' start (len₁ + len₂)).map letter)
      = wordEnd ((List.range' start len₁).map letter)
        * wordEnd ((List.range' (start + len₁) len₂).map letter) := by
  rw [← List.range'_append_1, List.map_append, wordEnd_append]

/-- **Cutting a window of a letter word in two.**  Recognisers for the products
over two consecutive windows combine, by guess-and-verify over the value of each
part, into a recogniser for the product over the concatenated window. -/
theorem exists_acc_letterWord_concat {n m w : Nat} {d s : Nat}
    (letter : Nat → (Fin n → Bool) → TransMonoid w) (start len₁ len₂ : Nat)
    (A : TransMonoid w → ACCCircuit n m) (hAwf : ∀ g, WellFormedACC (A g))
    (hAlay : ∀ g q, (A g).layer q ≤ d) (hAsz : ∀ g, (A g).gateCount ≤ s)
    (hAacc : ∀ g x, ACCAccepts (A g) x ↔
      wordEnd ((List.range' start len₁).map (fun i => letter i x)) = g)
    (B : TransMonoid w → ACCCircuit n m) (hBwf : ∀ g, WellFormedACC (B g))
    (hBlay : ∀ g q, (B g).layer q ≤ d) (hBsz : ∀ g, (B g).gateCount ≤ s)
    (hBacc : ∀ g x, ACCAccepts (B g) x ↔
      wordEnd ((List.range' (start + len₁) len₂).map (fun i => letter i x)) = g)
    (h : TransMonoid w) :
    ∃ a : ACCCircuit n m,
      WellFormedACC a ∧
      (∀ q, a.layer q ≤ max d 1 + 2) ∧
      a.gateCount ≤ Fintype.card (TransMonoid w) * Fintype.card (TransMonoid w) * (2 * s + 2) + 1 ∧
      (∀ x, ACCAccepts a x ↔
        wordEnd ((List.range' start (len₁ + len₂)).map (fun i => letter i x)) = h) := by
  obtain ⟨a, hwf, hlay, hsz, hacc⟩ :=
    exists_acc_mul_pair (M := TransMonoid w)
      (fun x => wordEnd ((List.range' start len₁).map (fun i => letter i x)))
      (fun x => wordEnd ((List.range' (start + len₁) len₂).map (fun i => letter i x)))
      A hAwf hAlay hAsz hAacc B hBwf hBlay hBsz hBacc h
  refine ⟨a, hwf, hlay, hsz, fun x => ?_⟩
  rw [hacc x, wordEnd_range'_split (fun i => letter i x) start len₁ len₂]

/-- The window word splits at any interior point. -/
theorem windowWord_split {n w : Nat} (c : ADRCircuit n) (cert : IncidenceCylinder c)
    (x : Fin n → Bool) (start len₁ len₂ : Nat) :
    windowWord c cert x w start (len₁ + len₂)
      = windowWord c cert x w start len₁ * windowWord c cert x w (start + len₁) len₂ :=
  wordEnd_range'_split (fun i => layerTrans c cert x i) start len₁ len₂

/-- Every window word lies in the non-crossing submonoid. -/
theorem windowWord_mem_nonCrossing {n w : Nat} (c : ADRCircuit n)
    (cert : IncidenceCylinder c) (hN : HMVNormal c) (hW : TotalWidthAtMost c w)
    (x : Fin n → Bool) (start len : Nat) :
    windowWord c cert x w start len ∈ NonCrossing w := by
  refine Submonoid.list_prod_mem _ ?_
  intro g hg
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hg
  exact layerTrans_mem_nonCrossing c cert x i hN hW

/-- The compressed suffix of the layer word is a window word. -/
theorem drop_layerWord_eq_windowWord {n w : Nat} (c : ADRCircuit n)
    (cert : IncidenceCylinder c) (x : Fin n → Bool) (k : Nat) :
    wordEnd ((layerWord c cert x w).drop k)
      = windowWord c cert x w k (c.layer c.output - k) := by
  have hdrop : (List.range (c.layer c.output)).drop k
      = List.range' k (c.layer c.output - k) := by
    rw [List.range_eq_range', List.drop_range']
    simp
  rw [windowWord, layerWord, ← List.map_drop, hdrop]

/-- **The short-word obligation.**  For every incidence-certified circuit of
total width `w`, every constant left factor `pre`, every window of layer indices
of length at most the gate count, and every target element `g`, the predicate
"`pre` times the product of the layer letters over the window equals `g`" is
decided by an `ACC[modulus]` circuit of constant depth and polynomial size. -/
def ShortWordProblemACC (w : Nat) : Prop :=
  ∃ modulus depth exponent : Nat,
    2 ≤ modulus ∧
      ∀ {n : Nat} (c : ADRCircuit n) (cert : IncidenceCylinder c),
        HMVNormal c →
        TotalWidthAtMost c w →
        ∀ (pre : TransMonoid w) (start len : Nat), len ≤ c.gateCount →
          ∀ g : TransMonoid w,
            ∃ a : ACCCircuit n modulus,
              WellFormedACC a ∧
              (∀ q, a.layer q ≤ depth) ∧
              a.gateCount ≤ (c.gateCount + 1) ^ exponent ∧
              (∀ x, ACCAccepts a x ↔ pre * windowWord c cert x w start len = g)

/-- **Only short words matter.** -/
theorem wordProblemACC_of_short {w : Nat} (H : ShortWordProblemACC w) :
    WordProblemACC w := by
  obtain ⟨M, D, e, hM, hshort⟩ := H
  refine ⟨M, D, e, hM, ?_⟩
  intro n c cert hN hW g
  obtain ⟨k, hkL, hlen, hk⟩ := exists_compression_index c cert
  obtain ⟨pre, -, hall⟩ := prefixEnd_layerWord_of_compression c cert hkL hk w
  obtain ⟨a, hwf, hlay, hsize, hacc⟩ :=
    hshort c cert hN hW pre k (c.layer c.output - k) hlen g
  refine ⟨a, hwf, hlay, hsize, fun x => ?_⟩
  rw [hacc x, outputWord_split c cert x w k, hall x,
    drop_layerWord_eq_windowWord c cert x k]

/-- **The quantitative cylindrical `ACC` principle follows from the short-word
problem of the transition monoid.** -/
theorem quantitativeCylindricalACC_of_shortWordProblem
    (H : ∀ w : Nat, ShortWordProblemACC w) : QuantitativeCylindricalACCPrinciple :=
  quantitativeCylindricalACC_of_wordProblem fun w => wordProblemACC_of_short (H w)

/-- **The window-word obligation.**  The `pre`-free core of
`ShortWordProblemACC`: for every incidence-certified circuit of total width `w`,
every window of layer indices of length at most the gate count and every target
element `h`, the predicate "the product of the layer letters over the window
equals `h`" is decided by an `ACC[modulus]` circuit of constant depth and
polynomial size. -/
def WindowWordACC (w : Nat) : Prop :=
  ∃ modulus depth exponent : Nat,
    2 ≤ modulus ∧
      ∀ {n : Nat} (c : ADRCircuit n) (cert : IncidenceCylinder c),
        HMVNormal c →
        TotalWidthAtMost c w →
        ∀ (start len : Nat), len ≤ c.gateCount →
          ∀ h : TransMonoid w,
            ∃ a : ACCCircuit n modulus,
              WellFormedACC a ∧
              (∀ q, a.layer q ≤ depth) ∧
              a.gateCount ≤ (c.gateCount + 1) ^ exponent ∧
              (∀ x, ACCAccepts a x ↔ windowWord c cert x w start len = h)

/-- **The constant left factor is free.**  Given a recogniser for each value of
the window word, the predicate `pre * windowWord = g` is the finite `OR`, over
the (constantly many) elements `h` of the transition monoid with `pre * h = g`,
of the recognisers for `windowWord = h`.  The assembly is a depth-two
`OR`-of-`AND`s, so the depth grows by `2` and the size by a factor depending only
on `w`, which is absorbed into the exponent. -/
theorem shortWordProblemACC_of_windowWord {w : Nat} (H : WindowWordACC w) :
    ShortWordProblemACC w := by
  classical
  obtain ⟨M, D, e, hM, hwin⟩ := H
  set K := Fintype.card (TransMonoid w) with hK
  refine ⟨M, max D 1 + 2, e + (K * 3 + 1), hM, ?_⟩
  intro n c cert hN hW pre start len hlen g
  set ee := Fintype.equivFin (TransMonoid w) with hee
  choose B hBwf hBlay hBsz hBacc using
    fun i : Fin K => hwin c cert hN hW start len hlen (ee.symm i)
  set blocks : (i : Fin K) → Fin 2 → ACCCircuit n M := fun i j =>
    if j.val = 0 then B i else accConst n M (decide (pre * ee.symm i = g)) with hblocks
  have hb0 : ∀ i, blocks i 0 = B i := by intro i; rw [hblocks]; simp
  have hb1 : ∀ i, blocks i 1 = accConst n M (decide (pre * ee.symm i = g)) := by
    intro i; rw [hblocks]; simp
  have hjcases : ∀ j : Fin 2, j = 0 ∨ j = 1 := by
    intro j
    rcases (show j.val = 0 ∨ j.val = 1 from by omega) with h | h
    · exact Or.inl (Fin.ext (by simp [h]))
    · exact Or.inr (Fin.ext (by simp [h]))
  have hbwf : ∀ i j, WellFormedACC (blocks i j) := by
    intro i j
    rcases hjcases j with h | h <;> subst h
    · rw [hb0 i]; exact hBwf i
    · rw [hb1 i]; exact wellFormedACC_accConst n M _
  have hblay : ∀ i j (q : Fin (blocks i j).gateCount),
      (blocks i j).layer q ≤ max D 1 := by
    intro i j
    rcases hjcases j with h | h <;> subst h
    · rw [hb0 i]; exact fun q => le_trans (hBlay i q) (le_max_left _ _)
    · rw [hb1 i]; intro q; rw [accConst_layer]; exact le_max_right _ _
  refine ⟨accOrAnd blocks (max D 1), wellFormedACC_accOrAnd hbwf hblay,
    accOrAnd_layer_le hblay, ?_, fun x => ?_⟩
  · -- size bound
    have hP : 2 ≤ c.gateCount + 1 := by
      have := c.output.isLt
      omega
    have hpow : 1 ≤ (c.gateCount + 1) ^ e := Nat.one_le_pow _ _ (by omega)
    have hb : ∀ i : Fin K, (∑ j, (blocks i j).gateCount) + 1
        ≤ (c.gateCount + 1) ^ e + 0 + 2 := by
      intro i
      have h0 : (blocks i 0).gateCount ≤ (c.gateCount + 1) ^ e := by
        rw [hb0 i]; exact hBsz i
      have h1 : (blocks i 1).gateCount = 1 := by rw [hb1 i]; exact accConst_gateCount n M _
      have hsum : ∑ j, (blocks i j).gateCount
          = (blocks i 0).gateCount + (blocks i 1).gateCount := by
        simp [Fin.sum_univ_two]
      omega
    have hsum : ∑ i : Fin K, ((∑ j, (blocks i j).gateCount) + 1)
        ≤ ∑ _i : Fin K, ((c.gateCount + 1) ^ e + 0 + 2) :=
      Finset.sum_le_sum fun i _ => hb i
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
    have hgc : (accOrAnd blocks (max D 1)).gateCount
        = (∑ i : Fin K, ((∑ j, (blocks i j).gateCount) + 1)) + 1 := rfl
    have hstep : K * ((c.gateCount + 1) ^ e + 0 + 2) + 1
        ≤ (K * (0 + 3) + 1) * (c.gateCount + 1) ^ e :=
      assemble_size_bound (K := K) (A := 0) hpow
    have hfin : (K * (0 + 3) + 1) * (c.gateCount + 1) ^ e
        ≤ (c.gateCount + 1) ^ (e + (K * 3 + 1)) := const_mul_pow_le_pow hP
    omega
  · -- semantics
    rw [accAccepts_accOrAnd hbwf hblay x]
    constructor
    · rintro ⟨i, hi⟩
      have h0 := (hBacc i x).mp (by rw [← hb0 i]; exact hi 0)
      have h1 := (accAccepts_accConst n M _ x).mp (by rw [← hb1 i]; exact hi 1)
      rw [h0]
      exact of_decide_eq_true h1
    · intro hg
      refine ⟨ee (windowWord c cert x w start len), fun j => ?_⟩
      have hsymm : ee.symm (ee (windowWord c cert x w start len))
          = windowWord c cert x w start len := ee.symm_apply_apply _
      rcases hjcases j with h | h <;> subst h
      · rw [hb0 _]
        exact (hBacc _ x).mpr hsymm.symm
      · rw [hb1 _]
        refine (accAccepts_accConst n M _ x).mpr ?_
        rw [hsymm]
        exact decide_eq_true hg

/-- **The abstract (circuit-free) word obligation.**  Letters are arbitrary
`NonCrossing w`-valued functions of the input, each of which is recognised by a
depth-two `ACC[2]` circuit of size at most `size`; the obligation is to
recognise the value of the product of a window of `len` consecutive letters by
an `ACC[modulus]` circuit of constant depth and size polynomial in
`size + len`.

This is the Barrington--Thérien statement for the fixed finite monoid
`NonCrossing w`, with all circuit-theoretic and incidence-geometric context of
the development stripped away: no `ADRCircuit`, no `IncidenceCylinder`, no
normal form, no width hypothesis occurs in it. -/
def LetterWordACC (w : Nat) : Prop :=
  ∃ modulus depth exponent : Nat,
    2 ≤ modulus ∧
      ∀ {n : Nat} (letter : Nat → (Fin n → Bool) → TransMonoid w) (size : Nat),
        (∀ i x, letter i x ∈ NonCrossing w) →
        (∀ (i : Nat) (m : TransMonoid w),
          ∃ a : ACCCircuit n 2,
            WellFormedACC a ∧
            (∀ q, a.layer q ≤ 2) ∧
            a.gateCount ≤ size ∧
            (∀ x, ACCAccepts a x ↔ letter i x = m)) →
        ∀ (start len : Nat) (h : TransMonoid w),
          ∃ a : ACCCircuit n modulus,
            WellFormedACC a ∧
            (∀ q, a.layer q ≤ depth) ∧
            a.gateCount ≤ (size + len + 2) ^ exponent ∧
            (∀ x, ACCAccepts a x ↔
              wordEnd ((List.range' start len).map (fun i => letter i x)) = h)

/-- **The generator form of the abstract word obligation.**  Identical to
`LetterWordACC`, except that every letter is required to be a single certified
layer map (`isNonCrossingMap w`) rather than an arbitrary member of the closure
`NonCrossing w`.  This is all the application ever produces — the letters of
`windowWordACC_of_letterWordGen` are literal `layerTrans` maps — and it hands
the leaf a per-letter incidence certificate: each letter comes with a concrete
HMV-normal bounded-width circuit layer whose non-crossing window geometry is
available (`GeneratorGeometry`), instead of an opaque product of such layers. -/
def LetterWordACCGen (w : Nat) : Prop :=
  ∃ modulus depth exponent : Nat,
    2 ≤ modulus ∧
      ∀ {n : Nat} (letter : Nat → (Fin n → Bool) → TransMonoid w) (size : Nat),
        (∀ i x, isNonCrossingMap w (letter i x)) →
        (∀ (i : Nat) (m : TransMonoid w),
          ∃ a : ACCCircuit n 2,
            WellFormedACC a ∧
            (∀ q, a.layer q ≤ 2) ∧
            a.gateCount ≤ size ∧
            (∀ x, ACCAccepts a x ↔ letter i x = m)) →
        ∀ (start len : Nat) (h : TransMonoid w),
          ∃ a : ACCCircuit n modulus,
            WellFormedACC a ∧
            (∀ q, a.layer q ≤ depth) ∧
            a.gateCount ≤ (size + len + 2) ^ exponent ∧
            (∀ x, ACCAccepts a x ↔
              wordEnd ((List.range' start len).map (fun i => letter i x)) = h)

/-- The generator obligation is implied by the closure obligation: a certified
layer map is in particular a member of `NonCrossing w`. -/
theorem letterWordACCGen_of_letterWord {w : Nat} (H : LetterWordACC w) :
    LetterWordACCGen w := by
  obtain ⟨M, D, e, hM, hcore⟩ := H
  refine ⟨M, D, e, hM, ?_⟩
  intro n letter size hmem hrec start len h
  exact hcore letter size (fun i x => Submonoid.subset_closure (hmem i x)) hrec start len h

/-- **The degenerate width.**  For `w = 0` the transition monoid is trivial, so
every window product equals every target and the recogniser is the constant
circuit. -/
theorem letterWordACC_zero : LetterWordACC 0 := by
  have hsub : Subsingleton (TransMonoid 0) := by
    constructor
    intro a b
    apply MulOpposite.unop_injective
    funext s j
    exact j.elim0
  refine ⟨2, 1, 1, le_refl 2, ?_⟩
  intro n letter size _ _ start len h
  refine ⟨accConst n 2 true, wellFormedACC_accConst n 2 true, ?_, ?_, ?_⟩
  · intro q
    exact le_of_eq (accConst_layer n 2 true q)
  · rw [accConst_gateCount, pow_one]
    omega
  · intro x
    rw [accAccepts_accConst]
    have hall := hsub.allEq (wordEnd ((List.range' start len).map (fun i => letter i x))) h
    simp [hall]

/-- A constant offset is absorbed into the exponent of a base at least two. -/
theorem add_const_le_pow {G C : Nat} (hP : 2 ≤ G + 1) :
    C + G + 2 ≤ (G + 1) ^ (C + 3) := by
  have h1 : C + G + 2 ≤ (C + 2) * (G + 1) := by nlinarith [Nat.zero_le (C * G)]
  have h2 : (C + 2) * (G + 1) ^ 1 ≤ (G + 1) ^ (1 + (C + 2)) :=
    const_mul_pow_le_pow hP
  calc C + G + 2 ≤ (C + 2) * (G + 1) ^ 1 := by simpa using h1
    _ ≤ (G + 1) ^ (1 + (C + 2)) := h2
    _ = (G + 1) ^ (C + 3) := by ring_nf

/-- **The window-word obligation is an instance of the abstract one.**  The
window letters are the layer transitions of the circuit; they lie in
`NonCrossing w` (`layerTrans_mem_nonCrossing`) and each single-letter test is
recognised by a depth-two `ACC[2]` circuit of size `2 * w + 2 ^ w + 1`
(`exists_acc_letterEq`), a constant depending only on the width.  The size bound
`(size + len + 2) ^ exponent` of the abstract obligation is therefore bounded by
`(c.gateCount + 1) ^ exponent'` for an exponent depending only on `w`. -/
theorem windowWordACC_of_letterWord {w : Nat} (H : LetterWordACC w) :
    WindowWordACC w := by
  classical
  obtain ⟨M, D, e, hM, hletter⟩ := H
  set C := 2 * w + 2 ^ w + 1 with hC
  refine ⟨M, D, (C + 3) * e, hM, ?_⟩
  intro n c cert hN hW start len hlen h
  obtain ⟨a, hwf, hlay, hsize, hacc⟩ :=
    hletter (fun i x => layerTrans (w := w) c cert x i) C
      (fun i x => layerTrans_mem_nonCrossing c cert x i hN hW)
      (fun i m => exists_acc_letterEq c cert hW i m) start len h
  refine ⟨a, hwf, hlay, ?_, ?_⟩
  · -- size bound
    have hP : 2 ≤ c.gateCount + 1 := by
      have := c.output.isLt
      omega
    have hbase : C + len + 2 ≤ (c.gateCount + 1) ^ (C + 3) :=
      le_trans (by omega) (add_const_le_pow (C := C) (G := c.gateCount) hP)
    calc a.gateCount ≤ (C + len + 2) ^ e := hsize
      _ ≤ ((c.gateCount + 1) ^ (C + 3)) ^ e := Nat.pow_le_pow_left hbase e
      _ = (c.gateCount + 1) ^ ((C + 3) * e) := by rw [← pow_mul]
  · intro x
    rw [hacc x, windowWord]

/-- The same instantiation through the generator form: the letters supplied by
the application are literal `layerTrans` maps, so the full generator witness
`⟨n, c, cert, i, x, hN, hW, rfl⟩` is available and the weaker obligation
`LetterWordACCGen` suffices for `WindowWordACC`. -/
theorem windowWordACC_of_letterWordGen {w : Nat} (H : LetterWordACCGen w) :
    WindowWordACC w := by
  classical
  obtain ⟨M, D, e, hM, hletter⟩ := H
  set C := 2 * w + 2 ^ w + 1 with hC
  refine ⟨M, D, (C + 3) * e, hM, ?_⟩
  intro n c cert hN hW start len hlen h
  obtain ⟨a, hwf, hlay, hsize, hacc⟩ :=
    hletter (fun i x => layerTrans (w := w) c cert x i) C
      (fun i x => ⟨n, c, cert, i, x, hN, hW, rfl⟩)
      (fun i m => exists_acc_letterEq c cert hW i m) start len h
  refine ⟨a, hwf, hlay, ?_, ?_⟩
  · have hP : 2 ≤ c.gateCount + 1 := by
      have := c.output.isLt
      omega
    have hbase : C + len + 2 ≤ (c.gateCount + 1) ^ (C + 3) :=
      le_trans (by omega) (add_const_le_pow (C := C) (G := c.gateCount) hP)
    calc a.gateCount ≤ (C + len + 2) ^ e := hsize
      _ ≤ ((c.gateCount + 1) ^ (C + 3)) ^ e := Nat.pow_le_pow_left hbase e
      _ = (c.gateCount + 1) ^ ((C + 3) * e) := by rw [← pow_mul]
  · intro x
    rw [hacc x, windowWord]

/-!
**The word problem of `NonCrossing w` is in `ACC0`.**  This is the single
remaining mathematical obligation of the whole development: the
Barrington--Thérien `ACC^0` upper bound for the word problem of the fixed finite
monoid `NonCrossing w`, for words of length `len` whose letters are individually
recognised by small depth-two circuits.

All circuit-theoretic and incidence-geometric context has been discharged
outside this leaf; what is left mentions no `ADRCircuit`, no
`IncidenceCylinder`, no normal form and no width bound.  The reductions
performed above are

* `windowWordACC_of_letterWord` — instantiating the letters with the layer
  transitions of a bounded-width incidence-certified circuit
  (`layerTrans_mem_nonCrossing` for membership in `NonCrossing w`,
  `exists_acc_letterEq` for the single-letter recognisers);
* `shortWordProblemACC_of_windowWord` — absorbing the constant left factor
  `pre` by a finite `OR` over `{h | pre * h = g}`;
* `wordProblemACC_of_short` — compressing the unbounded layer word to a window
  of length at most `c.gateCount` (`outputWord_split`, `outputWord_compress`);
* `quantitativeCylindricalACC_of_wordProblem` — the `ACC` assembly
  (`exists_acc_adrAccepts_of_word`) on top of the semantic bridge
  `adrAccepts_iff_runTrans_word`, plus `totalWidthAtMost_zero_elim` for the
  degenerate width.

Two cases of the leaf are already discharged: the degenerate width
(`letterWordACC_zero`) and the case in which every letter is a *unit* of
`NonCrossing w` (`letterWordACC_units`, proved from the cyclicity of the unit
group by a `MOD` count of the exponents).

**SOUNDNESS REFUTATION (2026-08-16, iter 14 analysis).**
The earlier route based on guessing R-descent boundaries and MOD-counting
per-block cyclic shift amounts is SOUNDNESS-REFUTED:
(1) **rank-1 collapse** — constant-map letters put the whole word in one
    rank-1 R-class; the Schützenberger groupoid is trivial and MOD counting
    proves nothing, while the within-block subproblem is the full point-
    trajectory problem;
(2) **moving basepoint** — per-letter rotation amounts are measured against
    the input-dependent current range set, whose computation is itself a
    prefix problem (width-2 example: `A(x₁,x₂) = (x₁, x₁∨x₂)` with
    alternating swaps — ranges move at constant rank).
Do NOT revive this route.

**Sound route (Barrington–Thérien prefix-evaluation cascade).**
The correct approach follows BT for the fixed monoid `NonCrossing w` via a
constant-length cascade of ACC layers.  The proved infrastructure is:

* `CascadeCoordinate.lean` — `shapeCoord` (rank × comparability count),
  bounded change count (`card_shapeCoord_changes_le_nonCrossing`), and
  order-iso on constant-shape blocks (`orderIso_blockEnd_of_shapeCoord_const`).
* `CascadeAperiodic.lean` — `cascade_aperiodic_layer`: a coordinate with at
  most `K` changes along any trajectory is ACC-recognisable (guess-and-verify
  the ≤ `len^K` change-position tuples).
* `CascadeCyclic.lean` — `cascade_cyclic_layer`: a cyclic-group-element
  coordinate driven by letter+driver recognisers, evaluable via MOD counts.
* `LetterWordUnits.lean` — `letterWordACC_units`: the unit-group case.
* `BlockBoundaries.lean` — the explicit block decomposition that the cascade
  guesses: `exists_block_boundaries` turns the change bound into constantly
  many boundary positions `0 = bs 0 ≤ … ≤ bs (K + 1) = len` with the coordinate
  constant on each `[bs j, bs (j + 1))`; `REquiv_mul_iff_injOn_range` and
  `injOn_range_of_shapeCoord_const` record that along such a block every letter
  is injective on the currently reachable configurations, so the prefix keeps
  its kernel.
* `ConfigInterval.lean` — cyclic-interval properties of configurations.
* `GeneratorGeometry.lean` — predecessor sets are cyclic intervals (with
  non-degeneracy hypothesis).

**Generator strengthening (2026-08-17).**  The leaf is now stated in the
generator form `LetterWordACCGen`: every letter is a single certified layer map
(`isNonCrossingMap`), which is all the application produces.  This hands the
leaf a per-letter incidence certificate (window geometry via
`GeneratorGeometry`) instead of an opaque product; the closure `NonCrossing w`
still governs the *algebra* (prefix products), but per-letter data — MOD-count
contributions, rotation offsets — can be read off the certificate directly.

**Heart confirmed computationally (2026-08-17).**  The localized cyclicity
statements the cascade needs (H1: for every `S : Finset (Config w)` the group
of realized permutations `{m|_S : m ∈ NonCrossing w, m(S) = S}` is cyclic; H2:
the holonomy brick-family version) were machine-verified for the fully
enumerated monoids at `w = 2, 3` — see `docs/HMV_ALGEBRA_NOTES.md` section 4
and `docs/experiments/`.  First Lean bricks are proved in
`LocalizedCyclicity.lean` (localized HMV L12: `bijOn_minIn`,
`bijOn_layerRest`).
**Top of the tower closed (2026-08-17).**  `RealizedOrderIso.lean` and
`RealizedFamUniv.lean` prove the two heart lemmas at the top level of the
holonomy tower, plus the order-theoretic bricks they rest on:

* `le_of_monotone_bijOn` / `realizedPerm_le_iff` — a realized permutation is an
  order *automorphism* of the subposet it acts on (the inverse is a positive
  iterate, hence monotone as well), so layer membership is preserved in both
  directions (`realizedPerm_mem_minLayer_iff`);
* `isUnit_of_bijOn_univ` — an element of `NonCrossing w` acting bijectively on
  all configurations is a unit;
* `isCyclic_realizedSubgroup_univ` — H1 for `S = univ`, and
  `Holonomy.isCyclic_realizedFamSubgroup_univ` — H2 for the family of all
  configuration sets, both obtained from `nonCrossing_units_cyclic` by
  identifying the realized permutations with the image of the unit group;
* `isCyclic_realizedSubgroup_of_chain` — H1 whenever the configurations of `S`
  are pairwise comparable (each antichain layer is then a singleton).

What remains is: (E2-b) the rotation form of H1/H2 for the *proper* levels of
the tower via the HMV interval
hierarchy (L9/L10/L11 for generators, then composition), and (E2-c) the
holonomy/wreath assembly over the subset lattice of `Config w`, feeding
`cascade_cyclic_layer` (groups cyclic by H1/H2) and `cascade_aperiodic_layer`
(per-level descent epochs are bounded by the lattice height).  Rank-1 point
dynamics is closed only by the full tower — do not regress to prefix-R-block
schemes. -/


end AllenderOQ3.Internal
