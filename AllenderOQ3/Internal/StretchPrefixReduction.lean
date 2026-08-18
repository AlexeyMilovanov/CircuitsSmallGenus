import AllenderOQ3.Internal.EpochReduction

/-!
# The prefix form of the per-stretch obligation

`EpochReduction` reduces `LetterWordACCGen w` to obligations that ask for the
*value* of a block product.  That is more than the holonomy argument can deliver
directly: on a stretch along which the rank/shape coordinate of the window
prefix products is constant, the letters are order isomorphisms *of the reachable
set of the current prefix*, so what the holonomy controls is the action of the
block on that set — equivalently the composite `gin * (block product)` for the
true incoming prefix `gin`, not the block product itself.

This file therefore records the obligation in the shape the holonomy argument can
actually meet:

* `StretchPrefixACC w` asks only for circuits `E a c gin gout` that certify
  `gin * (block product) = gout`, and only requires completeness when `gin` is
  the *true* window prefix at `a` and the stretch has constant shape at every
  step; and
* `letterWordACCGen_of_stretchPrefixACC` discharges, `sorry`-free, the whole
  combinatorial assembly around it, using the prefix-chain gadget
  `exists_acc_chainAssembly_of_cond` and the single-letter step
  `exists_acc_letterStep`.

Everything here is `sorry`-free.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace AllenderOQ3
namespace Internal

variable {w : Nat}

/-! ## Why the prefix form is a weaker demand -/

/-- **Only the restriction to the range matters.**  Two transitions that agree on
the range of `g` have the same composite with `g`.

This is what makes `StretchPrefixACC` a genuinely weaker obligation than
recognising the block product itself: on an order-isomorphism stretch the
holonomy controls the action of the block on the range of the incoming prefix,
and by this lemma that action already determines the outgoing prefix. -/
theorem mul_eq_mul_of_eqOn_rangeTrans {W : Nat} {g a b : TransMonoid W}
    (h : ∀ p ∈ rangeTrans g, runTrans a p = runTrans b p) : g * a = g * b := by
  refine MulOpposite.unop_injective (funext fun x => ?_)
  exact h (runTrans g x) (mem_rangeTrans.mpr ⟨x, rfl⟩)


/-- **The per-stretch recognition obligation, in prefix form.**

For every window of letters there are circuits `E a c gin gout` of constant depth
and polynomial size which

* never accept unless `gin * (product of the letters of `[start + a, start + c)`) = gout`
  (soundness), and
* do accept when `gin` and `gout` are the true window prefix products at `a` and
  at `c` and the rank/shape coordinate of the window prefix products is constant
  at every step of `[a, c)` (completeness on order-isomorphism stretches).

Only the *action of the block on the range of the incoming prefix* is ever
needed, which is exactly what the holonomy of an order-isomorphism stretch
controls. -/
def StretchPrefixACC (w : Nat) : Prop :=
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
          ∃ E : Nat → Nat → TransMonoid w → TransMonoid w → ACCCircuit n modulus,
            (∀ a c gin gout, WellFormedACC (E a c gin gout)) ∧
            (∀ a c gin gout q, (E a c gin gout).layer q ≤ depth) ∧
            (∀ a c gin gout, (E a c gin gout).gateCount ≤ (size + len + 2) ^ exponent) ∧
            (∀ (a c : Nat) (gin gout : TransMonoid w) (x : Fin n → Bool), a ≤ c →
              ACCAccepts (E a c gin gout) x → gin * blockProd letter start a c x = gout) ∧
            (∀ (x : Fin n → Bool) (a c : Nat), a ≤ c → c ≤ len →
              (∀ i, a ≤ i → i < c →
                windowShape letter start len x i = windowShape letter start len x (i + 1)) →
              ACCAccepts (E a c (blockProd letter start 0 a x)
                (blockProd letter start 0 c x)) x)

/-- **The letter word problem reduces to the per-stretch problem in prefix
form.**  Each of the at most `epochBound w + 1` epochs of the window is split
into an order-isomorphism stretch followed by the single letter that drops the
shape, so the window is covered by `2 * (epochBound w + 1)` blocks.  Every block
is certified in prefix form — a single letter by `exists_acc_letterStep`, a
stretch by the given recogniser — and the prefix-chain gadget
`exists_acc_chainAssembly_of_cond` assembles them into a recogniser for the whole
window. -/
theorem letterWordACCGen_of_stretchPrefixACC (H : StretchPrefixACC w) : LetterWordACCGen w := by
  classical
  obtain ⟨Ms, Ds, es, hMs, hcore⟩ := H
  set M := 2 * Ms with hMdef
  have hMpos : 0 < M := by omega
  have hdvdS : Ms ∣ M := ⟨2, by omega⟩
  have hdvd2 : 2 ∣ M := ⟨Ms, rfl⟩
  set K := epochBound w + 1 with hKdef
  set KK := 2 * K with hKKdef
  set A0 := Fintype.card (TransMonoid w) with hA0def
  set C1 := A0 * (M + 2) + 2 * (M + 2) + 1 with hC1def
  set C2 := (KK + 1) * C1 + KK + 2 with hC2def
  set A := Fintype.card (Fin (KK + 1) → TransMonoid w) with hAdef
  refine ⟨M, 2 * Ds + 10, KK + es + 3 + A * C2, by omega, ?_⟩
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
  -- the single-letter step, in prefix form
  have hstep : ∀ (i : Nat) (gin gout : TransMonoid w),
      ∃ a : ACCCircuit n M,
        WellFormedACC a ∧ (∀ q, a.layer q ≤ 8) ∧
        a.gateCount ≤ A0 * ((M + 2) * size + 2) + 1 ∧
        (∀ x, ACCAccepts a x ↔ gin * letter i x = gout) := by
    intro i gin gout
    obtain ⟨a, h1, h2, h3, h4⟩ :=
      exists_acc_letterStep (L := fun g => L i g) (p := letter i)
        (hLwf i) (hLlay i) (hLsz i) (hLacc i) gin gout
    exact ⟨a, h1, fun q => le_trans (h2 q) (by omega), h3, h4⟩
  choose Lstep hSwf hSlay hSsz hSacc using hstep
  -- the block recognisers: a single letter, or a stretch lifted to the modulus `M`
  set Szb := (A0 * ((M + 2) * size + 2) + 1) + (M + 2) * ((size + len + 2) ^ es + size)
    with hSzbdef
  set Bf : Nat → Nat → TransMonoid w → TransMonoid w → ACCCircuit n M := fun a b gin gout =>
    if b = a + 1 then Lstep (start + a) gin gout else accModulusLift (E a b gin gout) hdvdS
    with hBfdef
  have hBf_letter : ∀ a b gin gout, b = a + 1 → Bf a b gin gout = Lstep (start + a) gin gout := by
    intro a b gin gout hb
    simp only [hBfdef, if_pos hb]
  have hBf_stretch : ∀ a b gin gout, ¬ b = a + 1 →
      Bf a b gin gout = accModulusLift (E a b gin gout) hdvdS := by
    intro a b gin gout hb
    simp only [hBfdef, if_neg hb]
  have hBwf : ∀ a b gin gout, WellFormedACC (Bf a b gin gout) := by
    intro a b gin gout
    by_cases hb : b = a + 1
    · rw [hBf_letter a b gin gout hb]; exact hSwf _ _ _
    · rw [hBf_stretch a b gin gout hb]
      exact wellFormedACC_accModulusLift _ hdvdS (hEwf _ _ _ _)
  have hBlay : ∀ a b gin gout q, (Bf a b gin gout).layer q ≤ 2 * Ds + 8 := by
    intro a b gin gout
    by_cases hb : b = a + 1
    · rw [hBf_letter a b gin gout hb]
      exact fun q => le_trans (hSlay _ _ _ q) (by omega)
    · rw [hBf_stretch a b gin gout hb]
      exact fun q =>
        le_trans (accModulusLift_layer_le (c := E a b gin gout) (hM := hdvdS) (d := Ds)
          (hElay a b gin gout) q) (by omega)
  have hBsz : ∀ a b gin gout, (Bf a b gin gout).gateCount ≤ Szb := by
    intro a b gin gout
    by_cases hb : b = a + 1
    · rw [hBf_letter a b gin gout hb]
      exact le_trans (hSsz _ _ _) (by rw [hSzbdef]; omega)
    · rw [hBf_stretch a b gin gout hb]
      refine le_trans (accModulusLift_gateCount_le _ hdvdS) ?_
      have := Nat.mul_le_mul_left (M + 2)
        (le_trans (hEsz a b gin gout) (Nat.le_add_right _ size))
      rw [hSzbdef]
      omega
  have hBsound : ∀ (a b : Nat) (gin gout : TransMonoid w) (x : Fin n → Bool), a ≤ b →
      ACCAccepts (Bf a b gin gout) x → gin * blockProd letter start a b x = gout := by
    intro a b gin gout x hab hacc
    by_cases hb : b = a + 1
    · rw [hBf_letter a b gin gout hb] at hacc
      subst hb
      rw [blockProd_succ]
      exact (hSacc _ _ _ x).mp hacc
    · rw [hBf_stretch a b gin gout hb] at hacc
      rw [evalACC_accModulusLift_of_pos hMpos (hEwf a b gin gout) x] at hacc
      exact hEsound a b gin gout x hab hacc
  -- the decomposition of every input into `2 * K` blocks
  have hcomplete : ∀ x : Fin n → Bool, ∃ tf : Fin (KK + 1) → Fin (len + 1),
      (tf 0).val = 0 ∧ (tf (Fin.last KK)).val = len ∧
      (∀ j : Fin KK, (tf j.castSucc).val ≤ (tf j.succ).val) ∧
      (∀ j : Fin KK, ACCAccepts
          (Bf (tf j.castSucc).val (tf j.succ).val
            (blockProd letter start 0 (tf j.castSucc).val x)
            (blockProd letter start 0 (tf j.succ).val x)) x) := by
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
        ACCAccepts (Bf (t2 k) (t2 (k + 1))
          (blockProd letter start 0 (t2 k) x)
          (blockProd letter start 0 (t2 (k + 1)) x)) x := by
      have hsingle : ∀ a : Nat,
          ACCAccepts (Bf a (a + 1) (blockProd letter start 0 a x)
            (blockProd letter start 0 (a + 1) x)) x := by
        intro a
        rw [hBf_letter a (a + 1) _ _ rfl]
        refine (hSacc _ _ _ x).mpr ?_
        have hc := blockProd_concat letter start x (Nat.zero_le a) (Nat.le_succ a)
        rw [blockProd_succ] at hc
        exact hc
      have hstretchacc : ∀ a c : Nat, a ≤ c → c ≤ len → ¬ c = a + 1 →
          (∀ i, a ≤ i → i < c →
            windowShape letter start len x i = windowShape letter start len x (i + 1)) →
          ACCAccepts (Bf a c (blockProd letter start 0 a x)
            (blockProd letter start 0 c x)) x := by
        intro a c hac hcl hne hcond
        rw [hBf_stretch a c _ _ hne,
          evalACC_accModulusLift_of_pos hMpos (hEwf a c _ _) x]
        exact hEcomp x a c hac hcl hcond
      intro k hk
      rcases Nat.even_or_odd k with he | ho
      · obtain ⟨i, hi⟩ := he
        have hk2 : k = 2 * i := by omega
        subst hk2
        rw [ht2_even, ht2_odd]
        by_cases hb : max (t i) (t (i + 1) - 1) = t i + 1
        · rw [hb]; exact hsingle (t i)
        · refine hstretchacc _ _ (le_max_left _ _) ?_ hb ?_
          · have h1 := htle i
            have h2 := htle (i + 1)
            omega
          · intro i' hi1 hi2
            have hmi := htmono i
            have hlt : i' + 1 < t (i + 1) := by omega
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
          refine hstretchacc _ _ (le_refl _) (htle (i + 1)) (by omega) ?_
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
  obtain ⟨a, hawf, halay, hasz, hasound, hacomp⟩ :=
    exists_acc_chainAssembly_of_cond (G := TransMonoid w) (K := KK) (len := len)
      (d := 2 * Ds + 8) (Sz := Szb) (P := fun _ => True)
      letter start Bf hBwf hBlay hBsz hBsound (fun x _ => hcomplete x) h
  refine ⟨a, hawf, fun q => le_trans (halay q) (by omega), ?_, ?_⟩
  · -- size bound
    set S := size + len + 2 with hS
    have hS2 : 2 ≤ S := by omega
    have hScube : S ≤ S ^ (es + 1) := by
      calc S = S ^ 1 := (pow_one S).symm
        _ ≤ S ^ (es + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have hSe : 1 ≤ S ^ (es + 1) := Nat.one_le_pow _ _ (by omega)
    have hcard1 : Fintype.card (Fin (KK + 1) → Fin (len + 1)) ≤ S ^ (KK + 1) := by
      have hc : Fintype.card (Fin (KK + 1) → Fin (len + 1)) = (len + 1) ^ (KK + 1) := by
        simp
      rw [hc]
      exact Nat.pow_le_pow_left (by omega) _
    have hSzb : Szb ≤ C1 * S ^ (es + 1) := by
      have h1 : (M + 2) * size + 2 ≤ (M + 2) * S := by
        have : (M + 2) * size + (M + 2) * 2 = (M + 2) * (size + 2) := by ring
        have h2 : (M + 2) * (size + 2) ≤ (M + 2) * S := Nat.mul_le_mul_left _ (by omega)
        omega
      have h1' : A0 * ((M + 2) * size + 2) ≤ A0 * ((M + 2) * S ^ (es + 1)) :=
        Nat.mul_le_mul_left _ (le_trans h1 (Nat.mul_le_mul_left _ hScube))
      have h2 : S ^ es ≤ S ^ (es + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      have h3 : size ≤ S ^ (es + 1) := by omega
      have h4 : (M + 2) * (S ^ es + size) ≤ (M + 2) * (S ^ (es + 1) + S ^ (es + 1)) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add h2 h3)
      have h5 : A0 * ((M + 2) * S ^ (es + 1)) = (A0 * (M + 2)) * S ^ (es + 1) := by ring
      have h6 : (M + 2) * (S ^ (es + 1) + S ^ (es + 1)) = (2 * (M + 2)) * S ^ (es + 1) := by ring
      have h7 : C1 * S ^ (es + 1)
          = (A0 * (M + 2)) * S ^ (es + 1) + (2 * (M + 2)) * S ^ (es + 1) + S ^ (es + 1) := by
        rw [hC1def]; ring
      rw [hSzbdef]
      omega
    have hfactor : (KK + 1) * (Szb + 1) + 1 ≤ C2 * S ^ (es + 1) := by
      have hexp : (KK + 1) * (Szb + 1) = (KK + 1) * Szb + (KK + 1) := by
        rw [Nat.mul_add, Nat.mul_one]
      have h1 := Nat.mul_le_mul_left (KK + 1) hSzb
      have h2 : (KK + 2) ≤ (KK + 2) * S ^ (es + 1) := Nat.le_mul_of_pos_right _ (by omega)
      have h3 : (KK + 1) * (C1 * S ^ (es + 1)) + (KK + 2) * S ^ (es + 1) = C2 * S ^ (es + 1) := by
        rw [hC2def]; ring
      omega
    have hstepsz : Fintype.card (Fin (KK + 1) → Fin (len + 1)) * A
        * ((KK + 1) * (Szb + 1) + 1)
        ≤ (A * C2) * S ^ (KK + 1 + (es + 1)) := by
      calc Fintype.card (Fin (KK + 1) → Fin (len + 1)) * A * ((KK + 1) * (Szb + 1) + 1)
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
        ≤ Fintype.card (Fin (KK + 1) → Fin (len + 1)) * Fintype.card (Fin (KK + 1) → TransMonoid w)
            * ((KK + 1) * (Szb + 1) + 1) + 1 := hasz
      _ ≤ (A * C2) * S ^ (KK + 1 + (es + 1)) + 1 := Nat.add_le_add_right hstepsz 1
      _ ≤ S ^ (KK + 1 + (es + 1) + A * C2) + 1 := Nat.add_le_add_right hpow 1
      _ ≤ S ^ (KK + es + 3 + A * C2) := hlast
  · -- semantics
    intro x
    have hprod : blockProd letter start 0 len x
        = wordEnd ((List.range' start len).map (fun i => letter i x)) := by
      simp [blockProd, wordEnd]
    rw [← hprod]
    exact ⟨hasound x, fun hx => hacomp x trivial hx⟩

end Internal
end AllenderOQ3
