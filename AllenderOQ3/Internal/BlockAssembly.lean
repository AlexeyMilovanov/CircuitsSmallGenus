import AllenderOQ3.Base
import AllenderOQ3.Internal.ACCJoin
import AllenderOQ3.Internal.ACCLocal

/-!
# Guess-and-verify assembly of a window product from a bounded number of blocks

The holonomy cascade splits a window `[start, start + len)` of letters into a
number of *blocks* that is bounded by a constant `K` depending only on the
width (the epochs on which the rank/shape coordinate of the prefix products is
constant, cf. `card_shapeCoord_changes_le`).  This file supplies the purely
circuit-theoretic step that turns per-block recognisers into a recogniser for
the whole window: guess the `K + 1` block boundaries and the `K` block values,
verify each block with its recogniser, and check that the guessed values
multiply to the target.

The guess space has size `(len + 1) ^ (K + 1) * |G| ^ K`, i.e. polynomial in
`len` for constant `K`, and the verification is an `OR` of `AND`s, so the depth
grows by two.  The block recognisers are only required to be

* **sound**: whenever `B a b g` accepts `x`, the product of the letters in
  `[start + a, start + b)` really is `g`; and
* **complete on the intended decomposition**: for every input `x` there is
  *some* admissible sequence of boundaries whose blocks are accepted with their
  true values.

Nothing is assumed about the behaviour of `B a b g` on blocks that are not part
of an intended decomposition, which is what makes the gadget usable with
recognisers that only work on epochs.

Everything here is `sorry`-free.
-/

set_option autoImplicit false

namespace AllenderOQ3
namespace Internal

variable {n m : Nat}

/-- The product of the letters of the window `[start + a, start + b)`. -/
def blockProd {G : Type} [Monoid G] {n : Nat} (f : Nat → (Fin n → Bool) → G)
    (start a b : Nat) (x : Fin n → Bool) : G :=
  ((List.range' (start + a) (b - a)).map (fun i => f i x)).prod

@[simp] theorem blockProd_self {G : Type} [Monoid G] (f : Nat → (Fin n → Bool) → G)
    (start a : Nat) (x : Fin n → Bool) : blockProd f start a a x = 1 := by
  simp [blockProd]

/-- Adjacent blocks concatenate. -/
theorem blockProd_concat {G : Type} [Monoid G] (f : Nat → (Fin n → Bool) → G)
    (start : Nat) (x : Fin n → Bool) {a b c : Nat} (hab : a ≤ b) (hbc : b ≤ c) :
    blockProd f start a b x * blockProd f start b c x = blockProd f start a c x := by
  have hsplit : List.range' (start + a) (b - a) ++ List.range' (start + b) (c - b)
      = List.range' (start + a) (c - a) := by
    have h1 : start + b = (start + a) + (b - a) := by omega
    have h2 : (b - a) + (c - b) = c - a := by omega
    rw [h1, List.range'_append_1, h2]
  rw [blockProd, blockProd, blockProd, ← List.prod_append, ← List.map_append, hsplit]

/-- **Telescoping**: the blocks cut out by a monotone sequence of boundaries
multiply, in order, to the product over the whole range. -/
theorem blockProd_telescope {G : Type} [Monoid G] (f : Nat → (Fin n → Bool) → G)
    (start : Nat) (x : Fin n → Bool) (t : Nat → Nat) (hmono : ∀ j, t j ≤ t (j + 1)) :
    ∀ K : Nat,
      (List.ofFn (fun j : Fin K => blockProd f start (t j.val) (t (j.val + 1)) x)).prod
        = blockProd f start (t 0) (t K) x := by
  have hmono' : Monotone t := monotone_nat_of_le_succ hmono
  intro K
  induction K with
  | zero => simp
  | succ K ih =>
      rw [List.ofFn_succ', List.concat_eq_append, List.prod_append]
      simp only [Fin.val_castSucc, Fin.val_last, List.prod_cons, List.prod_nil, mul_one]
      rw [ih]
      exact blockProd_concat f start x (hmono' (Nat.zero_le K)) (hmono K)

/-- The `Fin`-indexed form of `blockProd_telescope`. -/
theorem blockProd_telescope_fin {G : Type} [Monoid G] (f : Nat → (Fin n → Bool) → G)
    (start : Nat) (x : Fin n → Bool) {K : Nat} (t : Fin (K + 1) → Nat)
    (hmono : ∀ j : Fin K, t j.castSucc ≤ t j.succ) :
    (List.ofFn (fun j : Fin K =>
        blockProd f start (t j.castSucc) (t j.succ) x)).prod
      = blockProd f start (t 0) (t (Fin.last K)) x := by
  classical
  set tt : Nat → Nat := fun k => t ⟨min k K, by omega⟩ with htt
  have hcast : ∀ j : Fin K, tt j.val = t j.castSucc := by
    intro j
    have hj : min j.val K = j.val := by have := j.isLt; omega
    simp only [htt, hj]
    rfl
  have hsucc : ∀ j : Fin K, tt (j.val + 1) = t j.succ := by
    intro j
    have hj : min (j.val + 1) K = j.val + 1 := by have := j.isLt; omega
    simp only [htt, hj]
    rfl
  have hmono' : ∀ j : Nat, tt j ≤ tt (j + 1) := by
    intro j
    rcases Nat.lt_or_ge j K with hj | hj
    · rw [hcast ⟨j, hj⟩, hsucc ⟨j, hj⟩]
      exact hmono ⟨j, hj⟩
    · have h1 : min j K = K := by omega
      have h2 : min (j + 1) K = K := by omega
      simp only [htt, h1, h2]
      exact le_refl _
  have hkey := blockProd_telescope f start x tt hmono' K
  have h0 : tt 0 = t 0 := by
    rcases Nat.eq_zero_or_pos K with hK | hK
    · subst hK
      simp only [htt]
      rfl
    · have : min 0 K = 0 := by omega
      simp only [htt, this]
      rfl
  have hK : tt K = t (Fin.last K) := by
    have : min K K = K := by omega
    simp only [htt, this]
    rfl
  have hfun : (fun j : Fin K => blockProd f start (t j.castSucc) (t j.succ) x)
      = fun j : Fin K => blockProd f start (tt j.val) (tt (j.val + 1)) x :=
    funext fun j => by rw [hcast, hsucc]
  rw [← h0, ← hK, ← hkey, hfun]

/-- **Guess-and-verify assembly of a window product from `K` blocks.**

Given per-block recognisers `B a b g` that are *sound* (they only accept when the
product of the letters of the block `[start + a, start + b)` really is `g`) and
*complete on some admissible decomposition of every input* into at most `K`
blocks, the value of the whole window product is recognised by an `OR` of `AND`s
over the `(len + 1) ^ (K + 1) * |G| ^ K` guesses of boundaries and block values.
The depth grows by two and the size by the (polynomial, for constant `K`) number
of guesses. -/
theorem exists_acc_blockAssembly_of_cond {G : Type} [Monoid G] [Fintype G]
    {len K d Sz : Nat} (P : (Fin n → Bool) → Prop)
    (f : Nat → (Fin n → Bool) → G) (start : Nat)
    (B : Nat → Nat → G → ACCCircuit n m)
    (hwf : ∀ a b g, WellFormedACC (B a b g))
    (hlay : ∀ a b g q, (B a b g).layer q ≤ d)
    (hsz : ∀ a b g, (B a b g).gateCount ≤ Sz)
    (hsound : ∀ (a b : Nat) (g : G) (x : Fin n → Bool), a ≤ b →
        ACCAccepts (B a b g) x → blockProd f start a b x = g)
    (hcomplete : ∀ x : Fin n → Bool, P x → ∃ t : Fin (K + 1) → Fin (len + 1),
        (t 0).val = 0 ∧ (t (Fin.last K)).val = len ∧
        (∀ j : Fin K, (t j.castSucc).val ≤ (t j.succ).val) ∧
        (∀ j : Fin K, ACCAccepts
            (B (t j.castSucc).val (t j.succ).val
              (blockProd f start (t j.castSucc).val (t j.succ).val x)) x))
    (h : G) :
    ∃ a : ACCCircuit n m,
      WellFormedACC a ∧
      (∀ q, a.layer q ≤ max d 1 + 2) ∧
      a.gateCount ≤ Fintype.card (Fin (K + 1) → Fin (len + 1)) * Fintype.card (Fin K → G)
          * ((K + 1) * (Sz + 1) + 1) + 1 ∧
      (∀ x, ACCAccepts a x → blockProd f start 0 len x = h) ∧
      (∀ x, P x → blockProd f start 0 len x = h → ACCAccepts a x) := by
  classical
  set nIdx := Fintype.card ((Fin (K + 1) → Fin (len + 1)) × (Fin K → G)) with hnIdx
  set ee := Fintype.equivFin ((Fin (K + 1) → Fin (len + 1)) × (Fin K → G)) with hee
  -- the admissibility predicate on a guess
  set Valid : ((Fin (K + 1) → Fin (len + 1)) × (Fin K → G)) → Prop := fun idx =>
    (idx.1 0).val = 0 ∧ (idx.1 (Fin.last K)).val = len ∧
      (∀ j : Fin K, (idx.1 j.castSucc).val ≤ (idx.1 j.succ).val) ∧
      (List.ofFn idx.2).prod = h with hValid
  set outer : Fin nIdx → Fin (K + 1) → ACCCircuit n m := fun i j =>
    if hj : j.val < K then
      B ((ee.symm i).1 (Fin.castSucc ⟨j.val, hj⟩)).val
        ((ee.symm i).1 (Fin.succ ⟨j.val, hj⟩)).val ((ee.symm i).2 ⟨j.val, hj⟩)
    else accConst n m (decide (Valid (ee.symm i))) with houter
  have hout_lt : ∀ (i : Fin nIdx) (j : Fin (K + 1)) (hj : j.val < K),
      outer i j = B ((ee.symm i).1 (Fin.castSucc ⟨j.val, hj⟩)).val
        ((ee.symm i).1 (Fin.succ ⟨j.val, hj⟩)).val ((ee.symm i).2 ⟨j.val, hj⟩) := by
    intro i j hj
    simp only [houter, dif_pos hj]
  have hout_last : ∀ (i : Fin nIdx) (j : Fin (K + 1)), ¬ j.val < K →
      outer i j = accConst n m (decide (Valid (ee.symm i))) := by
    intro i j hj
    simp only [houter, dif_neg hj]
  have hwf_out : ∀ i j, WellFormedACC (outer i j) := by
    intro i j
    by_cases hj : j.val < K
    · rw [hout_lt i j hj]; exact hwf _ _ _
    · rw [hout_last i j hj]; exact wellFormedACC_accConst n m _
  have hlay_out : ∀ i j (q : Fin (outer i j).gateCount),
      (outer i j).layer q ≤ max d 1 := by
    intro i j
    by_cases hj : j.val < K
    · rw [hout_lt i j hj]
      exact fun q => le_trans (hlay _ _ _ q) (le_max_left _ _)
    · rw [hout_last i j hj]
      intro q
      rw [accConst_layer]
      exact le_max_right _ _
  have hsz_out : ∀ i j, (outer i j).gateCount ≤ Sz + 1 := by
    intro i j
    by_cases hj : j.val < K
    · rw [hout_lt i j hj]
      exact le_trans (hsz _ _ _) (by omega)
    · rw [hout_last i j hj, accConst_gateCount]
      omega
  have hcard : nIdx
      = Fintype.card (Fin (K + 1) → Fin (len + 1)) * Fintype.card (Fin K → G) := by
    rw [hnIdx]
    exact Fintype.card_prod _ _
  refine ⟨accOrAnd outer (max d 1), wellFormedACC_accOrAnd hwf_out hlay_out,
    accOrAnd_layer_le hlay_out, ?_, ?_, ?_⟩
  · -- size bound
    simp only [accOrAnd_gateCount]
    have hinner : ∀ i : Fin nIdx,
        (∑ j : Fin (K + 1), (outer i j).gateCount) + 1 ≤ (K + 1) * (Sz + 1) + 1 := by
      intro i
      have hsum : (∑ j : Fin (K + 1), (outer i j).gateCount) ≤ (K + 1) * (Sz + 1) := by
        refine le_trans (Finset.sum_le_card_nsmul Finset.univ _ _ (fun j _ => hsz_out i j)) ?_
        simp
      omega
    have hsum_out : (∑ i : Fin nIdx, ((∑ j : Fin (K + 1), (outer i j).gateCount) + 1))
        ≤ nIdx * ((K + 1) * (Sz + 1) + 1) := by
      refine le_trans (Finset.sum_le_card_nsmul Finset.univ _ _ (fun i _ => hinner i)) ?_
      simp
    calc (∑ i : Fin nIdx, ((∑ j : Fin (K + 1), (outer i j).gateCount) + 1)) + 1
        ≤ nIdx * ((K + 1) * (Sz + 1) + 1) + 1 := by omega
      _ = Fintype.card (Fin (K + 1) → Fin (len + 1)) * Fintype.card (Fin K → G)
            * ((K + 1) * (Sz + 1) + 1) + 1 := by rw [hcard]
  · -- soundness
    intro x hx
    rw [accAccepts_accOrAnd hwf_out hlay_out x] at hx
    revert hx
    · rintro ⟨i, hi⟩
      have hlast : ¬ (Fin.last K).val < K := by simp
      have hV : Valid (ee.symm i) := by
        have hacc := hi (Fin.last K)
        rw [hout_last i (Fin.last K) hlast] at hacc
        exact of_decide_eq_true ((accAccepts_accConst n m _ x).mp hacc)
      obtain ⟨hV0, hVlast, hVmono, hVprod⟩ := hV
      have hblocks : ∀ j : Fin K,
          blockProd f start ((ee.symm i).1 j.castSucc).val ((ee.symm i).1 j.succ).val x
            = (ee.symm i).2 j := by
        intro j
        have hj : (j.castSucc : Fin (K + 1)).val < K := by simp
        have hacc := hi j.castSucc
        rw [hout_lt i j.castSucc hj] at hacc
        have hcast : (⟨(j.castSucc : Fin (K + 1)).val, hj⟩ : Fin K) = j := by
          apply Fin.ext; simp
        rw [hcast] at hacc
        exact hsound _ _ _ x (hVmono j) hacc
      have htel := blockProd_telescope_fin f start x (K := K)
        (fun j => ((ee.symm i).1 j).val) hVmono
      have hfun : (fun j : Fin K =>
            blockProd f start ((ee.symm i).1 j.castSucc).val ((ee.symm i).1 j.succ).val x)
          = (ee.symm i).2 := funext hblocks
      simp only [hfun] at htel
      have hmain : blockProd f start ((ee.symm i).1 0).val
          ((ee.symm i).1 (Fin.last K)).val x = h := by
        rw [← htel]; exact hVprod
      rwa [hV0, hVlast] at hmain
  · -- completeness under the side condition
    intro x hP hx
    rw [accAccepts_accOrAnd hwf_out hlay_out x]
    · obtain ⟨t, ht0, htlast, htmono, htacc⟩ := hcomplete x hP
      have htel := blockProd_telescope_fin f start x (K := K) (fun j => (t j).val) htmono
      simp only at htel
      rw [ht0, htlast] at htel
      refine ⟨ee (t, fun j : Fin K =>
        blockProd f start (t j.castSucc).val (t j.succ).val x), fun j => ?_⟩
      have hsymm : ee.symm (ee (t, fun j : Fin K =>
          blockProd f start (t j.castSucc).val (t j.succ).val x))
          = (t, fun j : Fin K => blockProd f start (t j.castSucc).val (t j.succ).val x) :=
        ee.symm_apply_apply _
      by_cases hj : j.val < K
      · rw [hout_lt _ j hj, hsymm]
        exact htacc ⟨j.val, hj⟩
      · rw [hout_last _ j hj, hsymm]
        refine (accAccepts_accConst n m _ x).mpr (decide_eq_true ?_)
        refine ⟨ht0, htlast, htmono, ?_⟩
        rw [htel]
        exact hx

/-- The unconditional form of `exists_acc_blockAssembly_of_cond`: if the block
recognisers are complete on a decomposition of *every* input, the assembled
circuit recognises the window product exactly. -/
theorem exists_acc_blockAssembly {G : Type} [Monoid G] [Fintype G]
    {len K d Sz : Nat}
    (f : Nat → (Fin n → Bool) → G) (start : Nat)
    (B : Nat → Nat → G → ACCCircuit n m)
    (hwf : ∀ a b g, WellFormedACC (B a b g))
    (hlay : ∀ a b g q, (B a b g).layer q ≤ d)
    (hsz : ∀ a b g, (B a b g).gateCount ≤ Sz)
    (hsound : ∀ (a b : Nat) (g : G) (x : Fin n → Bool), a ≤ b →
        ACCAccepts (B a b g) x → blockProd f start a b x = g)
    (hcomplete : ∀ x : Fin n → Bool, ∃ t : Fin (K + 1) → Fin (len + 1),
        (t 0).val = 0 ∧ (t (Fin.last K)).val = len ∧
        (∀ j : Fin K, (t j.castSucc).val ≤ (t j.succ).val) ∧
        (∀ j : Fin K, ACCAccepts
            (B (t j.castSucc).val (t j.succ).val
              (blockProd f start (t j.castSucc).val (t j.succ).val x)) x))
    (h : G) :
    ∃ a : ACCCircuit n m,
      WellFormedACC a ∧
      (∀ q, a.layer q ≤ max d 1 + 2) ∧
      a.gateCount ≤ Fintype.card (Fin (K + 1) → Fin (len + 1)) * Fintype.card (Fin K → G)
          * ((K + 1) * (Sz + 1) + 1) + 1 ∧
      (∀ x, ACCAccepts a x ↔ blockProd f start 0 len x = h) := by
  obtain ⟨a, hawf, halay, hasz, hasound, hacomp⟩ :=
    exists_acc_blockAssembly_of_cond (P := fun _ => True) f start B hwf hlay hsz hsound
      (fun x _ => hcomplete x) h
  exact ⟨a, hawf, halay, hasz, fun x => ⟨hasound x, fun hx => hacomp x trivial hx⟩⟩


/-! ## The prefix-chain form of the assembly -/

/-- **Chaining**: if `g` starts at `1` and each step multiplies by the product of
the corresponding block, then `g j` is the prefix product up to the boundary
`t j`. -/
theorem blockProd_chain_fin {G : Type} [Monoid G] (f : Nat → (Fin n → Bool) → G)
    (start : Nat) (x : Fin n → Bool) {K : Nat} (t : Fin (K + 1) → Nat) (g : Fin (K + 1) → G)
    (hmono : ∀ j : Fin K, t j.castSucc ≤ t j.succ) (h0 : t 0 = 0) (hg0 : g 0 = 1)
    (hstep : ∀ j : Fin K,
      g j.succ = g j.castSucc * blockProd f start (t j.castSucc) (t j.succ) x) :
    ∀ j : Fin (K + 1), g j = blockProd f start 0 (t j) x := by
  intro j
  induction j using Fin.induction with
  | zero => rw [hg0, h0]; simp
  | succ i ih =>
      rw [hstep i, ih, blockProd_concat f start x (Nat.zero_le _) (hmono i)]

/-- **A single-letter step in prefix form.**  From exact recognisers `L g` for
the value `p x` of a single letter one builds, for each pair `(gin, gout)`, a
circuit that accepts exactly when `gin * p x = gout`. -/
theorem exists_acc_letterStep {G : Type} [Monoid G] [Fintype G]
    {d Sz : Nat} (L : G → ACCCircuit n m) (p : (Fin n → Bool) → G)
    (hwf : ∀ g, WellFormedACC (L g))
    (hlay : ∀ g q, (L g).layer q ≤ d)
    (hsz : ∀ g, (L g).gateCount ≤ Sz)
    (hacc : ∀ g x, ACCAccepts (L g) x ↔ p x = g)
    (gin gout : G) :
    ∃ a : ACCCircuit n m,
      WellFormedACC a ∧
      (∀ q, a.layer q ≤ max d 1 + 2) ∧
      a.gateCount ≤ Fintype.card G * (Sz + 2) + 1 ∧
      (∀ x, ACCAccepts a x ↔ gin * p x = gout) := by
  classical
  set ee := Fintype.equivFin G with hee
  set outer : Fin (Fintype.card G) → Fin 1 → ACCCircuit n m := fun i _ =>
    if gin * ee.symm i = gout then L (ee.symm i) else accConst n m false with houter
  have hout_pos : ∀ (i : Fin (Fintype.card G)) (j : Fin 1), gin * ee.symm i = gout →
      outer i j = L (ee.symm i) := by
    intro i j hc
    simp only [houter, if_pos hc]
  have hout_neg : ∀ (i : Fin (Fintype.card G)) (j : Fin 1), ¬ gin * ee.symm i = gout →
      outer i j = accConst n m false := by
    intro i j hc
    simp only [houter, if_neg hc]
  have hwf_out : ∀ i j, WellFormedACC (outer i j) := by
    intro i j
    by_cases hc : gin * ee.symm i = gout
    · rw [hout_pos i j hc]; exact hwf _
    · rw [hout_neg i j hc]; exact wellFormedACC_accConst n m _
  have hlay_out : ∀ i j (q : Fin (outer i j).gateCount), (outer i j).layer q ≤ max d 1 := by
    intro i j
    by_cases hc : gin * ee.symm i = gout
    · rw [hout_pos i j hc]
      exact fun q => le_trans (hlay _ q) (le_max_left _ _)
    · rw [hout_neg i j hc]
      intro q; rw [accConst_layer]; exact le_max_right _ _
  have hsz_out : ∀ i j, (outer i j).gateCount ≤ Sz + 1 := by
    intro i j
    by_cases hc : gin * ee.symm i = gout
    · rw [hout_pos i j hc]; exact le_trans (hsz _) (by omega)
    · rw [hout_neg i j hc, accConst_gateCount]; omega
  refine ⟨accOrAnd outer (max d 1), wellFormedACC_accOrAnd hwf_out hlay_out,
    accOrAnd_layer_le hlay_out, ?_, ?_⟩
  · simp only [accOrAnd_gateCount]
    have hinner : ∀ i : Fin (Fintype.card G),
        (∑ j : Fin 1, (outer i j).gateCount) + 1 ≤ Sz + 2 := by
      intro i
      have hs : (∑ j : Fin 1, (outer i j).gateCount) ≤ Sz + 1 := by
        refine le_trans
          (Finset.sum_le_card_nsmul Finset.univ _ (Sz + 1) (fun j _ => hsz_out i j)) ?_
        simp
      omega
    have hsum : (∑ i : Fin (Fintype.card G), ((∑ j : Fin 1, (outer i j).gateCount) + 1))
        ≤ Fintype.card G * (Sz + 2) := by
      refine le_trans (Finset.sum_le_card_nsmul Finset.univ _ _ (fun i _ => hinner i)) ?_
      simp
    omega
  · intro x
    rw [accAccepts_accOrAnd hwf_out hlay_out x]
    constructor
    · rintro ⟨i, hi⟩
      have hacc0 := hi 0
      by_cases hc : gin * ee.symm i = gout
      · rw [hout_pos i 0 hc] at hacc0
        rw [(hacc _ x).mp hacc0]
        exact hc
      · rw [hout_neg i 0 hc] at hacc0
        exact absurd ((accAccepts_accConst n m false x).mp hacc0) (by simp)
    · intro hx
      have hsymm : ee.symm (ee (p x)) = p x := ee.symm_apply_apply _
      have hc : gin * ee.symm (ee (p x)) = gout := by rw [hsymm]; exact hx
      refine ⟨ee (p x), fun j => ?_⟩
      rw [hout_pos _ j hc, hsymm]
      exact (hacc _ x).mpr rfl

/-- **Guess-and-verify assembly in prefix form.**

Instead of guessing the value of each block, one guesses the *prefix product* at
each boundary and asks the block recognisers only to certify the transition
`gin ↦ gin * (block product)`.  This is a strictly weaker demand on the block
recognisers: they never have to determine the block product itself, only its
effect on the incoming prefix, and completeness is required only for the *true*
incoming prefix. -/
theorem exists_acc_chainAssembly_of_cond {G : Type} [Monoid G] [Fintype G]
    {len K d Sz : Nat} (P : (Fin n → Bool) → Prop)
    (f : Nat → (Fin n → Bool) → G) (start : Nat)
    (B : Nat → Nat → G → G → ACCCircuit n m)
    (hwf : ∀ a b gin gout, WellFormedACC (B a b gin gout))
    (hlay : ∀ a b gin gout q, (B a b gin gout).layer q ≤ d)
    (hsz : ∀ a b gin gout, (B a b gin gout).gateCount ≤ Sz)
    (hsound : ∀ (a b : Nat) (gin gout : G) (x : Fin n → Bool), a ≤ b →
        ACCAccepts (B a b gin gout) x → gin * blockProd f start a b x = gout)
    (hcomplete : ∀ x : Fin n → Bool, P x → ∃ t : Fin (K + 1) → Fin (len + 1),
        (t 0).val = 0 ∧ (t (Fin.last K)).val = len ∧
        (∀ j : Fin K, (t j.castSucc).val ≤ (t j.succ).val) ∧
        (∀ j : Fin K, ACCAccepts
            (B (t j.castSucc).val (t j.succ).val
              (blockProd f start 0 (t j.castSucc).val x)
              (blockProd f start 0 (t j.succ).val x)) x))
    (h : G) :
    ∃ a : ACCCircuit n m,
      WellFormedACC a ∧
      (∀ q, a.layer q ≤ max d 1 + 2) ∧
      a.gateCount ≤ Fintype.card (Fin (K + 1) → Fin (len + 1))
          * Fintype.card (Fin (K + 1) → G) * ((K + 1) * (Sz + 1) + 1) + 1 ∧
      (∀ x, ACCAccepts a x → blockProd f start 0 len x = h) ∧
      (∀ x, P x → blockProd f start 0 len x = h → ACCAccepts a x) := by
  classical
  set nIdx := Fintype.card ((Fin (K + 1) → Fin (len + 1)) × (Fin (K + 1) → G)) with hnIdx
  set ee := Fintype.equivFin ((Fin (K + 1) → Fin (len + 1)) × (Fin (K + 1) → G)) with hee
  set Valid : ((Fin (K + 1) → Fin (len + 1)) × (Fin (K + 1) → G)) → Prop := fun idx =>
    (idx.1 0).val = 0 ∧ (idx.1 (Fin.last K)).val = len ∧
      (∀ j : Fin K, (idx.1 j.castSucc).val ≤ (idx.1 j.succ).val) ∧
      idx.2 0 = 1 ∧ idx.2 (Fin.last K) = h with hValid
  set outer : Fin nIdx → Fin (K + 1) → ACCCircuit n m := fun i j =>
    if hj : j.val < K then
      B ((ee.symm i).1 (Fin.castSucc ⟨j.val, hj⟩)).val
        ((ee.symm i).1 (Fin.succ ⟨j.val, hj⟩)).val
        ((ee.symm i).2 (Fin.castSucc ⟨j.val, hj⟩))
        ((ee.symm i).2 (Fin.succ ⟨j.val, hj⟩))
    else accConst n m (decide (Valid (ee.symm i))) with houter
  have hout_lt : ∀ (i : Fin nIdx) (j : Fin (K + 1)) (hj : j.val < K),
      outer i j = B ((ee.symm i).1 (Fin.castSucc ⟨j.val, hj⟩)).val
        ((ee.symm i).1 (Fin.succ ⟨j.val, hj⟩)).val
        ((ee.symm i).2 (Fin.castSucc ⟨j.val, hj⟩))
        ((ee.symm i).2 (Fin.succ ⟨j.val, hj⟩)) := by
    intro i j hj
    simp only [houter, dif_pos hj]
  have hout_last : ∀ (i : Fin nIdx) (j : Fin (K + 1)), ¬ j.val < K →
      outer i j = accConst n m (decide (Valid (ee.symm i))) := by
    intro i j hj
    simp only [houter, dif_neg hj]
  have hwf_out : ∀ i j, WellFormedACC (outer i j) := by
    intro i j
    by_cases hj : j.val < K
    · rw [hout_lt i j hj]; exact hwf _ _ _ _
    · rw [hout_last i j hj]; exact wellFormedACC_accConst n m _
  have hlay_out : ∀ i j (q : Fin (outer i j).gateCount),
      (outer i j).layer q ≤ max d 1 := by
    intro i j
    by_cases hj : j.val < K
    · rw [hout_lt i j hj]
      exact fun q => le_trans (hlay _ _ _ _ q) (le_max_left _ _)
    · rw [hout_last i j hj]
      intro q
      rw [accConst_layer]
      exact le_max_right _ _
  have hsz_out : ∀ i j, (outer i j).gateCount ≤ Sz + 1 := by
    intro i j
    by_cases hj : j.val < K
    · rw [hout_lt i j hj]
      exact le_trans (hsz _ _ _ _) (by omega)
    · rw [hout_last i j hj, accConst_gateCount]
      omega
  have hcard : nIdx
      = Fintype.card (Fin (K + 1) → Fin (len + 1)) * Fintype.card (Fin (K + 1) → G) := by
    rw [hnIdx]
    exact Fintype.card_prod _ _
  refine ⟨accOrAnd outer (max d 1), wellFormedACC_accOrAnd hwf_out hlay_out,
    accOrAnd_layer_le hlay_out, ?_, ?_, ?_⟩
  · simp only [accOrAnd_gateCount]
    have hinner : ∀ i : Fin nIdx,
        (∑ j : Fin (K + 1), (outer i j).gateCount) + 1 ≤ (K + 1) * (Sz + 1) + 1 := by
      intro i
      have hsum : (∑ j : Fin (K + 1), (outer i j).gateCount) ≤ (K + 1) * (Sz + 1) := by
        refine le_trans (Finset.sum_le_card_nsmul Finset.univ _ _ (fun j _ => hsz_out i j)) ?_
        simp
      omega
    have hsum_out : (∑ i : Fin nIdx, ((∑ j : Fin (K + 1), (outer i j).gateCount) + 1))
        ≤ nIdx * ((K + 1) * (Sz + 1) + 1) := by
      refine le_trans (Finset.sum_le_card_nsmul Finset.univ _ _ (fun i _ => hinner i)) ?_
      simp
    calc (∑ i : Fin nIdx, ((∑ j : Fin (K + 1), (outer i j).gateCount) + 1)) + 1
        ≤ nIdx * ((K + 1) * (Sz + 1) + 1) + 1 := by omega
      _ = Fintype.card (Fin (K + 1) → Fin (len + 1)) * Fintype.card (Fin (K + 1) → G)
            * ((K + 1) * (Sz + 1) + 1) + 1 := by rw [hcard]
  · -- soundness
    intro x hx
    rw [accAccepts_accOrAnd hwf_out hlay_out x] at hx
    obtain ⟨i, hi⟩ := hx
    have hlast : ¬ (Fin.last K).val < K := by simp
    have hV : Valid (ee.symm i) := by
      have hacc := hi (Fin.last K)
      rw [hout_last i (Fin.last K) hlast] at hacc
      exact of_decide_eq_true ((accAccepts_accConst n m _ x).mp hacc)
    obtain ⟨hV0, hVlast, hVmono, hVg0, hVgh⟩ := hV
    have hstep : ∀ j : Fin K, (ee.symm i).2 j.succ
        = (ee.symm i).2 j.castSucc * blockProd f start
            ((ee.symm i).1 j.castSucc).val ((ee.symm i).1 j.succ).val x := by
      intro j
      have hj : (j.castSucc : Fin (K + 1)).val < K := by simp
      have hacc := hi j.castSucc
      rw [hout_lt i j.castSucc hj] at hacc
      have hcast : (⟨(j.castSucc : Fin (K + 1)).val, hj⟩ : Fin K) = j := by
        apply Fin.ext; simp
      rw [hcast] at hacc
      exact (hsound _ _ _ _ x (hVmono j) hacc).symm
    have hchain := blockProd_chain_fin f start x (K := K)
      (fun j => ((ee.symm i).1 j).val) (ee.symm i).2 hVmono hV0 hVg0 hstep (Fin.last K)
    rw [hVgh, hVlast] at hchain
    exact hchain.symm
  · -- completeness
    intro x hP hx
    rw [accAccepts_accOrAnd hwf_out hlay_out x]
    obtain ⟨t, ht0, htlast, htmono, htacc⟩ := hcomplete x hP
    refine ⟨ee (t, fun j : Fin (K + 1) => blockProd f start 0 (t j).val x), fun j => ?_⟩
    have hsymm : ee.symm (ee (t, fun j : Fin (K + 1) => blockProd f start 0 (t j).val x))
        = (t, fun j : Fin (K + 1) => blockProd f start 0 (t j).val x) :=
      ee.symm_apply_apply _
    by_cases hj : j.val < K
    · rw [hout_lt _ j hj, hsymm]
      exact htacc ⟨j.val, hj⟩
    · rw [hout_last _ j hj, hsymm]
      refine (accAccepts_accConst n m _ x).mpr (decide_eq_true ?_)
      refine ⟨ht0, htlast, htmono, ?_, ?_⟩
      · change blockProd f start 0 (t 0).val x = 1
        rw [ht0]
        exact blockProd_self f start 0 x
      · change blockProd f start 0 (t (Fin.last K)).val x = h
        rw [htlast]
        exact hx

end Internal
end AllenderOQ3
