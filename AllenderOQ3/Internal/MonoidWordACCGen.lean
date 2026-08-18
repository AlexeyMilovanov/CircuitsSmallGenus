import AllenderOQ3.Internal.MonoidWordACC
import AllenderOQ3.Internal.CommMonoidWordACC

set_option autoImplicit false
set_option linter.style.longLine false

namespace AllenderOQ3
namespace Internal

attribute [local instance] Classical.propDecidable

def MonoidWordACCGen (M : Type) [Monoid M] [Finite M] : Prop :=
  ∀ m_in d_in : Nat, 2 ≤ m_in → 2 ≤ d_in →
  ∃ m_out d_out exponent : Nat,
    2 ≤ m_out ∧ m_in ∣ m_out ∧
      ∀ {n : Nat} (letter : Nat → (Fin n → Bool) → M) (size : Nat),
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

theorem monoidWordACC_of_gen {M : Type} [Monoid M] [Finite M]
    (H : MonoidWordACCGen M) : MonoidWordACC M := by
  obtain ⟨m_out, d_out, exp, hmout2, hmoutdiv, h_all⟩ := H 2 2 (by decide) (by decide)
  exact ⟨m_out, d_out, exp, hmout2, h_all⟩

def commWordExponentGen (cM I P m_in : Nat) : Nat :=
  (I + P) ^ cM + (cM + (4 * (I + P) + 2 * (m_in * P + 3) + (m_in * P) * P + m_in * P + P + 30) + 3) + 5

/-- **The word problem of a finite commutative monoid is in `ACC⁰` (generalized).** -/
theorem monoidWordACCGen_of_comm (M : Type) [CommMonoid M] [Finite M] : MonoidWordACCGen M := by
  classical
  haveI : Fintype M := Fintype.ofFinite M
  intro m_in d_in hm_in hd_in
  have hm_in_pos : 0 < m_in := by omega
  obtain ⟨I, P0, hP0, hpow0⟩ := exists_index_period M
  have hP2 : 2 ≤ 2 * P0 := by omega
  have hpow : ∀ (g : M) (k : Nat), I ≤ k → g ^ (k + 2 * P0) = g ^ k :=
    fun g k hk => pow_add_mul_period (hpow0 g) 2 k hk
  have hModpos : 0 < m_in * (2 * P0) := by
    have : 0 < 2 * P0 := by omega
    exact Nat.mul_pos hm_in_pos this
  have hmoutdiv : m_in ∣ m_in * (2 * P0) := ⟨2 * P0, rfl⟩
  have hPMod : 2 * P0 ∣ m_in * (2 * P0) := ⟨m_in, Nat.mul_comm _ _⟩
  have hmout2 : 2 ≤ m_in * (2 * P0) := by
    have h1 : 2 ≤ m_in := hm_in
    have h2 : 2 ≤ 2 * P0 := hP2
    calc 2 ≤ 2 * 2 := by decide
      _ ≤ m_in * (2 * P0) := Nat.mul_le_mul h1 h2
  refine ⟨m_in * (2 * P0), max (2 * d_in + 2) 1 + 14, commWordExponentGen (Fintype.card M) I (2 * P0) m_in, hmout2, hmoutdiv, ?_⟩
  intro n letter size hrec start len
  have hletter : ∀ (i : Nat) (g : M), ∃ a : ACCCircuit n (m_in * (2 * P0)),
      WellFormedACC a ∧ (∀ q, a.layer q ≤ 2 * d_in + 2) ∧
      a.gateCount ≤ (m_in * (2 * P0) + 2) * size ∧
      (∀ x, ACCAccepts a x ↔ letter i x = g) := by
    intro i g
    obtain ⟨b, hbwf, hblay, hbsz, hbacc⟩ := hrec i g
    refine ⟨accModulusLift b hmoutdiv, wellFormedACC_accModulusLift b hmoutdiv hbwf, ?_, ?_, ?_⟩
    · exact accModulusLift_layer_le hblay
    · exact le_trans (accModulusLift_gateCount_le b hmoutdiv) (Nat.mul_le_mul_left _ hbsz)
    · intro x
      rw [evalACC_accModulusLift_of_pos hModpos hbwf x]
      exact hbacc x
  choose L hLwf hLlay hLsz hLacc using hletter
  have hS : 2 ≤ size + len + 2 := by omega
  have hsize1 : size ≤ (size + len + 2) ^ 1 := by rw [pow_one]; omega
  have hSzS : (m_in * (2 * P0) + 2) * size ≤ (size + len + 2) ^ (m_in * (2 * P0) + 3) :=
    le_trans (pow_bnd_mul (pow_bnd_const hS (m_in * (2 * P0) + 2)) hsize1)
      (pow_bnd_mono hS (by omega))
  have main : ∀ (a b : Nat) (g : M), ∃ c : ACCCircuit n (m_in * (2 * P0)),
      WellFormedACC c ∧ (∀ q, c.layer q ≤ max (2 * d_in + 2) 1 + 14) ∧
      c.gateCount ≤ (size + len + 2) ^ commWordExponentGen (Fintype.card M) I (2 * P0) m_in ∧
      (∀ x, ACCAccepts c x → blockProd letter start a b x = g) ∧
      (b - a ≤ len → ∀ x, ACCAccepts c x ↔ blockProd letter start a b x = g) := by
    intro a b g
    by_cases hbl : b - a ≤ len
    · have hblS : b - a ≤ size + len + 2 := by omega
      obtain ⟨c, hcwf, hclay, hcsz, hcacc⟩ :=
        exists_acc_prod_comm (M := M) (Mod := m_in * (2 * P0)) hModpos hP2 hPMod hpow
          (d := 2 * d_in + 2) (Sz := (m_in * (2 * P0) + 2) * size) (S := size + len + 2)
          (s := m_in * (2 * P0) + 3) (bl := b - a) hS hblS hSzS
          (fun p => start + a + p) letter L hLwf hLlay hLsz hLacc g
      refine ⟨c, hcwf, hclay, hcsz, ?_, ?_⟩
      · intro x hx
        rw [blockProd_eq_prod]
        exact (hcacc x).mp hx
      · intro _ x
        rw [blockProd_eq_prod]
        exact hcacc x
    · refine ⟨accConst n (m_in * (2 * P0)) false,
        wellFormedACC_accConst n (m_in * (2 * P0)) false, ?_, ?_, ?_, ?_⟩
      · intro q
        have hl : 1 ≤ max (2 * d_in + 2) 1 + 14 := by omega
        rw [accConst_layer]
        exact hl
      · rw [accConst_gateCount]; exact Nat.one_le_pow _ _ (by omega)
      · intro x hx
        exact absurd ((accAccepts_accConst n (m_in * (2 * P0)) false x).mp hx) (by simp)
      · intro h; exact absurd h hbl
  choose B hBwf hBlay hBsz hBsound hBcomp using main
  refine ⟨B, hBwf, hBlay, hBsz, hBsound, ?_⟩
  intro x a b hab hbl
  exact (hBcomp a b _ (by omega) x).mpr rfl

/-! ## Closure properties -/

/-- **The word problem passes to submonoids.** -/
theorem monoidWordACCGen_submonoid {N : Type} [Monoid N] [Finite N]
    (H : MonoidWordACCGen N) (S : Submonoid N) : MonoidWordACCGen S := by
  classical
  intro m_in d_in hm_in hd_in
  obtain ⟨M, D, e, hM, hmdiv, hcore⟩ := H m_in d_in hm_in hd_in
  refine ⟨M, max D 1, e, hM, hmdiv, ?_⟩
  intro n letter size hrec start len
  -- the same word, read in the ambient monoid
  set letterN : Nat → (Fin n → Bool) → N := fun i x => ((letter i x : S) : N) with hletterN
  have hrecN : ∀ (i : Nat) (mm : N),
      ∃ a : ACCCircuit n m_in,
        WellFormedACC a ∧ (∀ q, a.layer q ≤ d_in) ∧ a.gateCount ≤ size ∧
        (∀ x, ACCAccepts a x ↔ letterN i x = mm) := by
    intro i mm
    by_cases hmm : mm ∈ S
    · obtain ⟨a, h1, h2, h3, h4⟩ := hrec i ⟨mm, hmm⟩
      refine ⟨a, h1, h2, h3, fun x => ?_⟩
      rw [h4 x, hletterN]
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    · refine ⟨accConst n m_in false, wellFormedACC_accConst n m_in false, ?_, ?_, ?_⟩
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

/-- **The word problem passes to quotients**, i.e. along a surjective monoid
homomorphism. -/
theorem monoidWordACCGen_of_surjective {N M' : Type} [Monoid N] [Finite N] [Monoid M'] [Finite M']
    (H : MonoidWordACCGen N) (phi : N →* M') (hphi : Function.Surjective phi) :
    MonoidWordACCGen M' := by
  classical
  haveI : Fintype N := Fintype.ofFinite N
  intro m_in d_in hm_in hd_in
  obtain ⟨Mo, D, e, hMo, hmdiv, hcore⟩ := H m_in d_in hm_in hd_in
  -- a set-theoretic section of `phi`
  choose sec hsec using hphi
  have hsecinj : Function.Injective sec := Function.LeftInverse.injective hsec
  refine ⟨Mo, max D 1 + 2, e + (Fintype.card N * 3 + 1), hMo, hmdiv, ?_⟩
  intro n letter size hrec start len
  set letterN : Nat → (Fin n → Bool) → N := fun i x => sec (letter i x) with hletterN
  have hsize_pos : 1 ≤ size := by
    obtain ⟨a, _, _, h3, _⟩ := hrec 0 1
    have := a.output.isLt
    omega
  have hrecN : ∀ (i : Nat) (mm : N),
      ∃ a : ACCCircuit n m_in,
        WellFormedACC a ∧ (∀ q, a.layer q ≤ d_in) ∧ a.gateCount ≤ size ∧
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
    · refine ⟨accConst n m_in false, wellFormedACC_accConst n m_in false, ?_, ?_, ?_⟩
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
theorem monoidWordACCGen_of_divides {N M' : Type} [Monoid N] [Finite N] [Monoid M'] [Finite M']
    (H : MonoidWordACCGen N) (S : Submonoid N) (phi : S →* M') (hphi : Function.Surjective phi) :
    MonoidWordACCGen M' :=
  monoidWordACCGen_of_surjective (monoidWordACCGen_submonoid H S) phi hphi

end Internal
end AllenderOQ3
