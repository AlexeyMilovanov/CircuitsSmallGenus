import AllenderOQ3.Internal.RotationExists

/-!
# Deleting one edge of a circuit

Deleting an edge of an embedded graph never increases its genus.  This file
carries out the combinatorial surgery: a rotation system of the smaller graph
is obtained by *splicing* the two darts of the deleted edge out of the rotation,
and the resulting change of the face, edge, vertex and component counts is
computed exactly.
-/

set_option autoImplicit false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace AllenderOQ3.Internal

open Equiv Equiv.Perm

/-! ## The edge-deleted circuit

These declarations were originally stated in `AllenderOQ3.Internal.Surgery`;
they live here so that the surgery lemmas below can refer to them. -/

/-- Delete a single directed edge from the circuit. -/
def deleteEdge {n : Nat} (c : ADRCircuit n) (u v : Fin c.gateCount) : ADRCircuit n :=
  { c with edge := fun a b => if a = u ∧ b = v then false else c.edge a b }

@[simp]
theorem deleteEdge_gateCount {n : Nat} (c : ADRCircuit n) (u v : Fin c.gateCount) :
    (deleteEdge c u v).gateCount = c.gateCount := rfl

@[simp]
theorem deleteEdge_output {n : Nat} (c : ADRCircuit n) (u v : Fin c.gateCount) :
    (deleteEdge c u v).output = c.output := rfl

@[simp]
theorem deleteEdge_kind {n : Nat} (c : ADRCircuit n) (u v : Fin c.gateCount)
    (g : Fin c.gateCount) :
    (deleteEdge c u v).kind g = c.kind g := rfl

@[simp]
theorem deleteEdge_layer {n : Nat} (c : ADRCircuit n) (u v : Fin c.gateCount)
    (g : Fin c.gateCount) :
    (deleteEdge c u v).layer g = c.layer g := rfl

@[simp]
theorem deleteEdge_edge {n : Nat} (c : ADRCircuit n) (u v a b : Fin c.gateCount) :
    (deleteEdge c u v).edge a b = if a = u ∧ b = v then false else c.edge a b := rfl

theorem wellFormed_deleteEdge {n : Nat} {c : ADRCircuit n} (hc : WellFormedADR c)
    (u v : Fin c.gateCount) : WellFormedADR (deleteEdge c u v) := by
  constructor
  · intro a b hab
    dsimp [deleteEdge] at hab
    split at hab
    · contradiction
    · exact hc.1 a b hab
  · intro g hg h
    dsimp [deleteEdge]
    split
    · rfl
    · exact hc.2 g hg h

theorem width_deleteEdge {n : Nat} {c : ADRCircuit n} {u v : Fin c.gateCount}
    {w : Nat} (hw : ADRHasWidthAtMost c w) : ADRHasWidthAtMost (deleteEdge c u v) w := by
  intro ell
  exact hw ell


/-! ## Splicing one point out of a permutation -/

section Splice

variable {α : Type} [Fintype α] [DecidableEq α]

/-- The permutation `p` with the point `a` removed from its cycle. -/
def splicePerm (p : Perm α) (a : α) : Perm α := p * Equiv.swap (p⁻¹ a) a

omit [Fintype α] in
theorem splicePerm_fix (p : Perm α) (a : α) : splicePerm p a a = a := by
  simp [splicePerm]

omit [Fintype α] in
theorem splicePerm_pred (p : Perm α) (a : α) : splicePerm p a (p⁻¹ a) = p a := by
  by_cases h : p⁻¹ a = a
  · simp [splicePerm, h]
  · simp [splicePerm, Equiv.swap_apply_left]

omit [Fintype α] in
theorem splicePerm_of_ne (p : Perm α) (a : α) {x : α} (hxa : x ≠ a) (hxq : x ≠ p⁻¹ a) :
    splicePerm p a x = p x := by
  rw [splicePerm, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hxq hxa]

omit [Fintype α] in
/-- Points different from `a` that `p` connects are still connected after the
splice. -/
theorem splicePerm_pow_reach (p : Perm α) (a : α) (hqa : p⁻¹ a ≠ a) (k : Nat) :
    ∀ z : α, z ≠ a → (p ^ k) z ≠ a → ∃ m : Nat, ((splicePerm p a) ^ m) z = (p ^ k) z := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => intro z _ _; exact ⟨0, rfl⟩
    | 1 =>
        intro z hz hk
        refine ⟨1, ?_⟩
        have hzq : z ≠ p⁻¹ a := by
          intro h
          apply hk
          rw [pow_one, h]
          simp
        rw [pow_one, pow_one, splicePerm_of_ne p a hz hzq]
    | (k + 2) =>
        intro z hz hk
        have hstep : (p ^ (k + 2)) z = p ((p ^ (k + 1)) z) := by
          rw [pow_succ']; rfl
        by_cases hwa : (p ^ (k + 1)) z = a
        · have hkz : (p ^ k) z = p⁻¹ a := by
            have h1 : p ((p ^ k) z) = a := by
              have : (p ^ (k + 1)) z = p ((p ^ k) z) := by rw [pow_succ']; rfl
              rw [← this, hwa]
            rw [← h1]
            simp
          obtain ⟨m, hm⟩ := ih k (by omega) z hz (by rw [hkz]; exact hqa)
          refine ⟨m + 1, ?_⟩
          have : ((splicePerm p a) ^ (m + 1)) z = splicePerm p a (((splicePerm p a) ^ m) z) := by
            rw [pow_succ']; rfl
          rw [this, hm, hkz, splicePerm_pred, hstep, hwa]
        · obtain ⟨m, hm⟩ := ih (k + 1) (by omega) z hz hwa
          refine ⟨m + 1, ?_⟩
          have hval : ((splicePerm p a) ^ (m + 1)) z
              = splicePerm p a (((splicePerm p a) ^ m) z) := by
            rw [pow_succ']; rfl
          have hwq : (p ^ (k + 1)) z ≠ p⁻¹ a := by
            intro h
            apply hk
            rw [hstep, h]
            simp
          rw [hval, hm, splicePerm_of_ne p a hwa hwq, hstep]

/-- Splicing out `a` preserves the cycle relation among the other points. -/
theorem sameCycle_splicePerm (p : Perm α) (a : α) {x y : α} (hx : x ≠ a) (hy : y ≠ a)
    (h : p.SameCycle x y) : (splicePerm p a).SameCycle x y := by
  by_cases hqa : p⁻¹ a = a
  · have hs : splicePerm p a = p := by
      rw [splicePerm, hqa]
      simp
    rw [hs]
    exact h
  · obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
    obtain ⟨m, hm⟩ := splicePerm_pow_reach p a hqa k x hx (by rw [hk]; exact hy)
    exact ⟨(m : ℤ), by simpa using hm.trans hk⟩

/-! ## Splicing the two darts of an edge out of a rotation -/

omit [Fintype α] in
theorem source_splicePerm {β : Type} (p : Perm α) (s : α → β)
    (hp : ∀ x, s (p x) = s x) (a x : α) : s (splicePerm p a x) = s x := by
  have hqa : s (p⁻¹ a) = s a := by
    have h := hp (p⁻¹ a)
    simp only [Equiv.Perm.inv_def, Equiv.apply_symm_apply] at h
    exact h.symm
  rw [splicePerm, Equiv.Perm.mul_apply, hp]
  by_cases hx : x = p⁻¹ a
  · rw [hx, Equiv.swap_apply_left, hqa]
  · by_cases hx2 : x = a
    · rw [hx2, Equiv.swap_apply_right, hqa]
    · rw [Equiv.swap_apply_of_ne_of_ne hx hx2]

end Splice

section DartSplice

variable {n : Nat} {c : ADRCircuit n}

theorem dartReverse_reverse (d : CircuitDart c) : dartReverse c (dartReverse c d) = d := rfl

theorem dartReverse_ne_self (d : CircuitDart c) : dartReverse c d ≠ d := by
  intro h
  exact d.2.2 (congrArg (fun e : CircuitDart c => e.1.1) h).symm

theorem dartReverse_source (d : CircuitDart c) : (dartReverse c d).source = d.target := rfl

theorem dartReverse_mul_self : (dartReverse c) * (dartReverse c) = 1 := by
  apply Equiv.ext
  intro d
  exact dartReverse_reverse d

/-- Both darts of the edge carrying `d₀`, spliced out of a rotation. -/
def dartSplice (p : Perm (CircuitDart c)) (d₀ : CircuitDart c) : Perm (CircuitDart c) :=
  splicePerm (splicePerm p d₀) (dartReverse c d₀)

theorem dartSplice_reverse (p : Perm (CircuitDart c)) (d₀ : CircuitDart c) :
    dartSplice p d₀ (dartReverse c d₀) = dartReverse c d₀ := splicePerm_fix _ _

theorem dartSplice_self (p : Perm (CircuitDart c)) (d₀ : CircuitDart c) :
    dartSplice p d₀ d₀ = d₀ := by
  have h1 : splicePerm p d₀ d₀ = d₀ := splicePerm_fix _ _
  have hne : d₀ ≠ dartReverse c d₀ := fun h => dartReverse_ne_self d₀ h.symm
  have hq : d₀ ≠ (splicePerm p d₀)⁻¹ (dartReverse c d₀) := by
    intro h
    have h2 := congrArg (splicePerm p d₀) h
    simp only [Equiv.Perm.inv_def, Equiv.apply_symm_apply] at h2
    rw [h1] at h2
    exact hne h2
  rw [dartSplice, splicePerm_of_ne _ _ hne hq, h1]

theorem dartSplice_source (p : Perm (CircuitDart c))
    (hp : ∀ x : CircuitDart c, (p x).source = x.source) (d₀ x : CircuitDart c) :
    (dartSplice p d₀ x).source = x.source := by
  have h1 : ∀ y : CircuitDart c, (splicePerm p d₀ y).source = y.source :=
    source_splicePerm p CircuitDart.source hp d₀
  exact source_splicePerm _ CircuitDart.source h1 _ x

theorem sameCycle_dartSplice (p : Perm (CircuitDart c)) (d₀ : CircuitDart c)
    {x y : CircuitDart c} (hx0 : x ≠ d₀) (hx1 : x ≠ dartReverse c d₀)
    (hy0 : y ≠ d₀) (hy1 : y ≠ dartReverse c d₀) (h : p.SameCycle x y) :
    (dartSplice p d₀).SameCycle x y :=
  sameCycle_splicePerm _ _ hx1 hy1 (sameCycle_splicePerm _ _ hx0 hy0 h)

theorem dartSplice_eq_mul (r : OrientableRotation c) (d₀ : CircuitDart c) :
    dartSplice r.rotation d₀
      = r.rotation * Equiv.swap (r.rotation⁻¹ d₀) d₀
        * Equiv.swap (r.rotation⁻¹ (dartReverse c d₀)) (dartReverse c d₀) := by
  have hsrcinv : ∀ x : CircuitDart c, (r.rotation⁻¹ x).source = x.source := by
    intro x
    have h := r.preservesSource (r.rotation⁻¹ x)
    simp only [Equiv.Perm.inv_def, Equiv.apply_symm_apply] at h
    exact h.symm
  have hsrcne : (dartReverse c d₀).source ≠ d₀.source := fun h => d₀.2.2 h.symm
  have hne1 : r.rotation⁻¹ (dartReverse c d₀) ≠ d₀ := by
    intro h
    apply hsrcne
    rw [← hsrcinv (dartReverse c d₀), h]
  have hne2 : r.rotation⁻¹ (dartReverse c d₀) ≠ r.rotation⁻¹ d₀ := by
    intro h
    exact dartReverse_ne_self d₀ ((Equiv.injective _) h)
  have hstep : splicePerm r.rotation d₀ (r.rotation⁻¹ (dartReverse c d₀)) = dartReverse c d₀ := by
    rw [splicePerm_of_ne _ _ hne1 hne2]
    simp
  have hinv : (splicePerm r.rotation d₀)⁻¹ (dartReverse c d₀)
      = r.rotation⁻¹ (dartReverse c d₀) := by
    have h := congrArg (fun x => (splicePerm r.rotation d₀)⁻¹ x) hstep
    simp only [Equiv.Perm.inv_def, Equiv.symm_apply_apply] at h
    exact h.symm
  rw [dartSplice, splicePerm, hinv, splicePerm]

theorem faceSplice_eq (r : OrientableRotation c) (d₀ : CircuitDart c) :
    dartSplice r.rotation d₀ * dartReverse c
      = facePermutation r * Equiv.swap ((facePermutation r)⁻¹ d₀) (dartReverse c d₀)
        * Equiv.swap ((facePermutation r)⁻¹ (dartReverse c d₀)) d₀ := by
  have hainv : (dartReverse c)⁻¹ = dartReverse c :=
    inv_eq_of_mul_eq_one_right dartReverse_mul_self
  have hface : facePermutation r = r.rotation * dartReverse c := rfl
  have hfaceinv : (facePermutation r)⁻¹ = dartReverse c * r.rotation⁻¹ := by
    rw [hface, mul_inv_rev, hainv]
  have h0 : (facePermutation r)⁻¹ d₀ = dartReverse c (r.rotation⁻¹ d₀) := by rw [hfaceinv]; rfl
  have h1 : (facePermutation r)⁻¹ (dartReverse c d₀)
      = dartReverse c (r.rotation⁻¹ (dartReverse c d₀)) := by rw [hfaceinv]; rfl
  have hswap0 : Equiv.swap ((facePermutation r)⁻¹ d₀) (dartReverse c d₀)
      = dartReverse c * Equiv.swap (r.rotation⁻¹ d₀) d₀ * (dartReverse c)⁻¹ := by
    rw [← Equiv.swap_apply_apply, h0]
  have hswap1 : Equiv.swap ((facePermutation r)⁻¹ (dartReverse c d₀)) d₀
      = dartReverse c * Equiv.swap (r.rotation⁻¹ (dartReverse c d₀)) (dartReverse c d₀)
        * (dartReverse c)⁻¹ := by
    rw [← Equiv.swap_apply_apply, h1, dartReverse_reverse]
  rw [dartSplice_eq_mul, hswap0, hswap1, hface, hainv]
  have key : ∀ X : Perm (CircuitDart c), dartReverse c * (dartReverse c * X) = X := by
    intro X
    rw [← mul_assoc, dartReverse_mul_self, one_mul]
  simp only [mul_assoc, key]

theorem faceSplice_apply_self (p : Perm (CircuitDart c)) (d₀ : CircuitDart c) :
    (dartSplice p d₀ * dartReverse c) d₀ = dartReverse c d₀ :=
  dartSplice_reverse p d₀

theorem faceSplice_apply_reverse (p : Perm (CircuitDart c)) (d₀ : CircuitDart c) :
    (dartSplice p d₀ * dartReverse c) (dartReverse c d₀) = d₀ := by
  change dartSplice p d₀ (dartReverse c (dartReverse c d₀)) = d₀
  rw [dartReverse_reverse]
  exact dartSplice_self p d₀

theorem dartSplice_invariant (p : Perm (CircuitDart c)) (d₀ x : CircuitDart c) :
    (dartSplice p d₀ x ≠ d₀ ∧ dartSplice p d₀ x ≠ dartReverse c d₀)
      ↔ (x ≠ d₀ ∧ x ≠ dartReverse c d₀) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun hx => h1 ?_, fun hx => h2 ?_⟩
    · rw [hx]; exact dartSplice_self p d₀
    · rw [hx]; exact dartSplice_reverse p d₀
  · rintro ⟨h1, h2⟩
    refine ⟨fun hx => h1 ?_, fun hx => h2 ?_⟩
    · refine Equiv.injective (dartSplice p d₀) ?_
      rw [hx, dartSplice_self]
    · refine Equiv.injective (dartSplice p d₀) ?_
      rw [hx, dartSplice_reverse]

end DartSplice

section TwoCycle

variable {α : Type} [Fintype α] [DecidableEq α]

omit [Fintype α] [DecidableEq α] in
/-- A permutation that swaps `a` and `b` has `{a, b}` as the orbit of `a`. -/
theorem two_cycle_pow {P : Perm α} {a b : α} (hab : P a = b) (hba : P b = a) :
    ∀ k : Nat, (P ^ k) a = a ∨ (P ^ k) a = b := by
  intro k
  induction k with
  | zero => exact Or.inl rfl
  | succ k ih =>
      have hval : (P ^ (k + 1)) a = P ((P ^ k) a) := by rw [pow_succ']; rfl
      rcases ih with h | h
      · exact Or.inr (by rw [hval, h, hab])
      · exact Or.inl (by rw [hval, h, hba])

omit [DecidableEq α] in
theorem two_cycle_sameCycle {P : Perm α} {a b x : α} (hab : P a = b) (hba : P b = a)
    (h : P.SameCycle a x) : x = a ∨ x = b := by
  obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
  rcases two_cycle_pow hab hba k with hp | hp
  · exact Or.inl (by rw [← hk, hp])
  · exact Or.inr (by rw [← hk, hp])

end TwoCycle

section FaceCount

variable {n : Nat} {c : ADRCircuit n}

/-- Splicing both darts of an edge out of the rotation changes the number of
faces by one, in the direction dictated by whether the two darts lie on a
common face.  The two `if`s on the left account for an endpoint of the edge
that has no other dart. -/
theorem permCycleCount_faceSplice (r : OrientableRotation c) (d₀ : CircuitDart c) :
    permCycleCount (dartSplice r.rotation d₀ * dartReverse c)
      + (if (facePermutation r)⁻¹ d₀ = dartReverse c d₀ then 1 else 0)
      + (if (facePermutation r)⁻¹ (dartReverse c d₀) = d₀ then 1 else 0)
      = permCycleCount (facePermutation r)
        + (if (facePermutation r).SameCycle d₀ (dartReverse c d₀) then 2 else 0) := by
  classical
  set d₁ := dartReverse c d₀ with hd1
  set fp := facePermutation r with hfp
  set fh := dartSplice r.rotation d₀ * dartReverse c with hfh
  set a0 := fp⁻¹ d₀ with ha0def
  set a1 := fp⁻¹ d₁ with ha1def
  have hd01 : d₀ ≠ d₁ := fun h => dartReverse_ne_self d₀ h.symm
  have hsrc : d₁.source ≠ d₀.source := fun h => d₀.2.2 h.symm
  have hfp0 : fp d₀ = r.rotation d₁ := rfl
  have hfp1 : fp d₁ = r.rotation d₀ := by
    change r.rotation (dartReverse c d₁) = r.rotation d₀
    rw [hd1, dartReverse_reverse]
  have hne0 : fp d₀ ≠ d₀ := by
    intro h
    apply hsrc
    rw [hfp0] at h
    rw [← h, r.preservesSource d₁]
  have hne1 : fp d₁ ≠ d₁ := by
    intro h
    apply hsrc.symm
    rw [hfp1] at h
    rw [← h, r.preservesSource d₀]
  have ha0 : a0 ≠ d₀ := by
    intro h
    apply hne0
    have hc := congrArg fp h
    rw [ha0def] at hc
    simp only [Equiv.Perm.inv_def, Equiv.apply_symm_apply] at hc
    exact hc.symm
  have ha1 : a1 ≠ d₁ := by
    intro h
    apply hne1
    have hc := congrArg fp h
    rw [ha1def] at hc
    simp only [Equiv.Perm.inv_def, Equiv.apply_symm_apply] at hc
    exact hc.symm
  have hfh0 : fh d₀ = d₁ := faceSplice_apply_self r.rotation d₀
  have hfh1 : fh d₁ = d₀ := faceSplice_apply_reverse r.rotation d₀
  have hkey : fh = fp * Equiv.swap a0 d₁ * Equiv.swap a1 d₀ := faceSplice_eq r d₀
  have hSC : fp.SameCycle a0 d₁ ↔ fp.SameCycle d₀ d₁ := by
    rw [ha0def, Equiv.Perm.inv_def, Equiv.Perm.sameCycle_symm_apply_left]
  by_cases h0 : a0 = d₁
  · have hfpd1 : fp d₁ = d₀ := by
      rw [← h0, ha0def]
      simp
    have hsame : fp.SameCycle d₀ d₁ :=
      (show fp.SameCycle d₁ d₀ from ⟨1, by simpa using hfpd1⟩).symm
    by_cases h1 : a1 = d₀
    · have hfheq : fh = fp := by
        rw [hkey, h0, h1]
        simp
      rw [hfheq]
      simp [h0, h1, hsame]
    · have hfheq : fh = fp * Equiv.swap a1 d₀ := by
        rw [hkey, h0]
        simp
      have hfhback : fh * Equiv.swap a1 d₀ = fp := by
        rw [hfheq, mul_assoc, Equiv.swap_mul_self, mul_one]
      have hnsc : ¬ fh.SameCycle a1 d₀ := by
        intro hc
        rcases two_cycle_sameCycle hfh0 hfh1 hc.symm with h | h
        · exact h1 h
        · exact ha1 h
      have hcount := permCycleCount_mul_swap_of_not_sameCycle hnsc
      rw [hfhback] at hcount
      simp only [if_pos h0, if_neg h1, if_pos hsame]
      omega
  · by_cases h1 : a1 = d₀
    · have hfpd0 : fp d₀ = d₁ := by
        rw [← h1, ha1def]
        simp
      have hsame : fp.SameCycle d₀ d₁ := ⟨1, by simpa using hfpd0⟩
      have hfheq : fh = fp * Equiv.swap a0 d₁ := by
        rw [hkey, h1]
        simp
      have hfhback : fh * Equiv.swap a0 d₁ = fp := by
        rw [hfheq, mul_assoc, Equiv.swap_mul_self, mul_one]
      have hnsc : ¬ fh.SameCycle a0 d₁ := by
        intro hc
        rcases two_cycle_sameCycle hfh1 hfh0 hc.symm with h | h
        · exact h0 h
        · exact ha0 h
      have hcount := permCycleCount_mul_swap_of_not_sameCycle hnsc
      rw [hfhback] at hcount
      simp only [if_neg h0, if_pos h1, if_pos hsame]
      omega
    · have hpsi : fh * Equiv.swap a1 d₀ = fp * Equiv.swap a0 d₁ := by
        rw [hkey, mul_assoc, mul_assoc, Equiv.swap_mul_self, mul_one]
      have hnsc1 : ¬ fh.SameCycle a1 d₀ := by
        intro hc
        rcases two_cycle_sameCycle hfh0 hfh1 hc.symm with h | h
        · exact h1 h
        · exact ha1 h
      have hstep1 := permCycleCount_mul_swap_of_not_sameCycle hnsc1
      rw [hpsi] at hstep1
      by_cases hsc : fp.SameCycle d₀ d₁
      · have hstep2 : permCycleCount (fp * Equiv.swap a0 d₁) = permCycleCount fp + 1 :=
          permCycleCount_mul_swap_of_sameCycle h0 (hSC.mpr hsc)
        simp only [if_neg h0, if_neg h1, if_pos hsc]
        omega
      · have hstep2 : permCycleCount (fp * Equiv.swap a0 d₁) + 1 = permCycleCount fp :=
          permCycleCount_mul_swap_of_not_sameCycle (fun hc => hsc (hSC.mp hc))
        simp only [if_neg h0, if_neg h1, if_neg hsc]
        omega

/-- The two darts of the deleted edge form a cycle of the spliced face
permutation, so the remaining darts are invariant. -/
theorem faceSplice_invariant (p : Perm (CircuitDart c)) (d₀ x : CircuitDart c) :
    ((dartSplice p d₀ * dartReverse c) x ≠ d₀
        ∧ (dartSplice p d₀ * dartReverse c) x ≠ dartReverse c d₀)
      ↔ (x ≠ d₀ ∧ x ≠ dartReverse c d₀) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun hx => h2 ?_, fun hx => h1 ?_⟩
    · rw [hx]; exact faceSplice_apply_self p d₀
    · rw [hx]; exact faceSplice_apply_reverse p d₀
  · rintro ⟨h1, h2⟩
    refine ⟨fun hx => h2 ?_, fun hx => h1 ?_⟩
    · refine Equiv.injective (dartSplice p d₀ * dartReverse c) ?_
      rw [hx, faceSplice_apply_reverse]
    · refine Equiv.injective (dartSplice p d₀ * dartReverse c) ?_
      rw [hx, faceSplice_apply_self]

/-- The spliced face permutation has exactly one more cycle than its restriction
to the surviving darts. -/
theorem permCycleCount_faceSplice_split (p : Perm (CircuitDart c)) (d₀ : CircuitDart c) :
    permCycleCount (dartSplice p d₀ * dartReverse c)
      = permCycleCount ((dartSplice p d₀ * dartReverse c).subtypePerm
          (p := fun x => x ≠ d₀ ∧ x ≠ dartReverse c d₀)
          (fun x => faceSplice_invariant p d₀ x)) + 1 := by
  classical
  have hcomp : permCycleCount ((dartSplice p d₀ * dartReverse c).subtypePerm
      (p := fun x => ¬ (x ≠ d₀ ∧ x ≠ dartReverse c d₀))
      (fun x => not_congr (faceSplice_invariant p d₀ x))) = 1 := by
    haveI : Nonempty {x : CircuitDart c // ¬ (x ≠ d₀ ∧ x ≠ dartReverse c d₀)} :=
      ⟨⟨d₀, by simp⟩⟩
    apply permCycleCount_eq_one
    intro x y
    rw [Equiv.Perm.sameCycle_subtypePerm]
    have hx : x.1 = d₀ ∨ x.1 = dartReverse c d₀ := by
      by_contra hc
      push_neg at hc
      exact x.2 ⟨hc.1, hc.2⟩
    have hy : y.1 = d₀ ∨ y.1 = dartReverse c d₀ := by
      by_contra hc
      push_neg at hc
      exact y.2 ⟨hc.1, hc.2⟩
    rcases hx with hx | hx <;> rcases hy with hy | hy <;> rw [hx, hy]
    · exact ⟨1, by simp only [zpow_one]; exact faceSplice_apply_self p d₀⟩
    · exact ⟨1, by simp only [zpow_one]; exact faceSplice_apply_reverse p d₀⟩
  rw [permCycleCount_split (dartSplice p d₀ * dartReverse c)
    (fun x => x ≠ d₀ ∧ x ≠ dartReverse c d₀) (fun x => faceSplice_invariant p d₀ x), hcomp]

end FaceCount


/-! ## The underlying graph after deletion -/

theorem deleteEdge_edge_of_ne {n : Nat} (c : ADRCircuit n) (u v a b : Fin c.gateCount)
    (h : ¬ (a = u ∧ b = v)) : (deleteEdge c u v).edge a b = c.edge a b := if_neg h

theorem adj_deleteEdge_of_adj {n : Nat} (c : ADRCircuit n) (u v a b : Fin c.gateCount)
    (h : UnderlyingAdj (deleteEdge c u v) a b) : UnderlyingAdj c a b := by
  refine ⟨?_, h.2⟩
  rcases h.1 with he | he
  · rw [deleteEdge_edge] at he
    split at he
    · exact absurd he (by simp)
    · exact Or.inl he
  · rw [deleteEdge_edge] at he
    split at he
    · exact absurd he (by simp)
    · exact Or.inr he

/-- If the deleted edge is absent, doubled, or a loop, the underlying graph does
not change. -/
theorem adj_deleteEdge_iff_of_degenerate {n : Nat} (c : ADRCircuit n) (u v : Fin c.gateCount)
    (h : c.edge u v = false ∨ c.edge v u = true ∨ u = v) (a b : Fin c.gateCount) :
    UnderlyingAdj (deleteEdge c u v) a b ↔ UnderlyingAdj c a b := by
  refine ⟨adj_deleteEdge_of_adj c u v a b, fun hd => ⟨?_, hd.2⟩⟩
  have hne := hd.2
  by_cases hab : a = u ∧ b = v
  · obtain ⟨rfl, rfl⟩ := hab
    have hba : (deleteEdge c a b).edge b a = c.edge b a :=
      deleteEdge_edge_of_ne c a b b a (fun hc => hne hc.2)
    have hvu : c.edge b a = true := by
      rcases hd.1 with he | he
      · rcases h with h1 | h1 | h1
        · rw [h1] at he; exact absurd he (by simp)
        · exact h1
        · exact absurd h1 hne
      · exact he
    exact Or.inr (by rw [hba, hvu])
  · have hab' : (deleteEdge c u v).edge a b = c.edge a b := deleteEdge_edge_of_ne c u v a b hab
    rcases hd.1 with he | he
    · exact Or.inl (by rw [hab', he])
    · by_cases hba : b = u ∧ a = v
      · obtain ⟨rfl, rfl⟩ := hba
        have hvu : c.edge a b = true := by
          rcases h with h1 | h1 | h1
          · rw [h1] at he; exact absurd he (by simp)
          · exact h1
          · exact absurd h1 (Ne.symm hne)
        exact Or.inl (by rw [hab', hvu])
      · exact Or.inr (by rw [deleteEdge_edge_of_ne c u v b a hba, he])

/-- In the interesting case exactly the two darts of the edge `u → v` disappear. -/
theorem adj_deleteEdge_iff {n : Nat} (c : ADRCircuit n) (u v : Fin c.gateCount)
    (hvu : c.edge v u = false) (a b : Fin c.gateCount) :
    UnderlyingAdj (deleteEdge c u v) a b ↔
      UnderlyingAdj c a b ∧ ¬ (a = u ∧ b = v) ∧ ¬ (a = v ∧ b = u) := by
  constructor
  · intro hd
    refine ⟨adj_deleteEdge_of_adj c u v a b hd, ?_, ?_⟩
    · rintro ⟨rfl, rfl⟩
      have h1 : (deleteEdge c a b).edge a b = false := if_pos ⟨rfl, rfl⟩
      have h2 : (deleteEdge c a b).edge b a = false := by
        rw [deleteEdge_edge_of_ne c a b b a (fun hc => hd.2 hc.2)]
        exact hvu
      rcases hd.1 with he | he
      · rw [h1] at he; exact Bool.noConfusion he
      · rw [h2] at he; exact Bool.noConfusion he
    · rintro ⟨rfl, rfl⟩
      have h1 : (deleteEdge c b a).edge a b = false := by
        rw [deleteEdge_edge_of_ne c b a a b (fun hc => hd.2 hc.1)]
        exact hvu
      have h2 : (deleteEdge c b a).edge b a = false := if_pos ⟨rfl, rfl⟩
      rcases hd.1 with he | he
      · rw [h1] at he; exact Bool.noConfusion he
      · rw [h2] at he; exact Bool.noConfusion he
  · rintro ⟨hd, h1, h2⟩
    refine ⟨?_, hd.2⟩
    rcases hd.1 with he | he
    · exact Or.inl (by rw [deleteEdge_edge_of_ne c u v a b h1, he])
    · exact Or.inr (by rw [deleteEdge_edge_of_ne c u v b a (fun hc => h2 ⟨hc.2, hc.1⟩), he])

/-! ## The degenerate case -/

/-- If the deletion does not change the underlying graph, the genus is unchanged. -/
theorem genus_deleteEdge_eq_of_adj_eq {n : Nat} (c : ADRCircuit n) (u v : Fin c.gateCount)
    (h : ∀ a b : Fin c.gateCount, UnderlyingAdj (deleteEdge c u v) a b ↔ UnderlyingAdj c a b) :
    orientableCircuitGenus (deleteEdge c u v) = orientableCircuitGenus c := by
  classical
  set phi : CircuitDart (deleteEdge c u v) ≃ CircuitDart c :=
    Equiv.subtypeEquivRight (fun p => h p.1 p.2) with hphi
  have hs : ∀ d e : CircuitDart (deleteEdge c u v),
      (phi d).source = (phi e).source ↔ d.source = e.source := fun _ _ => Iff.rfl
  have hrev : ∀ d : CircuitDart (deleteEdge c u v),
      phi (dartReverse (deleteEdge c u v) d) = dartReverse c (phi d) := fun _ => rfl
  have hs' : ∀ d e : CircuitDart c,
      (phi.symm d).source = (phi.symm e).source ↔ d.source = e.source := fun _ _ => Iff.rfl
  have hrev' : ∀ d : CircuitDart c,
      phi.symm (dartReverse c d) = dartReverse (deleteEdge c u v) (phi.symm d) := by
    intro d
    apply phi.injective
    rw [Equiv.apply_symm_apply, hrev, Equiv.apply_symm_apply]
  have hI : isolatedVertexCount (deleteEdge c u v) = isolatedVertexCount c := by
    unfold isolatedVertexCount
    congr 1
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact forall_congr' (fun x => not_congr (h w x))
  have hreach : ∀ a b : Fin c.gateCount,
      VertexReachable (deleteEdge c u v) a b ↔ VertexReachable c a b := by
    intro a b
    constructor
    · intro hr
      induction hr with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ hyz ih => exact ih.tail ((h _ _).mp hyz)
    · intro hr
      induction hr with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ hyz ih => exact ih.tail ((h _ _).mpr hyz)
  have hC : componentCount (deleteEdge c u v) = componentCount c := by
    unfold componentCount
    congr 1
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact forall_congr' (fun x => imp_congr_left (hreach w x))
  have hE : underlyingEdgeCount (deleteEdge c u v) = underlyingEdgeCount c := by
    have h1 := two_mul_underlyingEdgeCount (deleteEdge c u v)
    have h2 := two_mul_underlyingEdgeCount c
    have h3 : Fintype.card (CircuitDart (deleteEdge c u v)) = Fintype.card (CircuitDart c) :=
      Fintype.card_congr phi
    omega
  have harith : ∀ F : Nat,
      (2 * componentCount (deleteEdge c u v) + underlyingEdgeCount (deleteEdge c u v)
          - (deleteEdge c u v).gateCount - (F + isolatedVertexCount (deleteEdge c u v))) / 2
        = (2 * componentCount c + underlyingEdgeCount c - c.gateCount
          - (F + isolatedVertexCount c)) / 2 := by
    intro F
    have hg : (deleteEdge c u v).gateCount = c.gateCount := rfl
    rw [hI, hC, hE, hg]
  unfold orientableCircuitGenus
  congr 1
  ext g
  constructor
  · rintro ⟨r', hr'⟩
    refine ⟨transportRotation phi.symm hs' r', ?_⟩
    rw [← hr']
    have hface : permCycleCount (facePermutation (transportRotation phi.symm hs' r'))
        = permCycleCount (facePermutation r') :=
      permCycleCount_facePermutation_transport phi.symm hs' hrev' r'
    unfold rotationGenus
    simp only [hface]
    exact (harith _).symm
  · rintro ⟨r, hr⟩
    refine ⟨transportRotation phi hs r, ?_⟩
    rw [← hr]
    have hface : permCycleCount (facePermutation (transportRotation phi hs r))
        = permCycleCount (facePermutation r) :=
      permCycleCount_facePermutation_transport phi hs hrev r
    unfold rotationGenus
    simp only [hface]
    exact harith _

/-! ## The surviving darts and the spliced rotation -/

section RealDeletion

variable {n : Nat} {c : ADRCircuit n} {u v : Fin c.gateCount}

/-- The dart `u → v` of the edge that gets deleted. -/
def deletedDart (huv : c.edge u v = true) (hne : u ≠ v) : CircuitDart c :=
  ⟨(u, v), ⟨Or.inl huv, hne⟩⟩

theorem eq_deletedDart_iff (huv : c.edge u v = true) (hne : u ≠ v) (d : CircuitDart c) :
    d = deletedDart huv hne ↔ (d.1.1 = u ∧ d.1.2 = v) := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    apply Subtype.ext
    exact Prod.ext h1 h2

theorem eq_reverse_deletedDart_iff (huv : c.edge u v = true) (hne : u ≠ v) (d : CircuitDart c) :
    d = dartReverse c (deletedDart huv hne) ↔ (d.1.1 = v ∧ d.1.2 = u) := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    apply Subtype.ext
    exact Prod.ext h1 h2

/-- The darts of the smaller circuit are exactly the darts of `c` other than the
two darts of the deleted edge. -/
def deleteDartEquiv (huv : c.edge u v = true) (hvu : c.edge v u = false) (hne : u ≠ v) :
    CircuitDart (deleteEdge c u v)
      ≃ {d : CircuitDart c // d ≠ deletedDart huv hne
            ∧ d ≠ dartReverse c (deletedDart huv hne)} where
  toFun d :=
    ⟨⟨d.1, ((adj_deleteEdge_iff c u v hvu d.1.1 d.1.2).mp d.2).1⟩, by
      obtain ⟨-, h1, h2⟩ := (adj_deleteEdge_iff c u v hvu d.1.1 d.1.2).mp d.2
      exact ⟨fun h => h1 ((eq_deletedDart_iff huv hne _).mp h),
        fun h => h2 ((eq_reverse_deletedDart_iff huv hne _).mp h)⟩⟩
  invFun t :=
    ⟨t.1.1, (adj_deleteEdge_iff c u v hvu t.1.1.1 t.1.1.2).mpr
      ⟨t.1.2, fun h => t.2.1 ((eq_deletedDart_iff huv hne _).mpr h),
        fun h => t.2.2 ((eq_reverse_deletedDart_iff huv hne _).mpr h)⟩⟩
  left_inv d := rfl
  right_inv t := rfl

/-- The rotation of the smaller circuit obtained by splicing both darts of the
deleted edge out of `r`. -/
def deleteRotation (huv : c.edge u v = true) (hvu : c.edge v u = false) (hne : u ≠ v)
    (r : OrientableRotation c) : OrientableRotation (deleteEdge c u v) where
  rotation :=
    (deleteDartEquiv huv hvu hne).trans
      (((dartSplice r.rotation (deletedDart huv hne)).subtypePerm
          (p := fun x => x ≠ deletedDart huv hne ∧ x ≠ dartReverse c (deletedDart huv hne))
          (fun x => dartSplice_invariant r.rotation (deletedDart huv hne) x)).trans
        (deleteDartEquiv huv hvu hne).symm)
  preservesSource := by
    intro d
    change (dartSplice r.rotation (deletedDart huv hne)
      ((deleteDartEquiv huv hvu hne d).1)).source = d.source
    rw [dartSplice_source r.rotation r.preservesSource]
    rfl
  cyclicAtVertex := by
    intro d e hde
    have hsrc : ((deleteDartEquiv huv hvu hne d).1).source
        = ((deleteDartEquiv huv hvu hne e).1).source := hde
    obtain ⟨k, hk⟩ := r.cyclicAtVertex _ _ hsrc
    have hsame : (dartSplice r.rotation (deletedDart huv hne)).SameCycle
        ((deleteDartEquiv huv hvu hne d).1) ((deleteDartEquiv huv hvu hne e).1) :=
      sameCycle_dartSplice _ _ (deleteDartEquiv huv hvu hne d).2.1
        (deleteDartEquiv huv hvu hne d).2.2 (deleteDartEquiv huv hvu hne e).2.1
        (deleteDartEquiv huv hvu hne e).2.2 ⟨(k : ℤ), by simpa using hk⟩
    obtain ⟨m, hm⟩ := (Equiv.Perm.sameCycle_subtypePerm.mpr hsame).exists_nat_pow_eq
    refine ⟨m, ?_⟩
    rw [pow_conj_apply (deleteDartEquiv huv hvu hne) _ m d, hm, Equiv.symm_apply_apply]

theorem permCycleCount_facePermutation_deleteRotation (huv : c.edge u v = true)
    (hvu : c.edge v u = false) (hne : u ≠ v) (r : OrientableRotation c) :
    permCycleCount (facePermutation (deleteRotation huv hvu hne r))
      = permCycleCount ((dartSplice r.rotation (deletedDart huv hne) * dartReverse c).subtypePerm
          (p := fun x => x ≠ deletedDart huv hne ∧ x ≠ dartReverse c (deletedDart huv hne))
          (fun x => faceSplice_invariant r.rotation (deletedDart huv hne) x)) := by
  have hEq : facePermutation (deleteRotation huv hvu hne r)
      = (deleteDartEquiv huv hvu hne).trans
        (((dartSplice r.rotation (deletedDart huv hne) * dartReverse c).subtypePerm
          (p := fun x => x ≠ deletedDart huv hne ∧ x ≠ dartReverse c (deletedDart huv hne))
          (fun x => faceSplice_invariant r.rotation (deletedDart huv hne) x)).trans
        (deleteDartEquiv huv hvu hne).symm) := by
    apply Equiv.ext
    intro d
    rfl
  rw [hEq, permCycleCount_conj_quot]

theorem card_dart_deleteEdge (huv : c.edge u v = true) (hvu : c.edge v u = false) (hne : u ≠ v) :
    Fintype.card (CircuitDart (deleteEdge c u v)) + 2 = Fintype.card (CircuitDart c) := by
  classical
  set d₀ := deletedDart huv hne with hd0
  set d₁ := dartReverse c d₀ with hd1
  have hd01 : d₀ ≠ d₁ := fun h => dartReverse_ne_self d₀ h.symm
  have h1 : Fintype.card (CircuitDart (deleteEdge c u v))
      = Fintype.card {d : CircuitDart c // d ≠ d₀ ∧ d ≠ d₁} :=
    Fintype.card_congr (deleteDartEquiv huv hvu hne)
  have h2 : (Finset.univ.filter (fun d : CircuitDart c => d ≠ d₀ ∧ d ≠ d₁))
      = Finset.univ \ {d₀, d₁} := by
    ext x
    simp [Finset.mem_sdiff, not_or]
  have h3 : ({d₀, d₁} : Finset (CircuitDart c)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [hd01]), Finset.card_singleton]
  have h4 := Finset.card_sdiff_add_card_eq_card
    (Finset.subset_univ ({d₀, d₁} : Finset (CircuitDart c)))
  rw [h3, Finset.card_univ] at h4
  rw [h1, Fintype.card_subtype, h2]
  omega

/-- An endpoint of the deleted edge becomes isolated exactly when its dart is
fixed by the rotation. -/
theorem rotation_fixed_iff_isolated (huv : c.edge u v = true) (hvu : c.edge v u = false)
    (hne : u ≠ v) (r : OrientableRotation c) (e₀ : CircuitDart c)
    (h0 : e₀ = deletedDart huv hne ∨ e₀ = dartReverse c (deletedDart huv hne)) :
    r.rotation e₀ = e₀ ↔ ∀ w : Fin c.gateCount, ¬ UnderlyingAdj (deleteEdge c u v) e₀.source w := by
  classical
  set d₀ := deletedDart huv hne with hd0
  set d₁ := dartReverse c d₀ with hd1
  have hsrc0 : d₀.source = u := rfl
  have hsrc1 : d₁.source = v := rfl
  have hother : ∀ e : CircuitDart c, (e = d₀ ∨ e = d₁) → e ≠ e₀ → e.source ≠ e₀.source := by
    rintro e (rfl | rfl) hee
    · rcases h0 with rfl | rfl
      · exact absurd rfl hee
      · rw [hsrc0, hsrc1]; exact hne
    · rcases h0 with rfl | rfl
      · rw [hsrc0, hsrc1]; exact fun h => hne h.symm
      · exact absurd rfl hee
  have hnotmem : ∀ e : CircuitDart c, e ≠ d₀ → e ≠ d₁ →
      UnderlyingAdj (deleteEdge c u v) e.1.1 e.1.2 := by
    intro e he0 he1
    refine (adj_deleteEdge_iff c u v hvu e.1.1 e.1.2).mpr ⟨e.2, ?_, ?_⟩
    · intro hc
      exact he0 ((eq_deletedDart_iff huv hne e).mpr hc)
    · intro hc
      exact he1 ((eq_reverse_deletedDart_iff huv hne e).mpr hc)
  constructor
  · intro hfix w hw
    obtain ⟨hadj, hp0, hp1⟩ := (adj_deleteEdge_iff c u v hvu e₀.source w).mp hw
    set e : CircuitDart c := ⟨(e₀.source, w), hadj⟩ with he
    have he0 : e ≠ d₀ := fun hc => hp0 ((eq_deletedDart_iff huv hne e).mp hc)
    have he1 : e ≠ d₁ := fun hc => hp1 ((eq_reverse_deletedDart_iff huv hne e).mp hc)
    obtain ⟨k, hk⟩ := r.cyclicAtVertex e₀ e rfl
    have hpow : ∀ m : Nat, (r.rotation ^ m) e₀ = e₀ := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih =>
          have hval : (r.rotation ^ (m + 1)) e₀ = r.rotation ((r.rotation ^ m) e₀) := by
            rw [pow_succ']; rfl
          rw [hval, ih, hfix]
    rw [hpow k] at hk
    rcases h0 with rfl | rfl
    · exact he0 hk.symm
    · exact he1 hk.symm
  · intro hiso
    by_contra hfix
    have hsrc : (r.rotation e₀).source = e₀.source := r.preservesSource e₀
    have hne0 : r.rotation e₀ ≠ d₀ := by
      intro hc
      rcases h0 with rfl | rfl
      · exact hfix hc
      · exact hother d₀ (Or.inl rfl) (fun h => hfix (by rw [hc, h])) (by rw [← hc, hsrc])
    have hne1 : r.rotation e₀ ≠ d₁ := by
      intro hc
      rcases h0 with rfl | rfl
      · exact hother d₁ (Or.inr rfl) (fun h => hfix (by rw [hc, h])) (by rw [← hc, hsrc])
      · exact hfix hc
    have hadj := hnotmem (r.rotation e₀) hne0 hne1
    exact hiso (r.rotation e₀).1.2 (by rw [← hsrc] at hiso ⊢; exact hadj)

theorem isolatedVertexCount_deleteEdge (huv : c.edge u v = true) (hvu : c.edge v u = false)
    (hne : u ≠ v) :
    isolatedVertexCount (deleteEdge c u v)
      = isolatedVertexCount c
        + (if ∀ w : Fin c.gateCount, ¬ UnderlyingAdj (deleteEdge c u v) u w then 1 else 0)
        + (if ∀ w : Fin c.gateCount, ¬ UnderlyingAdj (deleteEdge c u v) v w then 1 else 0) := by
  classical
  have hsub : (Finset.univ.filter (fun w : Fin c.gateCount => ∀ x, ¬ UnderlyingAdj c w x))
      ⊆ Finset.univ.filter
        (fun w : Fin c.gateCount => ∀ x : Fin c.gateCount,
          ¬ UnderlyingAdj (deleteEdge c u v) w x) := by
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    exact fun x hx => hw x (adj_deleteEdge_of_adj c u v w x hx)
  have hnotQu : ¬ (∀ x, ¬ UnderlyingAdj c u x) := fun h => h v ⟨Or.inl huv, hne⟩
  have hnotQv : ¬ (∀ x, ¬ UnderlyingAdj c v x) := fun h => h u ⟨Or.inr huv, fun hc => hne hc.symm⟩
  have hdiff : (Finset.univ.filter
        (fun w : Fin c.gateCount => ∀ x : Fin c.gateCount, ¬ UnderlyingAdj (deleteEdge c u v) w x))
      \ (Finset.univ.filter (fun w : Fin c.gateCount => ∀ x, ¬ UnderlyingAdj c w x))
      = ({u, v} : Finset (Fin c.gateCount)).filter
        (fun w => ∀ x : Fin c.gateCount, ¬ UnderlyingAdj (deleteEdge c u v) w x) := by
    ext w
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hp, hq⟩
      refine ⟨?_, hp⟩
      by_contra hw
      push_neg at hw
      exact hq (fun x hx => hp x ((adj_deleteEdge_iff c u v hvu w x).mpr
        ⟨hx, fun hc => hw.1 hc.1, fun hc => hw.2 hc.1⟩))
    · rintro ⟨hw, hp⟩
      refine ⟨hp, ?_⟩
      rcases hw with rfl | rfl
      · exact hnotQu
      · exact hnotQv
  have hfilter2 : (({u, v} : Finset (Fin c.gateCount)).filter
        (fun w => ∀ x : Fin c.gateCount, ¬ UnderlyingAdj (deleteEdge c u v) w x)).card
      = (if ∀ w : Fin c.gateCount, ¬ UnderlyingAdj (deleteEdge c u v) u w then 1 else 0)
        + (if ∀ w : Fin c.gateCount, ¬ UnderlyingAdj (deleteEdge c u v) v w then 1 else 0) := by
    by_cases h1 : ∀ w : Fin c.gateCount, ¬ UnderlyingAdj (deleteEdge c u v) u w <;>
      by_cases h2 : ∀ w : Fin c.gateCount, ¬ UnderlyingAdj (deleteEdge c u v) v w <;>
      simp [Finset.filter_insert, Finset.filter_singleton, h1, h2, hne]
  have hcard := Finset.card_sdiff_add_card_eq_card hsub
  rw [hdiff, hfilter2] at hcard
  have hsame : (Finset.univ.filter (fun w : Fin (deleteEdge c u v).gateCount =>
        ∀ x : Fin (deleteEdge c u v).gateCount, ¬ UnderlyingAdj (deleteEdge c u v) w x)).card
      = (Finset.univ.filter (fun w : Fin c.gateCount =>
        ∀ x : Fin c.gateCount, ¬ UnderlyingAdj (deleteEdge c u v) w x)).card := rfl
  unfold isolatedVertexCount
  omega

theorem facePermutation_source (r : OrientableRotation c) (d : CircuitDart c) :
    (facePermutation r d).source = d.target := by
  change (r.rotation (dartReverse c d)).source = d.target
  rw [r.preservesSource]
  rfl

theorem reach_of_reach_deleteEdge {a b : Fin c.gateCount}
    (h : VertexReachable (deleteEdge c u v) a b) : VertexReachable c a b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hyz ih => exact ih.tail (adj_deleteEdge_of_adj c u v _ _ hyz)

theorem reach_deleteEdge_of_adj (hvu : c.edge v u = false)
    (hr : VertexReachable (deleteEdge c u v) u v) (y z : Fin c.gateCount)
    (hyz : UnderlyingAdj c y z) : VertexReachable (deleteEdge c u v) y z := by
  by_cases hd : UnderlyingAdj (deleteEdge c u v) y z
  · exact Relation.ReflTransGen.single hd
  · have hcases : (y = u ∧ z = v) ∨ (y = v ∧ z = u) := by
      by_contra hcon
      push_neg at hcon
      exact hd ((adj_deleteEdge_iff c u v hvu y z).mpr
        ⟨hyz, fun hc => (hcon.1 hc.1) hc.2, fun hc => (hcon.2 hc.1) hc.2⟩)
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hr
    · exact (vertexReachable_equiv _).symm hr

theorem componentCount_deleteEdge_of_reach (hvu : c.edge v u = false)
    (hr : VertexReachable (deleteEdge c u v) u v) :
    componentCount (deleteEdge c u v) = componentCount c := by
  have hiff : ∀ a b : Fin c.gateCount,
      VertexReachable (deleteEdge c u v) a b ↔ VertexReachable c a b := by
    intro a b
    refine ⟨reach_of_reach_deleteEdge, fun h => ?_⟩
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hyz ih => exact ih.trans (reach_deleteEdge_of_adj hvu hr _ _ hyz)
  unfold componentCount
  congr 1
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact forall_congr' (fun x => imp_congr_left (hiff w x))

theorem componentCount_deleteEdge_of_not_reach (huv : c.edge u v = true)
    (hvu : c.edge v u = false) (hne : u ≠ v)
    (hr : ¬ VertexReachable (deleteEdge c u v) u v) :
    componentCount (deleteEdge c u v) = componentCount c + 1 := by
  classical
  have hequiv := vertexReachable_equiv (deleteEdge c u v)
  have hstep : ∀ y z : Fin c.gateCount, UnderlyingAdj c y z →
      MergeRel (VertexReachable (deleteEdge c u v)) u v y z := by
    intro y z hyz
    by_cases hd : UnderlyingAdj (deleteEdge c u v) y z
    · exact Or.inl (Relation.ReflTransGen.single hd)
    · have hcases : (y = u ∧ z = v) ∨ (y = v ∧ z = u) := by
        by_contra hcon
        push_neg at hcon
        exact hd ((adj_deleteEdge_iff c u v hvu y z).mpr
          ⟨hyz, fun hc => (hcon.1 hc.1) hc.2, fun hc => (hcon.2 hc.1) hc.2⟩)
      rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr (Or.inl ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩)
      · exact Or.inr (Or.inr ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩)
  have hmerge : ∀ a b : Fin c.gateCount,
      VertexReachable c a b ↔ MergeRel (VertexReachable (deleteEdge c u v)) u v a b := by
    intro a b
    constructor
    · intro h
      induction h with
      | refl => exact Or.inl Relation.ReflTransGen.refl
      | tail _ hyz ih =>
          exact (mergeRel_equivalence hequiv hr).trans ih (hstep _ _ hyz)
    · have huvreach : VertexReachable c u v :=
        Relation.ReflTransGen.single ⟨Or.inl huv, hne⟩
      rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact reach_of_reach_deleteEdge h
      · exact ((reach_of_reach_deleteEdge h1).trans huvreach).trans
          ((vertexReachable_equiv c).symm (reach_of_reach_deleteEdge h2))
      · exact ((reach_of_reach_deleteEdge h1).trans ((vertexReachable_equiv c).symm huvreach)).trans
          ((vertexReachable_equiv c).symm (reach_of_reach_deleteEdge h2))
  have hcongr : Nat.card (Quot (VertexReachable c))
      = Nat.card (Quot (MergeRel (VertexReachable (deleteEdge c u v)) u v)) :=
    natCard_quot_congr (Equiv.refl (Fin c.gateCount)) (fun a b => hmerge a b)
  have hcount := natCard_quot_merge hequiv hr
  rw [componentCount_eq_natCard_quot, componentCount_eq_natCard_quot]
  omega

/-- If the deleted edge is a bridge, its two darts lie on a common face. -/
theorem sameCycle_of_not_reach (huv : c.edge u v = true) (hvu : c.edge v u = false)
    (hne : u ≠ v) (r : OrientableRotation c)
    (hr : ¬ VertexReachable (deleteEdge c u v) u v) :
    (facePermutation r).SameCycle (deletedDart huv hne)
      (dartReverse c (deletedDart huv hne)) := by
  classical
  set d₀ := deletedDart huv hne with hd0
  set d₁ := dartReverse c d₀ with hd1
  set fp := facePermutation r with hfp
  by_contra hsc
  have hexists : ∃ k : Nat, 0 < k ∧ (fp ^ k) d₀ = d₀ := by
    refine ⟨orderOf fp, orderOf_pos fp, ?_⟩
    rw [pow_orderOf_eq_one]
    rfl
  set m := Nat.find hexists with hm
  obtain ⟨hmpos, hmfix⟩ := Nat.find_spec hexists
  have hnotd1 : ∀ k : Nat, (fp ^ k) d₀ ≠ d₁ := by
    intro k hk
    exact hsc ⟨(k : ℤ), by simpa using hk⟩
  have hkey : ∀ k : Nat, 1 ≤ k → k ≤ m →
      VertexReachable (deleteEdge c u v) v ((fp ^ k) d₀).source := by
    intro k
    induction k with
    | zero => intro h; exact absurd h (by omega)
    | succ k ih =>
        intro _ hkm
        rcases Nat.eq_zero_or_pos k with rfl | hkpos
        · have : (fp ^ 1) d₀ = fp d₀ := by rw [pow_one]
          rw [this, facePermutation_source]
          exact Relation.ReflTransGen.refl
        · have hIH := ih hkpos (by omega)
          have hne0 : (fp ^ k) d₀ ≠ d₀ := by
            intro hcon
            exact absurd (Nat.find_min hexists (m := k) (by omega) ⟨hkpos, hcon⟩) (by simp)
          have hadj : UnderlyingAdj (deleteEdge c u v) ((fp ^ k) d₀).source
              ((fp ^ k) d₀).target := by
            refine (adj_deleteEdge_iff c u v hvu _ _).mpr ⟨((fp ^ k) d₀).2, ?_, ?_⟩
            · intro hc
              exact hne0 ((eq_deletedDart_iff huv hne _).mpr hc)
            · intro hc
              exact hnotd1 k ((eq_reverse_deletedDart_iff huv hne _).mpr hc)
          have hval : (fp ^ (k + 1)) d₀ = fp ((fp ^ k) d₀) := by
            rw [pow_succ']; rfl
          rw [hval, facePermutation_source]
          exact hIH.tail hadj
  have hfinal := hkey m hmpos le_rfl
  rw [hmfix] at hfinal
  exact hr ((vertexReachable_equiv (deleteEdge c u v)).symm hfinal)

/-- Deleting an edge that really is present never increases the genus. -/
theorem genus_deleteEdge_le_of_present (huv : c.edge u v = true) (hvu : c.edge v u = false)
    (hne : u ≠ v) :
    orientableCircuitGenus (deleteEdge c u v) ≤ orientableCircuitGenus c := by
  classical
  obtain ⟨r, hr⟩ := exists_rotation_genus_eq c
  have hsplit := permCycleCount_faceSplice_split r.rotation (deletedDart huv hne)
  have hface := permCycleCount_faceSplice r (deletedDart huv hne)
  have hfaceNew := permCycleCount_facePermutation_deleteRotation huv hvu hne r
  have hiso := isolatedVertexCount_deleteEdge huv hvu hne
  have hcard := card_dart_deleteEdge huv hvu hne
  have hE1 := two_mul_underlyingEdgeCount (deleteEdge c u v)
  have hE2 := two_mul_underlyingEdgeCount c
  have hgate : (deleteEdge c u v).gateCount = c.gateCount := rfl
  -- the two `if`s of the face count are the two new isolated vertices
  have hu : ((facePermutation r)⁻¹ (deletedDart huv hne)
        = dartReverse c (deletedDart huv hne))
      ↔ (∀ w : Fin c.gateCount, ¬ UnderlyingAdj (deleteEdge c u v) u w) := by
    refine Iff.trans ?_
      (rotation_fixed_iff_isolated huv hvu hne r (deletedDart huv hne) (Or.inl rfl))
    rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq]
    constructor
    · intro h
      have h2 : facePermutation r (dartReverse c (deletedDart huv hne))
          = r.rotation (deletedDart huv hne) := by
        change r.rotation (dartReverse c (dartReverse c (deletedDart huv hne)))
          = r.rotation (deletedDart huv hne)
        rw [dartReverse_reverse]
      rw [h2] at h
      exact h.symm
    · intro h
      have h2 : facePermutation r (dartReverse c (deletedDart huv hne))
          = r.rotation (deletedDart huv hne) := by
        change r.rotation (dartReverse c (dartReverse c (deletedDart huv hne)))
          = r.rotation (deletedDart huv hne)
        rw [dartReverse_reverse]
      rw [h2, h]
  have hv : ((facePermutation r)⁻¹ (dartReverse c (deletedDart huv hne))
        = deletedDart huv hne)
      ↔ (∀ w : Fin c.gateCount, ¬ UnderlyingAdj (deleteEdge c u v) v w) := by
    refine Iff.trans ?_ (rotation_fixed_iff_isolated huv hvu hne r
      (dartReverse c (deletedDart huv hne)) (Or.inr rfl))
    rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq]
    have h2 : facePermutation r (deletedDart huv hne)
        = r.rotation (dartReverse c (deletedDart huv hne)) := rfl
    rw [h2]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  simp only [hu, hv] at hface
  have hgenus : rotationGenus (deleteRotation huv hvu hne r) ≤ rotationGenus r := by
    simp only [rotationGenus]
    by_cases hreach : VertexReachable (deleteEdge c u v) u v
    · have hC := componentCount_deleteEdge_of_reach hvu hreach
      by_cases hsc : (facePermutation r).SameCycle (deletedDart huv hne)
          (dartReverse c (deletedDart huv hne))
      · rw [if_pos hsc] at hface
        omega
      · rw [if_neg hsc] at hface
        omega
    · have hC := componentCount_deleteEdge_of_not_reach huv hvu hne hreach
      have hsc := sameCycle_of_not_reach huv hvu hne r hreach
      rw [if_pos hsc] at hface
      omega
  calc orientableCircuitGenus (deleteEdge c u v)
      ≤ rotationGenus (deleteRotation huv hvu hne r) :=
        Nat.sInf_le ⟨deleteRotation huv hvu hne r, rfl⟩
    _ ≤ rotationGenus r := hgenus
    _ = orientableCircuitGenus c := hr

end RealDeletion

end AllenderOQ3.Internal
