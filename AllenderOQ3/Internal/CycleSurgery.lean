import AllenderOQ3.Internal.CountInvariance

/-!
# Cycle surgery for permutations

The genus of an embedded graph changes in a controlled way when an edge is
deleted, because the face permutation changes by multiplication with a
transposition.  This file collects the required permutation combinatorics.
-/

set_option autoImplicit false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace AllenderOQ3.Internal

open Equiv Equiv.Perm

/-- The relation obtained from `S` by merging the classes of `a` and `b`. -/
def MergeRel {α : Type} (S : α → α → Prop) (a b : α) (x y : α) : Prop :=
  S x y ∨ (S x a ∧ S y b) ∨ (S x b ∧ S y a)

theorem mergeRel_equivalence {α : Type} {S : α → α → Prop} (hS : Equivalence S)
    {a b : α} (hab : ¬ S a b) : Equivalence (MergeRel S a b) := by
  have hba : ¬ S b a := fun h => hab (hS.symm h)
  refine ⟨fun x => Or.inl (hS.refl x), ?_, ?_⟩
  · rintro x y (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl (hS.symm h)
    · exact Or.inr (Or.inr ⟨h2, h1⟩)
    · exact Or.inr (Or.inl ⟨h2, h1⟩)
  · rintro x y z (hxy | ⟨hx, hy⟩ | ⟨hx, hy⟩) (hyz | ⟨hy', hz⟩ | ⟨hy', hz⟩)
    · exact Or.inl (hS.trans hxy hyz)
    · exact Or.inr (Or.inl ⟨hS.trans hxy hy', hz⟩)
    · exact Or.inr (Or.inr ⟨hS.trans hxy hy', hz⟩)
    · exact Or.inr (Or.inl ⟨hx, hS.trans (hS.symm hyz) hy⟩)
    · exact absurd (hS.trans (hS.symm hy) hy') (fun h => hba h)
    · exact Or.inl (hS.trans hx (hS.symm hz))
    · exact Or.inr (Or.inr ⟨hx, hS.trans (hS.symm hyz) hy⟩)
    · exact Or.inl (hS.trans hx (hS.symm hz))
    · exact absurd (hS.trans (hS.symm hy) hy') (fun h => hab h)

/-- Merging the two distinct `S`-classes of `a` and `b` drops the number of
classes by exactly one. -/
theorem natCard_quot_merge {α : Type} [Finite α] {S : α → α → Prop} (hS : Equivalence S)
    {a b : α} (hab : ¬ S a b) :
    Nat.card (Quot (MergeRel S a b)) + 1 = Nat.card (Quot S) := by
  classical
  have hR := mergeRel_equivalence hS hab
  set R := MergeRel S a b with hRdef
  set psi : Quot S → Quot R :=
    Quot.lift (fun x => Quot.mk R x) (fun x y h => Quot.sound (Or.inl h)) with hpsi
  have hbij : Function.Bijective (fun z : {z : Quot S // z ≠ Quot.mk S b} => psi z.1) := by
    constructor
    · rintro ⟨z, hz⟩ ⟨z', hz'⟩ heq
      induction z using Quot.ind with
      | _ x =>
        induction z' using Quot.ind with
        | _ y =>
          have hxy : R x y := (hR.eqvGen_iff).mp (Quot.eq.mp heq)
          have hsxy : S x y := by
            rcases hxy with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact h
            · exact absurd (Quot.sound h2) hz'
            · exact absurd (Quot.sound h1) hz
          exact Subtype.ext (Quot.sound hsxy)
    · intro w
      induction w using Quot.ind with
      | _ x =>
        by_cases hx : Quot.mk S x = Quot.mk S b
        · have hsx : S x b := (hS.eqvGen_iff).mp (Quot.eq.mp hx)
          refine ⟨⟨Quot.mk S a, fun hcon => hab ((hS.eqvGen_iff).mp (Quot.eq.mp hcon))⟩, ?_⟩
          exact Quot.sound (Or.inr (Or.inl ⟨hS.refl a, hsx⟩))
        · exact ⟨⟨Quot.mk S x, hx⟩, rfl⟩
  have h1 : Nat.card {z : Quot S // z ≠ Quot.mk S b} = Nat.card (Quot R) :=
    Nat.card_eq_of_bijective _ hbij
  have h2 : Nat.card (Quot S) = Nat.card {z : Quot S // z ≠ Quot.mk S b} + 1 := by
    rw [← Nat.card_congr (Equiv.optionSubtypeNe (Quot.mk S b)), Finite.card_option]
  omega


/-- `permCycleCount` counts the cycles, i.e. the `SameCycle` classes. -/
theorem permCycleCount_eq_natCard_quot_sameCycle {α : Type} [Fintype α] [DecidableEq α]
    (p : Perm α) : permCycleCount p = Nat.card (Quot p.SameCycle) := by
  rw [permCycleCount_eq_natCard_quot]
  refine natCard_quot_congr (Equiv.refl α) ?_
  intro x y
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨(k : ℤ), by simpa using hk⟩
  · intro h
    exact h.exists_nat_pow_eq

/-- If `a` and `b` lie in different cycles of `p`, then they lie in the same
cycle of `p * swap a b`. -/
theorem sameCycle_mul_swap_of_not_sameCycle {α : Type} [Fintype α] [DecidableEq α]
    {p : Perm α} {a b : α} (h : ¬ p.SameCycle a b) :
    (p * Equiv.swap a b).SameCycle a b := by
  classical
  set q := p * Equiv.swap a b with hq
  have hab : a ≠ b := fun hcon => h (hcon ▸ SameCycle.rfl)
  have hqa : q a = p b := by simp [hq]
  have hqb : q b = p a := by simp [hq]
  have hexists : ∃ k : Nat, 0 < k ∧ (p ^ k) b = b := by
    refine ⟨orderOf p, orderOf_pos p, ?_⟩
    rw [pow_orderOf_eq_one]
    rfl
  classical
  set k := Nat.find hexists with hk
  obtain ⟨hkpos, hkb⟩ := Nat.find_spec hexists
  have hstep : ∀ i : Nat, 1 ≤ i → i ≤ k → (q ^ i) a = (p ^ i) b := by
    intro i
    induction i with
    | zero => intro h1; exact absurd h1 (by omega)
    | succ i ih =>
        intro _ hik
        rcases Nat.eq_zero_or_pos i with hi | hi
        · subst hi
          simp [pow_one, hqa]
        · have hIH := ih hi (by omega)
          have hne_b : (p ^ i) b ≠ b := by
            intro hcon
            exact absurd (Nat.find_min hexists (m := i) (by omega) ⟨hi, hcon⟩) (by simp)
          have hne_a : (p ^ i) b ≠ a := by
            intro hcon
            exact h (SameCycle.symm ⟨(i : ℤ), by simpa using hcon⟩)
          rw [pow_succ' q i, Equiv.Perm.mul_apply, hIH, hq, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne hne_a hne_b, ← Equiv.Perm.mul_apply, ← pow_succ' p i]
  exact ⟨(k : ℤ), by rw [zpow_natCast, hstep k hkpos le_rfl, hkb]⟩

/-- One step of the new permutation stays inside the merged relation. -/
theorem sameCycle_mul_swap_step {α : Type} [Fintype α] [DecidableEq α]
    (p : Perm α) (a b : α) (x : α) :
    MergeRel p.SameCycle a b x ((p * Equiv.swap a b) x) := by
  classical
  rcases eq_or_ne x a with rfl | hxa
  · have hval : (p * Equiv.swap x b) x = p b := by simp
    rw [hval]
    exact Or.inr (Or.inl ⟨SameCycle.rfl, sameCycle_apply_left.mpr SameCycle.rfl⟩)
  · rcases eq_or_ne x b with rfl | hxb
    · have hval : (p * Equiv.swap a x) x = p a := by simp
      rw [hval]
      exact Or.inr (Or.inr ⟨SameCycle.rfl, sameCycle_apply_left.mpr SameCycle.rfl⟩)
    · have hval : (p * Equiv.swap a b) x = p x := by
        simp [Equiv.swap_apply_of_ne_of_ne hxa hxb]
      rw [hval]
      exact Or.inl (sameCycle_apply_right.mpr SameCycle.rfl)

/-- Multiplying by a transposition joining two different cycles merges them. -/
theorem sameCycle_mul_swap_iff_merge {α : Type} [Fintype α] [DecidableEq α]
    {p : Perm α} {a b : α} (h : ¬ p.SameCycle a b) (x y : α) :
    (p * Equiv.swap a b).SameCycle x y ↔ MergeRel p.SameCycle a b x y := by
  classical
  set q := p * Equiv.swap a b with hq
  have hR := mergeRel_equivalence (SameCycle.equivalence p) h
  have hqab : q.SameCycle a b := sameCycle_mul_swap_of_not_sameCycle h
  have hfwd : ∀ (k : Nat) (z : α), MergeRel p.SameCycle a b z ((q ^ k) z) := by
    intro k
    induction k with
    | zero => intro z; exact hR.refl z
    | succ k ih =>
        intro z
        have hval : (q ^ (k + 1)) z = (q ^ k) (q z) := by
          rw [pow_succ]; rfl
        rw [hval]
        exact hR.trans (sameCycle_mul_swap_step p a b z) (ih (q z))
  have hstepQ : ∀ z : α, q.SameCycle z (p z) := by
    intro z
    rcases eq_or_ne z a with rfl | hza
    · have hval : p z = q b := by simp [hq]
      rw [hval]
      exact sameCycle_apply_right.mpr hqab
    · rcases eq_or_ne z b with rfl | hzb
      · have hval : p z = q a := by simp [hq]
        rw [hval]
        exact sameCycle_apply_right.mpr hqab.symm
      · have hval : p z = q z := by
          simp [hq, Equiv.swap_apply_of_ne_of_ne hza hzb]
        rw [hval]
        exact sameCycle_apply_right.mpr SameCycle.rfl
  have hmono : ∀ z w : α, p.SameCycle z w → q.SameCycle z w := by
    have haux : ∀ (j : Nat) (t : α), q.SameCycle t ((p ^ j) t) := by
      intro j
      induction j with
      | zero => intro t; exact SameCycle.rfl
      | succ j ih =>
          intro t
          have hval : (p ^ (j + 1)) t = (p ^ j) (p t) := by
            rw [pow_succ]; rfl
          rw [hval]
          exact (hstepQ t).trans (ih (p t))
    intro z w hzw
    obtain ⟨k, hk⟩ := hzw.exists_nat_pow_eq
    rw [← hk]
    exact haux k z
  constructor
  · intro hxy
    obtain ⟨k, hk⟩ := hxy.exists_nat_pow_eq
    rw [← hk]
    exact hfwd k x
  · rintro (hxy | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact hmono _ _ hxy
    · exact ((hmono _ _ h1).trans hqab).trans (hmono _ _ h2).symm
    · exact ((hmono _ _ h1).trans hqab.symm).trans (hmono _ _ h2).symm

/-- Multiplying by a transposition joining two different cycles decreases the
number of cycles by one. -/
theorem permCycleCount_mul_swap_of_not_sameCycle {α : Type} [Fintype α] [DecidableEq α]
    {p : Perm α} {a b : α} (h : ¬ p.SameCycle a b) :
    permCycleCount (p * Equiv.swap a b) + 1 = permCycleCount p := by
  rw [permCycleCount_eq_natCard_quot_sameCycle, permCycleCount_eq_natCard_quot_sameCycle]
  have hcongr : Nat.card (Quot (p * Equiv.swap a b).SameCycle)
      = Nat.card (Quot (MergeRel p.SameCycle a b)) :=
    natCard_quot_congr (Equiv.refl α) (fun x y => sameCycle_mul_swap_iff_merge h x y)
  rw [hcongr]
  exact natCard_quot_merge (SameCycle.equivalence p) h


/-- If `a` and `b` lie in the same cycle of `p`, they lie in different cycles
of `p * swap a b`. -/
theorem not_sameCycle_mul_swap_of_sameCycle {α : Type} [Fintype α] [DecidableEq α]
    {p : Perm α} {a b : α} (hab : a ≠ b) (h : p.SameCycle a b) :
    ¬ (p * Equiv.swap a b).SameCycle a b := by
  classical
  set q := p * Equiv.swap a b with hq
  have hexists : ∃ k : Nat, 0 < k ∧ (p ^ k) a = b := by
    obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
    refine ⟨k, ?_, hk⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp at hk
      exact absurd hk.symm hab.symm
    · exact hk0
  set k := Nat.find hexists with hkdef
  obtain ⟨hkpos, hkb⟩ := Nat.find_spec hexists
  have hkey : ∀ i : Nat, 1 ≤ i → i < k → (p ^ i) a ≠ a ∧ (p ^ i) a ≠ b := by
    intro i hi hik
    constructor
    · intro hcon
      have hsplit : (p ^ k) a = (p ^ (k - i)) ((p ^ i) a) := by
        rw [← Equiv.Perm.mul_apply, ← pow_add]
        congr 2
        omega
      rw [hcon] at hsplit
      exact absurd (Nat.find_min hexists (m := k - i) (by omega) ⟨by omega, by rw [← hsplit, hkb]⟩)
        (by simp)
    · intro hcon
      exact absurd (Nat.find_min hexists (m := i) hik ⟨hi, hcon⟩) (by simp)
  have hstep : ∀ i : Nat, 1 ≤ i → i ≤ k → (q ^ i) b = (p ^ i) a := by
    intro i
    induction i with
    | zero => intro h1; exact absurd h1 (by omega)
    | succ i ih =>
        intro _ hik
        rcases Nat.eq_zero_or_pos i with rfl | hi
        · simp [hq]
        · have hIH := ih hi (by omega)
          obtain ⟨hne_a, hne_b⟩ := hkey i hi (by omega)
          rw [pow_succ' q i, Equiv.Perm.mul_apply, hIH, hq, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne hne_a hne_b, ← Equiv.Perm.mul_apply, ← pow_succ' p i]
  have hper : (q ^ k) b = b := by rw [hstep k hkpos le_rfl, hkb]
  have hcycle : ∀ (t s : Nat), (q ^ (k * t + s)) b = (q ^ s) b := by
    intro t
    induction t with
    | zero => intro s; simp
    | succ t ih =>
        intro s
        have harith : k * (t + 1) + s = k * t + s + k := by ring
        rw [harith, pow_add, Equiv.Perm.mul_apply, hper, ih]
  intro hcon
  obtain ⟨j, hj⟩ := hcon.symm.exists_nat_pow_eq
  have hjd : j = k * (j / k) + j % k := (Nat.div_add_mod j k).symm
  have hja : (q ^ (j % k)) b = a := by
    rw [← hcycle (j / k) (j % k)]
    rw [← hjd]
    exact hj
  rcases Nat.eq_zero_or_pos (j % k) with hz | hpos
  · rw [hz] at hja
    simp at hja
    exact hab hja.symm
  · have hlt : j % k < k := Nat.mod_lt _ hkpos
    rw [hstep (j % k) hpos (le_of_lt hlt)] at hja
    exact (hkey (j % k) hpos hlt).1 hja

/-- Multiplying by a transposition joining two points of one cycle splits it. -/
theorem permCycleCount_mul_swap_of_sameCycle {α : Type} [Fintype α] [DecidableEq α]
    {p : Perm α} {a b : α} (hab : a ≠ b) (h : p.SameCycle a b) :
    permCycleCount (p * Equiv.swap a b) = permCycleCount p + 1 := by
  have h2 := permCycleCount_mul_swap_of_not_sameCycle
    (not_sameCycle_mul_swap_of_sameCycle hab h)
  rw [mul_assoc, Equiv.swap_mul_self, mul_one] at h2
  omega


/-- Cycles do not cross an invariant subset. -/
theorem sameCycle_iff_of_invariant {D : Type} [Fintype D] [DecidableEq D] (P : Perm D)
    (S : D → Prop) (h : ∀ x, S (P x) ↔ S x) {x y : D} (hxy : P.SameCycle x y) :
    (S x ↔ S y) := by
  obtain ⟨k, hk⟩ := hxy.exists_nat_pow_eq
  subst hk
  clear hxy
  induction k with
  | zero => simp
  | succ k ih =>
      have hval : (P ^ (k + 1)) x = P ((P ^ k) x) := by
        rw [pow_succ']; rfl
      rw [hval, h]
      exact ih

/-- The cycle count is additive over an invariant subset and its complement. -/
theorem permCycleCount_split {D : Type} [Fintype D] [DecidableEq D] (P : Perm D)
    (S : D → Prop) [DecidablePred S] (h : ∀ x, S (P x) ↔ S x) :
    permCycleCount P
      = permCycleCount (P.subtypePerm h)
        + permCycleCount (P.subtypePerm (p := fun x => ¬ S x) (fun x => not_congr (h x))) := by
  classical
  rw [permCycleCount_eq_natCard_quot_sameCycle, permCycleCount_eq_natCard_quot_sameCycle,
    permCycleCount_eq_natCard_quot_sameCycle]
  set G : Quot (P.subtypePerm h).SameCycle ⊕ Quot (P.subtypePerm (p := fun x => ¬ S x) (fun x => not_congr (h x))).SameCycle
      → Quot P.SameCycle :=
    Sum.elim
      (Quot.lift (fun x : {x // S x} => Quot.mk P.SameCycle x.1)
        (fun x y hxy => Quot.sound (sameCycle_subtypePerm.mp hxy)))
      (Quot.lift (fun x : {x // ¬ S x} => Quot.mk P.SameCycle x.1)
        (fun x y hxy => Quot.sound (sameCycle_subtypePerm.mp hxy))) with hG
  have hbij : Function.Bijective G := by
    constructor
    · rintro (q | q) (q' | q') heq
      · revert heq
        induction q using Quot.ind with
        | _ x =>
          induction q' using Quot.ind with
          | _ y =>
            intro heq
            have hxy : P.SameCycle x.1 y.1 :=
              ((SameCycle.equivalence P).eqvGen_iff).mp (Quot.eq.mp heq)
            exact congrArg Sum.inl (Quot.sound (sameCycle_subtypePerm.mpr hxy))
      · revert heq
        induction q using Quot.ind with
        | _ x =>
          induction q' using Quot.ind with
          | _ y =>
            intro heq
            have hxy : P.SameCycle x.1 y.1 :=
              ((SameCycle.equivalence P).eqvGen_iff).mp (Quot.eq.mp heq)
            exact absurd ((sameCycle_iff_of_invariant P S h hxy).mp x.2) y.2
      · revert heq
        induction q using Quot.ind with
        | _ x =>
          induction q' using Quot.ind with
          | _ y =>
            intro heq
            have hxy : P.SameCycle x.1 y.1 :=
              ((SameCycle.equivalence P).eqvGen_iff).mp (Quot.eq.mp heq)
            exact absurd ((sameCycle_iff_of_invariant P S h hxy).mpr y.2) x.2
      · revert heq
        induction q using Quot.ind with
        | _ x =>
          induction q' using Quot.ind with
          | _ y =>
            intro heq
            have hxy : P.SameCycle x.1 y.1 :=
              ((SameCycle.equivalence P).eqvGen_iff).mp (Quot.eq.mp heq)
            exact congrArg Sum.inr (Quot.sound (sameCycle_subtypePerm.mpr hxy))
    · intro w
      induction w using Quot.ind with
      | _ x =>
        by_cases hx : S x
        · exact ⟨Sum.inl (Quot.mk _ ⟨x, hx⟩), rfl⟩
        · exact ⟨Sum.inr (Quot.mk _ ⟨x, hx⟩), rfl⟩
  rw [← Nat.card_eq_of_bijective G hbij, Nat.card_sum]

/-- A permutation all of whose points are in one cycle has cycle count one. -/
theorem permCycleCount_eq_one {D : Type} [Fintype D] [DecidableEq D] [Nonempty D] (P : Perm D)
    (h : ∀ x y : D, P.SameCycle x y) : permCycleCount P = 1 := by
  rw [permCycleCount_eq_natCard_quot_sameCycle]
  refine Nat.card_eq_one_iff_unique.mpr ⟨⟨?_⟩, ?_⟩
  · intro z z'
    induction z using Quot.ind with
    | _ x =>
      induction z' using Quot.ind with
      | _ y => exact Quot.sound (h x y)
  · exact ⟨Quot.mk _ (Classical.arbitrary D)⟩

end AllenderOQ3.Internal
