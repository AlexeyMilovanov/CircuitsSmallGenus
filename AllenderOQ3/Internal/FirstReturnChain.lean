import AllenderOQ3.Internal.MinCorner
import AllenderOQ3.Internal.CutNecklace
import AllenderOQ3.Internal.FaceUnimodal

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# The first-return chain of a cut

Two foundations for the involutivity of `firstReturn` at genus zero:

* `cut_mem_firstReturn_chain` — every cut dart on the face walk from a cut
  dart `x` is reached by iterating `firstReturn` from `x`: the first-return
  chain exhausts the cut darts of the face orbit, in walk order.
* `exists_minCorner_on_descent` / `exists_maxCorner_on_ascent` — between a
  downward (upward) crossing and its first return the walk passes a min
  (max) corner.  Together with the uniqueness of corners per face
  (`FaceUnimodal`), this pins the number of crossings of each face at two,
  which is the involutivity of `firstReturn`.
-/

namespace AllenderOQ3.Internal

variable {n : Nat} {c : ADRCircuit n}

/-- Under proper layering, a dart raising the layer is ascending. -/
theorem dartIsUp_of_layer (hpl : ProperLayered c) (d : CircuitDart c)
    (h : c.layer d.target = c.layer d.source + 1) : dartIsUp d = true := by
  cases hup : dartIsUp d
  · have := layer_of_not_dartIsUp hpl d hup
    omega
  · rfl

/-- Under proper layering, a dart lowering the layer is descending. -/
theorem dartIsUp_eq_false_of_layer (hpl : ProperLayered c) (d : CircuitDart c)
    (h : c.layer d.source = c.layer d.target + 1) : dartIsUp d = false := by
  cases hup : dartIsUp d
  · rfl
  · have := layer_of_dartIsUp hpl d hup
    omega

/-- A downward cut dart is descending. -/
theorem down_of_cutDart (hpl : ProperLayered c) {ell : Nat} (y : CutDart c ell)
    (hdown : c.layer y.1.source = ell + 1) : dartIsUp y.1 = false := by
  have hcut : min (c.layer y.1.source) (c.layer y.1.target) = ell := by
    have h := y.2
    rwa [isCutDart, beq_iff_eq] at h
  refine dartIsUp_eq_false_of_layer hpl y.1 ?_
  rcases dart_layer_cases hpl y.1 with h | h
  · omega
  · omega

/-- An upward cut dart is ascending. -/
theorem up_of_cutDart (hpl : ProperLayered c) {ell : Nat} (y : CutDart c ell)
    (hup : c.layer y.1.source = ell) : dartIsUp y.1 = true := by
  have hcut : min (c.layer y.1.source) (c.layer y.1.target) = ell := by
    have h := y.2
    rwa [isCutDart, beq_iff_eq] at h
  refine dartIsUp_of_layer hpl y.1 ?_
  rcases dart_layer_cases hpl y.1 with h | h
  · omega
  · omega

/-- Every cut dart on the face walk from a cut dart is reached by iterating
the first-return map. -/
theorem cut_mem_firstReturn_chain (r : OrientableRotation c) (ell : Nat) :
    ∀ m : Nat, 1 ≤ m → ∀ x : CutDart c ell,
      ∀ hc : isCutDart c ell ((facePermutation r ^ m) x.1) = true,
        ∃ s : Nat, ((firstReturn r ell) ^ s) x
          = ⟨(facePermutation r ^ m) x.1, hc⟩ := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm x hc
    have hT_le : firstReturnTime (facePermutation r)
        (fun d => isCutDart c ell d = true) x ≤ m :=
      Nat.find_min' (exists_firstReturn (facePermutation r) _ x) ⟨hm, hc⟩
    set T := firstReturnTime (facePermutation r)
      (fun d => isCutDart c ell d = true) x with hTdef
    have hT1 : 1 ≤ T := firstReturnTime_pos _ _ x
    rcases Nat.eq_or_lt_of_le hT_le with heq | hlt
    · refine ⟨1, ?_⟩
      rw [pow_one]
      apply Subtype.ext
      rw [firstReturn_val]
      rw [← hTdef, heq]
    · have harith : m - T + T = m := by omega
      have hsplit : (facePermutation r ^ m) x.1
          = (facePermutation r ^ (m - T)) (((firstReturn r ell) x).1) := by
        rw [firstReturn_val, ← hTdef, ← Equiv.Perm.mul_apply, ← pow_add, harith]
      have hc' : isCutDart c ell
          ((facePermutation r ^ (m - T)) (((firstReturn r ell) x).1)) = true := by
        rw [← hsplit]
        exact hc
      obtain ⟨s, hs⟩ := ih (m - T) (by omega) (by omega) ((firstReturn r ell) x) hc'
      refine ⟨s + 1, ?_⟩
      rw [pow_succ, Equiv.Perm.mul_apply, hs]
      apply Subtype.ext
      exact hsplit.symm

/-- Between a downward crossing and its first return, the walk passes a
descending-to-ascending switch (a min corner of the face). -/
theorem exists_switch_on_descent (hpl : ProperLayered c)
    (r : OrientableRotation c) {ell : Nat} (y : CutDart c ell)
    (hdown : c.layer y.1.source = ell + 1) :
    ∃ j : Nat,
      j + 1 ≤ firstReturnTime (facePermutation r)
        (fun d => isCutDart c ell d = true) y ∧
      dartIsUp ((facePermutation r ^ j) y.1) = false ∧
      dartIsUp ((facePermutation r ^ (j + 1)) y.1) = true := by
  set T := firstReturnTime (facePermutation r)
    (fun d => isCutDart c ell d = true) y with hTdef
  have hT1 : 1 ≤ T := firstReturnTime_pos _ _ y
  have hret := firstReturn_up hpl r y hdown
  have hretval : ((firstReturn r ell) y).1 = (facePermutation r ^ T) y.1 :=
    firstReturn_val r ell y
  rw [hretval] at hret
  have hTup : dartIsUp ((facePermutation r ^ T) y.1) = true := by
    refine dartIsUp_of_layer hpl _ ?_
    omega
  have hex : ∃ j : Nat, dartIsUp ((facePermutation r ^ j) y.1) = true := ⟨T, hTup⟩
  classical
  set j0 := Nat.find hex with hj0def
  have hj0_spec : dartIsUp ((facePermutation r ^ j0) y.1) = true := Nat.find_spec hex
  have hj0_le : j0 ≤ T := Nat.find_min' hex hTup
  have hy_down : dartIsUp y.1 = false := down_of_cutDart hpl y hdown
  have hj0_pos : 1 ≤ j0 := by
    rcases Nat.eq_zero_or_pos j0 with h0 | h1
    · exfalso
      have h := hj0_spec
      rw [h0, pow_zero] at h
      have hyy : ((1 : Equiv.Perm (CircuitDart c))) y.1 = y.1 := rfl
      rw [hyy] at h
      rw [hy_down] at h
      exact absurd h (by simp)
    · exact h1
  refine ⟨j0 - 1, by omega, ?_, ?_⟩
  · rcases Nat.eq_or_lt_of_le hj0_pos with h1 | h1
    · rw [show j0 - 1 = 0 from by omega, pow_zero]
      have hyy : ((1 : Equiv.Perm (CircuitDart c))) y.1 = y.1 := rfl
      rw [hyy]
      exact hy_down
    · have hmin := Nat.find_min hex (m := j0 - 1) (by omega)
      cases h : dartIsUp ((facePermutation r ^ (j0 - 1)) y.1)
      · rfl
      · exact absurd h hmin
  · rw [show j0 - 1 + 1 = j0 from by omega]
    exact hj0_spec

/-- Between a downward crossing and its first return the face passes a min
corner: an ascending dart whose rotation successor is ascending, with both
explicitly located on the walk. -/
theorem exists_minCorner_on_descent (hpl : ProperLayered c)
    (r : OrientableRotation c) {ell : Nat} (y : CutDart c ell)
    (hdown : c.layer y.1.source = ell + 1) :
    ∃ x : CircuitDart c,
      dartIsUp x = true ∧ dartIsUp (r.rotation x) = true ∧
      ∃ j : Nat,
        j + 1 ≤ firstReturnTime (facePermutation r)
          (fun d => isCutDart c ell d = true) y ∧
        dartReverse c x = (facePermutation r ^ j) y.1 ∧
        r.rotation x = (facePermutation r ^ (j + 1)) y.1 := by
  obtain ⟨j, hj, hdj, hdj1⟩ := exists_switch_on_descent hpl r y hdown
  refine ⟨dartReverse c ((facePermutation r ^ j) y.1), ?_, ?_, j, hj, ?_, ?_⟩
  · rw [dartIsUp_dartReverse hpl, hdj]
    rfl
  · have hval : r.rotation (dartReverse c ((facePermutation r ^ j) y.1))
        = facePermutation r ((facePermutation r ^ j) y.1) := rfl
    rw [hval, ← Equiv.Perm.mul_apply, ← pow_succ']
    exact hdj1
  · exact (dartReverse c).left_inv ((facePermutation r ^ j) y.1)
  · have hval : r.rotation (dartReverse c ((facePermutation r ^ j) y.1))
        = facePermutation r ((facePermutation r ^ j) y.1) := rfl
    rw [hval, ← Equiv.Perm.mul_apply, ← pow_succ']

theorem perm_pow_apply_pow {α : Type} (p : Equiv.Perm α) (a b : Nat) (v : α) :
    (p ^ a) ((p ^ b) v) = (p ^ (a + b)) v := by
  rw [← Equiv.Perm.mul_apply, ← pow_add]

/-- A cut dart crosses in one of the two directions. -/
theorem cutDart_source_cases (hpl : ProperLayered c) {ell : Nat}
    (x : CutDart c ell) :
    c.layer x.1.source = ell ∨ c.layer x.1.source = ell + 1 := by
  have hcut : min (c.layer x.1.source) (c.layer x.1.target) = ell := by
    have h := x.2
    rwa [isCutDart, beq_iff_eq] at h
  rcases dart_layer_cases hpl x.1 with h | h
  · omega
  · omega

/-- **Involutivity of the first return at genus zero.**  Every straddling face
crosses the cut exactly twice, so following the face from a crossing and back
returns to the starting crossing. -/
theorem firstReturn_involutive (hpl : ProperLayered c)
    (hS : ∃! s, IsGraphSource c s) (hT : ∃! t, IsGraphSink c t)
    (r : OrientableRotation c) (hZero : rotationGenus r = 0)
    {ell : Nat} (x : CutDart c ell) :
    (firstReturn r ell) ((firstReturn r ell) x) = x := by
  classical
  have hup_case : ∀ u : CutDart c ell, c.layer u.1.source = ell →
      (firstReturn r ell) ((firstReturn r ell) u) = u := by
    intro u hu
    by_contra hne
    set y := (firstReturn r ell) u with hydef
    set z := (firstReturn r ell) y with hzdef
    have hzx : z ≠ u := hne
    have hydown : c.layer y.1.source = ell + 1 ∧ c.layer y.1.target = ell :=
      firstReturn_down hpl r u hu
    have hzup : c.layer z.1.source = ell ∧ c.layer z.1.target = ell + 1 :=
      firstReturn_up hpl r y hydown.1
    set y2 := (firstReturn r ell) z with hy2def
    have hy2y : y2 ≠ y := by
      intro h
      exact hzx ((firstReturn r ell).injective (h.trans hydef))
    have hy2down : c.layer y2.1.source = ell + 1 ∧ c.layer y2.1.target = ell :=
      firstReturn_down hpl r z hzup.1
    set Ty := firstReturnTime (facePermutation r)
      (fun d => isCutDart c ell d = true) y with hTydef
    set Tz := firstReturnTime (facePermutation r)
      (fun d => isCutDart c ell d = true) z with hTzdef
    set Ty2 := firstReturnTime (facePermutation r)
      (fun d => isCutDart c ell d = true) y2 with hTy2def
    have hTy1 : 1 ≤ Ty := firstReturnTime_pos _ _ y
    have hTz1 : 1 ≤ Tz := firstReturnTime_pos _ _ z
    have hzval : z.1 = (facePermutation r ^ Ty) y.1 := firstReturn_val r ell y
    have hy2val : y2.1 = (facePermutation r ^ (Tz + Ty)) y.1 := by
      have h1 : y2.1 = (facePermutation r ^ Tz) z.1 := firstReturn_val r ell z
      rw [h1, hzval]
      exact perm_pow_apply_pow (facePermutation r) Tz Ty y.1
    have hNret : (facePermutation r ^ orbitPeriod (facePermutation r) y.1) y.1
        = y.1 := orbitPeriod_return (facePermutation r) y.1
    have hN1 : 1 ≤ orbitPeriod (facePermutation r) y.1 :=
      orbitPeriod_pos (facePermutation r) y.1
    have hcN : isCutDart c ell
        ((facePermutation r ^ orbitPeriod (facePermutation r) y.1) y.1)
        = true := by
      rw [hNret]
      exact y.2
    have hTyN : Ty ≤ orbitPeriod (facePermutation r) y.1 := by
      rw [hTydef]
      exact Nat.find_min' (exists_firstReturn (facePermutation r) _ y) ⟨hN1, hcN⟩
    have hTyN' : Ty < orbitPeriod (facePermutation r) y.1 := by
      rcases Nat.eq_or_lt_of_le hTyN with heq | h
      · exfalso
        have hzy : z.1 = y.1 := by
          rw [hzval, heq, hNret]
        have h1 := hzup.1
        have h2 := hydown.1
        rw [hzy] at h1
        omega
      · exact h
    have hcNz : isCutDart c ell
        ((facePermutation r ^ (orbitPeriod (facePermutation r) y.1 - Ty)) z.1)
        = true := by
      rw [hzval, perm_pow_apply_pow, show orbitPeriod (facePermutation r) y.1
        - Ty + Ty = orbitPeriod (facePermutation r) y.1 from by omega, hNret]
      exact y.2
    have hTzN : Tz ≤ orbitPeriod (facePermutation r) y.1 - Ty := by
      rw [hTzdef]
      exact Nat.find_min' (exists_firstReturn (facePermutation r) _ z)
        ⟨by omega, hcNz⟩
    have hTzN' : Tz < orbitPeriod (facePermutation r) y.1 - Ty := by
      rcases Nat.eq_or_lt_of_le hTzN with heq | h
      · exfalso
        apply hy2y
        apply Subtype.ext
        rw [hy2val, show Tz + Ty = orbitPeriod (facePermutation r) y.1
          from by omega, hNret]
      · exact h
    have hcNy2 : isCutDart c ell
        ((facePermutation r
          ^ (orbitPeriod (facePermutation r) y.1 - (Tz + Ty))) y2.1) = true := by
      rw [hy2val, perm_pow_apply_pow, show orbitPeriod (facePermutation r) y.1
        - (Tz + Ty) + (Tz + Ty) = orbitPeriod (facePermutation r) y.1
        from by omega, hNret]
      exact y.2
    have hTy2N : Ty2 ≤ orbitPeriod (facePermutation r) y.1 - (Tz + Ty) := by
      rw [hTy2def]
      exact Nat.find_min' (exists_firstReturn (facePermutation r) _ y2)
        ⟨by omega, hcNy2⟩
    obtain ⟨x1, hx1u, hx1ru, j1, hj1, hrev1, hrot1⟩ :=
      exists_minCorner_on_descent hpl r y hydown.1
    obtain ⟨x2, hx2u, hx2ru, j2, hj2, hrev2, hrot2⟩ :=
      exists_minCorner_on_descent hpl r y2 hy2down.1
    rw [← hTydef] at hj1
    rw [← hTy2def] at hj2
    have hrot2' : r.rotation x2
        = (facePermutation r ^ (j2 + 1 + (Tz + Ty))) y.1 := by
      rw [hrot2, hy2val]
      exact perm_pow_apply_pow (facePermutation r) (j2 + 1) (Tz + Ty) y.1
    have hydart : dartIsUp y.1 = false := down_of_cutDart hpl y hydown.1
    have hpos2N : j2 + 1 + (Tz + Ty) < orbitPeriod (facePermutation r) y.1 := by
      rcases Nat.lt_or_ge (j2 + 1 + (Tz + Ty))
        (orbitPeriod (facePermutation r) y.1) with h | h
      · exact h
      · exfalso
        have heq : j2 + 1 + (Tz + Ty)
            = orbitPeriod (facePermutation r) y.1 := by omega
        have hyy : r.rotation x2 = y.1 := by
          rw [hrot2', heq, hNret]
        rw [hyy, hydart] at hx2ru
        exact absurd hx2ru (by simp)
    have hsame : (facePermutation r).SameCycle (r.rotation x1)
        (r.rotation x2) := by
      have hD : (facePermutation r ^ ((j2 + 1 + (Tz + Ty)) - (j1 + 1)))
          (r.rotation x1) = r.rotation x2 := by
        rw [hrot1, hrot2', perm_pow_apply_pow, show
          (j2 + 1 + (Tz + Ty)) - (j1 + 1) + (j1 + 1)
            = j2 + 1 + (Tz + Ty) from by omega]
      exact ⟨(((j2 + 1 + (Tz + Ty)) - (j1 + 1) : Nat) : ℤ), hD⟩
    have hx12 : x1 = x2 :=
      minCorner_unique_in_faceOrbit hpl hS hT r hZero hx1u hx1ru hx2u hx2ru hsame
    have hroteq : (facePermutation r ^ (j1 + 1)) y.1
        = (facePermutation r ^ (j2 + 1 + (Tz + Ty))) y.1 := by
      rw [← hrot1, ← hrot2', hx12]
    have hj1N : j1 + 1 < orbitPeriod (facePermutation r) y.1 := by omega
    have := orbitList_pow_injective (facePermutation r) y.1 hj1N hpos2N hroteq
    omega
  rcases cutDart_source_cases hpl x with hx | hx
  · exact hup_case x hx
  · have hu : c.layer ((firstReturn r ell) x).1.source = ell :=
      (firstReturn_up hpl r x hx).1
    have h := hup_case ((firstReturn r ell) x) hu
    exact (firstReturn r ell).injective h

/-- At genus zero the necklace permutation is conjugated to its inverse by
the dart reversal: stepping the necklace on the reversed side undoes a step.
This transports the corner-step identities between the ascending and the
descending sides of the necklace. -/
theorem neckPerm_rev_neckPerm (hpl : ProperLayered c)
    (hS : ∃! s, IsGraphSource c s) (hT : ∃! t, IsGraphSink c t)
    (r : OrientableRotation c) (hZero : rotationGenus r = 0)
    {ell : Nat} (x : CutDart c ell) :
    (neckPerm r ell) ((cutDartReverse c ell) ((neckPerm r ell) x))
      = (cutDartReverse c ell) x := by
  have h1 : (cutDartReverse c ell) ((neckPerm r ell) x)
      = (firstReturn r ell) x := by
    change (cutDartReverse c ell) ((cutDartReverse c ell) ((firstReturn r ell) x))
      = (firstReturn r ell) x
    exact (cutDartReverse c ell).left_inv _
  rw [h1]
  change (cutDartReverse c ell) ((firstReturn r ell) ((firstReturn r ell) x))
    = (cutDartReverse c ell) x
  rw [firstReturn_involutive hpl hS hT r hZero x]

/-! ## Arc-level corner steps

The corner identities transported to the necklace permutation of the
transition arcs.  At a max corner the identity is already on the ascending
side, so no genus hypothesis is needed; at a min corner it is transported
through the conjugation `neckPerm_rev_neckPerm`, which uses involutivity. -/

theorem upDart_cut_self (hpl : ProperLayered c) (d : CircuitDart c)
    (h1 : dartIsUp d = true) :
    isCutDart c (c.layer d.source) d = true := by
  rw [isCutDart, beq_iff_eq]
  have := layer_of_dartIsUp hpl d h1
  omega

theorem cutDartReverse_involutive {ell : Nat} (w : CutDart c ell) :
    (cutDartReverse c ell) ((cutDartReverse c ell) w) = w := by
  apply Subtype.ext
  exact (dartReverse c).left_inv w.1

theorem upOfArc_arcOfUpDart (hpl : ProperLayered c) {ell : Nat}
    (z : CutDart c ell) (hup : c.layer z.1.source = ell) :
    upOfArc (arcOfUpDart hpl z hup) = z := by
  apply Subtype.ext
  apply Subtype.ext
  rfl

/-- The ascending-side necklace step at a min corner: the necklace
permutation maps the later of two rotation-consecutive out-darts to the
earlier one. -/
theorem neckPerm_up_of_minCorner (hpl : ProperLayered c)
    (hS : ∃! s, IsGraphSource c s) (hT : ∃! t, IsGraphSink c t)
    (r : OrientableRotation c) (hZero : rotationGenus r = 0)
    (d : CircuitDart c)
    (h1 : dartIsUp d = true) (h2 : dartIsUp (r.rotation d) = true) :
    (neckPerm r (c.layer d.source))
        ⟨r.rotation d, rotDart_cut_of_corner hpl r d h2⟩
      = ⟨d, upDart_cut_self hpl d h1⟩ := by
  have hconj := neckPerm_rev_neckPerm hpl hS hT r hZero
    (x := ⟨dartReverse c d, revDart_cut_of_up hpl d h1⟩)
  rw [neckPerm_of_minCorner hpl r d h1 h2] at hconj
  rw [cutDartReverse_involutive] at hconj
  have hrevrev : (cutDartReverse c (c.layer d.source))
      ⟨dartReverse c d, revDart_cut_of_up hpl d h1⟩
      = ⟨d, upDart_cut_self hpl d h1⟩ := by
    apply Subtype.ext
    exact (dartReverse c).left_inv d
  rw [hrevrev] at hconj
  exact hconj

/-- The arc-level necklace step at a min corner: for rotation-consecutive
out-darts `d, r.rotation d` of a vertex, the arc permutation maps the arc of
the successor to the arc of the predecessor (the out-fiber is traversed in
reversed rotation order). -/
theorem arcPerm_of_minCorner (hpl : ProperLayered c)
    (hS : ∃! s, IsGraphSource c s) (hT : ∃! t, IsGraphSink c t)
    (r : OrientableRotation c) (hZero : rotationGenus r = 0)
    (d : CircuitDart c)
    (h1 : dartIsUp d = true) (h2 : dartIsUp (r.rotation d) = true) :
    (arcPerm hpl r (c.layer d.source))
        (arcOfUpDart hpl ⟨r.rotation d, rotDart_cut_of_corner hpl r d h2⟩
          (congrArg c.layer (r.preservesSource d)))
      = arcOfUpDart hpl ⟨d, upDart_cut_self hpl d h1⟩ rfl := by
  apply Subtype.ext
  change ((neckPerm r (c.layer d.source))
      (upOfArc (arcOfUpDart hpl ⟨r.rotation d, rotDart_cut_of_corner hpl r d h2⟩
        (congrArg c.layer (r.preservesSource d))))).1.1 = d.1
  rw [upOfArc_arcOfUpDart hpl ⟨r.rotation d, rotDart_cut_of_corner hpl r d h2⟩
    (congrArg c.layer (r.preservesSource d))]
  rw [neckPerm_up_of_minCorner hpl hS hT r hZero d h1 h2]

/-- The arc-level necklace step at a max corner: for rotation-consecutive
in-darts `d, r.rotation d` of a vertex, the arc permutation maps the arc of
the predecessor to the arc of the successor (the in-fiber is traversed in
rotation order).  No genus hypothesis is needed. -/
theorem arcPerm_of_maxCorner (hpl : ProperLayered c)
    (r : OrientableRotation c) (d : CircuitDart c)
    (h1 : dartIsUp d = false) (h2 : dartIsUp (r.rotation d) = false) :
    (arcPerm hpl r (c.layer d.target))
        (arcOfUpDart hpl ⟨dartReverse c d, revDart_cut_of_down hpl d h1⟩ rfl)
      = arcOfUpDart hpl
          ((cutDartReverse c (c.layer d.target))
            ⟨r.rotation d, rotDart_cut_of_maxCorner hpl r d h1 h2⟩)
          (by
            change c.layer (r.rotation d).target = c.layer d.target
            have hs := congrArg c.layer (r.preservesSource d)
            have h3 := layer_of_not_dartIsUp hpl d h1
            have h4 := layer_of_not_dartIsUp hpl (r.rotation d) h2
            omega) := by
  apply Subtype.ext
  change ((neckPerm r (c.layer d.target))
      (upOfArc (arcOfUpDart hpl
        ⟨dartReverse c d, revDart_cut_of_down hpl d h1⟩ rfl))).1.1
    = ((cutDartReverse c (c.layer d.target))
        ⟨r.rotation d, rotDart_cut_of_maxCorner hpl r d h1 h2⟩).1.1
  rw [upOfArc_arcOfUpDart hpl
    ⟨dartReverse c d, revDart_cut_of_down hpl d h1⟩ rfl]
  rw [neckPerm_of_maxCorner hpl r d h1 h2]

/-! ## Single orbit at the source level

At the layer of the unique graph source every dart is ascending, so every
rotation-consecutive pair of its out-darts is a min corner and the arc
permutation chains the whole out-fan together: the transition at the source
level has a single necklace orbit. -/

theorem rotation_pow_source (r : OrientableRotation c) :
    ∀ (k : Nat) (d : CircuitDart c), ((r.rotation ^ k) d).source = d.source := by
  intro k
  induction k with
  | zero =>
    intro d
    rw [pow_zero]
    rfl
  | succ m ih =>
    intro d
    rw [pow_succ, Equiv.Perm.mul_apply, ih (r.rotation d), r.preservesSource]

theorem dart_at_source_up {s : Fin c.gateCount} (hs : IsGraphSource c s)
    (d : CircuitDart c) (hd : d.source = s) : dartIsUp d = true := by
  rcases d.property.1 with he | he
  · exact he
  · exfalso
    have hd' : (d.1).1 = s := hd
    rw [hd'] at he
    rw [hs (d.1).2] at he
    exact absurd he (by simp)

/-- Level-generalized form of `arcPerm_of_minCorner`. -/
theorem arcPerm_of_minCorner' (hpl : ProperLayered c)
    (hS : ∃! s, IsGraphSource c s) (hT : ∃! t, IsGraphSink c t)
    (r : OrientableRotation c) (hZero : rotationGenus r = 0)
    {ell : Nat} (d : CircuitDart c)
    (h1 : dartIsUp d = true) (h2 : dartIsUp (r.rotation d) = true)
    (hlv : c.layer d.source = ell)
    (hcrot : isCutDart c ell (r.rotation d) = true)
    (hsrot : c.layer (r.rotation d).source = ell)
    (hcd : isCutDart c ell d = true) :
    (arcPerm hpl r ell) (arcOfUpDart hpl ⟨r.rotation d, hcrot⟩ hsrot)
      = arcOfUpDart hpl ⟨d, hcd⟩ hlv := by
  subst hlv
  exact arcPerm_of_minCorner hpl hS hT r hZero d h1 h2

theorem arcOfUpDart_upOfArc (hpl : ProperLayered c) {ell : Nat}
    (e : TransitionArc c ell) (hup : c.layer (upOfArc e).1.source = ell) :
    arcOfUpDart hpl (upOfArc e) hup = e := by
  apply Subtype.ext
  rfl

/-- Chaining min-corner steps along the rotation at the source: the arc of
the `k`-th rotation successor reaches the arc of the base dart in `k`
necklace steps. -/
theorem arcPerm_pow_rot_chain (hpl : ProperLayered c)
    (hS : ∃! s, IsGraphSource c s) (hT : ∃! t, IsGraphSink c t)
    (r : OrientableRotation c) (hZero : rotationGenus r = 0)
    {s : Fin c.gateCount} (hs : IsGraphSource c s) {ell : Nat} :
    ∀ (k : Nat) (d : CircuitDart c), d.source = s →
      ∀ (hlv : c.layer d.source = ell)
        (hcut : isCutDart c ell ((r.rotation ^ k) d) = true)
        (hsrc : c.layer ((r.rotation ^ k) d).source = ell)
        (hcd : isCutDart c ell d = true),
        ((arcPerm hpl r ell) ^ k)
            (arcOfUpDart hpl ⟨(r.rotation ^ k) d, hcut⟩ hsrc)
          = arcOfUpDart hpl ⟨d, hcd⟩ hlv := by
  intro k
  induction k with
  | zero =>
    intro d hd hlv hcut hsrc hcd
    rw [pow_zero]
    change arcOfUpDart hpl ⟨(r.rotation ^ 0) d, hcut⟩ hsrc
      = arcOfUpDart hpl ⟨d, hcd⟩ hlv
    apply Subtype.ext
    change ((r.rotation ^ 0) d).1 = d.1
    rw [pow_zero]
    rfl
  | succ m ih =>
    intro d hd hlv hcut hsrc hcd
    have hrs : (r.rotation d).source = s := by
      rw [r.preservesSource]
      exact hd
    have hlv' : c.layer (r.rotation d).source = ell := by
      rw [r.preservesSource]
      exact hlv
    have hup_rot : dartIsUp (r.rotation d) = true :=
      dart_at_source_up hs (r.rotation d) hrs
    have hcd' : isCutDart c ell (r.rotation d) = true := by
      rw [isCutDart, beq_iff_eq]
      have := layer_of_dartIsUp hpl (r.rotation d) hup_rot
      omega
    have hcut' : isCutDart c ell ((r.rotation ^ m) (r.rotation d)) = true := by
      have hval : (r.rotation ^ m) (r.rotation d) = (r.rotation ^ (m + 1)) d := by
        rw [pow_succ, Equiv.Perm.mul_apply]
      rw [hval]
      exact hcut
    have hsrc' : c.layer ((r.rotation ^ m) (r.rotation d)).source = ell := by
      rw [rotation_pow_source, r.preservesSource]
      exact hlv
    have hih := ih (r.rotation d) hrs hlv' hcut' hsrc' hcd'
    have hstep : ((arcPerm hpl r ell) ^ m)
        (arcOfUpDart hpl ⟨(r.rotation ^ (m + 1)) d, hcut⟩ hsrc)
        = arcOfUpDart hpl ⟨r.rotation d, hcd'⟩ hlv' := hih
    rw [pow_succ', Equiv.Perm.mul_apply, hstep]
    have hup_d : dartIsUp d = true := dart_at_source_up hs d hd
    exact arcPerm_of_minCorner' hpl hS hT r hZero d hup_d hup_rot hlv hcd' hlv' hcd

/-- At a level where every transition arc leaves the same source vertex, the
necklace has a single orbit: every arc reaches every other by iterating the
arc permutation. -/
theorem single_orbit_of_common_source (hpl : ProperLayered c)
    (hS : ∃! s, IsGraphSource c s) (hT : ∃! t, IsGraphSink c t)
    (r : OrientableRotation c) (hZero : rotationGenus r = 0)
    {s : Fin c.gateCount} (hs : IsGraphSource c s) {ell : Nat}
    (hall : ∀ e : TransitionArc c ell, e.1.1 = s) :
    ∀ e e' : TransitionArc c ell, ∃ k : Nat, ((arcPerm hpl r ell) ^ k) e' = e := by
  intro e e'
  have hsrc_e : (upOfArc e).1.source = s := hall e
  have hsrc_e' : (upOfArc e').1.source = s := hall e'
  obtain ⟨k, hk⟩ := r.cyclicAtVertex (upOfArc e).1 (upOfArc e').1
    (by rw [hsrc_e, hsrc_e'])
  refine ⟨k, ?_⟩
  have hlv : c.layer (upOfArc e).1.source = ell := e.2.2.1
  have hcd : isCutDart c ell (upOfArc e).1 = true := (upOfArc e).2
  have hcut : isCutDart c ell ((r.rotation ^ k) (upOfArc e).1) = true := by
    rw [hk]
    exact (upOfArc e').2
  have hsrc : c.layer ((r.rotation ^ k) (upOfArc e).1).source = ell := by
    rw [hk]
    exact e'.2.2.1
  have hchain := arcPerm_pow_rot_chain hpl hS hT r hZero hs k (upOfArc e).1
    hsrc_e hlv hcut hsrc hcd
  have harc' : arcOfUpDart hpl ⟨(r.rotation ^ k) (upOfArc e).1, hcut⟩ hsrc
      = e' := by
    apply Subtype.ext
    change ((r.rotation ^ k) (upOfArc e).1).1 = e'.1
    rw [hk]
    rfl
  have harc : arcOfUpDart hpl ⟨(upOfArc e).1, hcd⟩ hlv = e := by
    apply Subtype.ext
    rfl
  rw [harc', harc] at hchain
  exact hchain

theorem necklaceWord_complete_base (hpl : ProperLayered c)
    (hS : ∃! s, IsGraphSource c s) (hT : ∃! t, IsGraphSink c t)
    (r : OrientableRotation c) (hZero : rotationGenus r = 0)
    {s : Fin c.gateCount} (hs : IsGraphSource c s) :
    ∀ e : TransitionArc c (c.layer s), e ∈ necklaceWord hpl r (c.layer s) := by
  intro e
  have hne : Nonempty (TransitionArc c (c.layer s)) := ⟨e⟩
  rw [mem_necklaceWord_iff hpl r hne e]
  have hall : ∀ x : TransitionArc c (c.layer s), x.1.1 = s := by
    intro x
    have h1 : c.layer x.1.1 = c.layer s := x.2.2.1
    exact source_alone_in_layer hpl hS hs x.1.1 h1
  exact single_orbit_of_common_source hpl hS hT r hZero hs hall e hne.some

end AllenderOQ3.Internal
