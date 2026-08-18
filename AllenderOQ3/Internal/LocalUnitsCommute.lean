import AllenderOQ3.Model

/-!
# All subgroups abelian, in first-order form

`LocalUnitsCommute M` says: any two invertible elements of a local monoid
`e M e` (with idempotent identity `e`) commute.  This is the exact algebraic
hypothesis of the local-divisor route to `monoidWordACC_nonCrossing`
(`docs/LOCAL_DIVISOR_PLAN.md`): it is equivalent to "every subgroup of `M` is
abelian", but is stated first-order so that it transports through submonoids
and surjections without any Green-relation library.

Proved here:

* `localUnitsCommute_submonoid` — the property passes to submonoids;
* `mul_comm_of_localUnitsCommute_units` — if additionally every element is a
  unit, the whole monoid is commutative (the base case of the induction);
* `isUnit_of_mul_eq_one_finite` — in a finite monoid a one-sided inverse is
  two-sided (used both here and for the local divisor).

Also proved here (S1, `docs/LOCAL_DIVISOR_PLAN.md` §2 — no longer open):

* `localUnitsCommute_of_surjective` — the property passes along surjective
  homomorphisms of finite monoids.  Route: lift the local unit group through
  the preimage semigroup `U`; a cardinality-minimal ideal `I = U¹z₀U¹` of `U`;
  an idempotent power `f ∈ I`; `f I f` is a group with identity `f` mapping
  onto the target local unit group; apply `LocalUnitsCommute` at `f`.

Everything in this file is `sorry`-free.
-/

set_option autoImplicit false

namespace AllenderOQ3
namespace Internal

/-- **Any two local units commute**: whenever `e` is idempotent and `a, b` are
invertible elements of the local monoid at `e` (with witnesses `a', b'`), they
commute.  Equivalent to "every subgroup of `M` is abelian". -/
def LocalUnitsCommute (M : Type) [Monoid M] : Prop :=
  ∀ e a a' b b' : M, e * e = e →
    e * a = a → a * e = a → e * a' = a' → a' * e = a' → a * a' = e → a' * a = e →
    e * b = b → b * e = b → e * b' = b' → b' * e = b' → b * b' = e → b' * b = e →
    a * b = b * a

/-- The property passes to submonoids. -/
theorem localUnitsCommute_submonoid {M : Type} [Monoid M] (S : Submonoid M)
    (h : LocalUnitsCommute M) : LocalUnitsCommute S := by
  intro e a a' b b' hee hea hae hea' ha'e haa' ha'a heb hbe heb' hb'e hbb' hb'b
  have lift : ∀ {x y z : S}, x * y = z → x.val * y.val = z.val := by
    intro x y z hxy
    exact congrArg Subtype.val hxy
  exact Subtype.ext (h e.val a.val a'.val b.val b'.val (lift hee)
    (lift hea) (lift hae) (lift hea') (lift ha'e) (lift haa') (lift ha'a)
    (lift heb) (lift hbe) (lift heb') (lift hb'e) (lift hbb') (lift hb'b))

/-- **Base case of the local-divisor induction**: if every element is a unit
and local units commute, the monoid is commutative (take `e = 1`). -/
theorem mul_comm_of_localUnitsCommute_units {M : Type} [Monoid M]
    (h : LocalUnitsCommute M) (hu : ∀ m : M, IsUnit m) (a b : M) :
    a * b = b * a := by
  obtain ⟨ua, hua⟩ := hu a
  obtain ⟨ub, hub⟩ := hu b
  subst hua
  subst hub
  exact h 1 ua.val (ua⁻¹).val ub.val (ub⁻¹).val (one_mul 1)
    (one_mul _) (mul_one _) (one_mul _) (mul_one _) ua.mul_inv ua.inv_mul
    (one_mul _) (mul_one _) (one_mul _) (mul_one _) ub.mul_inv ub.inv_mul

/-- **In a finite monoid, a right inverse makes a unit**: left multiplication
by `c` is surjective, hence injective, so the right inverse is two-sided. -/
theorem isUnit_of_mul_eq_one_finite {M : Type} [Monoid M] [Finite M] {c y : M}
    (h : c * y = 1) : IsUnit c := by
  have hsurj : Function.Surjective (fun m : M => c * m) := by
    intro m
    refine ⟨y * m, ?_⟩
    show c * (y * m) = m
    rw [← mul_assoc, h, one_mul]
  have hinj : Function.Injective (fun m : M => c * m) :=
    Finite.injective_iff_surjective.mpr hsurj
  have h2 : c * (y * c) = c * 1 := by
    rw [← mul_assoc, h, one_mul, mul_one]
  have h3 : y * c = 1 := hinj h2
  exact ⟨⟨c, y, h, h3⟩, rfl⟩

/-! ### Auxiliary material for the surjective-transport lemma (S1) -/

/-- The set of invertible elements of the local monoid at `e` (the "local unit
group" at `e`, when `e` is idempotent). -/
def LocalUnitSet {M : Type} [Monoid M] (e : M) : Set M :=
  {x | e * x = x ∧ x * e = x ∧
    ∃ x', e * x' = x' ∧ x' * e = x' ∧ x * x' = e ∧ x' * x = e}

/-- The local unit set at `e` is closed under multiplication. -/
theorem localUnitSet_mul {M : Type} [Monoid M] {e x y : M}
    (hx : x ∈ LocalUnitSet e) (hy : y ∈ LocalUnitSet e) : x * y ∈ LocalUnitSet e := by
  obtain ⟨hex, hxe, x', hex', hx'e, hxx', hx'x⟩ := hx
  obtain ⟨hey, hye, y', hey', hy'e, hyy', hy'y⟩ := hy
  refine ⟨by rw [← mul_assoc, hex], by rw [mul_assoc, hye], y' * x',
    by rw [← mul_assoc, hey'], by rw [mul_assoc, hx'e], ?_, ?_⟩
  · calc x * y * (y' * x') = x * (y * y') * x' := by simp only [mul_assoc]
      _ = x * x' := by rw [hyy', hxe]
      _ = e := hxx'
  · calc y' * x' * (x * y) = y' * (x' * x) * y := by simp only [mul_assoc]
      _ = y' * y := by rw [hx'x, hy'e]
      _ = e := hy'y

/-- An idempotent is a local unit at itself. -/
theorem localUnitSet_self {M : Type} [Monoid M] {e : M} (hee : e * e = e) :
    e ∈ LocalUnitSet e := ⟨hee, hee, e, hee, hee, hee, hee⟩

/-- The only idempotent local unit at `e` is `e` itself (a group has a unique
idempotent). -/
theorem localUnitSet_eq_of_idem {M : Type} [Monoid M] {e x : M}
    (hx : x ∈ LocalUnitSet e) (hxx : x * x = x) : x = e := by
  obtain ⟨_, hxe, x', _, _, hxx', _⟩ := hx
  calc x = x * e := hxe.symm
    _ = x * (x * x') := by rw [hxx']
    _ = x * x * x' := by rw [mul_assoc]
    _ = x * x' := by rw [hxx]
    _ = e := hxx'

/-- **Pigeonhole**: in a finite monoid every element has an idempotent positive
power. -/
theorem exists_idempotent_pow {N : Type} [Monoid N] [Finite N] (x : N) :
    ∃ n : Nat, 1 ≤ n ∧ x ^ n * x ^ n = x ^ n := by
  have main : ∀ i j : Nat, i < j → x ^ i = x ^ j →
      ∃ n : Nat, 1 ≤ n ∧ x ^ n * x ^ n = x ^ n := by
    intro i j hlt hEq
    have hjp : j = i + (j - i) := by omega
    have key : ∀ m, i ≤ m → x ^ (m + (j - i)) = x ^ m := by
      intro m hm
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
      have h1 : x ^ (i + d + (j - i)) = x ^ d * x ^ (i + (j - i)) := by
        rw [← pow_add]; ring_nf
      rw [h1, ← hjp, ← hEq, ← pow_add]
      ring_nf
    have key2 : ∀ t m, i ≤ m → x ^ (m + t * (j - i)) = x ^ m := by
      intro t
      induction t with
      | zero => intro m _; simp
      | succ k ih =>
        intro m hm
        have h2 : m + (k + 1) * (j - i) = (m + k * (j - i)) + (j - i) := by ring
        rw [h2, key _ (by omega), ih m hm]
    refine ⟨(i + 1) * (j - i), by nlinarith, ?_⟩
    rw [← pow_add]
    exact key2 (i + 1) ((i + 1) * (j - i)) (by nlinarith)
  obtain ⟨i, j, hij, hEq⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : Nat => x ^ n)
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact main i j hlt hEq
  · exact main j i hlt hEq.symm

/-- **In the local monoid at an idempotent `f` of a finite monoid, a right
inverse is a two-sided inverse.**  Left translation by `s` is surjective on
`fNf`, hence injective there, and `s * (t * s) = s * f`. -/
theorem local_right_inverse {N : Type} [Monoid N] [Finite N] {f s t : N}
    (hf : f * f = f) (hfs : f * s = s) (hsf : s * f = s)
    (hft : f * t = t) (hst : s * t = f) : t * s = f := by
  classical
  let K := {x : N // f * x = x ∧ x * f = x}
  have hmem : ∀ x : K, f * (s * x.1) = s * x.1 ∧ (s * x.1) * f = s * x.1 := by
    intro x
    exact ⟨by rw [← mul_assoc, hfs], by rw [mul_assoc, x.2.2]⟩
  let g : K → K := fun x => ⟨s * x.1, hmem x⟩
  have hsurj : Function.Surjective g := by
    intro x
    refine ⟨⟨t * x.1, ?_, ?_⟩, ?_⟩
    · rw [← mul_assoc, hft]
    · rw [mul_assoc, x.2.2]
    · apply Subtype.ext
      change s * (t * x.1) = x.1
      rw [← mul_assoc, hst, x.2.1]
  have hinj : Function.Injective g := Finite.injective_iff_surjective.mpr hsurj
  have hts : f * (t * s) = t * s ∧ (t * s) * f = t * s :=
    ⟨by rw [← mul_assoc, hft], by rw [mul_assoc, hsf]⟩
  have hgg : g ⟨t * s, hts⟩ = g ⟨f, hf, hf⟩ := by
    apply Subtype.ext
    change s * (t * s) = s * f
    rw [← mul_assoc, hst, hsf, hfs]
  exact congrArg Subtype.val (hinj hgg)

/-- **S1 (closed).  The property passes along surjective homomorphisms of
finite monoids.**  Complete paper proof in `docs/LOCAL_DIVISOR_PLAN.md` §2:
given local units `a, b` at an idempotent `e` of `M'`, lift the local unit
group `T'` of `e M' e` to the subsemigroup `U = φ⁻¹ T'` of `N`; choose
`z₀ ∈ U` with `U¹z₀U¹` of minimal cardinality, so `I := U¹z₀U¹` is a minimal
ideal of `U`; take an idempotent power `f ∈ I` (pigeonhole); then `f I f` is a
group with identity `f` (for `z ∈ fIf` write `f = azb` by minimality, pass to
`A = faf, B = fbf`, use `isUnit_of_mul_eq_one_finite` in the finite monoid
`fU¹f` to invert `z`, with `z⁻¹ = BA ∈ fIf`), `φ f = e` (unique idempotent of
a group), and `φ (fIf) ⊇ T'` (a nonempty ideal of a group is everything).
Lift `a, b` to the group `fIf` and apply `h` at the idempotent `f`. -/
theorem localUnitsCommute_of_surjective {N M' : Type} [Monoid N] [Finite N]
    [Monoid M'] (φ : N →* M') (hφ : Function.Surjective φ)
    (h : LocalUnitsCommute N) : LocalUnitsCommute M' := by
  classical
  intro e a a' b b' hee hea hae hea' ha'e haa' ha'a heb hbe heb' hb'e hbb' hb'b
  have haU : a ∈ LocalUnitSet e := ⟨hea, hae, a', hea', ha'e, haa', ha'a⟩
  have hbU : b ∈ LocalUnitSet e := ⟨heb, hbe, b', heb', hb'e, hbb', hb'b⟩
  -- `U` is the preimage of the local unit group at `e`; `V = U¹`.
  set U : Set N := φ ⁻¹' (LocalUnitSet e) with hU
  set V : Set N := insert 1 U with hV
  have hUmul : ∀ x ∈ U, ∀ y ∈ U, x * y ∈ U := by
    intro x hx y hy
    have hxy : φ x * φ y ∈ LocalUnitSet e := localUnitSet_mul hx hy
    simpa [hU, Set.mem_preimage, map_mul] using hxy
  have hVU : ∀ α ∈ V, ∀ z ∈ U, α * z ∈ U := by
    intro α hα z hz
    rcases hα with h1 | h1
    · simpa [h1] using hz
    · exact hUmul _ h1 _ hz
  have hUV : ∀ z ∈ U, ∀ β ∈ V, z * β ∈ U := by
    intro z hz β hβ
    rcases hβ with h1 | h1
    · simpa [h1] using hz
    · exact hUmul _ hz _ h1
  have hVmul : ∀ x ∈ V, ∀ y ∈ V, x * y ∈ V := by
    intro x hx y hy
    rcases hx with h1 | h1
    · simpa [h1] using hy
    · exact Set.mem_insert_of_mem _ (hUV _ h1 _ hy)
  have hone : (1 : N) ∈ V := Set.mem_insert _ _
  -- the principal ideals `U¹ z U¹`
  set J : N → Set N := fun z => {x | ∃ α ∈ V, ∃ β ∈ V, x = α * z * β} with hJ
  have hJsubU : ∀ z ∈ U, J z ⊆ U := by
    rintro z hz x ⟨α, hα, β, hβ, rfl⟩
    exact hUV _ (hVU _ hα _ hz) _ hβ
  have hJideal : ∀ z, ∀ x ∈ J z, ∀ γ ∈ V, γ * x ∈ J z ∧ x * γ ∈ J z := by
    rintro z x ⟨α, hα, β, hβ, rfl⟩ γ hγ
    exact ⟨⟨γ * α, hVmul _ hγ _ hα, β, hβ, by simp only [mul_assoc]⟩,
      ⟨α, hα, β * γ, hVmul _ hβ _ hγ, by simp only [mul_assoc]⟩⟩
  have hJmono : ∀ z, ∀ w ∈ J z, J w ⊆ J z := by
    rintro z w ⟨α, hα, β, hβ, rfl⟩ x ⟨γ, hγ, δ, hδ, rfl⟩
    exact ⟨γ * α, hVmul _ hγ _ hα, β * δ, hVmul _ hβ _ hδ, by simp only [mul_assoc]⟩
  obtain ⟨u₀, hu₀φ⟩ := hφ e
  have hu₀ : u₀ ∈ U := by
    rw [hU]
    refine Set.mem_preimage.mpr ?_
    rw [hu₀φ]
    exact localUnitSet_self hee
  -- a cardinality-minimal principal ideal `I = J z₀`
  have hex : ∃ n, ∃ z ∈ U, (J z).ncard = n := ⟨_, u₀, hu₀, rfl⟩
  obtain ⟨z₀, hz₀U, hz₀⟩ := Nat.find_spec hex
  have hminNat : ∀ z ∈ U, Nat.find hex ≤ (J z).ncard := fun z hz => Nat.find_le ⟨z, hz, rfl⟩
  have hminimal : ∀ w ∈ J z₀, J z₀ ⊆ J w := by
    intro w hw
    have hwU : w ∈ U := hJsubU _ hz₀U hw
    have hsub : J w ⊆ J z₀ := hJmono _ _ hw
    have hcard : (J z₀).ncard ≤ (J w).ncard := by rw [hz₀]; exact hminNat _ hwU
    exact (Set.eq_of_subset_of_ncard_le hsub hcard (Set.toFinite _)) ▸ subset_rfl
  -- an idempotent `f` inside the minimal ideal
  obtain ⟨n, hn1, hidem⟩ := exists_idempotent_pow z₀
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  set f := z₀ ^ (m + 1) with hfdef
  have hff : f * f = f := hidem
  have hpowV : ∀ k, z₀ ^ k ∈ V := by
    intro k
    induction k with
    | zero => simpa using hone
    | succ i ih => rw [pow_succ]; exact hVmul _ ih _ (Set.mem_insert_of_mem _ hz₀U)
  have hfI : f ∈ J z₀ := ⟨z₀ ^ m, hpowV m, 1, hone, by rw [hfdef, pow_succ, mul_one]⟩
  have hfU : f ∈ U := hJsubU _ hz₀U hfI
  have hfV : f ∈ V := Set.mem_insert_of_mem _ hfU
  -- `f (J z₀) f` is a group with identity `f`
  have hInv : ∀ y ∈ J z₀, f * y = y → y * f = y →
      ∃ y', f * y' = y' ∧ y' * f = y' ∧ y * y' = f ∧ y' * y = f := by
    intro y hy hfy hyf
    obtain ⟨α, hα, β, hβ, hfe⟩ := hminimal y hy hfI
    set A := f * α * f with hA
    set B := f * β * f with hB
    have hfA : f * A = A := by rw [hA, ← mul_assoc, ← mul_assoc, hff]
    have hAf : A * f = A := by rw [hA, mul_assoc, hff]
    have hfB : f * B = B := by rw [hB, ← mul_assoc, ← mul_assoc, hff]
    have hfy' : ∀ X : N, f * (y * X) = y * X := fun X => by rw [← mul_assoc, hfy]
    have hyf' : ∀ X : N, y * (f * X) = y * X := fun X => by rw [← mul_assoc, hyf]
    have hAyB : A * y * B = f := by
      calc A * y * B = f * (α * y * β) * f := by
            simp only [hA, hB, mul_assoc, hfy', hyf']
        _ = f * f * f := by rw [← hfe]
        _ = f := by rw [hff, hff]
    have hfs : f * (A * y) = A * y := by rw [← mul_assoc, hfA]
    have hsf : A * y * f = A * y := by rw [mul_assoc, hyf]
    have h1 : B * (A * y) = f := local_right_inverse hff hfs hsf hfB hAyB
    have hfs2 : f * (y * B) = y * B := by rw [← mul_assoc, hfy]
    have hAs2 : A * (y * B) = f := by rw [← mul_assoc]; exact hAyB
    have h2 : y * B * A = f := local_right_inverse hff hfA hAf hfs2 hAs2
    refine ⟨B * A, by rw [← mul_assoc, hfB], by rw [mul_assoc, hAf], ?_, ?_⟩
    · rw [← mul_assoc]; exact h2
    · rw [mul_assoc]; exact h1
  -- `φ f = e`, and `a`, `b` lift to the group `f (J z₀) f`
  have hfmem : φ f ∈ LocalUnitSet e := by rw [hU] at hfU; exact hfU
  have hφf : φ f = e := localUnitSet_eq_of_idem hfmem (by rw [← map_mul, hff])
  obtain ⟨u, hu⟩ := hφ a
  obtain ⟨v, hv⟩ := hφ b
  have huV : u ∈ V := Set.mem_insert_of_mem _ (by rw [hU]; exact Set.mem_preimage.mpr (hu ▸ haU))
  have hvV : v ∈ V := Set.mem_insert_of_mem _ (by rw [hU]; exact Set.mem_preimage.mpr (hv ▸ hbU))
  have hYaI : f * u * f ∈ J z₀ := (hJideal z₀ _ ((hJideal z₀ f hfI u huV).2) f hfV).2
  have hYbI : f * v * f ∈ J z₀ := (hJideal z₀ _ ((hJideal z₀ f hfI v hvV).2) f hfV).2
  have hfYa : f * (f * u * f) = f * u * f := by rw [← mul_assoc, ← mul_assoc, hff]
  have hYaf : f * u * f * f = f * u * f := by rw [mul_assoc, hff]
  have hfYb : f * (f * v * f) = f * v * f := by rw [← mul_assoc, ← mul_assoc, hff]
  have hYbf : f * v * f * f = f * v * f := by rw [mul_assoc, hff]
  obtain ⟨Ya', hfYa', hYa'f, hYaYa', hYa'Ya⟩ := hInv _ hYaI hfYa hYaf
  obtain ⟨Yb', hfYb', hYb'f, hYbYb', hYb'Yb⟩ := hInv _ hYbI hfYb hYbf
  have key := h f (f * u * f) Ya' (f * v * f) Yb' hff hfYa hYaf hfYa' hYa'f hYaYa' hYa'Ya
    hfYb hYbf hfYb' hYb'f hYbYb' hYb'Yb
  have hφYa : φ (f * u * f) = a := by rw [map_mul, map_mul, hφf, hu, hea, hae]
  have hφYb : φ (f * v * f) = b := by rw [map_mul, map_mul, hφf, hv, heb, hbe]
  have hres : φ (f * u * f) * φ (f * v * f) = φ (f * v * f) * φ (f * u * f) := by
    rw [← map_mul, ← map_mul, key]
  rw [hφYa, hφYb] at hres
  exact hres

end Internal
end AllenderOQ3
