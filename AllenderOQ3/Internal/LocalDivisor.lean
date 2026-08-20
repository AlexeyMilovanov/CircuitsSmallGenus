import AllenderOQ3.Internal.LocalUnitsCommute

/-!
# The local divisor of a monoid at an element

For `c : M`, the local divisor is `M_c = cM ∩ Mc` with the multiplication
`(x̃*c) ∘ (c*ỹ) = x̃*c*ỹ` and identity `c`.  It is the engine of the
Krohn–Rhodes-free induction of `docs/LOCAL_DIVISOR_PLAN.md`:

* `LocalDivisor.instMonoid` — the monoid structure, with the two workhorse
  computation rules `mul_val` (`p.val = x*c → (p*q).val = x*q.val`) and
  `mul_val'` (`q.val = c*y → (p*q).val = p.val*y`);
* `card_localDivisor_lt` — for a nonunit `c` the local divisor is strictly
  smaller than `M`;
* `localDivisorHom : localDivisorDom c →* LocalDivisor c` — the surjection
  `x ↦ c*x` from the submonoid `{x | c*x ∈ Mc}`, exhibiting `M_c` as a
  divisor of `M`;
* `localUnitsCommute_localDivisor` — "all subgroups abelian" passes to the
  local divisor (through `localUnitsCommute_of_surjective`, S1, now proved).

Everything here is `sorry`-free.
-/

set_option autoImplicit false

namespace AllenderOQ3
namespace Internal

variable {M : Type} [Monoid M]

/-- Membership in the local divisor at `c`: both a left and a right multiple
of `c`. -/
def InLocalDivisor (c x : M) : Prop := (∃ y, x = c * y) ∧ (∃ y, x = y * c)

/-- The local divisor `cM ∩ Mc` of `M` at `c`, as a type. -/
def LocalDivisor (c : M) : Type := {x : M // InLocalDivisor c x}

namespace LocalDivisor

variable {c : M}

instance [Finite M] : Finite (LocalDivisor c) := Subtype.finite

noncomputable instance : One (LocalDivisor c) :=
  ⟨⟨c, ⟨1, (mul_one c).symm⟩, ⟨1, (one_mul c).symm⟩⟩⟩

theorem one_val : (1 : LocalDivisor c).val = c := rfl

/-- The product `(x̃*c) ∘ (c*ỹ) = x̃*c*ỹ`, implemented through a chosen left
factor of the first argument; `mul_val`/`mul_val'` below show the choice is
irrelevant. -/
noncomputable instance : Mul (LocalDivisor c) :=
  ⟨fun p q =>
    ⟨Classical.choose p.2.2 * q.val, by
      obtain ⟨p', hp'⟩ := p.2.1
      obtain ⟨q', hq'⟩ := q.2.1
      obtain ⟨q'', hq''⟩ := q.2.2
      have hch : p.val = Classical.choose p.2.2 * c := Classical.choose_spec p.2.2
      constructor
      · refine ⟨p' * q', ?_⟩
        calc Classical.choose p.2.2 * q.val
            = Classical.choose p.2.2 * (c * q') := by rw [← hq']
          _ = (Classical.choose p.2.2 * c) * q' := (mul_assoc _ _ _).symm
          _ = p.val * q' := by rw [← hch]
          _ = (c * p') * q' := by rw [hp']
          _ = c * (p' * q') := mul_assoc _ _ _
      · refine ⟨Classical.choose p.2.2 * q'', ?_⟩
        calc Classical.choose p.2.2 * q.val
            = Classical.choose p.2.2 * (q'' * c) := by rw [← hq'']
          _ = (Classical.choose p.2.2 * q'') * c := (mul_assoc _ _ _).symm⟩⟩

/-- **Left computation rule**: the product only depends on any left
factorization of the first argument. -/
theorem mul_val {p q : LocalDivisor c} {x : M} (hx : p.val = x * c) :
    (p * q).val = x * q.val := by
  obtain ⟨q', hq'⟩ := q.2.1
  have hch : p.val = Classical.choose p.2.2 * c := Classical.choose_spec p.2.2
  change Classical.choose p.2.2 * q.val = x * q.val
  calc Classical.choose p.2.2 * q.val
      = Classical.choose p.2.2 * (c * q') := by rw [← hq']
    _ = (Classical.choose p.2.2 * c) * q' := (mul_assoc _ _ _).symm
    _ = p.val * q' := by rw [← hch]
    _ = (x * c) * q' := by rw [hx]
    _ = x * (c * q') := mul_assoc _ _ _
    _ = x * q.val := by rw [← hq']

/-- **Right computation rule**: through a right factorization of the second
argument. -/
theorem mul_val' {p q : LocalDivisor c} {y : M} (hy : q.val = c * y) :
    (p * q).val = p.val * y := by
  have hch : p.val = Classical.choose p.2.2 * c := Classical.choose_spec p.2.2
  change Classical.choose p.2.2 * q.val = p.val * y
  calc Classical.choose p.2.2 * q.val
      = Classical.choose p.2.2 * (c * y) := by rw [← hy]
    _ = (Classical.choose p.2.2 * c) * y := (mul_assoc _ _ _).symm
    _ = p.val * y := by rw [← hch]

noncomputable instance instMonoid : Monoid (LocalDivisor c) where
  mul_assoc p q r := by
    apply Subtype.ext
    obtain ⟨x, hx⟩ := p.2.2
    obtain ⟨q'', hq''⟩ := q.2.2
    have h1 : (p * q).val = x * q.val := mul_val hx
    have h2 : (p * q).val = (x * q'') * c := by
      rw [h1, hq'', ← mul_assoc]
    have h3 : ((p * q) * r).val = (x * q'') * r.val := mul_val h2
    have h4 : (q * r).val = q'' * r.val := mul_val hq''
    have h5 : (p * (q * r)).val = x * (q * r).val := mul_val hx
    rw [h3, h5, h4, mul_assoc]
  one_mul p := by
    apply Subtype.ext
    have h : ((1 : LocalDivisor c) * p).val = 1 * p.val :=
      mul_val (by rw [one_val, one_mul])
    rw [h, one_mul]
  mul_one p := by
    apply Subtype.ext
    have h : (p * (1 : LocalDivisor c)).val = p.val * 1 :=
      mul_val' (by rw [one_val, mul_one])
    rw [h, mul_one]

/-- **Strict decrease**: for a nonunit `c` the local divisor is strictly
smaller than `M` (it misses `1`). -/
theorem card_localDivisor_lt [Finite M] (hc : ¬ IsUnit c) :
    Nat.card (LocalDivisor c) < Nat.card M := by
  classical
  have hnot : ¬ InLocalDivisor c 1 := by
    rintro ⟨⟨y, hy⟩, -⟩
    exact hc (isUnit_of_mul_eq_one_finite (c := c) (y := y) hy.symm)
  haveI : Fintype M := Fintype.ofFinite M
  have h1 : Nat.card (LocalDivisor c)
      = Fintype.card {x : M // InLocalDivisor c x} := by
    have h2 : Nat.card {x : M // InLocalDivisor c x}
        = Fintype.card {x : M // InLocalDivisor c x} := Nat.card_eq_fintype_card
    exact h2
  rw [h1, Nat.card_eq_fintype_card]
  exact Fintype.card_subtype_lt (p := fun x : M => InLocalDivisor c x)
    (x := 1) hnot

end LocalDivisor

/-! ## The local divisor is a divisor of `M` -/

/-- The domain submonoid `{x | c*x ∈ Mc}` of the canonical surjection onto the
local divisor. -/
def localDivisorDom (c : M) : Submonoid M where
  carrier := {x | ∃ y, c * x = y * c}
  one_mem' := ⟨1, by rw [mul_one, one_mul]⟩
  mul_mem' := by
    rintro x₁ x₂ ⟨y₁, hy₁⟩ ⟨y₂, hy₂⟩
    refine ⟨y₁ * y₂, ?_⟩
    calc c * (x₁ * x₂) = (c * x₁) * x₂ := (mul_assoc _ _ _).symm
      _ = (y₁ * c) * x₂ := by rw [hy₁]
      _ = y₁ * (c * x₂) := mul_assoc _ _ _
      _ = y₁ * (y₂ * c) := by rw [hy₂]
      _ = (y₁ * y₂) * c := (mul_assoc _ _ _).symm

/-- The underlying map of the canonical surjection: `x ↦ c*x`. -/
noncomputable def toLocalDivisor (c : M) (x : localDivisorDom c) : LocalDivisor c :=
  ⟨c * x.val, ⟨x.val, rfl⟩, x.2⟩

theorem toLocalDivisor_val (c : M) (x : localDivisorDom c) :
    (toLocalDivisor c x).val = c * x.val := rfl

/-- **The canonical surjection** `localDivisorDom c →* LocalDivisor c`,
exhibiting the local divisor as a divisor of `M`. -/
noncomputable def localDivisorHom (c : M) : localDivisorDom c →* LocalDivisor c where
  toFun := toLocalDivisor c
  map_one' := Subtype.ext (mul_one c)
  map_mul' x y := by
    apply Subtype.ext
    obtain ⟨a, ha⟩ := x.2
    have hx : (toLocalDivisor c x).val = a * c := by
      rw [toLocalDivisor_val, ha]
    have h := LocalDivisor.mul_val (p := toLocalDivisor c x)
      (q := toLocalDivisor c y) hx
    calc (toLocalDivisor c (x * y)).val = c * (x.val * y.val) := rfl
      _ = (c * x.val) * y.val := (mul_assoc _ _ _).symm
      _ = (a * c) * y.val := by rw [ha]
      _ = a * (c * y.val) := mul_assoc _ _ _
      _ = a * (toLocalDivisor c y).val := rfl
      _ = (toLocalDivisor c x * toLocalDivisor c y).val := h.symm

theorem localDivisorHom_surjective (c : M) :
    Function.Surjective (localDivisorHom c) := by
  intro z
  obtain ⟨u, hu⟩ := z.2.1
  obtain ⟨v, hv⟩ := z.2.2
  refine ⟨⟨u, ⟨v, ?_⟩⟩, ?_⟩
  · rw [← hu, hv]
  · apply Subtype.ext
    change c * u = z.val
    rw [← hu]

/-- "All subgroups abelian" passes to the local divisor (modulo the open leaf
S1 `localUnitsCommute_of_surjective`). -/
theorem localUnitsCommute_localDivisor [Finite M] {c : M}
    (h : LocalUnitsCommute M) : LocalUnitsCommute (LocalDivisor c) :=
  localUnitsCommute_of_surjective (localDivisorHom c)
    (localDivisorHom_surjective c) (localUnitsCommute_submonoid _ h)

end Internal
end AllenderOQ3
