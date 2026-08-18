import AllenderOQ3.Internal.IntervalRouteCF
import AllenderOQ3.Internal.ClampFill
import AllenderOQ3.Internal.ConstantPropagation

/-!
# Constant elimination (T5): the conjugation glue, proved

Paper §6 / plan 6e: a local group of the full certified monoid embeds into the
constant-free submonoid by the clamp/fan-fill conjugation `Φ f = A * f * B`.
This file proves the entire algebraic content of that step; what remains open
are the two constructive leaves:

* **T5a** `exists_clamp_fill_layers` — the two explicit certified single
  layers: `A` clamps every coordinate outside `J` to its constant value and
  keeps `J`; `B` keeps `J` and fills every coordinate outside `J` with a copy
  of some `J`-coordinate.  Build them as in `ConstantMaps.lean`
  (`constCircuit`): `A` has literal gates outside `J` and diagonal copies on
  `J` (equal source/target arc words — `arcOrderCertificate_of_eq`); `B` has
  one fan per `J`-coordinate covering the following cyclic gap (source-major
  word = target-major word).
* **T5b** `mem_nonCrossingCF_of_no_constant_output` — word-wise constant
  propagation: a certified word whose underlying map has no constant output
  coordinate lies in the constant-free submonoid.  Per-layer surgery (drop
  gates made constant, absorb/neutralize constant predecessors, restrict the
  common arc word — a subsequence of a block-grouped word is block-grouped)
  folded over the `Submonoid.closure` word against an input-constancy pattern;
  the final pattern is empty because no output is forced constant, and an
  intermediate all-constant layer would make every output constant.

Proved here (the glue): `Φ` is multiplicative on the local group, transports
all thirteen local-unit equations, produces constant-free elements (via T5a
semantics + T5b), and is injective on the local group — so
`CFLocalUnitsCommute w` implies `LocalUnitsCommute (NonCrossing w)`
(`localUnitsCommute_of_cf`), and the route assembles into
`localUnitsCommute_nonCrossing_of_route`.
-/

set_option autoImplicit false

namespace AllenderOQ3
namespace Internal

attribute [local instance] Classical.propDecidable

variable {w : Nat}

/-! ## The varying coordinates of a finite set of configurations -/

open Classical in
/-- The coordinates on which `X` is not constant. -/
noncomputable def Jset (X : Finset (Config w)) : Finset (Fin w) :=
  Finset.univ.filter (fun i => ∃ x ∈ X, ∃ y ∈ X, x i ≠ y i)

theorem mem_Jset {X : Finset (Config w)} {i : Fin w} :
    i ∈ Jset X ↔ ∃ x ∈ X, ∃ y ∈ X, x i ≠ y i := by
  simp [Jset]

theorem eq_on_compl_Jset {X : Finset (Config w)} {i : Fin w} (hi : i ∉ Jset X)
    {x y : Config w} (hx : x ∈ X) (hy : y ∈ X) : x i = y i := by
  by_contra hne
  exact hi (mem_Jset.mpr ⟨x, hx, y, hy, hne⟩)

/-! ## The constructive leaves -/

/-- **T5a (open leaf): the clamp and fan-fill layers.**  For a basepoint `x₀`
and a nonempty set `J` of coordinates there are certified transitions `A`
(clamp: keep `J`, freeze the rest to the basepoint values) and `B` (fill:
keep `J`, copy each non-`J` coordinate from some `J`-coordinate). -/
theorem exists_clamp_fill_layers (x₀ : Config w) (J : Finset (Fin w))
    (hJ : J.Nonempty) :
    ∃ Al Bl : TransMonoid w, Al ∈ NonCrossing w ∧ Bl ∈ NonCrossing w ∧
      (∀ (z : Config w) (i : Fin w),
        runTrans Al z i = if i ∈ J then z i else x₀ i) ∧
      (∀ (z : Config w), ∀ j ∈ J, runTrans Bl z j = z j) ∧
      (∀ i : Fin w, i ∉ J → ∃ j ∈ J, ∀ z : Config w, runTrans Bl z i = z j) :=
  clamp_fill_layers x₀ J hJ

/-- **T5b (open leaf): word-wise constant propagation.**  A certified word
with no constant output coordinate lies in the constant-free submonoid. -/
theorem mem_nonCrossingCF_of_no_constant_output {m : TransMonoid w}
    (hm : m ∈ NonCrossing w)
    (hnc : ∀ i : Fin w, ∃ z z' : Config w, runTrans m z i ≠ runTrans m z' i) :
    m ∈ NonCrossingCF w := by
  exact mem_nonCrossingCF_of_no_constant_output_aux hm hnc

/-! ## The conjugation glue (proved) -/

/-- **T5 assembled: the constant-free case implies the general case.** -/
theorem localUnitsCommute_of_cf_glue (hcf : CFLocalUnitsCommute w) :
    LocalUnitsCommute (NonCrossing w) := by
  intro E A A' B B' hEE hEA hAE hEA' hA'E hAA' hA'A hEB hBE hEB' hB'E hBB' hB'B
  have hee : E.val * E.val = E.val := congrArg Subtype.val hEE
  have hea : E.val * A.val = A.val := congrArg Subtype.val hEA
  have hae : A.val * E.val = A.val := congrArg Subtype.val hAE
  have hea' : E.val * A'.val = A'.val := congrArg Subtype.val hEA'
  have ha'e : A'.val * E.val = A'.val := congrArg Subtype.val hA'E
  have haa' : A.val * A'.val = E.val := congrArg Subtype.val hAA'
  have ha'a : A'.val * A.val = E.val := congrArg Subtype.val hA'A
  have heb : E.val * B.val = B.val := congrArg Subtype.val hEB
  have hbe : B.val * E.val = B.val := congrArg Subtype.val hBE
  have heb' : E.val * B'.val = B'.val := congrArg Subtype.val hEB'
  have hb'e : B'.val * E.val = B'.val := congrArg Subtype.val hB'E
  have hbb' : B.val * B'.val = E.val := congrArg Subtype.val hBB'
  have hb'b : B'.val * B.val = E.val := congrArg Subtype.val hB'B
  set e := E.val with hedef
  set a := A.val with hadef
  set a' := A'.val with ha'def
  set b := B.val with hbdef
  set b' := B'.val with hb'def
  set X : Finset (Config w) := fixFinset e with hXdef
  -- absorption of products: images of the relevant elements land in `X`
  have habs_ab : (a * b) * e = a * b := by rw [mul_assoc, hbe]
  have habs_ba : (b * a) * e = b * a := by rw [mul_assoc, hae]
  have hleft_ab : e * (a * b) = a * b := by rw [← mul_assoc, hea]
  have hleft_ba : e * (b * a) = b * a := by rw [← mul_assoc, heb]
  by_cases hJ : (Jset X).Nonempty
  · -- the main case: clamp and fill exist
    have hXne : X.Nonempty := ⟨runTrans e (botConfig w), runTrans_mem_fixFinset hee _⟩
    obtain ⟨x₀, hx₀⟩ := hXne
    obtain ⟨Al, Bl, hAlmem, hBlmem, hAsem, hBJ, hBcopy⟩ :=
      exists_clamp_fill_layers x₀ (Jset X) hJ
    -- clamp is the identity on `X`
    have hAX : ∀ z ∈ X, runTrans Al z = z := by
      intro z hz
      funext i
      rw [hAsem z i]
      by_cases hi : i ∈ Jset X
      · rw [if_pos hi]
      · rw [if_neg hi]
        exact eq_on_compl_Jset hi hx₀ hz
    -- clamp-after-fill is the identity on `X`
    have hABX : ∀ z ∈ X, runTrans Al (runTrans Bl z) = z := by
      intro z hz
      funext i
      rw [hAsem (runTrans Bl z) i]
      by_cases hi : i ∈ Jset X
      · rw [if_pos hi]
        exact hBJ z i hi
      · rw [if_neg hi]
        exact eq_on_compl_Jset hi hx₀ hz
    set Phi : TransMonoid w → TransMonoid w := fun f => Al * f * Bl with hPhidef
    have hPhirun : ∀ (f : TransMonoid w) (z : Config w),
        runTrans (Phi f) z = runTrans Bl (runTrans f (runTrans Al z)) := by
      intro f z
      show runTrans (Al * f * Bl) z = _
      rw [runTrans_mul, runTrans_mul]
    -- multiplicativity on right-`e`-absorbed elements
    have hmult : ∀ f g : TransMonoid w, f * e = f →
        Phi f * Phi g = Phi (f * g) := by
      intro f g hfe
      refine transMonoid_ext ?_
      intro z
      have h1 : runTrans (Phi f * Phi g) z
          = runTrans (Phi g) (runTrans (Phi f) z) := runTrans_mul _ _ _
      rw [h1, hPhirun, hPhirun, hPhirun]
      have hfX : runTrans f (runTrans Al z) ∈ X := mapsTo_fixFinset hfe _
      rw [hABX _ hfX]
      rw [runTrans_mul]
    -- membership of the conjugates in the full monoid
    have hPhiNC : ∀ f : TransMonoid w, f ∈ NonCrossing w →
        Phi f ∈ NonCrossing w := by
      intro f hf
      exact Submonoid.mul_mem _ (Submonoid.mul_mem _ hAlmem hf) hBlmem
    -- no constant output coordinate, given surjectivity on `X`
    have hPhiCF : ∀ f : TransMonoid w, f ∈ NonCrossing w → f * e = f →
        (∀ x ∈ X, ∃ y ∈ X, runTrans f y = x) →
        Phi f ∈ NonCrossingCF w := by
      intro f hf hfe hsurj
      refine mem_nonCrossingCF_of_no_constant_output (hPhiNC f hf) ?_
      intro i
      -- the `i`-th output of `Phi f` copies the `j`-th output of `f ∘ A`
      obtain ⟨j, hjJ, hout⟩ : ∃ j ∈ Jset X, ∀ z : Config w,
          runTrans (Phi f) z i = runTrans f (runTrans Al z) j := by
        by_cases hi : i ∈ Jset X
        · refine ⟨i, hi, ?_⟩
          intro z
          rw [hPhirun]
          exact hBJ _ i hi
        · obtain ⟨j, hjJ, hcopy⟩ := hBcopy i hi
          refine ⟨j, hjJ, ?_⟩
          intro z
          rw [hPhirun]
          exact hcopy _
      obtain ⟨x₁, hx₁, x₂, hx₂, hne⟩ := mem_Jset.mp hjJ
      obtain ⟨y₁, hy₁, hfy₁⟩ := hsurj x₁ hx₁
      obtain ⟨y₂, hy₂, hfy₂⟩ := hsurj x₂ hx₂
      refine ⟨y₁, y₂, ?_⟩
      rw [hout y₁, hout y₂, hAX _ hy₁, hAX _ hy₂, hfy₁, hfy₂]
      exact hne
    -- surjectivity on `X` for the five local elements
    have hsurj_e : ∀ x ∈ X, ∃ y ∈ X, runTrans e y = x := by
      intro x hx
      exact ⟨x, hx, mem_fixFinset.mp hx⟩
    have hsurj_of_inv : ∀ f f' : TransMonoid w, f' * f = e →
        (∀ z : Config w, runTrans f' z ∈ X) →
        ∀ x ∈ X, ∃ y ∈ X, runTrans f y = x := by
      intro f f' hf'f hmaps x hx
      refine ⟨runTrans f' x, hmaps x, ?_⟩
      exact runTrans_local_inv (a := f') (a' := f) hf'f hx
    have hsurj_a : ∀ x ∈ X, ∃ y ∈ X, runTrans a y = x :=
      hsurj_of_inv a a' ha'a (fun z => mapsTo_fixFinset ha'e z)
    have hsurj_a' : ∀ x ∈ X, ∃ y ∈ X, runTrans a' y = x :=
      hsurj_of_inv a' a haa' (fun z => mapsTo_fixFinset hae z)
    have hsurj_b : ∀ x ∈ X, ∃ y ∈ X, runTrans b y = x :=
      hsurj_of_inv b b' hb'b (fun z => mapsTo_fixFinset hb'e z)
    have hsurj_b' : ∀ x ∈ X, ∃ y ∈ X, runTrans b' y = x :=
      hsurj_of_inv b' b hbb' (fun z => mapsTo_fixFinset hbe z)
    -- the thirteen equations transport through `Phi`
    have hm_ee : Phi e * Phi e = Phi e := by rw [hmult e e hee, hee]
    have hm_ea : Phi e * Phi a = Phi a := by rw [hmult e a hee, hea]
    have hm_ae : Phi a * Phi e = Phi a := by rw [hmult a e hae, hae]
    have hm_ea' : Phi e * Phi a' = Phi a' := by rw [hmult e a' hee, hea']
    have hm_a'e : Phi a' * Phi e = Phi a' := by rw [hmult a' e ha'e, ha'e]
    have hm_aa' : Phi a * Phi a' = Phi e := by rw [hmult a a' hae, haa']
    have hm_a'a : Phi a' * Phi a = Phi e := by rw [hmult a' a ha'e, ha'a]
    have hm_eb : Phi e * Phi b = Phi b := by rw [hmult e b hee, heb]
    have hm_be : Phi b * Phi e = Phi b := by rw [hmult b e hbe, hbe]
    have hm_eb' : Phi e * Phi b' = Phi b' := by rw [hmult e b' hee, heb']
    have hm_b'e : Phi b' * Phi e = Phi b' := by rw [hmult b' e hb'e, hb'e]
    have hm_bb' : Phi b * Phi b' = Phi e := by rw [hmult b b' hbe, hbb']
    have hm_b'b : Phi b' * Phi b = Phi e := by rw [hmult b' b hb'e, hb'b]
    -- constant-free memberships
    have hcf_e : Phi e ∈ NonCrossingCF w := hPhiCF e E.property hee hsurj_e
    have hcf_a : Phi a ∈ NonCrossingCF w := hPhiCF a A.property hae hsurj_a
    have hcf_a' : Phi a' ∈ NonCrossingCF w := hPhiCF a' A'.property ha'e hsurj_a'
    have hcf_b : Phi b ∈ NonCrossingCF w := hPhiCF b B.property hbe hsurj_b
    have hcf_b' : Phi b' ∈ NonCrossingCF w := hPhiCF b' B'.property hb'e hsurj_b'
    -- the constant-free case
    have hcomm : Phi a * Phi b = Phi b * Phi a :=
      hcf (Phi e) (Phi a) (Phi a') (Phi b) (Phi b')
        hcf_e hcf_a hcf_a' hcf_b hcf_b'
        hm_ee hm_ea hm_ae hm_ea' hm_a'e hm_aa' hm_a'a
        hm_eb hm_be hm_eb' hm_b'e hm_bb' hm_b'b
    have hPhieq : Phi (a * b) = Phi (b * a) := by
      rw [← hmult a b hae, ← hmult b a hbe, hcomm]
    -- injectivity of `Phi` on left-and-right absorbed elements
    have hval : a * b = b * a := by
      have hpt : ∀ z : Config w,
          runTrans (a * b) (runTrans Al z) = runTrans (b * a) (runTrans Al z) := by
        intro z
        have h1 : runTrans (Phi (a * b)) z = runTrans (Phi (b * a)) z :=
          congrArg (fun m => runTrans m z) hPhieq
        rw [hPhirun, hPhirun] at h1
        -- recover from the fill: both images lie in `X` and agree on `Jset X`
        have hmem1 : runTrans (a * b) (runTrans Al z) ∈ X :=
          mapsTo_fixFinset habs_ab _
        have hmem2 : runTrans (b * a) (runTrans Al z) ∈ X :=
          mapsTo_fixFinset habs_ba _
        funext i
        by_cases hi : i ∈ Jset X
        · have h2 := congrArg (fun c : Config w => c i) h1
          simpa [hBJ _ i hi] using h2
        · exact (eq_on_compl_Jset hi hmem1 hmem2)
      refine transMonoid_ext ?_
      intro y
      have hy : runTrans e y ∈ X := runTrans_mem_fixFinset hee y
      have h1 : runTrans (a * b) y = runTrans (a * b) (runTrans Al (runTrans e y)) := by
        rw [hAX _ hy]
        have h : runTrans (e * (a * b)) y = runTrans (a * b) y :=
          congrArg (fun m => runTrans m y) hleft_ab
        rw [runTrans_mul] at h
        exact h.symm
      have h2 : runTrans (b * a) y = runTrans (b * a) (runTrans Al (runTrans e y)) := by
        rw [hAX _ hy]
        have h : runTrans (e * (b * a)) y = runTrans (b * a) y :=
          congrArg (fun m => runTrans m y) hleft_ba
        rw [runTrans_mul] at h
        exact h.symm
      rw [h1, h2, hpt]
    exact Subtype.ext hval
  · -- degenerate case: `X` is constant in every coordinate, so it is a
    -- singleton and both products collapse to it
    have hall : ∀ x ∈ X, ∀ y ∈ X, x = y := by
      intro x hx y hy
      funext i
      have hi : i ∉ Jset X := fun hmem => hJ ⟨i, hmem⟩
      exact eq_on_compl_Jset hi hx hy
    have hval : a * b = b * a := by
      refine transMonoid_ext ?_
      intro z
      have h1 : runTrans (a * b) z ∈ X := mapsTo_fixFinset habs_ab z
      have h2 : runTrans (b * a) z ∈ X := mapsTo_fixFinset habs_ba z
      exact hall _ h1 _ h2
    exact Subtype.ext hval

/-- **S5 assembled through the constant-free interval route** — the statement
consumed by `LocalDivisorRoute.lean`. -/
theorem localUnitsCommute_nonCrossing_route (w : Nat) :
    LocalUnitsCommute (NonCrossing w) :=
  localUnitsCommute_of_cf_glue
    (cfLocalUnitsCommute_holds (intervalAntichainsCommuteCF_holds w))

end Internal
end AllenderOQ3
