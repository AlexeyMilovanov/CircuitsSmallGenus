import AllenderOQ3.Internal.LocalUnitsRealized
import AllenderOQ3.Internal.ComponentLemma
import AllenderOQ3.Internal.IntervalReduction
import AllenderOQ3.Internal.IntervalCountBridge
import AllenderOQ3.Internal.StartRank
import AllenderOQ3.Internal.AntichainRotation

/-!
# The constant-free interval route to S5 (reroute T0.1)

The strategy round of iteration 31 identified that the open leaf
`AntichainsCommute w` is stronger than what the verified paper proves: the
paper's geometry (`docs/localdivisor/…-minimal-algebraic-target…`, §§3–6) only
needs commutativity for antichains of **nonempty proper interval**
configurations under permutations realized by the **constant-free** submonoid.
This file installs that exact statement (`IntervalAntichainsCommuteCF`, the
reshaped open leaf S5''), and proves — fully, with no geometric input — the
stratification glue of paper §5:

* `cfLocalUnitsCommute_of_intervalAntichains` — given S5'' and the two
  component-lemma leaves T2a/T2b below, any two local units of an idempotent
  of `NonCrossingCF w` commute.  Route: the pieces of every configuration of
  `Fix e` are themselves `e`-fixed (T2b plus idempotence and injectivity);
  the local units act on the piece family `intervalFamily (fixFinset e)`,
  preserving its antichain strata (`bijOn_layerRest`); each stratum is either
  the singleton `{⊤}` or a top-free antichain of interval configurations,
  where S5'' applies; the strata cover the family, and a configuration is
  reconstructed from its pieces (`mem_intervalsOf_true_iff`), so the two
  actions commute on all of `Fix e`, hence — through the `e`-collapse — in
  the monoid.

Open leaves consumed here (see `docs/LOCAL_DIVISOR_PLAN.md` §6 and the
iteration-31 backlog):

* **T2a/T2b** — the component lemma, imported from `ComponentLemma.lean`,
  where the word level is proved and only the single-layer geometry is open;
* **T5** `localUnitsCommute_of_cf` — constant elimination (paper §6), sorried
  here;
* **S5''** `intervalAntichainsCommuteCF_holds` — the rotation geometry
  (paper §4, plan 6c), sorried here, consumed through this file's glue.
-/

set_option autoImplicit false

namespace AllenderOQ3
namespace Internal

attribute [local instance] Classical.propDecidable

variable {w : Nat}

/-! ## The reshaped open leaf -/

/-- A nonempty proper cyclic-interval configuration (`⊥` is excluded by
`IsIntervalConfig`, `⊤` explicitly). -/
def ProperIntervalConfig (y : Config w) : Prop :=
  IsIntervalConfig y ∧ y ≠ topConfig w

/-- **S5'' — the reshaped geometric leaf.**  Realized-by-constant-free
permutations of an antichain of nonempty proper interval configurations
commute, element-wise. -/
def IntervalAntichainsCommuteCF (w : Nat) : Prop :=
  ∀ L : Finset (Config w), (∀ y ∈ L, ProperIntervalConfig y) →
    (∀ x ∈ L, ∀ y ∈ L, x ≤ y → x = y) →
    ∀ m₁ m₂ : TransMonoid w, m₁ ∈ NonCrossingCF w → m₂ ∈ NonCrossingCF w →
      Set.BijOn (runTrans m₁) ↑L ↑L → Set.BijOn (runTrans m₂) ↑L ↑L →
      ∀ x ∈ L, runTrans m₂ (runTrans m₁ x) = runTrans m₁ (runTrans m₂ x)

/-! ## Consequences of T2 (`ComponentLemma.lean`) on a fixed-point set
(proved) -/

/-- Count invariance along a locally inverted trajectory. -/
theorem intervalCount_eq_of_inverse {m m' : TransMonoid w}
    (hm : m ∈ NonCrossingCF w) (hm' : m' ∈ NonCrossingCF w) {x : Config w}
    (hinv : runTrans m' (runTrans m x) = x) :
    intervalCount (runTrans m x) = intervalCount x := by
  have h1 := intervalCount_le_of_mem_nonCrossingCF hm x
  have h2 := intervalCount_le_of_mem_nonCrossingCF hm' (runTrans m x)
  rw [hinv] at h2
  omega

/-- **Pieces of an `e`-fixed configuration are `e`-fixed** (the "small point"
of paper §5): `runTrans e` permutes the pieces, and an idempotent injective
self-map of a finite set is the identity. -/
theorem piece_mem_fixFinset {e : TransMonoid w} (he : e ∈ NonCrossingCF w)
    (hee : e * e = e) {x : Config w} (hx : x ∈ fixFinset e) {I : Config w}
    (hI : I ∈ intervalsOf x) : I ∈ fixFinset e := by
  rw [mem_fixFinset] at hx ⊢
  have hcnt : intervalCount (runTrans e x) = intervalCount x := by rw [hx]
  have himg := intervalsOf_image_of_mem_nonCrossingCF he hcnt
  rw [hx] at himg
  have hinj : Set.InjOn (runTrans e) ↑(intervalsOf x) :=
    Finset.injOn_of_card_image_eq (by rw [← himg])
  have hidem : ∀ y : Config w, runTrans e (runTrans e y) = runTrans e y := by
    intro y
    have h : runTrans (e * e) y = runTrans e y := by rw [hee]
    rwa [runTrans_mul] at h
  have hmemI : runTrans e I ∈ intervalsOf x := by
    rw [himg]
    exact Finset.mem_image_of_mem _ hI
  exact hinj (Finset.mem_coe.mpr hmemI) (Finset.mem_coe.mpr hI) (hidem I)

/-- The piece family of a fixed-point set sits inside the fixed-point set. -/
theorem intervalFamily_subset_fixFinset {e : TransMonoid w}
    (he : e ∈ NonCrossingCF w) (hee : e * e = e) :
    intervalFamily (fixFinset e) ⊆ fixFinset e := by
  intro I hI
  obtain ⟨x, hx, hIx⟩ := mem_intervalFamily.mp hI
  exact piece_mem_fixFinset he hee hx hIx

section LocalUnits

variable {e a a' : TransMonoid w}

/-- A local unit maps the piece family into itself. -/
theorem mapsTo_intervalFamily (he : e ∈ NonCrossingCF w) (ha : a ∈ NonCrossingCF w)
    (ha' : a' ∈ NonCrossingCF w) (hee : e * e = e) (hae : a * e = a)
    (haa' : a * a' = e) {I : Config w} (hI : I ∈ intervalFamily (fixFinset e)) :
    runTrans a I ∈ intervalFamily (fixFinset e) := by
  obtain ⟨x, hx, hIx⟩ := mem_intervalFamily.mp hI
  have hcnt : intervalCount (runTrans a x) = intervalCount x :=
    intervalCount_eq_of_inverse ha ha' (runTrans_local_inv haa' hx)
  have himg := intervalsOf_image_of_mem_nonCrossingCF ha hcnt
  refine mem_intervalFamily.mpr ⟨runTrans a x, mapsTo_fixFinset hae x, ?_⟩
  rw [himg]
  exact Finset.mem_image_of_mem _ hIx

/-- A local unit permutes the piece family. -/
theorem bijOn_intervalFamily_of_localUnit (he : e ∈ NonCrossingCF w)
    (ha : a ∈ NonCrossingCF w) (ha' : a' ∈ NonCrossingCF w) (hee : e * e = e)
    (hae : a * e = a) (ha'e : a' * e = a') (haa' : a * a' = e) (ha'a : a' * a = e) :
    Set.BijOn (runTrans a) ↑(intervalFamily (fixFinset e))
      ↑(intervalFamily (fixFinset e)) := by
  have hsub := intervalFamily_subset_fixFinset he hee
  refine ⟨?_, ?_, ?_⟩
  · intro I hI
    exact Finset.mem_coe.mpr
      (mapsTo_intervalFamily he ha ha' hee hae haa' (Finset.mem_coe.mp hI))
  · intro I hI J hJ hIJ
    have hIe : I ∈ fixFinset e := hsub (Finset.mem_coe.mp hI)
    have hJe : J ∈ fixFinset e := hsub (Finset.mem_coe.mp hJ)
    have h1 : runTrans a' (runTrans a I) = I := runTrans_local_inv haa' hIe
    have h2 : runTrans a' (runTrans a J) = J := runTrans_local_inv haa' hJe
    rw [← h1, ← h2, hIJ]
  · intro J hJ
    have hJ' : J ∈ intervalFamily (fixFinset e) := Finset.mem_coe.mp hJ
    have hJe : J ∈ fixFinset e := hsub hJ'
    refine ⟨runTrans a' J, ?_, ?_⟩
    · exact Finset.mem_coe.mpr
        (mapsTo_intervalFamily he ha' ha hee ha'e ha'a hJ')
    · exact runTrans_local_inv (a := a') (a' := a) ha'a hJe

end LocalUnits

/-! ## Reconstruction from pieces -/

/-- A configuration is determined by its piece set. -/
theorem config_eq_of_intervalsOf_eq {y z : Config w}
    (h : intervalsOf y = intervalsOf z) : y = z := by
  funext j
  have hiff : y j = true ↔ z j = true := by
    rw [mem_intervalsOf_true_iff (x := y), h, ← mem_intervalsOf_true_iff (x := z)]
  cases hy : y j with
  | true =>
    exact (hiff.mp hy).symm
  | false =>
    cases hz : z j with
    | true =>
      rw [hiff.mpr hz] at hy
      exact absurd hy (by simp)
    | false => rfl

/-! ## The stratification glue (paper §5, proved) -/

/-- **Local units of a constant-free idempotent commute, given S5'' and T2.**
The heart of the reroute: element-wise commutation on the piece family via the
strata, then reconstruction, then the `e`-collapse to the monoid. -/
theorem cfLocalUnitsCommute_of_intervalAntichains
    (hgeo : IntervalAntichainsCommuteCF w)
    {e a a' b b' : TransMonoid w}
    (he : e ∈ NonCrossingCF w) (ha : a ∈ NonCrossingCF w) (ha' : a' ∈ NonCrossingCF w)
    (hb : b ∈ NonCrossingCF w) (hb' : b' ∈ NonCrossingCF w)
    (hee : e * e = e)
    (hea : e * a = a) (hae : a * e = a) (hea' : e * a' = a') (ha'e : a' * e = a')
    (haa' : a * a' = e) (ha'a : a' * a = e)
    (heb : e * b = b) (hbe : b * e = b) (heb' : e * b' = b') (hb'e : b' * e = b')
    (hbb' : b * b' = e) (hb'b : b' * b = e) :
    a * b = b * a := by
  set F : Finset (Config w) := intervalFamily (fixFinset e) with hF
  have hsub : F ⊆ fixFinset e := intervalFamily_subset_fixFinset he hee
  have hbija : Set.BijOn (runTrans a) ↑F ↑F :=
    bijOn_intervalFamily_of_localUnit he ha ha' hee hae ha'e haa' ha'a
  have hbijb : Set.BijOn (runTrans b) ↑F ↑F :=
    bijOn_intervalFamily_of_localUnit he hb hb' hee hbe hb'e hbb' hb'b
  have hmona : Monotone (runTrans a) := monotone_of_mem_nonCrossingCF ha
  have hmonb : Monotone (runTrans b) := monotone_of_mem_nonCrossingCF hb
  -- element-wise commutation on every antichain stratum of the family
  have hstrata : ∀ (j : Nat), ∀ I ∈ minLayer F j,
      runTrans b (runTrans a I) = runTrans a (runTrans b I) := by
    intro j
    by_cases htop : topConfig w ∈ minLayer F j
    · -- the stratum is the singleton {⊤}, fixed by both actions
      intro I hI
      have hIle : I ≤ topConfig w := by
        intro i
        cases hIi : I i with
        | true => simp [topConfig]
        | false => simp
      have hItop : I = topConfig w := minLayer_antichain j hI htop hIle
      rw [hItop, runTrans_topConfig_of_mem_nonCrossingCF ha,
        runTrans_topConfig_of_mem_nonCrossingCF hb,
        runTrans_topConfig_of_mem_nonCrossingCF ha]
    · -- a top-free antichain of interval configurations: apply S5''
      have hbijaL : Set.BijOn (runTrans a) ↑(minLayer F j) ↑(minLayer F j) :=
        (bijOn_layerRest hmona hbija j).2
      have hbijbL : Set.BijOn (runTrans b) ↑(minLayer F j) ↑(minLayer F j) :=
        (bijOn_layerRest hmonb hbijb j).2
      intro I hI
      refine hgeo (minLayer F j) ?_ ?_ a b ha hb hbijaL hbijbL I hI
      · intro y hy
        refine ⟨isIntervalConfig_of_mem_intervalFamily (minLayer_subset j hy), ?_⟩
        intro hytop
        rw [hytop] at hy
        exact htop hy
      · intro x hx y hy hxy
        exact minLayer_antichain j hx hy hxy
  -- commutation on the whole family
  have hfam : ∀ I ∈ F, runTrans b (runTrans a I) = runTrans a (runTrans b I) := by
    intro I hI
    obtain ⟨j, -, hj⟩ := exists_mem_minLayer hI
    exact hstrata j I hj
  -- commutation on the fixed-point set, by reconstruction from pieces
  have hX : ∀ x ∈ fixFinset e,
      runTrans b (runTrans a x) = runTrans a (runTrans b x) := by
    intro x hx
    have hax : runTrans a x ∈ fixFinset e := mapsTo_fixFinset hae x
    have hbx : runTrans b x ∈ fixFinset e := mapsTo_fixFinset hbe x
    have hcnta : intervalCount (runTrans a x) = intervalCount x :=
      intervalCount_eq_of_inverse ha ha' (runTrans_local_inv haa' hx)
    have hcntb : intervalCount (runTrans b x) = intervalCount x :=
      intervalCount_eq_of_inverse hb hb' (runTrans_local_inv hbb' hx)
    have hcntba : intervalCount (runTrans b (runTrans a x))
        = intervalCount (runTrans a x) :=
      intervalCount_eq_of_inverse hb hb' (runTrans_local_inv hbb' hax)
    have hcntab : intervalCount (runTrans a (runTrans b x))
        = intervalCount (runTrans b x) :=
      intervalCount_eq_of_inverse ha ha' (runTrans_local_inv haa' hbx)
    apply config_eq_of_intervalsOf_eq
    have h1 : intervalsOf (runTrans b (runTrans a x))
        = (intervalsOf (runTrans a x)).image (runTrans b) :=
      intervalsOf_image_of_mem_nonCrossingCF hb hcntba
    have h2 : intervalsOf (runTrans a x) = (intervalsOf x).image (runTrans a) :=
      intervalsOf_image_of_mem_nonCrossingCF ha hcnta
    have h3 : intervalsOf (runTrans a (runTrans b x))
        = (intervalsOf (runTrans b x)).image (runTrans a) :=
      intervalsOf_image_of_mem_nonCrossingCF ha hcntab
    have h4 : intervalsOf (runTrans b x) = (intervalsOf x).image (runTrans b) :=
      intervalsOf_image_of_mem_nonCrossingCF hb hcntb
    rw [h1, h2, h3, h4, Finset.image_image, Finset.image_image]
    refine Finset.image_congr ?_
    intro I hI
    exact hfam I (mem_intervalFamily.mpr ⟨x, hx, Finset.mem_coe.mp hI⟩)
  -- the `e`-collapse: from commutation on `Fix e` to the monoid identity
  refine transMonoid_ext ?_
  intro y
  have hy : runTrans e y ∈ fixFinset e := runTrans_mem_fixFinset hee y
  have hAcollapse : runTrans a (runTrans e y) = runTrans a y := by
    have h : runTrans (e * a) y = runTrans a y := by rw [hea]
    rwa [runTrans_mul] at h
  have hBcollapse : runTrans b (runTrans e y) = runTrans b y := by
    have h : runTrans (e * b) y = runTrans b y := by rw [heb]
    rwa [runTrans_mul] at h
  have hkey := hX _ hy
  rw [hAcollapse, hBcollapse] at hkey
  change runTrans (a * b) y = runTrans (b * a) y
  rw [runTrans_mul, runTrans_mul]
  exact hkey

/-! ## The constant-elimination leaf (T5) and the assembled reduction -/

/-- Local units of `NonCrossingCF w` commute. -/
def CFLocalUnitsCommute (w : Nat) : Prop :=
  ∀ e a a' b b' : TransMonoid w,
    e ∈ NonCrossingCF w → a ∈ NonCrossingCF w → a' ∈ NonCrossingCF w →
    b ∈ NonCrossingCF w → b' ∈ NonCrossingCF w →
    e * e = e →
    e * a = a → a * e = a → e * a' = a' → a' * e = a' → a * a' = e → a' * a = e →
    e * b = b → b * e = b → e * b' = b' → b' * e = b' → b * b' = e → b' * b = e →
    a * b = b * a

/-- S5'' plus T2 give the constant-free case. -/
theorem cfLocalUnitsCommute_holds (hgeo : IntervalAntichainsCommuteCF w) :
    CFLocalUnitsCommute w := by
  intro e a a' b b' he ha ha' hb hb' hee hea hae hea' ha'e haa' ha'a heb hbe heb' hb'e hbb' hb'b
  exact cfLocalUnitsCommute_of_intervalAntichains hgeo he ha ha' hb hb' hee
    hea hae hea' ha'e haa' ha'a heb hbe heb' hb'e hbb' hb'b

/- T5 (constant elimination) lives in `ConstantElimination.lean`: the
conjugation glue `localUnitsCommute_of_cf_glue` is proved there, with two
constructive leaves (`exists_clamp_fill_layers`,
`mem_nonCrossingCF_of_no_constant_output`). -/

/-- **S5'' (open leaf): the rotation geometry.**  Realized-by-constant-free
permutations of a top-free antichain of interval configurations commute.
Paper §4 / plan 6c: the arcs from an interval form a contiguous block of the
common arc word; the blocks form an antichain at arc level; the
first-true-target map is weakly cyclic-order-preserving of degree one and
sends leading cuts to output starts; distinct starts
(`startOf_ne_of_incomparable`) force a rotation, and rotations of a fixed
cyclic list commute; word extension keeps intermediate images nonempty proper
intervals.  Numerical anchor: zero exceptions over 14,238,180 instances on
the exact `w = 4` monoid. -/
theorem intervalAntichainsCommuteCF_holds (w : Nat) :
    IntervalAntichainsCommuteCF w := by
  intro L hL hanti m₁ m₂ hm₁ hm₂ hbij₁ hbij₂ x hx
  -- `0 < w` is witnessed by any member of `L` (its canonical start lives in `Fin w`).
  have hw : 0 < w := by
    have h := (hL x hx).1
    unfold IsIntervalConfig IsIntervalPiece at h
    obtain ⟨start, _, _, _⟩ := h
    have := start.isLt; omega
  have hInt : ∀ y ∈ L, IsIntervalConfig y := fun y hy => (hL y hy).1
  -- B2: each realized permutation is a rotation of the start cyclic order.
  have hrot₁ : IsStartRotation hw L (runTrans m₁) :=
    isStartRotation_of_mem_nonCrossingCF hw hm₁ hL hanti hbij₁
  have hrot₂ : IsStartRotation hw L (runTrans m₂) :=
    isStartRotation_of_mem_nonCrossingCF hw hm₂ hL hanti hbij₂
  -- B3 + B4: two rotations of one finite cyclic order commute element-wise.
  exact startRotations_commute hw hInt hanti hrot₂ hrot₁ hbij₂.1 hbij₁.1 hx

end Internal
end AllenderOQ3
