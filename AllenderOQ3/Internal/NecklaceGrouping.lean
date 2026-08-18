import AllenderOQ3.Internal.FirstReturnChain
import AllenderOQ3.Internal.OrbitContiguity
import AllenderOQ3.Internal.VertexCorner

set_option autoImplicit false

/-!
# The target fibres of a necklace are cyclically contiguous

This closes the target grouping obligation of `CutNecklace`.

The necklace step out of an arc `e` is computed at the *target* vertex of `e`:
reversing `e` gives a descending dart `downDart e` there, and if its rotation
successor also descends (a max corner) then, by `arcPerm_of_maxCorner`, the
necklace moves to another arc with the *same* target.  So an arc can only
leave its target fibre at a down→up corner of the rotation at that vertex, and
`downUp_corner_unique` says a genus-zero rotation of a properly layered
st-graph has at most one such corner per vertex.

A fibre with at most one exit is a cyclic block of the orbit word
(`cyclicContiguous_orbitList`), which is exactly
`necklace_arcTarget_cyclicContiguous`.
-/

namespace AllenderOQ3.Internal

variable {n : Nat} {c : ADRCircuit n}

/-- The descending dart at the head of a transition arc. -/
def downDart {ell : Nat} (e : TransitionArc c ell) : CircuitDart c :=
  dartReverse c (upOfArc e).1

theorem downDart_source {ell : Nat} (e : TransitionArc c ell) :
    (downDart e).source = e.1.2 := rfl

theorem downDart_target {ell : Nat} (e : TransitionArc c ell) :
    (downDart e).target = e.1.1 := rfl

theorem downDart_layer {ell : Nat} (e : TransitionArc c ell) :
    c.layer (downDart e).target = ell := e.2.2.1

theorem downDart_not_up (hpl : ProperLayered c) {ell : Nat}
    (e : TransitionArc c ell) : dartIsUp (downDart e) = false := by
  rw [Bool.eq_false_iff]
  intro hup
  have h : c.edge e.1.2 e.1.1 = true := hup
  have h1 := hpl _ _ h
  have h2 := e.2.2.1
  have h3 := e.2.2.2
  omega

theorem downDart_injective {ell : Nat} {e1 e2 : TransitionArc c ell}
    (h : downDart e1 = downDart e2) : e1 = e2 := by
  have h1 : ((downDart e1).1.2, (downDart e1).1.1)
      = ((downDart e2).1.2, (downDart e2).1.1) := by rw [h]
  exact Subtype.ext h1

/-- Level-generalized form of `arcPerm_of_maxCorner`. -/
theorem arcPerm_of_maxCorner' (hpl : ProperLayered c) (r : OrientableRotation c)
    {ell : Nat} (d : CircuitDart c)
    (h1 : dartIsUp d = false) (h2 : dartIsUp (r.rotation d) = false)
    (hlv : c.layer d.target = ell)
    (hc1 : isCutDart c ell (dartReverse c d) = true)
    (hu1 : c.layer (dartReverse c d).source = ell)
    (hc2 : isCutDart c ell (r.rotation d) = true)
    (hu2 : c.layer ((cutDartReverse c ell) ⟨r.rotation d, hc2⟩).1.source = ell) :
    (arcPerm hpl r ell) (arcOfUpDart hpl ⟨dartReverse c d, hc1⟩ hu1)
      = arcOfUpDart hpl ((cutDartReverse c ell) ⟨r.rotation d, hc2⟩) hu2 := by
  subst hlv
  exact arcPerm_of_maxCorner hpl r d h1 h2

/-- **The necklace stays at a max corner.**  If the rotation successor of the
descending dart of `e` also descends, the next arc on the necklace has the same
target as `e`. -/
theorem arcTarget_arcPerm_of_maxCorner (hpl : ProperLayered c)
    (r : OrientableRotation c) {ell : Nat} (e : TransitionArc c ell)
    (h2 : dartIsUp (r.rotation (downDart e)) = false) :
    arcTarget ((arcPerm hpl r ell) e) = arcTarget e := by
  have h1 : dartIsUp (downDart e) = false := downDart_not_up hpl e
  have hlv : c.layer (downDart e).target = ell := downDart_layer e
  have hc1 : isCutDart c ell (dartReverse c (downDart e)) = true := (upOfArc e).2
  have hu1 : c.layer (dartReverse c (downDart e)).source = ell := e.2.2.1
  have hc2 : isCutDart c ell (r.rotation (downDart e)) = true := by
    have hc2' := rotDart_cut_of_maxCorner hpl r (downDart e) h1 h2
    rw [isCutDart, beq_iff_eq] at hc2' ⊢
    rw [hc2', hlv]
  have hu2 : c.layer ((cutDartReverse c ell)
      ⟨r.rotation (downDart e), hc2⟩).1.source = ell := by
    have hs := congrArg c.layer (r.preservesSource (downDart e))
    have hd := layer_of_not_dartIsUp hpl (r.rotation (downDart e)) h2
    have hd0 := layer_of_not_dartIsUp hpl (downDart e) h1
    change c.layer (r.rotation (downDart e)).target = ell
    omega
  have hkey := arcPerm_of_maxCorner' hpl r (downDart e) h1 h2 hlv hc1 hu1 hc2 hu2
  have harg : arcOfUpDart hpl ⟨dartReverse c (downDart e), hc1⟩ hu1 = e :=
    Subtype.ext rfl
  rw [harg] at hkey
  rw [hkey]
  refine Subtype.ext ?_
  change (r.rotation (downDart e)).source = e.1.2
  rw [r.preservesSource]
  rfl

/-- An arc leaving its target fibre sits at a down→up corner. -/
theorem downUp_of_arcTarget_exit (hpl : ProperLayered c)
    (r : OrientableRotation c) {ell : Nat} (e : TransitionArc c ell)
    (hex : arcTarget ((arcPerm hpl r ell) e) ≠ arcTarget e) :
    dartIsUp (r.rotation (downDart e)) = true := by
  cases h : dartIsUp (r.rotation (downDart e)) with
  | false => exact absurd (arcTarget_arcPerm_of_maxCorner hpl r e h) hex
  | true => rfl

/-- **At most one exit per target fibre.** -/
theorem arcTarget_exit_unique (hpl : ProperLayered c)
    (hsrc : ∃! s, IsGraphSource c s) (hsnk : ∃! t, IsGraphSink c t)
    (r : OrientableRotation c) (hg : rotationGenus r = 0) {ell : Nat}
    (e1 e2 : TransitionArc c ell) (hkey : arcTarget e1 = arcTarget e2)
    (hex1 : arcTarget ((arcPerm hpl r ell) e1) ≠ arcTarget e1)
    (hex2 : arcTarget ((arcPerm hpl r ell) e2) ≠ arcTarget e2) :
    e1 = e2 := by
  have hv : e1.1.2 = e2.1.2 := congrArg Subtype.val hkey
  refine downDart_injective ?_
  refine downUp_corner_unique hpl hsrc hsnk r hg
    (downDart_source e1) (downDart_not_up hpl e1)
    (downUp_of_arcTarget_exit hpl r e1 hex1) ?_ (downDart_not_up hpl e2)
    (downUp_of_arcTarget_exit hpl r e2 hex2)
  rw [downDart_source e2, hv]

/-- **Target fibres do not interleave along the necklace.**  Reading the
incoming arcs of transition `ell` in necklace order, all arcs into a common
target vertex appear as one contiguous block of the *cyclic* word. -/
theorem necklace_arcTarget_cyclicContiguous (hpl : ProperLayered c)
    (r : OrientableRotation c) (hg : rotationGenus r = 0)
    (hsrc : ∃! s, IsGraphSource c s) (hsnk : ∃! t, IsGraphSink c t)
    (ell : Nat) :
    CyclicContiguous arcTarget (necklaceWord hpl r ell) := by
  unfold necklaceWord
  split
  · refine cyclicContiguous_orbitList (arcPerm hpl r ell) _ arcTarget ?_
    intro x _ y _ hxy hx hy
    exact arcTarget_exit_unique hpl hsrc hsnk r hg x y hxy hx hy
  · exact ⟨[], ⟨[], [], rfl, rfl⟩, fun x t y hsub _ => absurd hsub (by simp)⟩

/-! ## The source side

The mirror argument at the tail of an arc.  By `arcPerm_of_minCorner` the
necklace walks the out-fan of a vertex *backwards* along the rotation, so an
arc leaves its source fibre exactly when the rotation predecessor of its
ascending dart descends -- again a down→up corner, again unique. -/

/-- The rotation predecessor of the ascending dart of an arc. -/
def prevDart (r : OrientableRotation c) {ell : Nat} (e : TransitionArc c ell) :
    CircuitDart c :=
  r.rotation.symm (upOfArc e).1

theorem prevDart_rot (r : OrientableRotation c) {ell : Nat}
    (e : TransitionArc c ell) : r.rotation (prevDart r e) = (upOfArc e).1 :=
  r.rotation.apply_symm_apply _

theorem prevDart_source (r : OrientableRotation c) {ell : Nat}
    (e : TransitionArc c ell) : (prevDart r e).source = e.1.1 := by
  have h := r.preservesSource (prevDart r e)
  rw [prevDart_rot] at h
  exact h.symm

theorem prevDart_rot_up {ell : Nat} (r : OrientableRotation c)
    (e : TransitionArc c ell) : dartIsUp (r.rotation (prevDart r e)) = true := by
  rw [prevDart_rot]
  exact e.2.1

theorem prevDart_injective {ell : Nat} (r : OrientableRotation c)
    {e1 e2 : TransitionArc c ell} (h : prevDart r e1 = prevDart r e2) :
    e1 = e2 := by
  have h1 : (upOfArc e1).1 = (upOfArc e2).1 := by
    rw [← prevDart_rot r e1, ← prevDart_rot r e2, h]
  exact Subtype.ext (congrArg (fun d : CircuitDart c => d.1) h1)

/-- **The necklace stays at a min corner.**  If the rotation predecessor of the
ascending dart of `e` also ascends, the next arc on the necklace has the same
source as `e`. -/
theorem arcSource_arcPerm_of_minCorner (hpl : ProperLayered c)
    (hsrc : ∃! s, IsGraphSource c s) (hsnk : ∃! t, IsGraphSink c t)
    (r : OrientableRotation c) (hg : rotationGenus r = 0) {ell : Nat}
    (e : TransitionArc c ell) (h1 : dartIsUp (prevDart r e) = true) :
    arcSource ((arcPerm hpl r ell) e) = arcSource e := by
  have h2 : dartIsUp (r.rotation (prevDart r e)) = true := prevDart_rot_up r e
  have hlv : c.layer (prevDart r e).source = ell := by
    rw [prevDart_source]
    exact e.2.2.1
  have hcrot : isCutDart c ell (r.rotation (prevDart r e)) = true := by
    rw [prevDart_rot]
    exact (upOfArc e).2
  have hsrot : c.layer (r.rotation (prevDart r e)).source = ell := by
    rw [prevDart_rot]
    exact e.2.2.1
  have hcd : isCutDart c ell (prevDart r e) = true := by
    rw [isCutDart, beq_iff_eq]
    have hup := layer_of_dartIsUp hpl (prevDart r e) h1
    omega
  have hkey := arcPerm_of_minCorner' hpl hsrc hsnk r hg (prevDart r e) h1 h2
    hlv hcrot hsrot hcd
  have harg : arcOfUpDart hpl ⟨r.rotation (prevDart r e), hcrot⟩ hsrot = e :=
    Subtype.ext (congrArg (fun d : CircuitDart c => d.1) (prevDart_rot r e))
  rw [harg] at hkey
  rw [hkey]
  refine Subtype.ext ?_
  change (prevDart r e).1.1 = e.1.1
  exact prevDart_source r e

/-- An arc leaving its source fibre sits at a down→up corner. -/
theorem downUp_of_arcSource_exit (hpl : ProperLayered c)
    (hsrc : ∃! s, IsGraphSource c s) (hsnk : ∃! t, IsGraphSink c t)
    (r : OrientableRotation c) (hg : rotationGenus r = 0) {ell : Nat}
    (e : TransitionArc c ell)
    (hex : arcSource ((arcPerm hpl r ell) e) ≠ arcSource e) :
    dartIsUp (prevDart r e) = false := by
  cases h : dartIsUp (prevDart r e) with
  | false => rfl
  | true =>
    exact absurd (arcSource_arcPerm_of_minCorner hpl hsrc hsnk r hg e h) hex

/-- **At most one exit per source fibre.** -/
theorem arcSource_exit_unique (hpl : ProperLayered c)
    (hsrc : ∃! s, IsGraphSource c s) (hsnk : ∃! t, IsGraphSink c t)
    (r : OrientableRotation c) (hg : rotationGenus r = 0) {ell : Nat}
    (e1 e2 : TransitionArc c ell) (hkey : arcSource e1 = arcSource e2)
    (hex1 : arcSource ((arcPerm hpl r ell) e1) ≠ arcSource e1)
    (hex2 : arcSource ((arcPerm hpl r ell) e2) ≠ arcSource e2) :
    e1 = e2 := by
  have hv : e1.1.1 = e2.1.1 := congrArg Subtype.val hkey
  refine prevDart_injective r ?_
  refine downUp_corner_unique hpl hsrc hsnk r hg
    (prevDart_source r e1)
    (downUp_of_arcSource_exit hpl hsrc hsnk r hg e1 hex1) (prevDart_rot_up r e1)
    ?_ (downUp_of_arcSource_exit hpl hsrc hsnk r hg e2 hex2) (prevDart_rot_up r e2)
  rw [prevDart_source r e2, hv]

/-- **Source fibres do not interleave along the necklace.**  Reading the
outgoing arcs of transition `ell` in necklace order, all arcs out of a common
source vertex appear as one contiguous block of the *cyclic* word. -/
theorem necklace_arcSource_cyclicContiguous (hpl : ProperLayered c)
    (r : OrientableRotation c) (hg : rotationGenus r = 0)
    (hsrc : ∃! s, IsGraphSource c s) (hsnk : ∃! t, IsGraphSink c t)
    (ell : Nat) :
    CyclicContiguous arcSource (necklaceWord hpl r ell) := by
  unfold necklaceWord
  split
  · refine cyclicContiguous_orbitList (arcPerm hpl r ell) _ arcSource ?_
    intro x _ y _ hxy hx hy
    exact arcSource_exit_unique hpl hsrc hsnk r hg x y hxy hx hy
  · exact ⟨[], ⟨[], [], rfl, rfl⟩, fun x t y hsub _ => absurd hsub (by simp)⟩

/-- **The target grouping obligation.**  Because the layer listing above
transition `ell` is by construction
`listingOfPrefix ((necklaceWord … ell).map arcTarget)`
(`necklaceLayerOrder_succ`), the grouping follows from
`necklace_arcTarget_cyclicContiguous` through
`groupedAlong_listingOfPrefix_of_cyclicContiguous`, which rotates the listing
by exactly the amount that the word is rotated. -/
theorem necklace_groupedAlong_target (hpl : ProperLayered c)
    (r : OrientableRotation c) (hg : rotationGenus r = 0)
    (hsrc : ∃! s, IsGraphSource c s) (hsnk : ∃! t, IsGraphSink c t)
    (ell : Nat) :
    ∃ (targetList : List (LayerVertex c (ell + 1)))
      (wordT : List (TransitionArc c ell)),
      CyclicRotation (necklaceLayerOrder hpl r (ell + 1)).entries targetList ∧
      CyclicRotation (necklaceWord hpl r ell) wordT ∧
      GroupedAlong arcTarget targetList wordT := by
  obtain ⟨ls, v, hls, hv, hgr⟩ :=
    groupedAlong_listingOfPrefix_of_cyclicContiguous arcTarget
      (necklaceWord hpl r ell)
      (necklace_arcTarget_cyclicContiguous hpl r hg hsrc hsnk ell)
  refine ⟨ls, v, ?_, hv, hgr⟩
  rw [necklaceLayerOrder_succ hpl r ell]
  exact hls

/-!
## The source grouping obligation and completeness

The source grouping obligation above the bottom layer, and the completeness
obligation, both need the cross-layer coherence of the necklaces; they are
proved in `AllenderOQ3.Internal.NecklaceCross`.
-/

end AllenderOQ3.Internal
