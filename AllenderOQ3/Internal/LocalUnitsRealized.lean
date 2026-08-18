import AllenderOQ3.Internal.LayerProduct
import AllenderOQ3.Internal.LocalUnitsCommute

/-!
# Local units act by realized permutations of a fixed-point set

This file reduces S5 (`localUnitsCommute_nonCrossing`, the abelianness of the
local groups of `NonCrossing w`) to a statement about the *realized permutation
groups* of `RealizedPerms.lean` / `LayerProduct.lean`.

Let `e` be an idempotent of `NonCrossing w` and let `a` be a unit of the local
monoid at `e`, with local inverse `a'`.  Then `runTrans a` restricts to a
bijection of the finite set `fixFinset e = {x | runTrans e x = x}`, with inverse
the restriction of `runTrans a'` (`localPerm`); the resulting permutation is
realized by `a` itself, hence lies in `realizedSubgroup (fixFinset e)`.
Conversely `a = e * a` means that the action of `a` on all of `Config w`
factors through `runTrans e`, so an equality of the two restricted permutations
propagates back to an equality in the monoid.  Therefore:

* `localUnitsCommute_of_realizedComm` — if every realized permutation group is
  commutative, then `LocalUnitsCommute (NonCrossing w)`;
* `localUnitsCommute_of_antichainsCommute` — combined with
  `realizedSubgroup_comm_of_antichains` (`LayerProduct.lean`), commutativity of
  the realized permutation groups of *antichains* already suffices;
* `localUnitsCommute_of_antichainsCyclic` — the same from `AntichainsCyclic`.

So S5 is now a consequence of the purely geometric statement `AntichainsCommute
w`; no local-divisor or Green-relation input is left in it.  Nothing here
asserts `AntichainsCommute w` itself — that is the content of stages 6b–6c of
`docs/LOCAL_DIVISOR_PLAN.md`.

Everything here is `sorry`-free.
-/

set_option autoImplicit false

namespace AllenderOQ3
namespace Internal

attribute [local instance] Classical.propDecidable

variable {w : Nat}

/-! ## The fixed-point set of a transition -/

/-- The configurations fixed by a transition, as a `Finset`. -/
noncomputable def fixFinset (e : TransMonoid w) : Finset (Config w) :=
  Finset.univ.filter (fun x => runTrans e x = x)

theorem mem_fixFinset {e : TransMonoid w} {x : Config w} :
    x ∈ fixFinset e ↔ runTrans e x = x := by
  simp [fixFinset]

/-- For an idempotent `e`, the image of `runTrans e` lands in `fixFinset e`. -/
theorem runTrans_mem_fixFinset {e : TransMonoid w} (hee : e * e = e) (x : Config w) :
    runTrans e x ∈ fixFinset e := by
  rw [mem_fixFinset]
  have h : runTrans (e * e) x = runTrans e x := by rw [hee]
  rwa [runTrans_mul] at h

/-! ## A local unit permutes the fixed-point set -/

section LocalUnit

variable {e a a' : TransMonoid w}

/-- An element absorbed by `e` on the right lands in `fixFinset e`. -/
theorem mapsTo_fixFinset (hae : a * e = a) (x : Config w) :
    runTrans a x ∈ fixFinset e := by
  rw [mem_fixFinset]
  have h : runTrans (a * e) x = runTrans a x := by rw [hae]
  rwa [runTrans_mul] at h

/-- On `fixFinset e`, a local inverse really inverts. -/
theorem runTrans_local_inv (haa' : a * a' = e) {x : Config w} (hx : x ∈ fixFinset e) :
    runTrans a' (runTrans a x) = x := by
  rw [mem_fixFinset] at hx
  have h : runTrans (a * a') x = runTrans e x := by rw [haa']
  rw [runTrans_mul] at h
  rw [h, hx]

/-- **The permutation of `fixFinset e` induced by a local unit at `e`.** -/
noncomputable def localPerm (e a a' : TransMonoid w) (hae : a * e = a) (ha'e : a' * e = a')
    (haa' : a * a' = e) (ha'a : a' * a = e) : Equiv.Perm {x // x ∈ fixFinset e} where
  toFun x := ⟨runTrans a x.val, mapsTo_fixFinset hae x.val⟩
  invFun x := ⟨runTrans a' x.val, mapsTo_fixFinset ha'e x.val⟩
  left_inv x := Subtype.ext (runTrans_local_inv haa' x.2)
  right_inv x := Subtype.ext (runTrans_local_inv ha'a x.2)

@[simp] theorem localPerm_apply (hae : a * e = a) (ha'e : a' * e = a')
    (haa' : a * a' = e) (ha'a : a' * a = e) (x : {x // x ∈ fixFinset e}) :
    (localPerm e a a' hae ha'e haa' ha'a x).val = runTrans a x.val := rfl

/-- The induced permutation is realized, by the local unit itself. -/
theorem realizedPerm_localPerm (ha : a ∈ NonCrossing w) (hae : a * e = a) (ha'e : a' * e = a')
    (haa' : a * a' = e) (ha'a : a' * a = e) :
    RealizedPerm (fixFinset e) (localPerm e a a' hae ha'e haa' ha'a) :=
  ⟨a, ha, fun _ => rfl⟩

end LocalUnit

/-! ## The reduction of S5 -/

/-- **S5 follows from commutativity of the realized permutation groups.** -/
theorem localUnitsCommute_of_realizedComm
    (h : ∀ (S : Finset (Config w)) (p q : realizedSubgroup S), p * q = q * p) :
    LocalUnitsCommute (NonCrossing w) := by
  intro E A A' B B' hEE hEA hAE hEA' hA'E hAA' hA'A hEB hBE hEB' hB'E hBB' hB'B
  have hee : E.val * E.val = E.val := congrArg Subtype.val hEE
  have hea : E.val * A.val = A.val := congrArg Subtype.val hEA
  have hae : A.val * E.val = A.val := congrArg Subtype.val hAE
  have ha'e : A'.val * E.val = A'.val := congrArg Subtype.val hA'E
  have haa' : A.val * A'.val = E.val := congrArg Subtype.val hAA'
  have ha'a : A'.val * A.val = E.val := congrArg Subtype.val hA'A
  have heb : E.val * B.val = B.val := congrArg Subtype.val hEB
  have hbe : B.val * E.val = B.val := congrArg Subtype.val hBE
  have hb'e : B'.val * E.val = B'.val := congrArg Subtype.val hB'E
  have hbb' : B.val * B'.val = E.val := congrArg Subtype.val hBB'
  have hb'b : B'.val * B.val = E.val := congrArg Subtype.val hB'B
  set pa : Equiv.Perm {x // x ∈ fixFinset E.val} :=
    localPerm E.val A.val A'.val hae ha'e haa' ha'a with hpa
  set pb : Equiv.Perm {x // x ∈ fixFinset E.val} :=
    localPerm E.val B.val B'.val hbe hb'e hbb' hb'b with hpb
  have hpaMem : pa ∈ realizedSubgroup (fixFinset E.val) :=
    realizedPerm_localPerm A.property hae ha'e haa' ha'a
  have hpbMem : pb ∈ realizedSubgroup (fixFinset E.val) :=
    realizedPerm_localPerm B.property hbe hb'e hbb' hb'b
  have hcomm : pa * pb = pb * pa := by
    have := h (fixFinset E.val) ⟨pa, hpaMem⟩ ⟨pb, hpbMem⟩
    exact congrArg Subtype.val this
  -- The two restricted actions agree on the fixed-point set.
  have hfix : ∀ x : Config w, x ∈ fixFinset E.val →
      runTrans B.val (runTrans A.val x) = runTrans A.val (runTrans B.val x) := by
    intro x hx
    have h1 := congrArg (fun p : Equiv.Perm {x // x ∈ fixFinset E.val} =>
      (p ⟨x, hx⟩).val) hcomm
    simpa [hpa, hpb, localPerm] using h1.symm
  refine Subtype.ext (transMonoid_ext ?_)
  intro y
  have hy : runTrans E.val y ∈ fixFinset E.val := runTrans_mem_fixFinset hee y
  have hAcollapse : runTrans A.val (runTrans E.val y) = runTrans A.val y := by
    have h : runTrans (E.val * A.val) y = runTrans A.val y := by rw [hea]
    rwa [runTrans_mul] at h
  have hBcollapse : runTrans B.val (runTrans E.val y) = runTrans B.val y := by
    have h : runTrans (E.val * B.val) y = runTrans B.val y := by rw [heb]
    rwa [runTrans_mul] at h
  have hkey := hfix _ hy
  rw [hAcollapse, hBcollapse] at hkey
  change runTrans (A.val * B.val) y = runTrans (B.val * A.val) y
  rw [runTrans_mul, runTrans_mul]
  exact hkey

/-- **S5 follows from the antichain case**, via
`realizedSubgroup_comm_of_antichains`. -/
theorem localUnitsCommute_of_antichainsCommute (hcomm : AntichainsCommute w) :
    LocalUnitsCommute (NonCrossing w) :=
  localUnitsCommute_of_realizedComm (realizedSubgroup_comm_of_antichains hcomm)

/-- **S5 follows from antichain cyclicity.** -/
theorem localUnitsCommute_of_antichainsCyclic (hcyc : AntichainsCyclic w) :
    LocalUnitsCommute (NonCrossing w) :=
  localUnitsCommute_of_antichainsCommute (antichainsCommute_of_cyclic hcyc)

end Internal
end AllenderOQ3
