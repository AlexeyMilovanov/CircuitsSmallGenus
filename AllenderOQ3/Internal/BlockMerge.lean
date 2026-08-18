import AllenderOQ3.Internal.EulerDefect

/-!
# Merging two block rotations into one rotation of the whole circuit

`AllenderOQ3.Internal.BlockGenus` splits a rotation system of a separated
circuit into rotation systems of its two blocks.  This file provides the
converse construction: given rotation systems of `blockIn c A` and
`blockOut c A` for a separating set `A`, the two rotations glue into a rotation
system of `c` whose faces are exactly the union of the faces of the two blocks.

Combined with Euler's formula (`AllenderOQ3.Internal.EulerDefect`) this yields
the statement that is needed for the layer planarizer: a circuit whose blocks are
all rotation-planar is itself rotation-planar, hence a non-planar circuit always
has a non-planar connected component.
-/

set_option autoImplicit false

namespace AllenderOQ3.Internal

open AllenderOQ3

variable {n : Nat}

/-! ## Two small permutation lemmas -/

/-- Iterating a permutation transported along an equivalence. -/
theorem permCongr_pow {alpha beta : Type} (e : alpha ≃ beta) (P : Equiv.Perm alpha) :
    ∀ (k : Nat) (x : beta), ((e.permCongr P) ^ k) x = e ((P ^ k) (e.symm x)) := by
  intro k
  induction k with
  | zero => intro x; simp
  | succ k ih =>
      intro x
      rw [pow_succ, Equiv.Perm.mul_apply, ih, Equiv.permCongr_apply, Equiv.symm_apply_apply,
        pow_succ, Equiv.Perm.mul_apply]

/-- Iterating a `subtypeCongr` permutation on the positive side. -/
theorem subtypeCongr_pow_left {E : Type} {p : E → Prop} [DecidablePred p]
    (ep : Equiv.Perm {a // p a}) (en : Equiv.Perm {a // ¬ p a}) :
    ∀ (k : Nat) (a : E) (h : p a),
      ((ep.subtypeCongr en) ^ k) a = ((ep ^ k) ⟨a, h⟩ : {a // p a}).1 := by
  intro k
  induction k with
  | zero => intro a h; rfl
  | succ k ih =>
      intro a h
      rw [pow_succ, Equiv.Perm.mul_apply, Equiv.Perm.subtypeCongr.left_apply ep en h,
        ih _ (ep ⟨a, h⟩).2]
      have hs : (⟨(ep ⟨a, h⟩ : {a // p a}).1, (ep ⟨a, h⟩).2⟩ : {a // p a}) = ep ⟨a, h⟩ := rfl
      rw [hs, pow_succ, Equiv.Perm.mul_apply]

/-- Iterating a `subtypeCongr` permutation on the negative side. -/
theorem subtypeCongr_pow_right {E : Type} {p : E → Prop} [DecidablePred p]
    (ep : Equiv.Perm {a // p a}) (en : Equiv.Perm {a // ¬ p a}) :
    ∀ (k : Nat) (a : E) (h : ¬ p a),
      ((ep.subtypeCongr en) ^ k) a = ((en ^ k) ⟨a, h⟩ : {a // ¬ p a}).1 := by
  intro k
  induction k with
  | zero => intro a h; rfl
  | succ k ih =>
      intro a h
      rw [pow_succ, Equiv.Perm.mul_apply, Equiv.Perm.subtypeCongr.right_apply ep en h,
        ih _ (en ⟨a, h⟩).2]
      have hs : (⟨(en ⟨a, h⟩ : {a // ¬ p a}).1, (en ⟨a, h⟩).2⟩ : {a // ¬ p a}) = en ⟨a, h⟩ := rfl
      rw [hs, pow_succ, Equiv.Perm.mul_apply]

/-! ## The merged rotation -/

/-- The rotation system of `c` obtained by using `rIn` at the vertices of `A` and
`rOut` at the vertices outside `A`. -/
noncomputable def mergeRotation {c : ADRCircuit n} {A : Finset (Fin c.gateCount)}
    (hsep : SeparatedBy c A) (rIn : OrientableRotation (blockIn c A))
    (rOut : OrientableRotation (blockOut c A)) : OrientableRotation c where
  rotation :=
    Equiv.Perm.subtypeCongr (p := fun d : CircuitDart c => d.source ∈ A)
      (Equiv.permCongr (blockDartIn hsep) rIn.rotation)
      (Equiv.permCongr (blockDartOut hsep) rOut.rotation)
  preservesSource := by
    intro d
    by_cases h : d.source ∈ A
    · rw [Equiv.Perm.subtypeCongr.left_apply
        (p := fun d : CircuitDart c => d.source ∈ A) _ _ h]
      exact rIn.preservesSource _
    · rw [Equiv.Perm.subtypeCongr.right_apply
        (p := fun d : CircuitDart c => d.source ∈ A) _ _ h]
      exact rOut.preservesSource _
  cyclicAtVertex := by
    intro d e hde
    by_cases h : d.source ∈ A
    · have he : e.source ∈ A := by rw [← hde]; exact h
      obtain ⟨k, hk⟩ := rIn.cyclicAtVertex ((blockDartIn hsep).symm ⟨d, h⟩)
        ((blockDartIn hsep).symm ⟨e, he⟩) hde
      refine ⟨k, ?_⟩
      rw [subtypeCongr_pow_left _ _ k d h, permCongr_pow, hk, Equiv.apply_symm_apply]
    · have he : ¬ e.source ∈ A := by rw [← hde]; exact h
      obtain ⟨k, hk⟩ := rOut.cyclicAtVertex ((blockDartOut hsep).symm ⟨d, h⟩)
        ((blockDartOut hsep).symm ⟨e, he⟩) hde
      refine ⟨k, ?_⟩
      rw [subtypeCongr_pow_right _ _ k d h, permCongr_pow, hk, Equiv.apply_symm_apply]

/-- The faces of the merged rotation are exactly the faces of the two blocks. -/
theorem permCycleCount_mergeRotation {c : ADRCircuit n} {A : Finset (Fin c.gateCount)}
    (hsep : SeparatedBy c A) (rIn : OrientableRotation (blockIn c A))
    (rOut : OrientableRotation (blockOut c A)) :
    permCycleCount (facePermutation (mergeRotation hsep rIn rOut))
      = permCycleCount (facePermutation rIn) + permCycleCount (facePermutation rOut) := by
  classical
  have hface := face_source_mem_invariant hsep (mergeRotation hsep rIn rOut)
  have hsplit := permCycleCount_split (facePermutation (mergeRotation hsep rIn rOut))
    (fun d : CircuitDart c => d.source ∈ A) hface
  have hIn : permCycleCount (facePermutation rIn)
      = permCycleCount ((facePermutation (mergeRotation hsep rIn rOut)).subtypePerm
          (p := fun d : CircuitDart c => d.source ∈ A) hface) := by
    refine permCycleCount_of_subtype_transport (facePermutation (mergeRotation hsep rIn rOut))
      (fun d : CircuitDart c => d.source ∈ A) hface (blockDartIn hsep) _ (fun e => ?_)
    have h' : (dartReverse c ((blockDartIn hsep) e).1).source ∈ A :=
      (dart_source_mem_iff hsep _).mp ((blockDartIn hsep) e).2
    show ((blockDartIn hsep) (rIn.rotation (dartReverse (blockIn c A) e))).1
      = (mergeRotation hsep rIn rOut).rotation (dartReverse c ((blockDartIn hsep) e).1)
    rw [show (mergeRotation hsep rIn rOut).rotation
          (dartReverse c ((blockDartIn hsep) e).1)
        = ((Equiv.permCongr (blockDartIn hsep) rIn.rotation)
            ⟨dartReverse c ((blockDartIn hsep) e).1, h'⟩ :
              {d : CircuitDart c // d.source ∈ A}).1 from
      Equiv.Perm.subtypeCongr.left_apply (p := fun d : CircuitDart c => d.source ∈ A)
        (Equiv.permCongr (blockDartIn hsep) rIn.rotation)
        (Equiv.permCongr (blockDartOut hsep) rOut.rotation) h']
    rfl
  have hOut : permCycleCount (facePermutation rOut)
      = permCycleCount ((facePermutation (mergeRotation hsep rIn rOut)).subtypePerm
          (p := fun d : CircuitDart c => ¬ (d.source ∈ A)) (fun x => not_congr (hface x))) := by
    refine permCycleCount_of_subtype_transport (facePermutation (mergeRotation hsep rIn rOut))
      (fun d : CircuitDart c => ¬ (d.source ∈ A)) (fun x => not_congr (hface x))
      (blockDartOut hsep) _ (fun e => ?_)
    have h' : ¬ (dartReverse c ((blockDartOut hsep) e).1).source ∈ A := fun hmem =>
      ((blockDartOut hsep) e).2 ((dart_source_mem_iff hsep _).mpr hmem)
    show ((blockDartOut hsep) (rOut.rotation (dartReverse (blockOut c A) e))).1
      = (mergeRotation hsep rIn rOut).rotation (dartReverse c ((blockDartOut hsep) e).1)
    rw [show (mergeRotation hsep rIn rOut).rotation
          (dartReverse c ((blockDartOut hsep) e).1)
        = ((Equiv.permCongr (blockDartOut hsep) rOut.rotation)
            ⟨dartReverse c ((blockDartOut hsep) e).1, h'⟩ :
              {d : CircuitDart c // ¬ (d.source ∈ A)}).1 from
      Equiv.Perm.subtypeCongr.right_apply (p := fun d : CircuitDart c => d.source ∈ A)
        (Equiv.permCongr (blockDartIn hsep) rIn.rotation)
        (Equiv.permCongr (blockDartOut hsep) rOut.rotation) h']
    rfl
  omega

/-- If both blocks of a separated circuit are rotation-planar, so is the circuit. -/
theorem rotationPlanar_of_blocks {c : ADRCircuit n} {A : Finset (Fin c.gateCount)}
    (hsep : SeparatedBy c A) (hIn : RotationPlanar (blockIn c A))
    (hOut : RotationPlanar (blockOut c A)) : RotationPlanar c := by
  obtain ⟨rIn, hrIn⟩ := hIn
  obtain ⟨rOut, hrOut⟩ := hOut
  refine ⟨mergeRotation hsep rIn rOut, ?_⟩
  have dIn := defect_eq_of_rotationGenus_zero hrIn
  have dOut := defect_eq_of_rotationGenus_zero hrOut
  have hC := componentCount_block hsep
  have hI := isolatedVertexCount_block hsep
  have hE := underlyingEdgeCount_block hsep
  have hF := permCycleCount_mergeRotation hsep rIn rOut
  simp only [blockIn_gateCount, blockOut_gateCount] at dIn dOut
  change (2 * componentCount c + underlyingEdgeCount c - c.gateCount -
    (permCycleCount (facePermutation (mergeRotation hsep rIn rOut))
      + isolatedVertexCount c)) / 2 = 0
  omega

end AllenderOQ3.Internal
