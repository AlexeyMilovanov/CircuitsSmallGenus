import AllenderOQ3.Base
import AllenderOQ3.Internal.ConstancyPattern
import AllenderOQ3.Internal.LayerSurgery

/-!
# Word-wise constant propagation (T5b, steps C5)

This file folds the per-layer surgery `surgery_step` (proved in
`LayerSurgery.lean`) over a generator word and assembles
`mem_nonCrossingCF_of_no_constant_output_aux`, the map called by the frozen
leaf `ConstantElimination.mem_nonCrossingCF_of_no_constant_output` (T5b).

Everything here is `sorry`-free, and so is `surgery_step`: T5b is complete.
-/

namespace AllenderOQ3.Internal

variable {w : Nat}

/-- The empty pattern constrains no coordinate, so every configuration respects it. -/
theorem respects_emptyPattern (z : Config w) : Respects (emptyPattern w) z := by
  intro i b h
  simp [emptyPattern] at h

/-- **Soundness of the propagated pattern.**  If `z` respects `σ`, then the
configuration produced by running the whole word respects the folded pattern. -/
theorem respects_foldl :
    ∀ (gs : List (TransMonoid w)) (σ : ConstancyPattern w) (z : Config w),
      Respects σ z →
      Respects (List.foldl (fun acc g => propagate g acc) σ gs) (runTrans gs.prod z) := by
  intro gs
  induction gs with
  | nil => intro σ z hz; simpa using hz
  | cons g gs ih =>
    intro σ z hz
    simp only [List.foldl_cons, List.prod_cons, runTrans_mul]
    exact ih (propagate g σ) (runTrans g z) (respects_propagate hz)

/-- **The fold of the per-layer surgery.**  For a word of certified non-crossing
layers `gs` and an input pattern `σ`, there is a constant-free element `m'` that
reproduces the word on the coordinates the word leaves non-constant, for inputs
agreeing on `σ`-live coordinates. -/
theorem fold_surgery :
    ∀ (gs : List (TransMonoid w)) (_ : ∀ g ∈ gs, isNonCrossingMap w g) (σ : ConstancyPattern w),
      ∃ m' : TransMonoid w, m' ∈ NonCrossingCF w ∧
        ∀ z z' : Config w, Respects σ z → AgreeOnLive σ z z' →
          AgreeOnLive (List.foldl (fun acc g => propagate g acc) σ gs)
            (runTrans gs.prod z) (runTrans m' z') := by
  intro gs
  induction gs with
  | nil =>
    intro _ σ
    refine ⟨1, Submonoid.one_mem _, ?_⟩
    intro z z' _ hag
    simpa using hag
  | cons g gs ih =>
    intro hgs σ
    obtain ⟨g', hg'CF, hg'⟩ :=
      surgery_step g (hgs g (List.mem_cons.mpr (Or.inl rfl))) σ
    obtain ⟨m'', hm''CF, hm''⟩ :=
      ih (fun g hg => hgs g (List.mem_cons.mpr (Or.inr hg))) (propagate g σ)
    refine ⟨g' * m'', Submonoid.mul_mem _ hg'CF hm''CF, ?_⟩
    intro z z' hz hag
    simp only [List.foldl_cons, List.prod_cons, runTrans_mul]
    exact hm'' (runTrans g z) (runTrans g' z') (respects_propagate hz) (hg' z z' hz hag)

/-- **T5b (assembled).**  A certified word whose underlying map has no constant
output coordinate lies in the constant-free submonoid.  Called by the frozen
leaf statement in `ConstantElimination.lean`. -/
theorem mem_nonCrossingCF_of_no_constant_output_aux {m : TransMonoid w}
    (hm : m ∈ NonCrossing w)
    (hnc : ∀ i : Fin w, ∃ z z' : Config w, runTrans m z i ≠ runTrans m z' i) :
    m ∈ NonCrossingCF w := by
  -- a generator word for `m` in the certified non-crossing submonoid
  obtain ⟨gs, hgsA, hgsprod⟩ := Submonoid.exists_list_of_mem_closure hm
  have hgsNC : ∀ g ∈ gs, isNonCrossingMap w g := fun g hg => hgsA g hg
  obtain ⟨m', hm'CF, hm'⟩ := fold_surgery gs hgsNC (emptyPattern w)
  -- Non-degeneracy: no output is forced constant, so the folded pattern is empty
  have hfinal : List.foldl (fun acc g => propagate g acc) (emptyPattern w) gs = emptyPattern w := by
    funext i
    cases hval : (List.foldl (fun acc g => propagate g acc) (emptyPattern w) gs) i with
    | none => rfl
    | some b =>
      exfalso
      obtain ⟨z, z', hzz'⟩ := hnc i
      have e1 : runTrans gs.prod z i = b :=
        respects_foldl gs (emptyPattern w) z (respects_emptyPattern z) i b hval
      have e2 : runTrans gs.prod z' i = b :=
        respects_foldl gs (emptyPattern w) z' (respects_emptyPattern z') i b hval
      rw [hgsprod] at e1 e2
      exact hzz' (e1.trans e2.symm)
  -- hence `m` and `m'` agree everywhere, so `m = m' ∈ NonCrossingCF`
  have hmm' : m = m' := by
    apply transMonoid_ext
    intro z
    funext i
    have key := hm' z z (respects_emptyPattern z) (fun j _ => rfl)
    rw [hfinal] at key
    have hi := key i (by simp [emptyPattern])
    rw [hgsprod] at hi
    exact hi
  rw [hmm']
  exact hm'CF

end AllenderOQ3.Internal
