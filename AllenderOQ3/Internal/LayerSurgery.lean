import AllenderOQ3.Base
import AllenderOQ3.Internal.ConstancyPattern
import AllenderOQ3.Internal.ConstantFreeLayers
import AllenderOQ3.Internal.CFPairGateSemantics
import AllenderOQ3.Internal.CFCopyLayer
import AllenderOQ3.Internal.TransitionMonoid
import AllenderOQ3.Internal.CycSortedWord
import AllenderOQ3.Internal.CFLayerBuilder
import AllenderOQ3.Internal.LayerExtract

/-!
# Per-layer surgery (T5b, step C4)

`surgery_step` is the per-layer step of the word-wise constant propagation.
Given one certified non-crossing layer `g` and an input constancy pattern `σ`,
it produces a *constant-free* element `g' ∈ NonCrossingCF w` that computes the
same thing as `g` on the coordinates that `g` does **not** force constant,
whenever the two inputs agree on the coordinates that `σ` leaves live.

The precise (two-configuration) shape is what the fold in `ConstantPropagation`
consumes: it relates the *original* `g` run on the clean input `z` to the
*surgered* `g'` run on an input `z'` that agrees with `z` on `σ`-live
coordinates.  This locality is essential — a one-configuration statement
(`g'` and `g` on the *same* `z`) does not compose through the fold.

The construction reads `g` as an AND/OR predecessor assignment with a
cyclically sorted arc word (`exists_layerData`), deletes the arcs coming from
`σ`-forced coordinates (they are neutral at every output slot that stays
non-constant), fills the targets left without predecessors (`exists_fill`) —
their outputs are forced, so their values are unconstrained — and rebuilds a
certified constant-free layer (`exists_memCF_of_cycSorted`).
-/

namespace AllenderOQ3.Internal

variable {w : Nat}

/-! ## Constancy bookkeeping -/

/-- Every pattern is respected by some configuration. -/
theorem exists_respects (σ : ConstancyPattern w) : ∃ z : Config w, Respects σ z := by
  refine ⟨fun i => (σ i).getD false, ?_⟩
  intro i b hb
  simp [hb]

/-- A coordinate on which the image of every `σ`-respecting configuration agrees
is forced by the propagated pattern. -/
theorem propagate_ne_none_of_const {g : TransMonoid w} {σ : ConstancyPattern w} {p : Fin w}
    {b : Bool} (h : ∀ z : Config w, Respects σ z → runTrans g z p = b) :
    propagate g σ p ≠ none := by
  classical
  have hex : ∃ b, ∀ z, Respects σ z → runTrans g z p = b := ⟨b, h⟩
  simp only [propagate, dif_pos hex]
  exact Option.some_ne_none _

/-! ## Deleting neutral predecessors -/

theorem all_congr_mem {α : Type} (l : List α) (f h : α → Bool)
    (hfh : ∀ a ∈ l, f a = h a) : l.all f = l.all h := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ih' := ih (fun b hb => hfh b (List.mem_cons_of_mem a hb))
    simp [List.all_cons, ih', hfh a List.mem_cons_self]

theorem any_congr_mem {α : Type} (l : List α) (f h : α → Bool)
    (hfh : ∀ a ∈ l, f a = h a) : l.any f = l.any h := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ih' := ih (fun b hb => hfh b (List.mem_cons_of_mem a hb))
    simp [List.any_cons, ih', hfh a List.mem_cons_self]

theorem all_eq_all_filter {α : Type} (l : List α) (f : α → Bool) (Q : α → Bool)
    (h : ∀ a ∈ l, Q a = false → f a = true) : l.all f = (l.filter Q).all f := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ih' := ih (fun b hb hQ => h b (List.mem_cons_of_mem a hb) hQ)
    cases hQa : Q a with
    | true => simp [hQa, ih']
    | false =>
      have hfa : f a = true := h a List.mem_cons_self hQa
      simp [hQa, ih', hfa]

theorem any_eq_any_filter {α : Type} (l : List α) (f : α → Bool) (Q : α → Bool)
    (h : ∀ a ∈ l, Q a = false → f a = false) : l.any f = (l.filter Q).any f := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ih' := ih (fun b hb hQ => h b (List.mem_cons_of_mem a hb) hQ)
    cases hQa : Q a with
    | true => simp [hQa, ih']
    | false =>
      have hfa : f a = false := h a List.mem_cons_self hQa
      simp [hQa, ih', hfa]

/-! ## The surgery -/

/-- **T5b step C4.**  Per-layer surgery: a certified non-crossing layer `g` and
a pattern `σ` yield a constant-free `g'` that reproduces `g` on the coordinates
`g` leaves non-constant, for inputs agreeing on `σ`-live coordinates. -/
theorem surgery_step (g : TransMonoid w) (hg : isNonCrossingMap w g) (σ : ConstancyPattern w) :
    ∃ g' : TransMonoid w, g' ∈ NonCrossingCF w ∧
      ∀ z z' : Config w, Respects σ z → AgreeOnLive σ z z' →
        AgreeOnLive (propagate g σ) (runTrans g z) (runTrans g' z') := by
  classical
  rcases Nat.eq_zero_or_pos w with hw0 | hw
  · subst hw0
    exact ⟨1, Submonoid.one_mem _, fun _ _ _ _ i _ => absurd i.isLt (by omega)⟩
  obtain ⟨P, K, hnd, hlen, hsort, hsemA, hsemO⟩ := exists_layerData hg
  set live : Fin w → Bool := fun q => decide (σ q = none) with hlive
  set P₁ : Fin w → List (Fin w) := fun p => (P p).filter live with hP₁
  have hmemP₁ : ∀ p q, q ∈ P₁ p ↔ q ∈ P p ∧ σ q = none := by
    intro p q
    simp [hP₁, List.mem_filter, hlive]
  have hlen₁ : ∀ p, (P₁ p).length ≤ 2 := fun p =>
    le_trans (List.length_filter_le _ _) (hlen p)
  have hnd₁ : ∀ p, (P₁ p).Nodup := fun p => (hnd p).filter _
  have hsort₁ : CycSortedSrc (arcPairWord P₁) := by
    have h := cycSortedSrc_filter (W := arcPairWord P) (fun e => live e.1) hsort
    rwa [arcPairWord_filter P live] at h
  have hdead : ∀ (q : Fin w), live q = false → ∃ b, σ q = some b := by
    intro q hq
    rcases hσ : σ q with _ | b
    · exfalso
      have htrue : live q = true := by simp [hlive, hσ]
      rw [hq] at htrue
      exact Bool.false_ne_true htrue
    · exact ⟨b, rfl⟩
  -- On σ-respecting inputs the deleted predecessors are neutral at every live output.
  have hkeyA : ∀ (p : Fin w), K p = true → propagate g σ p = none → ∀ z : Config w,
      Respects σ z → runTrans g z p = (P₁ p).all (fun q => z q) := by
    intro p hK hp z hz
    rw [hsemA z p hK]
    refine all_eq_all_filter _ _ _ ?_
    intro q hq hlq
    obtain ⟨b, hb⟩ := hdead q hlq
    cases b with
    | true => exact hz q true hb
    | false =>
      exact absurd hp (propagate_ne_none_of_const (b := false) (fun y hy => by
        rw [hsemA y p hK]
        exact List.all_eq_false.mpr ⟨q, hq, by simp [hy q false hb]⟩))
  have hkeyO : ∀ (p : Fin w), K p = false → propagate g σ p = none → ∀ z : Config w,
      Respects σ z → runTrans g z p = (P₁ p).any (fun q => z q) := by
    intro p hK hp z hz
    rw [hsemO z p hK]
    refine any_eq_any_filter _ _ _ ?_
    intro q hq hlq
    obtain ⟨b, hb⟩ := hdead q hlq
    cases b with
    | false => exact hz q false hb
    | true =>
      exact absurd hp (propagate_ne_none_of_const (b := true) (fun y hy => by
        rw [hsemO y p hK]
        exact List.any_eq_true.mpr ⟨q, hq, hy q true hb⟩))
  -- A target with no surviving predecessor is constant, hence not live.
  have hlivene : ∀ p : Fin w, propagate g σ p = none → P₁ p ≠ [] := by
    intro p hp hnil
    cases hK : K p with
    | true =>
      refine propagate_ne_none_of_const (b := true) (fun y hy => ?_) hp
      rw [hkeyA p hK hp y hy, hnil]
      rfl
    | false =>
      refine propagate_ne_none_of_const (b := false) (fun y hy => ?_) hp
      rw [hkeyO p hK hp y hy, hnil]
      rfl
  by_cases hne : ∃ p, P₁ p ≠ []
  · obtain ⟨P', hkeep, hne', hlen', hnd', hsort'⟩ := exists_fill P₁ hlen₁ hnd₁ hsort₁ hne
    obtain ⟨g', hg'CF, hg'A, hg'O⟩ :=
      exists_memCF_of_cycSorted hw P' K hne' hlen' hnd' hsort'
    refine ⟨g', hg'CF, ?_⟩
    intro z z' hz hag p hp
    have hzz : ∀ q ∈ P₁ p, z q = z' q := fun q hq => hag q ((hmemP₁ p q).mp hq).2
    have hP'p : P' p = P₁ p := hkeep p (hlivene p hp)
    cases hK : K p with
    | true =>
      rw [hkeyA p hK hp z hz, hg'A z' p hK, hP'p]
      exact all_congr_mem _ _ _ hzz
    | false =>
      rw [hkeyO p hK hp z hz, hg'O z' p hK, hP'p]
      exact any_congr_mem _ _ _ hzz
  · push_neg at hne
    refine ⟨1, Submonoid.one_mem _, ?_⟩
    intro z z' _ _ p hp
    exact absurd (hne p) (hlivene p hp)

end AllenderOQ3.Internal
