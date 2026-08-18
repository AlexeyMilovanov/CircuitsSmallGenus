import AllenderOQ3.Internal.RealizedPerms
import AllenderOQ3.Internal.TransBlock

set_option autoImplicit false

/-!
# The holonomy skeleton of `(NonCrossing w, Config w)` — reachability preorder

First file of the E2-c assembly (docs/ASSEMBLY_DESIGN.md, section 4, item 1).
The holonomy tower is built over the *reachability preorder* on finite sets of
configurations: `Reach S T` iff `T` is the image of `S` under some element of
`NonCrossing w`.  This file provides the constant-size combinatorial spine:

* `Reach` is reflexive and transitive, and images cannot grow cardinality;
* mutually reachable sets have equal cardinality;
* the strict part `StrictReach` is transitive and irreflexive;
* `hgtMeasure S` — the number of sets strictly below `S` — strictly drops
  along every strict descent and is bounded by the constant
  `Fintype.card (Finset (Config w))`.  This is the engine of the epoch-count
  bound (care spot B of the design): every holonomy epoch event strictly
  descends the preorder, so there are at most constantly many events.

Everything here is `sorry`-free.
-/

namespace AllenderOQ3
namespace Internal
namespace Holonomy

attribute [local instance] Classical.propDecidable

variable {w : Nat}

/-- The image of a set of configurations under a transition. -/
noncomputable def ImageOf (m : TransMonoid w) (S : Finset (Config w)) :
    Finset (Config w) :=
  S.image (runTrans m)

theorem imageOf_one (S : Finset (Config w)) : ImageOf (1 : TransMonoid w) S = S := by
  have h : ImageOf (1 : TransMonoid w) S = S.image id := by
    apply Finset.image_congr
    intro x _
    exact runTrans_one x
  rw [h, Finset.image_id]

/-- Images compose in time order. -/
theorem imageOf_mul (m₁ m₂ : TransMonoid w) (S : Finset (Config w)) :
    ImageOf (m₁ * m₂) S = ImageOf m₂ (ImageOf m₁ S) := by
  simp only [ImageOf]
  rw [Finset.image_image]
  apply Finset.image_congr
  intro x _
  exact runTrans_mul m₁ m₂ x

/-- `T` is reachable from `S`: some element of `NonCrossing w` maps `S` onto
`T`. -/
def Reach (S T : Finset (Config w)) : Prop :=
  ∃ m ∈ NonCrossing w, T = ImageOf m S

theorem reach_refl (S : Finset (Config w)) : Reach S S :=
  ⟨1, Submonoid.one_mem _, (imageOf_one S).symm⟩

theorem reach_trans {S T U : Finset (Config w)} (h₁ : Reach S T) (h₂ : Reach T U) :
    Reach S U := by
  obtain ⟨m₁, hm₁, rfl⟩ := h₁
  obtain ⟨m₂, hm₂, rfl⟩ := h₂
  exact ⟨m₁ * m₂, Submonoid.mul_mem _ hm₁ hm₂, (imageOf_mul m₁ m₂ S).symm⟩

/-- Images cannot grow: reachability is cardinality-non-increasing. -/
theorem card_le_of_reach {S T : Finset (Config w)} (h : Reach S T) :
    T.card ≤ S.card := by
  obtain ⟨m, _, rfl⟩ := h
  exact Finset.card_image_le

/-- Mutual reachability. -/
def ReachEquiv (S T : Finset (Config w)) : Prop := Reach S T ∧ Reach T S

theorem card_eq_of_reachEquiv {S T : Finset (Config w)} (h : ReachEquiv S T) :
    S.card = T.card :=
  le_antisymm (card_le_of_reach h.2) (card_le_of_reach h.1)

/-- The strict part of the reachability preorder. -/
def StrictReach (T S : Finset (Config w)) : Prop :=
  Reach S T ∧ ¬ Reach T S

theorem strictReach_irrefl (S : Finset (Config w)) : ¬ StrictReach S S := by
  intro h
  exact h.2 (reach_refl S)

/-- Strict descents compose (with plain descents on either side). -/
theorem strictReach_of_strictReach_reach {U T S : Finset (Config w)}
    (h₁ : StrictReach T S) (h₂ : Reach T U) (h₃ : ¬ Reach U T) :
    StrictReach U S := by
  refine ⟨reach_trans h₁.1 h₂, fun hUS => ?_⟩
  exact h₃ (reach_trans hUS h₁.1)

theorem strictReach_trans {U T S : Finset (Config w)}
    (h₂ : StrictReach U T) (h₁ : StrictReach T S) : StrictReach U S := by
  refine ⟨reach_trans h₁.1 h₂.1, fun hUS => ?_⟩
  exact h₂.2 (reach_trans hUS h₁.1)

/-- The height measure: the number of sets strictly below `S`. -/
noncomputable def hgtMeasure (S : Finset (Config w)) : Nat :=
  (Finset.univ.filter (fun T : Finset (Config w) => StrictReach T S)).card

/-- The height measure is bounded by the constant `2 ^ 2 ^ w`-ish cardinality
of the subset lattice. -/
theorem hgtMeasure_le (S : Finset (Config w)) :
    hgtMeasure S ≤ Fintype.card (Finset (Config w)) := by
  classical
  calc hgtMeasure S ≤ (Finset.univ : Finset (Finset (Config w))).card :=
        Finset.card_filter_le _ _
    _ = Fintype.card (Finset (Config w)) := Finset.card_univ

/-- **The height measure strictly drops along every strict descent.**  The
strictly-below family of `T` is contained in that of `S` (transitivity), and
`T` itself witnesses the strictness of the inclusion. -/
theorem hgtMeasure_lt_of_strictReach {T S : Finset (Config w)}
    (h : StrictReach T S) : hgtMeasure T < hgtMeasure S := by
  classical
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨T, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ T, h⟩
    · intro hmem
      exact strictReach_irrefl T (Finset.mem_filter.mp hmem).2
  · intro U hU
    have hUT : StrictReach U T := (Finset.mem_filter.mp hU).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ U, strictReach_trans hUT h⟩

/-- Reachability from the full configuration set (the sets appearing in a run
of the cascade all satisfy this). -/
def ReachableSet (S : Finset (Config w)) : Prop :=
  Reach Finset.univ S

theorem reachableSet_univ : ReachableSet (Finset.univ : Finset (Config w)) :=
  reach_refl _

theorem reachableSet_of_reach {S T : Finset (Config w)}
    (hS : ReachableSet S) (h : Reach S T) : ReachableSet T :=
  reach_trans hS h

/-- The prefix images of a word of monoid elements are reachable, and each
step is a `Reach` step: the run of the cascade descends the preorder. -/
theorem reach_imageOf {S : Finset (Config w)} {m : TransMonoid w}
    (hm : m ∈ NonCrossing w) : Reach S (ImageOf m S) :=
  ⟨m, hm, rfl⟩

/-! ## The run of a word down the preorder -/

/-- The image of the full configuration set under the `t`-th prefix of a word:
the reached set of the run at time `t`. -/
noncomputable def runImage (word : List (TransMonoid w)) (t : Nat) :
    Finset (Config w) :=
  ImageOf (prefixEnd word t) Finset.univ

theorem runImage_zero (word : List (TransMonoid w)) :
    runImage word 0 = Finset.univ := by
  simp only [runImage]
  rw [prefixEnd_zero, imageOf_one]

/-- Every block of a word with letters in `NonCrossing w` multiplies to an
element of `NonCrossing w`. -/
theorem blockEnd_mem_nonCrossing {word : List (TransMonoid w)}
    (hword : ∀ m ∈ word, m ∈ NonCrossing w) (a b : Nat) :
    blockEnd word a b ∈ NonCrossing w := by
  have h : blockEnd word a b = ((word.take b).drop a).prod := rfl
  rw [h]
  refine Submonoid.list_prod_mem _ ?_
  intro m hm
  exact hword m (List.mem_of_mem_take (List.mem_of_mem_drop hm))

/-- **The run descends the reachability preorder**: any later reached set is
reachable from any earlier one (via the intervening block). -/
theorem reach_runImage_of_le {word : List (TransMonoid w)}
    (hword : ∀ m ∈ word, m ∈ NonCrossing w) {a b : Nat} (hab : a ≤ b) :
    Reach (runImage word a) (runImage word b) := by
  refine ⟨blockEnd word a b, blockEnd_mem_nonCrossing hword a b, ?_⟩
  simp only [runImage]
  rw [prefixEnd_eq_mul_blockEnd word hab, imageOf_mul]

/-- Generic decreasing-measure change counting: if `g` is non-increasing along
consecutive steps and strictly decreases at every position satisfying `P`,
then the number of `P`-positions below `len` is at most `g 0`. -/
theorem card_filter_le_of_decreasing (g : Nat → Nat) (P : Nat → Prop)
    (hstep : ∀ i, g (i + 1) ≤ g i) (hdrop : ∀ i, P i → g (i + 1) < g i) :
    ∀ len : Nat,
      ((Finset.range len).filter P).card + g len ≤ g 0 := by
  intro len
  induction len with
  | zero => simp
  | succ len ih =>
    rw [Finset.range_add_one, Finset.filter_insert]
    by_cases hc : P len
    · have hlt : g (len + 1) < g len := hdrop len hc
      rw [if_pos hc, Finset.card_insert_of_notMem (by simp)]
      omega
    · rw [if_neg hc]
      have := hstep len
      omega

/-- **The epoch-count bound** (care spot B of the assembly design): along any
run, the number of positions at which the reached set strictly descends the
preorder — i.e. leaves its mutual-reachability class — is at most the constant
`Fintype.card (Finset (Config w))`.  These positions are the epoch events of
the top level of the holonomy tower. -/
theorem card_epoch_events_le {word : List (TransMonoid w)}
    (hword : ∀ m ∈ word, m ∈ NonCrossing w) (len : Nat) :
    ((Finset.range len).filter
        (fun t => ¬ ReachEquiv (runImage word t) (runImage word (t + 1)))).card
      ≤ Fintype.card (Finset (Config w)) := by
  classical
  have hstepReach : ∀ i : Nat, Reach (runImage word i) (runImage word (i + 1)) :=
    fun i => reach_runImage_of_le hword (Nat.le_succ i)
  have hmono : ∀ i, hgtMeasure (runImage word (i + 1)) ≤ hgtMeasure (runImage word i) := by
    intro i
    apply Finset.card_le_card
    intro U hU
    have hUT : StrictReach U (runImage word (i + 1)) := (Finset.mem_filter.mp hU).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ U, ?_, ?_⟩
    · exact reach_trans (hstepReach i) hUT.1
    · intro hUS
      exact hUT.2 (reach_trans hUS (hstepReach i))
  have hdrop : ∀ i, ¬ ReachEquiv (runImage word i) (runImage word (i + 1)) →
      hgtMeasure (runImage word (i + 1)) < hgtMeasure (runImage word i) := by
    intro i hne
    apply hgtMeasure_lt_of_strictReach
    refine ⟨hstepReach i, fun hback => ?_⟩
    exact hne ⟨hstepReach i, hback⟩
  have hkey : ∀ L : Nat,
      ((Finset.range L).filter
          (fun t => ¬ ReachEquiv (runImage word t) (runImage word (t + 1)))).card
        + hgtMeasure (runImage word L) ≤ hgtMeasure (runImage word 0) := by
    intro L
    induction L with
    | zero => simp
    | succ L ih =>
      rw [Finset.range_add_one, Finset.filter_insert]
      by_cases hc : ¬ ReachEquiv (runImage word L) (runImage word (L + 1))
      · rw [if_pos hc, Finset.card_insert_of_notMem (by simp)]
        have hlt := hdrop L hc
        omega
      · rw [if_neg hc]
        have hle := hmono L
        omega
  have hbound : hgtMeasure (runImage word 0) ≤ Fintype.card (Finset (Config w)) :=
    hgtMeasure_le _
  have hfin := hkey len
  omega

end Holonomy
end Internal
end AllenderOQ3
