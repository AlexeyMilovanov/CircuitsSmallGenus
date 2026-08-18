import AllenderOQ3.Internal.N4Words
import AllenderOQ3.Internal.AbstractCylinder

set_option autoImplicit false

namespace AllenderOQ3.Internal

open AllenderOQ3

/-!
# The refined circuit is again incidence-cylindrical

§3 of `docs/INCIDENCE_REFINEMENT.md`.  The layer listings of `N4Layers.lean` and the arc
words of `N4Words.lean` fit together: the source-major word of every transition is grouped
along the listing of its source layer, the target-major word is grouped along the listing
of its target layer, and the two words agree up to one cyclic rotation.  By
`incidenceCylinder_ofSpec_two` this makes the refined circuit incidence-cylindrical.
-/

variable {n : Nat} (c : ADRCircuit n) (F : Nat) (cyl : IncidenceCylinder c)

/-! ## Grouping along a guarded listing -/

/-- The old gate a node of the refined circuit belongs to. -/
def n4GateOf : N4Gate c.gateCount F → Fin c.gateCount
  | Sum.inl g => g
  | Sum.inr (g, _, _) => g

/-- A word whose letters all have the same endpoint is grouped along the guarded listing
of that endpoint. -/
theorem groupedAlong_n4LV {ell ellv : Nat}
    (key : SpecTransitionArc (n4Spec c F (n4Inc c cyl)) ell →
      SpecLayerVertex (n4Spec c F (n4Inc c cyl)) ellv)
    (u : N4Gate c.gateCount F) (w : List (SpecTransitionArc (n4Spec c F (n4Inc c cyl)) ell))
    (h : ∀ a ∈ w, (key a).1 = u) : GroupedAlong key (n4LV c F cyl ellv u) w := by
  unfold n4LV
  split
  · exact groupedAlong_singleton key _ w (fun a ha => Subtype.ext (h a ha))
  · next hu =>
      cases w with
      | nil => rfl
      | cons a t =>
          exfalso
          have h2 := (key a).2
          rw [h a (by simp)] at h2
          exact hu h2

theorem groupedAlong_n4LVSlot {ell ellv : Nat}
    (key : SpecTransitionArc (n4Spec c F (n4Inc c cyl)) ell →
      SpecLayerVertex (n4Spec c F (n4Inc c cyl)) ellv)
    (g : Fin c.gateCount) (j : Fin (F + 1)) (s : Nat)
    (w : List (SpecTransitionArc (n4Spec c F (n4Inc c cyl)) ell))
    (h : ∀ a ∈ w, (key a).1 = N4.node g j (finClamp F s))
    (hnil : ¬ s < F + 1 → w = []) :
    GroupedAlong key (n4LVSlot c F cyl ellv g j s) w := by
  by_cases hlt : s < F + 1
  · rw [n4LVSlot_of_lt c F cyl hlt]
    exact groupedAlong_n4LV c F cyl key _ w h
  · rw [n4LVSlot_of_ge c F cyl hlt, hnil hlt]
    rfl

/-- Grouping the slots of one strip. -/
theorem groupedAlong_slot_blocks {ell ellv : Nat}
    (key : SpecTransitionArc (n4Spec c F (n4Inc c cyl)) ell →
      SpecLayerVertex (n4Spec c F (n4Inc c cyl)) ellv)
    (g : Fin c.gateCount) (j : Fin (F + 1))
    (wb : Nat → List (SpecTransitionArc (n4Spec c F (n4Inc c cyl)) ell))
    (h : ∀ s, ∀ a ∈ wb s, (key a).1 = N4.node g j (finClamp F s))
    (hnil : ∀ s, ¬ s < F + 1 → wb s = []) :
    GroupedAlong key ((List.range (F + 1)).flatMap (n4LVSlot c F cyl ellv g j))
      ((List.range (F + 1)).flatMap wb) := by
  refine groupedAlong_flatMap_pair _ _ _ _ List.nodup_range
    (fun s _ => groupedAlong_n4LVSlot c F cyl key g j s (wb s) (h s) (hnil s)) ?_
  intro s hs t ht hst a ha u hu hcon
  obtain ⟨-, hu1⟩ := (mem_n4LVSlot c F cyl).mp hu
  have ha1 := h t a ha
  rw [hcon, hu1] at ha1
  have hval := congrArg (fun p => (p.2.2 : Fin (F + 1)).val) (Sum.inr.inj ha1)
  have hs' : s < F + 1 := List.mem_range.mp hs
  have ht' : t < F + 1 := List.mem_range.mp ht
  simp only [finClamp_val (show s ≤ F by omega), finClamp_val (show t ≤ F by omega)] at hval
  exact hst hval

/-- Grouping the strips of one layer. -/
theorem groupedAlong_gate_blocks {ell ellv m : Nat}
    (key : SpecTransitionArc (n4Spec c F (n4Inc c cyl)) ell →
      SpecLayerVertex (n4Spec c F (n4Inc c cyl)) ellv)
    (kb : LayerVertex c m → List (SpecLayerVertex (n4Spec c F (n4Inc c cyl)) ellv))
    (wb : LayerVertex c m → List (SpecTransitionArc (n4Spec c F (n4Inc c cyl)) ell))
    (hblock : ∀ v, GroupedAlong key (kb v) (wb v))
    (hkb : ∀ v, ∀ u ∈ kb v, n4GateOf c F u.1 = v.1)
    (hwb : ∀ v, ∀ a ∈ wb v, n4GateOf c F (key a).1 = v.1) :
    GroupedAlong key ((cyl.layerOrder m).entries.flatMap kb)
      ((cyl.layerOrder m).entries.flatMap wb) := by
  refine groupedAlong_flatMap_pair _ _ _ _ (cyl.layerOrder m).nodup (fun v _ => hblock v) ?_
  intro x _ y _ hxy a ha u hu hcon
  have h1 := hkb x u hu
  have h2 := hwb y a ha
  rw [hcon] at h2
  exact hxy (Subtype.ext (h1.symm.trans h2))

/-! ## The endpoints of the blocks of the three kinds of transition -/

theorem n4LeafOut_source {ell m : Nat} (v : LayerVertex c m)
    {a : SpecTransitionArc (n4Spec c F (n4Inc c cyl)) ell}
    (ha : a ∈ ((cyl.transitionOrder m).outgoing v).flatMap (n4LeafArc c F cyl ell)) :
    (specArcSource a).1 = N4.old v.1 := by
  obtain ⟨e, he, hae⟩ := List.mem_flatMap.mp ha
  have h1 := n4LeafArc_pair c F cyl hae
  have h2 := ((cyl.transitionOrder m).outgoing_exact v e).mp he
  change a.1.1 = N4.old v.1
  rw [congrArg Prod.fst h1, h2]

theorem n4LeafBlock_target {ell m : Nat} (v : LayerVertex c (m + 1))
    (s : Nat) {a : SpecTransitionArc (n4Spec c F (n4Inc c cyl)) ell}
    (ha : a ∈ n4LeafBlock c F cyl ell v s) :
    (specArcTarget a).1 = N4.node v.1 (finClamp F 0) (finClamp F s) := by
  cases s with
  | zero => exact absurd ha (List.not_mem_nil)
  | succ t =>
      rw [n4LeafBlock] at ha
      rcases hget : ((cyl.transitionOrder m).incoming v)[t]? with _ | e
      · rw [hget] at ha
        exact absurd ha (List.not_mem_nil)
      · rw [hget] at ha
        simp only [Option.elim] at ha
        have hpair := n4LeafArc_pair c F cyl ha
        obtain ⟨hlt, hgetv⟩ := List.getElem?_eq_some_iff.mp hget
        have hmem : e ∈ (cyl.transitionOrder m).incoming v := by
          rw [← hgetv]; exact List.getElem_mem hlt
        have hatgt : e.1.2 = v.1 := ((cyl.transitionOrder m).incoming_exact v e).mp hmem
        have hvert : (⟨e.1.2, e.2.2.2⟩ : LayerVertex c (m + 1)) = v := Subtype.ext hatgt
        have hidx : ((cyl.transitionOrder m).incoming v).idxOf e = t := by
          rw [← hgetv]
          exact ((cyl.transitionOrder m).incoming_nodup v).idxOf_getElem _ hlt
        have hslot : n4ArcSlot c F cyl e = finClamp F (t + 1) := by
          rw [n4ArcSlot, hvert, hidx]
        change a.1.2 = _
        rw [congrArg Prod.snd hpair, hatgt, hslot]

theorem n4LeafBlock_nil (hc : WellFormedADR c) (hf : ∀ g, predecessorCount c g ≤ F)
    {ell m : Nat} (v : LayerVertex c (m + 1)) (s : Nat) (hs : ¬ s < F + 1) :
    n4LeafBlock c F cyl ell v s = [] := by
  have hlen : ((cyl.transitionOrder m).incoming v).length ≤ F := by
    rw [length_incoming_eq_predecessorCount hc.1]
    exact hf v.1
  cases s with
  | zero => rfl
  | succ t =>
      rw [n4LeafBlock, List.getElem?_eq_none (by omega)]
      rfl

theorem n4StripArc_source {ell : Nat} (g : Fin c.gateCount) (s : Nat)
    {a : SpecTransitionArc (n4Spec c F (n4Inc c cyl)) ell}
    (ha : a ∈ n4StripArc c F cyl ell g s) :
    (specArcSource a).1 = N4.node g (n4MicroIdx F ell) (finClamp F s) := by
  change a.1.1 = _
  rw [congrArg Prod.fst (n4StripArc_pair c F cyl ha).2]

theorem n4StripBlock_target {ell : Nat} (g : Fin c.gateCount) (t : Nat)
    {a : SpecTransitionArc (n4Spec c F (n4Inc c cyl)) ell}
    (ha : a ∈ n4StripBlock c F cyl ell g t) :
    (specArcTarget a).1 = N4.node g (n4MicroIdx F (ell + 1)) (finClamp F t) := by
  change a.1.2 = _
  by_cases ht : t = 0
  · subst ht
    rw [n4StripBlock, if_pos rfl] at ha
    rcases List.mem_append.mp ha with h | h
    · obtain ⟨hlt, hpair⟩ := n4StripArc_pair c F cyl h
      have h2 : a.1.2
          = N4.node g (n4MicroIdx F (ell + 1)) (n4TargetSlot (finClamp F (0 : Nat))) := by
        rw [hpair]
      have h3 : n4TargetSlot (finClamp F (0 : Nat)) = finClamp F 0 :=
        Fin.ext (by simp [n4TargetSlot_val])
      rw [h2, h3]
    · obtain ⟨hlt, hpair⟩ := n4StripArc_pair c F cyl h
      have h2 : a.1.2
          = N4.node g (n4MicroIdx F (ell + 1)) (n4TargetSlot (finClamp F (1 : Nat))) := by
        rw [hpair]
      have h3 : n4TargetSlot (finClamp F (1 : Nat)) = finClamp F 0 :=
        Fin.ext (by
          rw [n4TargetSlot_val, finClamp_val (show (1 : Nat) ≤ F by omega), if_pos (by omega),
            finClamp_val (show (0 : Nat) ≤ F by omega)])
      rw [h2, h3]
  · rw [n4StripBlock, if_neg ht] at ha
    obtain ⟨hlt, hpair⟩ := n4StripArc_pair c F cyl ha
    have h2 : a.1.2
        = N4.node g (n4MicroIdx F (ell + 1)) (n4TargetSlot (finClamp F (t + 1))) := by
      rw [hpair]
    have h3 : n4TargetSlot (finClamp F (t + 1)) = finClamp F t :=
      Fin.ext (by
        rw [n4TargetSlot_val, finClamp_val (show t + 1 ≤ F by omega), if_neg (by omega),
          finClamp_val (show t ≤ F by omega)
        ]
        omega)
    rw [h2, h3]

theorem n4StripBlock_nil {ell : Nat} (g : Fin c.gateCount) (t : Nat) (ht : ¬ t < F + 1) :
    n4StripBlock c F cyl ell g t = [] := by
  rw [n4StripBlock, if_neg (by omega)]
  exact n4StripArc_of_ge c F cyl (by omega)

theorem n4FinalArc_source {ell : Nat} (g : Fin c.gateCount) (s : Nat)
    {a : SpecTransitionArc (n4Spec c F (n4Inc c cyl)) ell}
    (ha : a ∈ n4FinalArc c F cyl ell g s) :
    (specArcSource a).1 = N4.node g (n4MicroIdx F ell) (finClamp F s) := by
  obtain ⟨hs, hpair⟩ := n4FinalArc_pair c F cyl ha
  subst hs
  change a.1.1 = _
  rw [congrArg Prod.fst hpair]

theorem n4FinalArc_nil {ell : Nat} (g : Fin c.gateCount) (s : Nat) (hs : ¬ s < F + 1) :
    n4FinalArc c F cyl ell g s = [] := by
  rw [n4FinalArc, if_neg (by omega)]

theorem n4FinalWord_target {ell : Nat} (g : Fin c.gateCount)
    {a : SpecTransitionArc (n4Spec c F (n4Inc c cyl)) ell}
    (ha : a ∈ (List.range (F + 1)).flatMap (n4FinalArc c F cyl ell g)) :
    (specArcTarget a).1 = N4.old g := by
  obtain ⟨s, -, has⟩ := List.mem_flatMap.mp ha
  change a.1.2 = _
  rw [congrArg Prod.snd (n4FinalArc_pair c F cyl has).2]

/-! ## The source-major word is grouped along the source layer -/

theorem n4WordS_groupedSource (ell : Nat) :
    GroupedAlong specArcSource (n4LayerOrder c F cyl ell).entries (n4WordS c F cyl ell) := by
  change GroupedAlong specArcSource (n4LayerList c F cyl ell) (n4WordS c F cyl ell)
  by_cases hr : ell % (F + 2) = 0
  · rw [n4LayerList, if_pos hr, n4WordS, if_pos hr, List.flatMap_assoc]
    refine groupedAlong_gate_blocks c F cyl _ _ _ (fun v => ?_) (fun v u hu => ?_)
      (fun v a ha => ?_)
    · exact groupedAlong_n4LV c F cyl _ _ _ (fun a ha => n4LeafOut_source c F cyl v ha)
    · rw [(mem_n4LV c F cyl).mp hu]
      rfl
    · rw [n4LeafOut_source c F cyl v ha]
      rfl
  · rw [n4LayerList, if_neg hr, n4WordS, if_neg hr]
    split
    · refine groupedAlong_gate_blocks c F cyl _ _ _ (fun v => ?_) (fun v u hu => ?_)
        (fun v a ha => ?_)
      · refine groupedAlong_slot_blocks c F cyl _ _ _ _
          (fun s a ha => n4FinalArc_source c F cyl v.1 s ha)
          (fun s hs => n4FinalArc_nil c F cyl v.1 s hs)
      · obtain ⟨s, -, hus⟩ := List.mem_flatMap.mp hu
        rw [((mem_n4LVSlot c F cyl).mp hus).2]
        rfl
      · obtain ⟨s, -, has⟩ := List.mem_flatMap.mp ha
        rw [n4FinalArc_source c F cyl v.1 s has]
        rfl
    · refine groupedAlong_gate_blocks c F cyl _ _ _ (fun v => ?_) (fun v u hu => ?_)
        (fun v a ha => ?_)
      · refine groupedAlong_slot_blocks c F cyl _ _ _ _
          (fun s a ha => n4StripArc_source c F cyl v.1 s ha)
          (fun s hs => n4StripArc_of_ge c F cyl hs)
      · obtain ⟨s, -, hus⟩ := List.mem_flatMap.mp hu
        rw [((mem_n4LVSlot c F cyl).mp hus).2]
        rfl
      · obtain ⟨s, -, has⟩ := List.mem_flatMap.mp ha
        rw [n4StripArc_source c F cyl v.1 s has]
        rfl

/-! ## The target-major word is grouped along the target layer -/

theorem n4WordT_groupedTarget (hc : WellFormedADR c) (hf : ∀ g, predecessorCount c g ≤ F)
    (ell : Nat) :
    GroupedAlong specArcTarget (n4LayerOrder c F cyl (ell + 1)).entries
      (n4WordT c F cyl ell) := by
  change GroupedAlong specArcTarget (n4LayerList c F cyl (ell + 1)) (n4WordT c F cyl ell)
  by_cases hr : ell % (F + 2) = 0
  · rcases Nat.eq_zero_or_pos ell with rfl | hpos
    · rw [n4WordT_zero]
      exact groupedAlong_nil _ _
    obtain ⟨hm1, hm2⟩ := n4_succ_zero F hr
    have hdm : ell / (F + 2) * (F + 2) + ell % (F + 2) = ell := Nat.div_add_mod' ell (F + 2)
    have hq : 0 < ell / (F + 2) := by
      rcases Nat.eq_zero_or_pos (ell / (F + 2)) with h | h
      · exfalso; rw [h] at hdm; omega
      · exact h
    have hmid : n4MicroIdx F (ell + 1) = finClamp F 0 := Fin.ext (by simp [hm1])
    have hidx : (ell + 1) / (F + 2) = ell / (F + 2) - 1 + 1 := by omega
    rw [n4LayerList, if_neg (by omega), hidx, hmid, n4WordT, if_pos hr, List.flatMap_assoc]
    have hcongr : ∀ v ∈ (cyl.layerOrder (ell / (F + 2) - 1 + 1)).entries,
        ((cyl.transitionOrder (ell / (F + 2) - 1)).incoming v).flatMap (n4LeafArc c F cyl ell)
          = (List.range (F + 1)).flatMap (n4LeafBlock c F cyl ell v) := by
      intro v _
      exact n4LeafWord_eq c F cyl hc hf ell v
    rw [List.flatMap_congr hcongr]
    refine groupedAlong_gate_blocks c F cyl _ _ _ (fun v => ?_) (fun v u hu => ?_)
      (fun v a ha => ?_)
    · exact groupedAlong_slot_blocks c F cyl _ _ _ _
        (fun s a ha => n4LeafBlock_target c F cyl v s ha)
        (fun s hs => n4LeafBlock_nil c F cyl hc hf v s hs)
    · obtain ⟨s, -, hus⟩ := List.mem_flatMap.mp hu
      rw [((mem_n4LVSlot c F cyl).mp hus).2]
      rfl
    · obtain ⟨s, -, has⟩ := List.mem_flatMap.mp ha
      rw [n4LeafBlock_target c F cyl v s has]
      rfl
  · rw [n4WordT, if_neg hr, n4WordS, if_neg hr]
    by_cases hr2 : ell % (F + 2) = F + 1
    · obtain ⟨hm1, hm2⟩ := n4_succ_last F hr2
      rw [if_pos hr2, n4LayerList, if_pos hm1, hm2]
      rw [Nat.add_sub_cancel]
      refine groupedAlong_gate_blocks c F cyl _ _ _ (fun v => ?_) (fun v u hu => ?_)
        (fun v a ha => ?_)
      · exact groupedAlong_n4LV c F cyl _ _ _ (fun a ha => n4FinalWord_target c F cyl v.1 ha)
      · rw [(mem_n4LV c F cyl).mp hu]
        rfl
      · rw [n4FinalWord_target c F cyl v.1 ha]
        rfl
    · have hmod : ell % (F + 2) < F + 2 := n4_mod_lt ell F
      obtain ⟨hm1, hm2⟩ := n4_succ_mid F (ell := ell) (by omega)
      rw [if_neg hr2, n4LayerList, if_neg (by omega), hm2]
      have hcongr : ∀ v ∈ (cyl.layerOrder (ell / (F + 2))).entries,
          (List.range (F + 1)).flatMap (n4StripArc c F cyl ell v.1)
            = (List.range (F + 1)).flatMap (n4StripBlock c F cyl ell v.1) := by
        intro v _
        exact n4StripWord_eq c F cyl ell v.1
      rw [List.flatMap_congr hcongr]
      refine groupedAlong_gate_blocks c F cyl _ _ _ (fun v => ?_) (fun v u hu => ?_)
        (fun v a ha => ?_)
      · exact groupedAlong_slot_blocks c F cyl _ _ _ _
          (fun s a ha => n4StripBlock_target c F cyl v.1 s ha)
          (fun s hs => n4StripBlock_nil c F cyl v.1 s hs)
      · obtain ⟨s, -, hus⟩ := List.mem_flatMap.mp hu
        rw [((mem_n4LVSlot c F cyl).mp hus).2]
        rfl
      · obtain ⟨s, -, has⟩ := List.mem_flatMap.mp ha
        rw [n4StripBlock_target c F cyl v.1 s has]
        rfl

/-- **The refined circuit is incidence-cylindrical.** -/
theorem n4_incidence_cylinder_ofSpec (hc : WellFormedADR c)
    (hf : ∀ g, predecessorCount c g ≤ F) :
    Nonempty (IncidenceCylinder (ofSpec (n4Spec c F (n4Inc c cyl)))) :=
  incidenceCylinder_ofSpec_two (n4Spec c F (n4Inc c cyl)) (n4LayerOrder c F cyl)
    (n4WordS c F cyl) (n4WordT c F cyl) (n4Word_rot c F cyl)
    (n4WordS_nodup c F cyl) (n4WordS_complete c F cyl)
    (n4WordS_groupedSource c F cyl) (n4WordT_groupedTarget c F cyl hc hf)

end AllenderOQ3.Internal
