import AllenderOQ3.Internal.N4Layers

set_option autoImplicit false

namespace AllenderOQ3.Internal

open AllenderOQ3

/-!
# The arc words of the refined circuit

There are four kinds of transitions of the refined circuit: the empty one out of layer `0`,
the *leaf* transition from a checkpoint layer into the first micro-layer of the next strip,
the *reduction* transitions between two micro-layers of one strip, and the *final*
transition of a strip into its checkpoint.

Only the leaf transition needs the given certificate: its source-major word is the image of
the old source-major word and its target-major word is the image of the old target-major
word, and those two agree up to one cyclic rotation.  For the other transitions one single
word serves both purposes.

This file defines the words and proves that the source-major word lists every arc of its
transition exactly once.
-/

variable {n : Nat} (c : ADRCircuit n) (F : Nat) (cyl : IncidenceCylinder c)

/-! ## The arcs of the three kinds of transition -/

/-- The slot of the strip of `e.1.2` carrying the old arc `e`. -/
def n4ArcSlot {m : Nat} (e : TransitionArc c m) : Fin (F + 1) :=
  finClamp F (((cyl.transitionOrder m).incoming ⟨e.1.2, e.2.2.2⟩).idxOf e + 1)

/-- The leaf arc of an old arc: from the old checkpoint node to the rail carrying it. -/
def n4LeafArc (ell : Nat) {m : Nat} (e : TransitionArc c m) :
    List (SpecTransitionArc (n4Spec c F (n4Inc c cyl)) ell) :=
  n4Arc c F cyl ell (N4.old e.1.1) (N4.node e.1.2 (finClamp F 0) (n4ArcSlot c F cyl e))

/-- The leaf arcs into slot `s` of the strip of `v`. -/
def n4LeafBlock (ell : Nat) {m : Nat} (v : LayerVertex c (m + 1)) :
    Nat → List (SpecTransitionArc (n4Spec c F (n4Inc c cyl)) ell)
  | 0 => []
  | s + 1 => (((cyl.transitionOrder m).incoming v)[s]?).elim [] (n4LeafArc c F cyl ell)

/-- The reduction arc out of slot `s` of the strip of `g`. -/
def n4StripArc (ell : Nat) (g : Fin c.gateCount) (s : Nat) :
    List (SpecTransitionArc (n4Spec c F (n4Inc c cyl)) ell) :=
  if h : s < F + 1 then
    n4Arc c F cyl ell (N4.node g (n4MicroIdx F ell) ⟨s, h⟩)
      (N4.node g (n4MicroIdx F (ell + 1)) (n4TargetSlot ⟨s, h⟩))
  else []

/-- The reduction arcs into slot `t` of the strip of `g`: the accumulator absorbs the
first rail, every other rail shifts down by one slot. -/
def n4StripBlock (ell : Nat) (g : Fin c.gateCount) (t : Nat) :
    List (SpecTransitionArc (n4Spec c F (n4Inc c cyl)) ell) :=
  if t = 0 then n4StripArc c F cyl ell g 0 ++ n4StripArc c F cyl ell g 1
  else n4StripArc c F cyl ell g (t + 1)

/-- The final arc of the strip of `g`, indexed by the slot of its source. -/
def n4FinalArc (ell : Nat) (g : Fin c.gateCount) (s : Nat) :
    List (SpecTransitionArc (n4Spec c F (n4Inc c cyl)) ell) :=
  if s = 0 then
    n4Arc c F cyl ell (N4.node g (n4MicroIdx F ell) (finClamp F 0)) (N4.old g)
  else []

/-! ## The two words -/

/-- The source-major word of the transition out of layer `ell`. -/
def n4WordS (ell : Nat) : List (SpecTransitionArc (n4Spec c F (n4Inc c cyl)) ell) :=
  if ell % (F + 2) = 0 then
    ((cyl.layerOrder (ell / (F + 2) - 1)).entries.flatMap
      (cyl.transitionOrder (ell / (F + 2) - 1)).outgoing).flatMap (n4LeafArc c F cyl ell)
  else if ell % (F + 2) = F + 1 then
    (cyl.layerOrder (ell / (F + 2))).entries.flatMap
      (fun v => (List.range (F + 1)).flatMap (n4FinalArc c F cyl ell v.1))
  else
    (cyl.layerOrder (ell / (F + 2))).entries.flatMap
      (fun v => (List.range (F + 1)).flatMap (n4StripArc c F cyl ell v.1))

/-- The target-major word of the transition out of layer `ell`. -/
def n4WordT (ell : Nat) : List (SpecTransitionArc (n4Spec c F (n4Inc c cyl)) ell) :=
  if ell % (F + 2) = 0 then
    ((cyl.layerOrder (ell / (F + 2) - 1 + 1)).entries.flatMap
      (cyl.transitionOrder (ell / (F + 2) - 1)).incoming).flatMap (n4LeafArc c F cyl ell)
  else n4WordS c F cyl ell

/-! ## Reading off the endpoints -/

theorem n4LeafArc_pair {ell m : Nat} {e : TransitionArc c m}
    {x : SpecTransitionArc (n4Spec c F (n4Inc c cyl)) ell} (hx : x ∈ n4LeafArc c F cyl ell e) :
    x.1 = (N4.old e.1.1, N4.node e.1.2 (finClamp F 0) (n4ArcSlot c F cyl e)) :=
  (mem_n4Arc c F cyl).mp hx

theorem n4StripArc_of_ge {ell : Nat} {g : Fin c.gateCount} {s : Nat} (h : ¬ s < F + 1) :
    n4StripArc c F cyl ell g s = [] := by
  rw [n4StripArc, dif_neg h]

theorem n4StripArc_pair {ell : Nat} {g : Fin c.gateCount} {s : Nat}
    {x : SpecTransitionArc (n4Spec c F (n4Inc c cyl)) ell} (hx : x ∈ n4StripArc c F cyl ell g s) :
    s < F + 1 ∧ x.1 = (N4.node g (n4MicroIdx F ell) (finClamp F s),
        N4.node g (n4MicroIdx F (ell + 1)) (n4TargetSlot (finClamp F s))) := by
  by_cases h : s < F + 1
  · refine ⟨h, ?_⟩
    rw [n4StripArc, dif_pos h] at hx
    rw [← finClamp_eq h]
    exact (mem_n4Arc c F cyl).mp hx
  · rw [n4StripArc_of_ge c F cyl h] at hx
    exact absurd hx (List.not_mem_nil)

theorem n4FinalArc_pair {ell : Nat} {g : Fin c.gateCount} {s : Nat}
    {x : SpecTransitionArc (n4Spec c F (n4Inc c cyl)) ell} (hx : x ∈ n4FinalArc c F cyl ell g s) :
    s = 0 ∧ x.1 = (N4.node g (n4MicroIdx F ell) (finClamp F 0), N4.old g) := by
  by_cases h : s = 0
  · rw [n4FinalArc, if_pos h] at hx
    exact ⟨h, (mem_n4Arc c F cyl).mp hx⟩
  · rw [n4FinalArc, if_neg h] at hx
    exact absurd hx (List.not_mem_nil)

/-! ## The predecessor list of a certificate -/

/-- `n4Inc` computed at the layer at which a certificate lists the incoming arcs. -/
theorem n4Inc_eq_map' {m : Nat} (v : LayerVertex c (m + 1)) :
    n4Inc c cyl v.1 = ((cyl.transitionOrder m).incoming v).map (fun e => e.1.1) := by
  obtain ⟨g, hg⟩ := v
  have hg0 : c.layer g ≠ 0 := by omega
  obtain rfl : m = c.layer g - 1 := by omega
  rw [n4Inc, dif_neg hg0]

/-! ## Reindexing the words by target slot -/

/-- The reduction arcs of a strip, listed by target slot instead of by source slot. -/
theorem n4StripWord_eq (ell : Nat) (g : Fin c.gateCount) :
    (List.range (F + 1)).flatMap (n4StripArc c F cyl ell g)
      = (List.range (F + 1)).flatMap (n4StripBlock c F cyl ell g) := by
  have hA : n4StripArc c F cyl ell g (F + 1) = [] :=
    n4StripArc_of_ge c F cyl (by omega)
  rw [List.range_eq_range', List.range'_succ, List.flatMap_cons, List.flatMap_cons]
  have hblock0 : n4StripBlock c F cyl ell g 0
      = n4StripArc c F cyl ell g 0 ++ n4StripArc c F cyl ell g 1 := by
    rw [n4StripBlock, if_pos rfl]
  have hblock : ∀ t ∈ List.range' 1 F, n4StripBlock c F cyl ell g t
      = n4StripArc c F cyl ell g (t + 1) := by
    intro t ht
    obtain ⟨i, -, rfl⟩ := List.mem_range'.mp ht
    rw [n4StripBlock, if_neg (by omega)]
  rw [hblock0, List.flatMap_congr hblock,
    ← flatMap_range'_shift (n4StripArc c F cyl ell g) F 1, List.append_assoc]
  congr 1
  rcases Nat.eq_zero_or_pos F with hF | hF
  · subst hF
    rw [n4StripArc_of_ge c 0 cyl (show ¬ (1 : Nat) < 0 + 1 by omega)]
    simp
  · obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    have key : (List.range' 1 (F' + 1)).flatMap (n4StripArc c (F' + 1) cyl ell g)
        = n4StripArc c (F' + 1) cyl ell g 1
          ++ (List.range' 2 F').flatMap (n4StripArc c (F' + 1) cyl ell g) := by
      rw [List.range'_succ, List.flatMap_cons]
    have key2 : (List.range' 2 (F' + 1)).flatMap (n4StripArc c (F' + 1) cyl ell g)
        = (List.range' 2 F').flatMap (n4StripArc c (F' + 1) cyl ell g) := by
      rw [List.range'_concat, List.flatMap_append, show 2 + 1 * F' = F' + 2 by ring,
        List.flatMap_cons,
        n4StripArc_of_ge c (F' + 1) cyl (show ¬ F' + 2 < F' + 1 + 1 by omega)]
      simp
    rw [key, key2]

/-- The leaf arcs into one strip, listed by target slot. -/
theorem n4LeafWord_eq (hc : WellFormedADR c) (hf : ∀ g, predecessorCount c g ≤ F)
    (ell : Nat) {m : Nat} (v : LayerVertex c (m + 1)) :
    ((cyl.transitionOrder m).incoming v).flatMap (n4LeafArc c F cyl ell)
      = (List.range (F + 1)).flatMap (n4LeafBlock c F cyl ell v) := by
  set L := (cyl.transitionOrder m).incoming v with hL
  have hlen : L.length ≤ F := by
    rw [hL, length_incoming_eq_predecessorCount hc.1]
    exact hf v.1
  obtain ⟨d, hd⟩ : ∃ d, F = L.length + d := ⟨F - L.length, by omega⟩
  rw [List.range_eq_range', List.range'_succ, List.flatMap_cons]
  have h0 : n4LeafBlock c F cyl ell v 0 = [] := rfl
  rw [h0, List.nil_append, flatMap_range'_shift (n4LeafBlock c F cyl ell v) F 0]
  have hstep : ∀ s ∈ List.range' 0 F, n4LeafBlock c F cyl ell v (s + 1)
      = (L[s]?).elim [] (n4LeafArc c F cyl ell) := by
    intro s _
    rfl
  rw [List.flatMap_congr hstep, hd]
  exact (flatMap_range'_getElem? _ L d).symm

/-! ## The degenerate transition out of layer `0` -/

theorem n4WordS_zero : n4WordS c F cyl 0 = [] := by
  rw [n4WordS, if_pos (by simp)]
  refine List.flatMap_eq_nil_iff.mpr (fun e _ => ?_)
  rw [n4LeafArc, n4Arc, dif_neg]
  rintro ⟨-, h, -⟩
  exact n4Layer_ne_zero c F _ h

theorem n4WordT_zero : n4WordT c F cyl 0 = [] := by
  rw [n4WordT, if_pos (by simp)]
  refine List.flatMap_eq_nil_iff.mpr (fun e _ => ?_)
  rw [n4LeafArc, n4Arc, dif_neg]
  rintro ⟨-, h, -⟩
  exact n4Layer_ne_zero c F _ h

theorem n4_no_arc_zero (e : SpecTransitionArc (n4Spec c F (n4Inc c cyl)) 0) : False :=
  n4Layer_ne_zero c F _ e.2.2.1

/-! ## The source-major word lists every arc exactly once -/

theorem n4_old_word_nodup (m : Nat) :
    ((cyl.layerOrder m).entries.flatMap (cyl.transitionOrder m).outgoing).Nodup := by
  refine nodup_flatMap_of_ne _ _ (cyl.layerOrder m).nodup
    (fun v _ => (cyl.transitionOrder m).outgoing_nodup v) ?_
  intro v _ w _ hvw e he he'
  have h1 := ((cyl.transitionOrder m).outgoing_exact v e).mp he
  have h2 := ((cyl.transitionOrder m).outgoing_exact w e).mp he'
  exact hvw (Subtype.ext (h1.symm.trans h2))

theorem n4WordS_nodup (ell : Nat) : (n4WordS c F cyl ell).Nodup := by
  refine List.Nodup.of_map (fun e => e.1) ?_
  rw [n4WordS]
  split
  · rw [List.map_flatMap]
    refine nodup_flatMap_of_ne _ _ (n4_old_word_nodup c cyl _) ?_ ?_
    · intro e _
      exact List.Nodup.sublist (n4Arc_sublist c F cyl ell _ _) (by simp)
    · intro e _ f _ hef x hx hx'
      have h1 := eq_of_mem_n4Arc_val c F cyl hx
      have h2 := eq_of_mem_n4Arc_val c F cyl hx'
      rw [h1] at h2
      have hsrc : e.1.1 = f.1.1 := Sum.inl.inj (congrArg Prod.fst h2)
      have htgt : e.1.2 = f.1.2 := congrArg Prod.fst (Sum.inr.inj (congrArg Prod.snd h2))
      exact hef (Subtype.ext (Prod.ext hsrc htgt))
  · split
    · rw [List.map_flatMap]
      refine nodup_flatMap_of_ne _ _ (cyl.layerOrder _).nodup ?_ ?_
      · intro v _
        rw [List.map_flatMap]
        refine nodup_flatMap_of_ne _ _ List.nodup_range ?_ ?_
        · intro s _
          rw [n4FinalArc]
          split
          · exact List.Nodup.sublist (n4Arc_sublist c F cyl ell _ _) (by simp)
          · simp
        · intro s _ t _ hst x hx hx'
          rw [List.mem_map] at hx hx'
          obtain ⟨a, ha, rfl⟩ := hx
          obtain ⟨b, hb, hab⟩ := hx'
          exact absurd ((n4FinalArc_pair c F cyl ha).1.trans
            (n4FinalArc_pair c F cyl hb).1.symm) hst
      · intro v _ w _ hvw x hx hx'
        rw [List.map_flatMap, List.mem_flatMap] at hx hx'
        obtain ⟨s, -, hs⟩ := hx
        obtain ⟨t, -, ht⟩ := hx'
        rw [List.mem_map] at hs ht
        obtain ⟨a, ha, rfl⟩ := hs
        obtain ⟨b, hb, hab⟩ := ht
        have h1 := (n4FinalArc_pair c F cyl ha).2
        have h2 := (n4FinalArc_pair c F cyl hb).2
        rw [hab, h1] at h2
        exact hvw (Subtype.ext (Sum.inl.inj (congrArg Prod.snd h2)))
    · rw [List.map_flatMap]
      refine nodup_flatMap_of_ne _ _ (cyl.layerOrder _).nodup ?_ ?_
      · intro v _
        rw [List.map_flatMap]
        refine nodup_flatMap_of_ne _ _ List.nodup_range ?_ ?_
        · intro s _
          rw [n4StripArc]
          split
          · exact List.Nodup.sublist (n4Arc_sublist c F cyl ell _ _) (by simp)
          · simp
        · intro s hs t ht hst x hx hx'
          rw [List.mem_map] at hx hx'
          obtain ⟨a, ha, rfl⟩ := hx
          obtain ⟨b, hb, hab⟩ := hx'
          have h1 := (n4StripArc_pair c F cyl ha).2
          have h2 := (n4StripArc_pair c F cyl hb).2
          rw [hab, h1] at h2
          have hval := congrArg (fun p => (p.2.2 : Fin (F + 1)).val)
            (Sum.inr.inj (congrArg Prod.fst h2))
          have hs' : s < F + 1 := List.mem_range.mp hs
          have ht' : t < F + 1 := List.mem_range.mp ht
          simp only [finClamp_val (show s ≤ F by omega), finClamp_val (show t ≤ F by omega)] at hval
          exact hst hval
      · intro v _ w _ hvw x hx hx'
        rw [List.map_flatMap, List.mem_flatMap] at hx hx'
        obtain ⟨s, -, hs⟩ := hx
        obtain ⟨t, -, ht⟩ := hx'
        rw [List.mem_map] at hs ht
        obtain ⟨a, ha, rfl⟩ := hs
        obtain ⟨b, hb, hab⟩ := ht
        have h1 := (n4StripArc_pair c F cyl ha).2
        have h2 := (n4StripArc_pair c F cyl hb).2
        rw [hab, h1] at h2
        have hval := congrArg (fun p => p.1) (Sum.inr.inj (congrArg Prod.fst h2))
        exact hvw (Subtype.ext hval)

theorem n4WordS_complete (ell : Nat)
    (e : SpecTransitionArc (n4Spec c F (n4Inc c cyl)) ell) : e ∈ n4WordS c F cyl ell := by
  by_cases hr : ell % (F + 2) = 0
  · rcases Nat.eq_zero_or_pos ell with rfl | hpos
    · exact (n4_no_arc_zero c F cyl e).elim
    obtain ⟨u, g, k, hpair, hk1, hget, hlayerg⟩ := n4_leaf_arc_shape c F cyl hr e
    rw [n4WordS, if_pos hr]
    have hdm : ell / (F + 2) * (F + 2) + ell % (F + 2) = ell := Nat.div_add_mod' ell (F + 2)
    have hq : 0 < ell / (F + 2) := by
      rcases Nat.eq_zero_or_pos (ell / (F + 2)) with h | h
      · exfalso; rw [h] at hdm; omega
      · exact h
    set m := ell / (F + 2) - 1 with hm
    have hgm : c.layer g = m + 1 := by omega
    refine List.mem_flatMap.mpr ?_
    set v : LayerVertex c (m + 1) := ⟨g, hgm⟩ with hv
    set L := (cyl.transitionOrder m).incoming v with hL
    have hinc : n4Inc c cyl g = L.map (fun a => a.1.1) := n4Inc_eq_map' c cyl v
    rw [hinc, List.getElem?_map] at hget
    obtain ⟨a, ha, hau⟩ := Option.map_eq_some_iff.mp hget
    obtain ⟨hlt, hgetv⟩ := List.getElem?_eq_some_iff.mp ha
    have hmem : a ∈ L := by
      rw [← hgetv]
      exact List.getElem_mem hlt
    have hidx : L.idxOf a = k.val - 1 := by
      rw [← hgetv]
      exact ((cyl.transitionOrder m).incoming_nodup v).idxOf_getElem _ hlt
    have hatgt : a.1.2 = g := ((cyl.transitionOrder m).incoming_exact v a).mp hmem
    have hvert : (⟨a.1.2, a.2.2.2⟩ : LayerVertex c (m + 1)) = v := Subtype.ext hatgt
    have hslot : n4ArcSlot c F cyl a = k := by
      rw [n4ArcSlot, hvert, ← hL, hidx]
      have : k.val - 1 + 1 = k.val := by omega
      rw [this, finClamp_self]
    refine ⟨a, ?_, ?_⟩
    · refine List.mem_flatMap.mpr ⟨⟨a.1.1, a.2.2.1⟩, (cyl.layerOrder m).complete _, ?_⟩
      exact ((cyl.transitionOrder m).outgoing_exact _ a).mpr rfl
    · refine (mem_n4Arc c F cyl).mpr ?_
      rw [hpair, hau, hatgt, hslot]
  · by_cases hr2 : ell % (F + 2) = F + 1
    · obtain ⟨g, hpair, hlayerg, -⟩ := n4_final_arc_shape c F cyl hr2 e
      rw [n4WordS, if_neg hr, if_pos hr2]
      refine List.mem_flatMap.mpr ⟨⟨g, hlayerg⟩, (cyl.layerOrder _).complete _, ?_⟩
      refine List.mem_flatMap.mpr ⟨0, List.mem_range.mpr (by omega), ?_⟩
      rw [n4FinalArc, if_pos rfl]
      exact (mem_n4Arc c F cyl).mpr hpair
    · obtain ⟨g, k, hpair, hlayerg⟩ := n4_strip_arc_shape c F cyl hr hr2 e
      rw [n4WordS, if_neg hr, if_neg hr2]
      refine List.mem_flatMap.mpr ⟨⟨g, hlayerg⟩, (cyl.layerOrder _).complete _, ?_⟩
      refine List.mem_flatMap.mpr ⟨k.val, List.mem_range.mpr k.isLt, ?_⟩
      rw [n4StripArc, dif_pos k.isLt]
      exact (mem_n4Arc c F cyl).mpr hpair

/-! ## The two words are cyclic rotations of each other -/

theorem n4Word_rot (ell : Nat) : CyclicRotation (n4WordS c F cyl ell) (n4WordT c F cyl ell) := by
  by_cases hr : ell % (F + 2) = 0
  · rw [n4WordS, if_pos hr, n4WordT, if_pos hr]
    exact cyclicRotation_flatMap _ (cyl.transitionOrder (ell / (F + 2) - 1)).commonArcWord
  · rw [n4WordT, if_neg hr]
    exact cyclicRotation_refl _

end AllenderOQ3.Internal
