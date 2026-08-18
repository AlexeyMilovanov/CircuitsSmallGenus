import Mathlib
import AllenderOQ3.Internal.CycSortedWord
import AllenderOQ3.Internal.CFLayerBuilder
import AllenderOQ3.Internal.ComponentGateFacts
import AllenderOQ3.Internal.NonCrossingUnits
import AllenderOQ3.Internal.ConstantFreeLayers

/-!
# Reading a certified layer as a predecessor assignment

`exists_layerData` extracts from a certified non-crossing layer
`g : TransMonoid w` a predecessor assignment `P : Fin w → List (Fin w)` together
with a gate-type marking `K : Fin w → Bool` (`true` = AND, `false` = OR) such
that `g` computes, at every output slot `p`, the AND (resp. OR) of the input
slots `P p`.

Slots that carry a literal port or no vertex at all get `P p = []`; the empty
AND is `true` and the empty OR is `false`, so those slots are exactly the ones
on which `g` is constant, and the uniform formula still holds.

The arc word of `P` is cyclically sorted by source (`CycSortedSrc`): this is
precisely the incidence certificate of the layer, whose source-major and
target-major arc words agree up to rotation, read through the slot numbering.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace AllenderOQ3.Internal

section Extract

variable {n w : Nat} (c : ADRCircuit n) (cert : IncidenceCylinder c)
  (hW : TotalWidthAtMost c w) (ell : Nat)

/-! ## Coordinates -/

theorem vertCoord_symm_apply {m : Nat} (j : Nat) (h : j < (cert.layerOrder m).entries.length) :
    vertCoord c cert hW ((FullLayerIndexing c cert m).symm ⟨j, h⟩)
      = ⟨j, lt_of_lt_of_le h (layerOrder_length_le c cert hW m)⟩ := by
  apply Fin.ext
  change ((FullLayerIndexing c cert m) ((FullLayerIndexing c cert m).symm ⟨j, h⟩)).val = j
  rw [Equiv.apply_symm_apply]

theorem vertCoord_injective (m : Nat) :
    Function.Injective (fun u : LayerVertex c m => vertCoord c cert hW u) := by
  intro a b hab
  have h : (vertCoord c cert hW a).val = (vertCoord c cert hW b).val := congrArg Fin.val hab
  exact (FullLayerIndexing c cert m).injective (Fin.ext h)

theorem vertCoord_get {m : Nat} (i : Fin (cert.layerOrder m).entries.length) :
    (vertCoord c cert hW ((cert.layerOrder m).entries.get i)).val = i.val := by
  have h := full_symm_eq c cert m ((cert.layerOrder m).entries.get i) i rfl
  change ((FullLayerIndexing c cert m) ((cert.layerOrder m).entries.get i)).val = i.val
  rw [← h, Equiv.apply_symm_apply]

/-! ## Arc endpoints along the certificate blocks -/

theorem arcTarget_of_mem_incoming {v : LayerVertex c (ell + 1)} {e : TransitionArc c ell}
    (he : e ∈ (cert.transitionOrder ell).incoming v) : arcTarget e = v :=
  Subtype.ext (((cert.transitionOrder ell).incoming_exact v e).mp he)

theorem arcSource_of_mem_outgoing {u : LayerVertex c ell} {e : TransitionArc c ell}
    (he : e ∈ (cert.transitionOrder ell).outgoing u) : arcSource e = u :=
  Subtype.ext (((cert.transitionOrder ell).outgoing_exact u e).mp he)

theorem incoming_eq_nil_of_literal (hwf : WellFormedADR c) (v : LayerVertex c (ell + 1))
    (i : Fin n) (b : Bool) (hk : c.kind v.val = ADRGate.literal i b) :
    (cert.transitionOrder ell).incoming v = [] := by
  rcases hnil : (cert.transitionOrder ell).incoming v with _ | ⟨e, t⟩
  · rfl
  · exfalso
    have he : e ∈ (cert.transitionOrder ell).incoming v := by
      rw [hnil]; exact List.mem_cons_self
    have h2 : e.1.2 = v.1 := ((cert.transitionOrder ell).incoming_exact v e).mp he
    have hedge : c.edge e.1.1 v.1 = true := by rw [← h2]; exact e.2.1
    have hzero := hwf.2 v.1 ⟨i, b, hk⟩ e.1.1
    rw [hzero] at hedge
    exact Bool.false_ne_true hedge

/-! ## The extracted data -/

/-- The `(source, target)` coordinate pair of an arc. -/
noncomputable def arcKey (e : TransitionArc c ell) : Fin w × Fin w :=
  (vertCoord c cert hW (arcSource e), vertCoord c cert hW (arcTarget e))

/-- The predecessor slots of output slot `p`. -/
noncomputable def slotPreds (p : Fin w) : List (Fin w) :=
  if h : p.val < (cert.layerOrder (ell + 1)).entries.length then
    ((cert.transitionOrder ell).incoming ((FullLayerIndexing c cert (ell + 1)).symm ⟨p.val, h⟩)).map
      (fun e => vertCoord c cert hW (arcSource e))
  else []

/-- The gate marking of output slot `p`: `true` means "AND" (or a slot forced
`true`), `false` means "OR" (or a slot forced `false`). -/
noncomputable def slotKind (x : Fin n → Bool) (p : Fin w) : Bool :=
  if h : p.val < (cert.layerOrder (ell + 1)).entries.length then
    match c.kind ((FullLayerIndexing c cert (ell + 1)).symm ⟨p.val, h⟩).val with
    | .literal i b => if b then !(x i) else x i
    | .andGate => true
    | .orGate => false
  else false

theorem slotPreds_of_lt (p : Fin w) (h : p.val < (cert.layerOrder (ell + 1)).entries.length) :
    slotPreds c cert hW ell p
      = ((cert.transitionOrder ell).incoming
          ((FullLayerIndexing c cert (ell + 1)).symm ⟨p.val, h⟩)).map
        (fun e => vertCoord c cert hW (arcSource e)) := dif_pos h

theorem slotPreds_of_ge (p : Fin w) (h : ¬ p.val < (cert.layerOrder (ell + 1)).entries.length) :
    slotPreds c cert hW ell p = [] := dif_neg h

/-! ## Basic shape of the extracted assignment -/

theorem slotPreds_nodup (p : Fin w) : (slotPreds c cert hW ell p).Nodup := by
  rw [slotPreds]
  split
  · rename_i h
    refine List.Nodup.map_on ?_ ((cert.transitionOrder ell).incoming_nodup _)
    intro e he f hf hef
    have h1 : arcSource e = arcSource f := vertCoord_injective c cert hW ell hef
    have ht1 : e.1.2 = _ := ((cert.transitionOrder ell).incoming_exact _ e).mp he
    have ht2 : f.1.2 = _ := ((cert.transitionOrder ell).incoming_exact _ f).mp hf
    exact Subtype.ext (Prod.ext (congrArg Subtype.val h1) (by rw [ht1, ht2]))
  · exact List.nodup_nil

theorem slotPreds_length (hN : HMVNormal c) (p : Fin w) :
    (slotPreds c cert hW ell p).length ≤ 2 := by
  rw [slotPreds]
  split
  · rename_i h
    rw [List.length_map]
    set v := (FullLayerIndexing c cert (ell + 1)).symm ⟨p.val, h⟩ with hv
    rw [length_incoming_eq_predecessorCount hN.1.1 (cert.transitionOrder ell) v]
    cases hk : c.kind v.val with
    | literal i b =>
      have hnil := incoming_eq_nil_of_literal c cert ell hN.1 v i b hk
      have hlen := length_incoming_eq_predecessorCount hN.1.1 (cert.transitionOrder ell) v
      rw [hnil, List.length_nil] at hlen
      omega
    | andGate => exact hN.2 v.1 (by rw [hk]; rfl)
    | orGate => exact hN.2 v.1 (by rw [hk]; rfl)
  · simp

/-! ## Semantics -/

theorem mem_slotPreds_iff (hwf : WellFormedADR c) (p : Fin w)
    (h : p.val < (cert.layerOrder (ell + 1)).entries.length) (q : Fin w) :
    q ∈ slotPreds c cert hW ell p ↔
      ∃ (u : Fin c.gateCount) (hu : c.edge u
          ((FullLayerIndexing c cert (ell + 1)).symm ⟨p.val, h⟩).val = true),
        q = vertCoord c cert hW ⟨u, layer_pred_eq c hwf hu⟩ := by
  rw [slotPreds_of_lt c cert hW ell p h]
  constructor
  · intro hq
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hq
    have ht : e.1.2 = ((FullLayerIndexing c cert (ell + 1)).symm ⟨p.val, h⟩).val :=
      ((cert.transitionOrder ell).incoming_exact _ e).mp he
    have hu : c.edge e.1.1 ((FullLayerIndexing c cert (ell + 1)).symm ⟨p.val, h⟩).val = true := by
      rw [← ht]; exact e.2.1
    exact ⟨e.1.1, hu, congrArg (vertCoord c cert hW) (Subtype.ext rfl)⟩
  · rintro ⟨u, hu, rfl⟩
    refine List.mem_map.mpr ⟨incomingArc hwf.1 _ hu, ?_, ?_⟩
    · exact ((cert.transitionOrder ell).incoming_exact _ _).mpr rfl
    · exact congrArg (vertCoord c cert hW) (Subtype.ext rfl)

theorem layerTransMap_eq_all (hN : HMVNormal c) (x : Fin n → Bool) (z : Config w) (p : Fin w)
    (hK : slotKind c cert ell x p = true) :
    layerTransMap c cert x ell z p = (slotPreds c cert hW ell p).all (fun q => z q) := by
  by_cases h : p.val < (cert.layerOrder (ell + 1)).entries.length
  · set v := (FullLayerIndexing c cert (ell + 1)).symm ⟨p.val, h⟩ with hv
    cases hk : c.kind v.val with
    | literal i b =>
      have hnil : slotPreds c cert hW ell p = [] := by
        rw [slotPreds_of_lt c cert hW ell p h, ← hv,
          incoming_eq_nil_of_literal c cert ell hN.1 v i b hk]
        rfl
      have hval : layerTransMap c cert x ell z p = (if b then !(x i) else x i) := by
        dsimp only [layerTransMap]
        rw [dif_pos h]
        change (match c.kind v.val with
          | .literal i b => if b then !(x i) else x i
          | .andGate => _
          | .orGate => _) = _
        rw [hk]
      have hKv : (if b then !(x i) else x i) = true := by
        rw [slotKind, dif_pos h, ← hv] at hK
        change (match c.kind v.val with
          | .literal i b => (if b then !(x i) else x i)
          | .andGate => true
          | .orGate => false) = true at hK
        rw [hk] at hK
        exact hK
      rw [hnil, hval, hKv]
      rfl
    | andGate =>
      have hkind : c.kind ((FullLayerIndexing c cert (ell + 1)).symm ⟨p.val, h⟩).val
          = ADRGate.andGate := hk
      apply bool_eq_of_iff
      rw [List.all_eq_true, layerTransMap_and_true_iff c cert hN.1 hW x z h hkind]
      constructor
      · intro hall q hq
        obtain ⟨u, hu, rfl⟩ := (mem_slotPreds_iff c cert hW ell hN.1 p h q).mp hq
        exact hall u hu
      · intro hall u hu
        exact hall _ ((mem_slotPreds_iff c cert hW ell hN.1 p h _).mpr ⟨u, hu, rfl⟩)
    | orGate =>
      exfalso
      rw [slotKind, dif_pos h, ← hv] at hK
      change (match c.kind v.val with
        | .literal i b => (if b then !(x i) else x i)
        | .andGate => true
        | .orGate => false) = true at hK
      rw [hk] at hK
      exact Bool.false_ne_true hK
  · exfalso
    rw [slotKind, dif_neg h] at hK
    exact Bool.false_ne_true hK

theorem layerTransMap_eq_any (hN : HMVNormal c) (x : Fin n → Bool) (z : Config w) (p : Fin w)
    (hK : slotKind c cert ell x p = false) :
    layerTransMap c cert x ell z p = (slotPreds c cert hW ell p).any (fun q => z q) := by
  by_cases h : p.val < (cert.layerOrder (ell + 1)).entries.length
  · set v := (FullLayerIndexing c cert (ell + 1)).symm ⟨p.val, h⟩ with hv
    cases hk : c.kind v.val with
    | literal i b =>
      have hnil : slotPreds c cert hW ell p = [] := by
        rw [slotPreds_of_lt c cert hW ell p h, ← hv,
          incoming_eq_nil_of_literal c cert ell hN.1 v i b hk]
        rfl
      have hval : layerTransMap c cert x ell z p = (if b then !(x i) else x i) := by
        dsimp only [layerTransMap]
        rw [dif_pos h]
        change (match c.kind v.val with
          | .literal i b => if b then !(x i) else x i
          | .andGate => _
          | .orGate => _) = _
        rw [hk]
      have hKv : (if b then !(x i) else x i) = false := by
        rw [slotKind, dif_pos h, ← hv] at hK
        change (match c.kind v.val with
          | .literal i b => (if b then !(x i) else x i)
          | .andGate => true
          | .orGate => false) = false at hK
        rw [hk] at hK
        exact hK
      rw [hnil, hval, hKv]
      rfl
    | andGate =>
      exfalso
      rw [slotKind, dif_pos h, ← hv] at hK
      change (match c.kind v.val with
        | .literal i b => (if b then !(x i) else x i)
        | .andGate => true
        | .orGate => false) = false at hK
      rw [hk] at hK
      exact Bool.noConfusion hK
    | orGate =>
      have hkind : c.kind ((FullLayerIndexing c cert (ell + 1)).symm ⟨p.val, h⟩).val
          = ADRGate.orGate := hk
      apply bool_eq_of_iff
      rw [List.any_eq_true, layerTransMap_or_true_iff c cert hN.1 hW x z h hkind]
      constructor
      · rintro ⟨u, hu, hz⟩
        exact ⟨_, (mem_slotPreds_iff c cert hW ell hN.1 p h _).mpr ⟨u, hu, rfl⟩, hz⟩
      · rintro ⟨q, hq, hz⟩
        obtain ⟨u, hu, rfl⟩ := (mem_slotPreds_iff c cert hW ell hN.1 p h q).mp hq
        exact ⟨u, hu, hz⟩
  · have hzero : layerTransMap c cert x ell z p = false := by
      dsimp only [layerTransMap]
      rw [dif_neg h]
    rw [hzero, slotPreds_of_ge c cert hW ell p h]
    rfl

/-! ## Cyclic sortedness of the extracted arc word -/

theorem srcSorted_source_word :
    SrcSorted ((((cert.layerOrder ell).entries.flatMap
      (cert.transitionOrder ell).outgoing)).map (arcKey c cert hW ell)) := by
  have h1 : GroupedAlong arcSource (cert.layerOrder ell).entries
      ((cert.layerOrder ell).entries.flatMap (cert.transitionOrder ell).outgoing) :=
    groupedAlong_flatMap arcSource (cert.transitionOrder ell).outgoing
      (fun u e he => arcSource_of_mem_outgoing c cert ell he)
      (cert.layerOrder ell).entries (cert.layerOrder ell).nodup
  have h2 := groupedAlong_map arcSource (fun pr : Fin w × Fin w => pr.1)
    (arcKey c cert hW ell) (fun u => vertCoord c cert hW u)
    (vertCoord_injective c cert hW ell) (fun _ => rfl)
    (cert.layerOrder ell).entries _ h1
  have h3 : ((cert.layerOrder ell).entries.map (fun u => vertCoord c cert hW u)).Pairwise
      (· < ·) := by
    rw [List.pairwise_map]
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    have hvi := vertCoord_get c cert hW (m := ell) ⟨i, hi⟩
    have hvj := vertCoord_get c cert hW (m := ell) ⟨j, hj⟩
    have hi' : vertCoord c cert hW ((cert.layerOrder ell).entries[i]'hi)
        = vertCoord c cert hW ((cert.layerOrder ell).entries.get ⟨i, hi⟩) := rfl
    have hj' : vertCoord c cert hW ((cert.layerOrder ell).entries[j]'hj)
        = vertCoord c cert hW ((cert.layerOrder ell).entries.get ⟨j, hj⟩) := rfl
    rw [hi', hj', Fin.lt_def, hvi, hvj]
    exact hij
  exact pairwise_le_of_groupedAlong (fun pr : Fin w × Fin w => pr.1) _ _ h3 h2

theorem map_key_target_word :
    (((cert.layerOrder (ell + 1)).entries.flatMap
        (cert.transitionOrder ell).incoming)).map (arcKey c cert hW ell)
      = arcPairWord (slotPreds c cert hW ell) := by
  classical
  set TL := (cert.layerOrder (ell + 1)).entries with hTL
  have hLw : TL.length ≤ w := layerOrder_length_le c cert hW (ell + 1)
  -- the target word, indexed by positions
  have hstep1 : (TL.flatMap (cert.transitionOrder ell).incoming).map (arcKey c cert hW ell)
      = (List.finRange TL.length).flatMap
        (fun i => ((cert.transitionOrder ell).incoming (TL.get i)).map (arcKey c cert hW ell)) := by
    conv_lhs => rw [← List.map_get_finRange TL]
    rw [List.flatMap_map, List.map_flatMap]
  have hTake : (List.finRange w).take TL.length
      = (List.finRange TL.length).map
        (fun i => (⟨i.val, lt_of_lt_of_le i.isLt hLw⟩ : Fin w)) := by
    apply List.ext_getElem
    · simp [hLw]
    · intro i h1 h2
      apply Fin.ext
      simp
  -- the arc word, restricted to the used slots
  have hdrop : ((List.finRange w).drop TL.length).flatMap (arcBlock (slotPreds c cert hW ell))
      = [] := by
    refine List.flatMap_eq_nil_iff.mpr (fun p hp => ?_)
    have hge : TL.length ≤ p.val := by
      by_contra hcon
      push_neg at hcon
      have h1 : p ∈ (List.finRange w).take TL.length := by
        rw [hTake]
        exact List.mem_map.mpr ⟨⟨p.val, hcon⟩, List.mem_finRange _, Fin.ext rfl⟩
      have hnd : ((List.finRange w).take TL.length
          ++ (List.finRange w).drop TL.length).Nodup := by
        rw [List.take_append_drop]
        exact List.nodup_finRange w
      exact List.disjoint_of_nodup_append hnd h1 hp
    rw [arcBlock, slotPreds_of_ge c cert hW ell p (not_lt.mpr hge)]
    rfl
  have hstep2 : arcPairWord (slotPreds c cert hW ell)
      = ((List.finRange w).take TL.length).flatMap (arcBlock (slotPreds c cert hW ell)) := by
    rw [arcPairWord, ← List.take_append_drop TL.length (List.finRange w), List.flatMap_append,
      hdrop, List.append_nil, List.take_append_drop]
  have hblocks : ∀ i : Fin TL.length,
      arcBlock (slotPreds c cert hW ell) ⟨i.val, lt_of_lt_of_le i.isLt hLw⟩
        = ((cert.transitionOrder ell).incoming (TL.get i)).map (arcKey c cert hW ell) := by
    intro i
    have hi : (⟨i.val, lt_of_lt_of_le i.isLt hLw⟩ : Fin w).val < TL.length := i.isLt
    have hvtx : (FullLayerIndexing c cert (ell + 1)).symm ⟨i.val, hi⟩ = TL.get i :=
      full_symm_eq c cert (ell + 1) (TL.get i) ⟨i.val, hi⟩ rfl
    rw [arcBlock, slotPreds_of_lt c cert hW ell ⟨i.val, lt_of_lt_of_le i.isLt hLw⟩ hi, hvtx,
      List.map_map]
    refine List.map_congr_left (fun e he => ?_)
    have htgt : arcTarget e = TL.get i := arcTarget_of_mem_incoming c cert ell he
    apply Prod.ext
    · rfl
    · change (⟨i.val, lt_of_lt_of_le i.isLt hLw⟩ : Fin w) = vertCoord c cert hW (arcTarget e)
      rw [htgt, ← hvtx, vertCoord_symm_apply]
  rw [hstep1, hstep2, hTake, List.flatMap_map]
  exact List.flatMap_congr (fun i _ => (hblocks i).symm)

theorem slotPreds_cycSorted : CycSortedSrc (arcPairWord (slotPreds c cert hW ell)) := by
  obtain ⟨p₁, q₁, hS, hT⟩ := (cert.transitionOrder ell).commonArcWord
  refine ⟨q₁.map (arcKey c cert hW ell), p₁.map (arcKey c cert hW ell), ?_, ?_⟩
  · rw [← map_key_target_word c cert hW ell, hT, List.map_append]
  · have h := srcSorted_source_word c cert hW ell
    rw [hS, List.map_append] at h
    exact h

end Extract

variable {w : Nat}

/-- **A certified layer is an AND/OR assignment with a cyclically sorted arc
word.** -/
theorem exists_layerData {g : TransMonoid w} (hg : isNonCrossingMap w g) :
    ∃ (P : Fin w → List (Fin w)) (K : Fin w → Bool),
      (∀ p, (P p).Nodup) ∧ (∀ p, (P p).length ≤ 2) ∧
      CycSortedSrc (arcPairWord P) ∧
      (∀ (z : Config w) (p : Fin w), K p = true →
          runTrans g z p = (P p).all (fun q => z q)) ∧
      (∀ (z : Config w) (p : Fin w), K p = false →
          runTrans g z p = (P p).any (fun q => z q)) := by
  obtain ⟨n, c, cert, ell, x, hN, hW, hgeq⟩ := hg
  refine ⟨slotPreds c cert hW ell, slotKind c cert ell x,
    slotPreds_nodup c cert hW ell, slotPreds_length c cert hW ell hN,
    slotPreds_cycSorted c cert hW ell, ?_, ?_⟩
  · intro z p hK
    rw [← hgeq]
    exact layerTransMap_eq_all c cert hW ell hN x z p hK
  · intro z p hK
    rw [← hgeq]
    exact layerTransMap_eq_any c cert hW ell hN x z p hK

end AllenderOQ3.Internal
