import AllenderOQ3.Internal.ComponentGateFacts
import AllenderOQ3.Internal.ArcWordBlocksPartial
import AllenderOQ3.Internal.LivePosition
import AllenderOQ3.Internal.RotationPosition
import AllenderOQ3.Internal.TrueRun

/-!
# The merging-run core of the component lemma (Part A)

This file proves the single geometric fact that drives both halves of the
component lemma: **an input piece is touched by at most one output piece**.

`Touch I K` holds when some `true` target coordinate of the output piece `K`
has a predecessor whose source coordinate lies in the input piece `I`.  The
theorem `touch_uniq` says that if two output pieces `K1`, `K2` both touch the
same input piece `I`, they are equal.  The proof is the merging run: the two
source coordinates lie in the single `true` interval `I`; over the source
position circle they lie in one cyclic interval (`piece_to_live_position_interval`);
the arcs from that interval form one contiguous block of the common arc word
(`exists_arcWord_interval_block_pos`); transported to the target-major word
(`commonArcWord`) the merging-run lemma (`cyclic_merging_run`) shows every
target strictly between the two witnesses receives *all* of its predecessors
from inside `I`, hence — the layer being constant-free — evaluates to `true`;
that produces a contiguous `true` run of the output joining the two witness
targets (`rotation_position_interval` + `mem_same_piece_of_true_run`), so the
two output pieces coincide.

This replaces the earlier (mathematically **false**) helpers
`nbr_covers_preds` / `nbr_eq_of_layerTransMap_true`, which omitted the
equal-count hypothesis and fail on layers whose input blocks merge.
-/

set_option autoImplicit false

namespace AllenderOQ3.Internal

attribute [local instance] Classical.propDecidable

/-- `vertCoord` and `idxOfVtx` are the same width coordinate of a source vertex. -/
theorem vertCoord_eq_idxOfVtx {n w : Nat} (c : ADRCircuit n) (cert : IncidenceCylinder c)
    (hW : TotalWidthAtMost c w) (ell : Nat) (u : LayerVertex c ell) :
    vertCoord c cert hW u = idxOfVtx c cert ell (layerEntries_length_le hW ell) u := by
  apply Fin.ext
  rfl

/-- **`I` is touched by `K`**: some `true` target of `K` has a predecessor whose
source coordinate lies in `I`. -/
def Touch {n w : Nat} (c : ADRCircuit n) (cert : IncidenceCylinder c) (ell : Nat)
    (hfull : (cert.layerOrder (ell + 1)).entries.length = w) (hW : TotalWidthAtMost c w)
    (I K : Config w) : Prop :=
  ∃ (j : Fin w) (u : LayerVertex c ell),
    K j = true ∧
    c.edge u.val (vtxAt c cert (ell + 1) hfull j).val = true ∧
    I (idxOfVtx c cert ell (layerEntries_length_le hW ell) u) = true

/-- Every predecessor arc of `v` belongs to its incoming block. -/
theorem mem_incoming_of_edge {n : Nat} (c : ADRCircuit n) (cert : IncidenceCylinder c) (ell : Nat)
    {v : LayerVertex c (ell + 1)} {u : LayerVertex c ell}
    (hu : c.edge u.val v.val = true) :
    (⟨(u.val, v.val), hu, u.2, v.2⟩ : TransitionArc c ell)
      ∈ (cert.transitionOrder ell).incoming v :=
  ((cert.transitionOrder ell).incoming_exact v _).mpr rfl

/-- The merging-run key hypothesis: an incoming arc's target is its block key. -/
theorem arcTarget_of_mem_incoming {n : Nat} (c : ADRCircuit n) (cert : IncidenceCylinder c)
    (ell : Nat) (v : LayerVertex c (ell + 1)) (e : TransitionArc c ell)
    (he : e ∈ (cert.transitionOrder ell).incoming v) : arcTarget e = v := by
  apply Subtype.ext
  exact ((cert.transitionOrder ell).incoming_exact v e).mp he

section Merge

variable {n w : Nat} (c : ADRCircuit n) (cert : IncidenceCylinder c)
variable (xIn : Fin n → Bool) (ell : Nat)
variable (hN : HMVNormal c) (hW : TotalWidthAtMost c w)
variable (hfull : (cert.layerOrder (ell + 1)).entries.length = w)
variable (hcf : ConstantFreeLayer c ell)
variable (x : Config w)

include hN hcf in
/-- **The merging run.**  If two output pieces both touch the same input piece,
they are equal. -/
theorem touch_uniq {I K1 K2 : Config w}
    (hI : I ∈ intervalsOf x)
    (hK1 : K1 ∈ intervalsOf (layerTransMap c cert xIn ell x))
    (hK2 : K2 ∈ intervalsOf (layerTransMap c cert xIn ell x))
    (ht1 : Touch c cert ell hfull hW I K1)
    (ht2 : Touch c cert ell hfull hW I K2) :
    K1 = K2 := by
  classical
  set y := layerTransMap c cert xIn ell x with hy
  have hLe : (cert.layerOrder ell).entries.length ≤ w := layerEntries_length_le hW ell
  set L := (cert.layerOrder ell).entries.length with hLdef
  obtain ⟨j1, u1, hK1j1, he1edge, hIu1⟩ := ht1
  obtain ⟨j2, u2, hK2j2, he2edge, hIu2⟩ := ht2
  set v1 := vtxAt c cert (ell + 1) hfull j1 with hv1def
  set v2 := vtxAt c cert (ell + 1) hfull j2 with hv2def
  -- Reduce to the case `j1 ≠ j2`.
  by_cases hjeq : j1 = j2
  · subst hjeq
    exact eq_of_mem_intervalsOf_of_true hK1 hK2 hK1j1 hK2j2
  · -- Source positions.
    set p1 : Fin L := vtxPos ell u1 with hp1def
    set p2 : Fin L := vtxPos ell u2 with hp2def
    have hp1val : (idxOfVtx c cert ell hLe u1).val = p1.val := rfl
    have hp2val : (idxOfVtx c cert ell hLe u2).val = p2.val := rfl
    -- Unpack the input piece.
    obtain ⟨aI, lenI, hcycI, hIeq⟩ := mem_intervalsOf.mp hI
    have hIu1' : pieceConfig aI lenI (idxOfVtx c cert ell hLe u1) = true := by
      rw [← hIeq]; exact hIu1
    have hIu2' : pieceConfig aI lenI (idxOfVtx c cert ell hLe u2) = true := by
      rw [← hIeq]; exact hIu2
    -- Live-position interval of `I`.
    have hLw : L ≤ w := hLe
    have hlive : ∃ j, j.val < L ∧ (pieceConfig aI lenI) j = true :=
      ⟨idxOfVtx c cert ell hLe u1, by rw [hp1val]; exact p1.isLt, hIu1'⟩
    obtain ⟨a', haL, len', hlen'L, ha'true, hbridge⟩ :=
      piece_to_live_position_interval hLw hcycI hlive
    set start' : Fin L := ⟨a'.val, haL⟩ with hstart'def
    have hInterval1 : ∃ k, k < len' ∧ finShift k start' = p1 := by
      apply (hbridge p1).2
      have : (⟨p1.val, lt_of_lt_of_le p1.isLt hLw⟩ : Fin w) = idxOfVtx c cert ell hLe u1 := by
        apply Fin.ext; rw [hp1val]
      rw [this]; exact hIu1'
    have hInterval2 : ∃ k, k < len' ∧ finShift k start' = p2 := by
      apply (hbridge p2).2
      have : (⟨p2.val, lt_of_lt_of_le p2.isLt hLw⟩ : Fin w) = idxOfVtx c cert ell hLe u2 := by
        apply Fin.ext; rw [hp2val]
      rw [this]; exact hIu2'
    -- The interval block of the source-major arc word.
    obtain ⟨P, Q, hrotPQ, hP_src, hQ_src, hP_all⟩ :=
      exists_arcWord_interval_block_pos (c := c) (cert := cert) ell start' len' hlen'L
    -- The two witness arcs (inline).
    set e1 : TransitionArc c ell := ⟨(u1.val, v1.val), he1edge, u1.2, v1.2⟩ with he1def
    set e2 : TransitionArc c ell := ⟨(u2.val, v2.val), he2edge, u2.2, v2.2⟩ with he2def
    have he1src : arcSource e1 = u1 := rfl
    have he2src : arcSource e2 = u2 := rfl
    have he1tgt : arcTarget e1 = v1 := rfl
    have he2tgt : arcTarget e2 = v2 := rfl
    -- Both witnesses lie in the source block `P`.
    have he1P : e1 ∈ P := by
      apply hP_all
      obtain ⟨k, hk, hke⟩ := hInterval1
      exact ⟨k, hk, by rw [he1src]; exact hke.symm⟩
    have he2P : e2 ∈ P := by
      apply hP_all
      obtain ⟨k, hk, hke⟩ := hInterval2
      exact ⟨k, hk, by rw [he2src]; exact hke.symm⟩
    have he1ne2 : e1 ≠ e2 := by
      intro h
      apply hjeq
      have hvv : v1 = v2 := by rw [← he1tgt, ← he2tgt, h]
      have := congrArg (idxOfVtx c cert (ell + 1) hfull.le) hvv
      rwa [hv1def, hv2def, idxOfVtx_vtxAt, idxOfVtx_vtxAt] at this
    -- Transport the block to the target-major word.
    have hrotTgt : CyclicRotation
        ((cert.layerOrder (ell + 1)).entries.flatMap (cert.transitionOrder ell).incoming)
        (P ++ Q) :=
      cyclicRotation_trans (cyclicRotation_symm (cert.transitionOrder ell).commonArcWord) hrotPQ
    -- A source arc in `P` has its source coordinate in `x`.
    have hP_in_I : ∀ e ∈ P, x (idxOfVtx c cert ell hLe (arcSource e)) = true := by
      intro e he
      obtain ⟨k, hk, hke⟩ := hP_src e he
      have hbr := (hbridge (finShift k start')).1 ⟨k, hk, rfl⟩
      have hcoord : (⟨(finShift k start').val, lt_of_lt_of_le (finShift k start').isLt hLw⟩ : Fin w)
          = idxOfVtx c cert ell hLe (arcSource e) := by
        apply Fin.ext
        exact (congrArg Fin.val hke).symm
      rw [hcoord] at hbr
      have hIle : I (idxOfVtx c cert ell hLe (arcSource e)) = true := by rw [hIeq]; exact hbr
      exact le_of_isIntervalPiece (mem_intervalsOf.mp hI) hIle
    -- The ordered-merge helper.
    have merge_ordered : ∀ (ja jb : Fin w) (Ka Kb : Config w)
        (ea eb : TransitionArc c ell)
        (heaT : arcTarget ea = vtxAt c cert (ell + 1) hfull ja)
        (hebT : arcTarget eb = vtxAt c cert (ell + 1) hfull jb),
        ja ≠ jb →
        Ka ∈ intervalsOf y → Kb ∈ intervalsOf y →
        Ka ja = true → Kb jb = true →
        ∀ S1 SM S3 : List (TransitionArc c ell),
          P = S1 ++ ea :: (SM ++ eb :: S3) → Ka = Kb := by
      intro ja jb Ka Kb ea eb heaT hebT hjne hKa hKb hKaja hKbjb S1 SM S3 hPeq
      set va := vtxAt c cert (ell + 1) hfull ja with hvadef
      set vb := vtxAt c cert (ell + 1) hfull jb with hvbdef
      -- Reshape the rotation into merging-run form.
      have hrotForm : CyclicRotation
          ((cert.layerOrder (ell + 1)).entries.flatMap (cert.transitionOrder ell).incoming)
          ((S1 ++ ea :: (SM ++ eb :: S3)) ++ Q) := by
        rw [← hPeq]; exact hrotTgt
      have hea_inc : ea ∈ (cert.transitionOrder ell).incoming va := by
        apply ((cert.transitionOrder ell).incoming_exact va ea).mpr
        exact congrArg Subtype.val heaT
      have heb_inc : eb ∈ (cert.transitionOrder ell).incoming vb := by
        apply ((cert.transitionOrder ell).incoming_exact vb eb).mpr
        exact congrArg Subtype.val hebT
      have hva_mem : va ∈ (cert.layerOrder (ell + 1)).entries :=
        (cert.layerOrder (ell + 1)).complete va
      have hvb_mem : vb ∈ (cert.layerOrder (ell + 1)).entries :=
        (cert.layerOrder (ell + 1)).complete vb
      have hvab_ne : va ≠ vb := by
        intro h
        apply hjne
        have := congrArg (idxOfVtx c cert (ell + 1) hfull.le) h
        rwa [hvadef, hvbdef, idxOfVtx_vtxAt, idxOfVtx_vtxAt] at this
      obtain ⟨T2', T3', hrotT, hSM⟩ :=
        cyclic_merging_run (key := arcTarget) (inc := (cert.transitionOrder ell).incoming)
          (T := (cert.layerOrder (ell + 1)).entries)
          (cert.layerOrder (ell + 1)).nodup (cert.transitionOrder ell).incoming_nodup
          (arcTarget_of_mem_incoming c cert ell) hva_mem hvb_mem hvab_ne hea_inc heb_inc hrotForm
      have hSM_subP : ∀ e ∈ SM, e ∈ P := by
        intro e he
        rw [hPeq]
        exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _
          (List.mem_append.mpr (Or.inl he))))
      -- Every target of `T2'` is `true` under `y`.
      have hT2'_true : ∀ v ∈ T2', y (idxOfVtx c cert (ell + 1) hfull.le v) = true := by
        intro v hv
        set jv := idxOfVtx c cert (ell + 1) hfull.le v with hjvdef
        have hvtx : vtxAt c cert (ell + 1) hfull jv = v := vtxAt_idxOfVtx (ell + 1) hfull v
        have hv_pred_true : ∀ (u' : LayerVertex c ell),
            c.edge u'.val v.val = true → x (idxOfVtx c cert ell hLe u') = true := by
          intro u' hu'
          have harc : (⟨(u'.val, v.val), hu', u'.2, v.2⟩ : TransitionArc c ell)
              ∈ (cert.transitionOrder ell).incoming v := mem_incoming_of_edge c cert ell hu'
          have hin_P := hSM_subP _ (hSM v hv _ harc)
          have hsrc := hP_in_I _ hin_P
          have : arcSource (⟨(u'.val, v.val), hu', u'.2, v.2⟩ : TransitionArc c ell) = u' := rfl
          rwa [this] at hsrc
        rcases kind_and_or_or_of_constantFree c hcf v with hand | hor
        · have hk : c.kind (vtxAt c cert (ell + 1) hfull jv).val = ADRGate.andGate := by
            rw [hvtx]; exact hand
          rw [hy, layerTransMap_and (x := xIn) hLe hfull hN.1 x jv hk]
          intro u' hu'edge
          exact hv_pred_true u' (by rwa [hvtx] at hu'edge)
        · have hk : c.kind (vtxAt c cert (ell + 1) hfull jv).val = ADRGate.orGate := by
            rw [hvtx]; exact hor
          have hne := incoming_ne_nil_of_constantFree c cert hN.1 hcf v
          obtain ⟨e0, he0⟩ := List.exists_mem_of_ne_nil _ hne
          have he0tgt : arcTarget e0 = v := arcTarget_of_mem_incoming c cert ell v e0 he0
          have he0edge : c.edge (arcSource e0).val v.val = true := by
            have h1 : c.edge e0.1.1 e0.1.2 = true := e0.2.1
            have h2 : e0.1.2 = v.val := congrArg Subtype.val he0tgt
            rw [h2] at h1
            exact h1
          have hu0true : x (idxOfVtx c cert ell hLe (arcSource e0)) = true :=
            hP_in_I _ (hSM_subP _ (hSM v hv e0 he0))
          rw [hy, layerTransMap_or (x := xIn) hLe hfull hN.1 x jv hk]
          exact ⟨arcSource e0, by rwa [hvtx], hu0true⟩
      -- Positional structure of the target run.
      obtain ⟨st, d, hst1, hst2, hst3, hdlen⟩ :=
        rotation_position_interval (c := c) (cert := cert) hfull hrotT
      have hstja : st = ja := by rw [← hst1, hvadef, idxOfVtx_vtxAt]
      have hjbfin : jb = finShift (d + 1) st := by rw [← hst2, hvbdef, idxOfVtx_vtxAt]
      -- `y` true along the whole run.
      have hrun : ∀ k, k ≤ d + 1 → y (finShift k st) = true := by
        intro k hk
        rcases Nat.eq_zero_or_pos k with hk0 | hkpos
        · subst hk0
          rw [finShift_zero, hstja]
          exact le_of_isIntervalPiece (mem_intervalsOf.mp hKa) hKaja
        · by_cases hkd : k ≤ d
          · have hmemcoord : finShift k st ∈ T2'.map (idxOfVtx c cert (ell + 1) hfull.le) := by
              rw [hst3, List.mem_map]
              refine ⟨k - 1, ?_, ?_⟩
              · rw [List.mem_range]; omega
              · have : k - 1 + 1 = k := by omega
                rw [this]
            rw [List.mem_map] at hmemcoord
            obtain ⟨v, hvmem, hvcoord⟩ := hmemcoord
            rw [← hvcoord]
            exact hT2'_true v hvmem
          · have hkeq : k = d + 1 := by omega
            subst hkeq
            rw [← hjbfin]
            exact le_of_isIntervalPiece (mem_intervalsOf.mp hKb) hKbjb
      have hKast : Ka st = true := by rw [hstja]; exact hKaja
      have hKbjb' : Kb (finShift (d + 1) st) = true := by rw [← hjbfin]; exact hKbjb
      exact mem_same_piece_of_true_run hKa hKb hKast hKbjb' hrun rfl
    -- Split `P` around `e1` and orient.
    obtain ⟨A1, B1, hPsplit1⟩ := List.append_of_mem he1P
    have he2inAB : e2 ∈ A1 ++ B1 := by
      have : e2 ∈ A1 ++ e1 :: B1 := hPsplit1 ▸ he2P
      rcases List.mem_append.mp this with h | h
      · exact List.mem_append.mpr (Or.inl h)
      · rcases List.mem_cons.mp h with h' | h'
        · exact absurd h'.symm he1ne2
        · exact List.mem_append.mpr (Or.inr h')
    rcases List.mem_append.mp he2inAB with h2A | h2B
    · obtain ⟨Sa, Sb, hA1eq⟩ := List.append_of_mem h2A
      have hPeq : P = Sa ++ e2 :: (Sb ++ e1 :: B1) := by
        rw [hPsplit1, hA1eq]; simp [List.append_assoc]
      exact (merge_ordered j2 j1 K2 K1 e2 e1 he2tgt he1tgt (Ne.symm hjeq)
        hK2 hK1 hK2j2 hK1j1 Sa Sb B1 hPeq).symm
    · obtain ⟨Sa, Sb, hB1eq⟩ := List.append_of_mem h2B
      have hPeq : P = A1 ++ e1 :: (Sa ++ e2 :: Sb) := by
        rw [hPsplit1, hB1eq]
      exact merge_ordered j1 j2 K1 K2 e1 e2 he1tgt he2tgt hjeq
        hK1 hK2 hK1j1 hK2j2 A1 Sa Sb hPeq

end Merge

end AllenderOQ3.Internal
