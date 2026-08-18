import Mathlib
import AllenderOQ3.Internal.CycSortedWord
import AllenderOQ3.Internal.CFPairGate
import AllenderOQ3.Internal.CFPairGateCert
import AllenderOQ3.Internal.ComponentGateFacts
import AllenderOQ3.Internal.ConstantFreeLayers

/-!
# The general constant-free layer builder

`exists_memCF_of_cycSorted` turns a predecessor assignment `P : Fin w → List (Fin w)`
into an element of `NonCrossingCF w` computing the prescribed AND/OR of the
predecessor slots, provided

* every target slot has one or two (distinct) predecessor slots — this is
  constant-freeness together with the fan-in-two bound, and
* the target-major arc word of `P` is cyclically sorted by source
  (`CycSortedSrc`) — this is the non-crossing (incidence-cylindrical) condition.

The witness circuit is the two-layer `pairCircuit` of `CFPairGate.lean`; the
certificate comes from `arcOrderCertificate_of_rotatedDoubleGrouped`, the target
grouping being the target-major word itself and the source grouping its sorted
rotation.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace AllenderOQ3.Internal

/-- Reading the inverse full-layer indexing off the layer order list. -/
theorem full_symm_eq {n : Nat} (c : ADRCircuit n) (cert : IncidenceCylinder c) (ell : Nat)
    (v : LayerVertex c ell) (j : Fin (cert.layerOrder ell).entries.length)
    (h : (cert.layerOrder ell).entries.get j = v) :
    (FullLayerIndexing c cert ell).symm j = v := by
  simpa [FullLayerIndexing, subtypeUnivEquiv] using h

variable {w : Nat} (hw : 0 < w) (P : Fin w → List (Fin w)) (tgtKind : Fin w → ADRGate 1)

/-! ## Coordinates of arcs -/

/-- The source coordinate of an arc of the two-layer circuit. -/
def arcSrcCoord (e : TransitionArc (pairCircuit hw P tgtKind) 0) : Fin w :=
  ⟨e.1.1.val % w, Nat.mod_lt _ hw⟩

/-- The target coordinate of an arc of the two-layer circuit. -/
def arcTgtCoord (e : TransitionArc (pairCircuit hw P tgtKind) 0) : Fin w :=
  ⟨e.1.2.val % w, Nat.mod_lt _ hw⟩

theorem arcSrcCoord_pairArc (p q : Fin w) (h : q ∈ P p) :
    arcSrcCoord hw P tgtKind (pairArc hw P tgtKind p q h) = q := by
  apply Fin.ext
  change q.val % w = q.val
  exact Nat.mod_eq_of_lt q.isLt

theorem arcTgtCoord_pairArc (p q : Fin w) (h : q ∈ P p) :
    arcTgtCoord hw P tgtKind (pairArc hw P tgtKind p q h) = p := by
  apply Fin.ext
  change (w + p.val) % w = p.val
  rw [Nat.add_mod_left, Nat.mod_eq_of_lt p.isLt]

theorem arcSource_eq (e : TransitionArc (pairCircuit hw P tgtKind) 0) :
    arcSource e = pair_srcVertex hw P tgtKind (arcSrcCoord hw P tgtKind e) := by
  obtain ⟨hu, -, -⟩ := (pairCircuit_edge_iff hw P tgtKind).mp e.2.1
  apply Subtype.ext
  apply Fin.ext
  change e.1.1.val = e.1.1.val % w
  exact (Nat.mod_eq_of_lt hu).symm

theorem arcTarget_eq (e : TransitionArc (pairCircuit hw P tgtKind) 0) :
    arcTarget e = pair_tgtVertex hw P tgtKind (arcTgtCoord hw P tgtKind e) := by
  obtain ⟨-, hv, -⟩ := (pairCircuit_edge_iff hw P tgtKind).mp e.2.1
  have hlt : e.1.2.val < 2 * w := e.1.2.isLt
  apply Subtype.ext
  apply Fin.ext
  change e.1.2.val = w + e.1.2.val % w
  rw [Nat.mod_eq_sub_mod hv, Nat.mod_eq_of_lt (by omega)]
  omega

/-- The coordinate of a target-layer vertex. -/
def tgtVertexCoord (v : LayerVertex (pairCircuit hw P tgtKind) 1) : Fin w :=
  ⟨v.val.val % w, Nat.mod_lt _ hw⟩

theorem pair_tgtVertex_coord (v : LayerVertex (pairCircuit hw P tgtKind) 1) :
    pair_tgtVertex hw P tgtKind (tgtVertexCoord hw P tgtKind v) = v := by
  have h1 : v.val.val / w = 1 := v.2
  have h2 : v.val.val < 2 * w := v.val.isLt
  have hge : w ≤ v.val.val := by
    by_contra hcon
    push_neg at hcon
    have : v.val.val / w = 0 := Nat.div_eq_of_lt hcon
    omega
  apply Subtype.ext
  apply Fin.ext
  change w + v.val.val % w = v.val.val
  rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
  omega

theorem tgtVertexCoord_pair_tgtVertex (p : Fin w) :
    tgtVertexCoord hw P tgtKind (pair_tgtVertex hw P tgtKind p) = p := by
  apply Fin.ext
  change (w + p.val) % w = p.val
  rw [Nat.add_mod_left, Nat.mod_eq_of_lt p.isLt]

/-! ## The arc word -/

/-- The arcs into target slot `p`. -/
noncomputable def incArcs (p : Fin w) : List (TransitionArc (pairCircuit hw P tgtKind) 0) :=
  (P p).pmap (fun q hq => pairArc hw P tgtKind p q hq) (fun _ hq => hq)

/-- The target-major arc word of the two-layer circuit. -/
noncomputable def pairWordT : List (TransitionArc (pairCircuit hw P tgtKind) 0) :=
  (List.finRange w).flatMap (incArcs hw P tgtKind)

theorem arcTarget_of_mem_incArcs {p : Fin w} {e : TransitionArc (pairCircuit hw P tgtKind) 0}
    (he : e ∈ incArcs hw P tgtKind p) : arcTarget e = pair_tgtVertex hw P tgtKind p := by
  obtain ⟨q, hq, rfl⟩ := List.mem_pmap.mp he
  exact pairArc_target hw P tgtKind p q hq

theorem map_incArcs (p : Fin w) :
    (incArcs hw P tgtKind p).map
        (fun e => (arcSrcCoord hw P tgtKind e, arcTgtCoord hw P tgtKind e))
      = arcBlock P p := by
  rw [incArcs, List.map_pmap, arcBlock,
    ← List.pmap_eq_map (p := fun q => q ∈ P p) (H := fun _ h => h)]
  refine List.pmap_congr_left _ (fun q hq h₁ h₂ => ?_)
  rw [arcSrcCoord_pairArc, arcTgtCoord_pairArc]

theorem map_pairWordT :
    (pairWordT hw P tgtKind).map
        (fun e => (arcSrcCoord hw P tgtKind e, arcTgtCoord hw P tgtKind e))
      = arcPairWord P := by
  rw [pairWordT, arcPairWord, List.map_flatMap]
  exact List.flatMap_congr (fun p _ => map_incArcs hw P tgtKind p)

theorem mem_pairWordT (e : TransitionArc (pairCircuit hw P tgtKind) 0) :
    e ∈ pairWordT hw P tgtKind := by
  obtain ⟨p, q, h, rfl⟩ := pairArc_cases hw P tgtKind e
  exact List.mem_flatMap.mpr ⟨p, List.mem_finRange p, List.mem_pmap.mpr ⟨q, h, rfl⟩⟩

theorem nodup_pairWordT (hnd : ∀ p, (P p).Nodup) : (pairWordT hw P tgtKind).Nodup :=
  List.Nodup.of_map _ (by rw [map_pairWordT]; exact arcPairWord_nodup P hnd)

/-! ## The certificate -/

theorem exists_base_cert (hnd : ∀ p, (P p).Nodup) (hsort : CycSortedSrc (arcPairWord P)) :
    Nonempty (ArcOrderCertificate (pairCircuit hw P tgtKind) 0
      (pair_srcListing hw P tgtKind) (pair_tgtListing hw P tgtKind)) := by
  classical
  obtain ⟨A, B, hAB, hsorted⟩ := hsort
  set T := pairWordT hw P tgtKind with hT
  set k := A.length with hk
  set keyPair : TransitionArc (pairCircuit hw P tgtKind) 0 → Fin w × Fin w :=
    fun e => (arcSrcCoord hw P tgtKind e, arcTgtCoord hw P tgtKind e) with hkeyPair
  have hTmap : T.map keyPair = arcPairWord P := map_pairWordT hw P tgtKind
  have hTnodup : T.Nodup := nodup_pairWordT hw P tgtKind hnd
  have hperm : (T.drop k ++ T.take k).Perm T := by
    have h := List.perm_append_comm (l₁ := T.drop k) (l₂ := T.take k)
    rw [List.take_append_drop] at h
    exact h
  -- the rotated word maps onto `B ++ A`
  have hmapS : (T.drop k ++ T.take k).map keyPair = B ++ A := by
    rw [List.map_append, List.map_drop, List.map_take, hTmap, hAB,
      List.drop_left' hk.symm, List.take_left' hk.symm]
  have hpwS : (T.drop k ++ T.take k).Pairwise
      (fun a b => arcSrcCoord hw P tgtKind a ≤ arcSrcCoord hw P tgtKind b) := by
    have h : ((T.drop k ++ T.take k).map keyPair).Pairwise (fun a b => a.1 ≤ b.1) := by
      rw [hmapS]; exact hsorted
    have h2 := (List.pairwise_map (f := keyPair) (R := fun a b => a.1 ≤ b.1)).mp h
    exact h2
  have hS : GroupedAlong arcSource (pair_srcListing hw P tgtKind).entries
      (T.drop k ++ T.take k) := by
    have h1 : GroupedAlong (arcSrcCoord hw P tgtKind) (List.finRange w) (T.drop k ++ T.take k) :=
      groupedAlong_of_pairwise_le (arcSrcCoord hw P tgtKind) (List.finRange w) _
        (List.pairwise_lt_finRange w) (fun a _ => List.mem_finRange _) hpwS
    have h2 := groupedAlong_map (arcSrcCoord hw P tgtKind) arcSource id
      (pair_srcVertex hw P tgtKind) (pair_srcVertex_injective hw P tgtKind)
      (fun e => arcSource_eq hw P tgtKind e) (List.finRange w) _ h1
    simpa [pair_srcListing] using h2
  have hTgrouped : GroupedAlong arcTarget (pair_tgtListing hw P tgtKind).entries T := by
    have hblocks : ((pair_tgtListing hw P tgtKind).entries).flatMap
        (fun v => incArcs hw P tgtKind (tgtVertexCoord hw P tgtKind v)) = T := by
      have h : ((List.finRange w).map (pair_tgtVertex hw P tgtKind)).flatMap
          (fun v => incArcs hw P tgtKind (tgtVertexCoord hw P tgtKind v))
          = (List.finRange w).flatMap (incArcs hw P tgtKind) := by
        rw [List.flatMap_map]
        exact List.flatMap_congr (fun p _ => by
          rw [tgtVertexCoord_pair_tgtVertex])
      simpa [pair_tgtListing, hT, pairWordT] using h
    have h := groupedAlong_flatMap arcTarget
      (fun v => incArcs hw P tgtKind (tgtVertexCoord hw P tgtKind v))
      (fun v e he => by
        rw [arcTarget_of_mem_incArcs hw P tgtKind he, pair_tgtVertex_coord])
      (pair_tgtListing hw P tgtKind).entries (pair_tgtListing hw P tgtKind).nodup
    rwa [hblocks] at h
  exact ⟨arcOrderCertificate_of_rotatedDoubleGrouped
    (pair_srcListing hw P tgtKind).entries (pair_tgtListing hw P tgtKind).entries
    (T.drop k ++ T.take k) T
    (cyclicRotation_refl _) (cyclicRotation_refl _)
    ⟨T.drop k, T.take k, rfl, (List.take_append_drop k T).symm⟩
    (hperm.nodup_iff.mpr hTnodup)
    (fun e => hperm.mem_iff.mpr (mem_pairWordT hw P tgtKind e))
    hS hTgrouped⟩

/-! ## Semantics of the built layer -/

section Semantics

variable (base : ArcOrderCertificate (pairCircuit hw P tgtKind) 0
    (pair_srcListing hw P tgtKind) (pair_tgtListing hw P tgtKind))

/-- The transition realised by the built layer. -/
noncomputable def pairLayerTrans : TransMonoid w :=
  layerTrans (pairCircuit hw P tgtKind) (pairCylinder hw P tgtKind base) (fun _ => true) 0

theorem pairCyl_len_one :
    ((pairCylinder hw P tgtKind base).layerOrder 1).entries.length = w := by
  change ((pair_tgtListing hw P tgtKind).entries).length = w
  simp [pair_tgtListing]

theorem pair_tgt_symm' (p : Fin w)
    (hp : p.val < ((pairCylinder hw P tgtKind base).layerOrder (0 + 1)).entries.length) :
    (FullLayerIndexing (pairCircuit hw P tgtKind) (pairCylinder hw P tgtKind base) (0 + 1)).symm
        ⟨p.val, hp⟩
      = pair_tgtVertex hw P tgtKind p := by
  refine full_symm_eq _ _ _ _ ⟨p.val, hp⟩ ?_
  change ((List.finRange w).map (pair_tgtVertex hw P tgtKind)).get ⟨p.val, _⟩
    = pair_tgtVertex hw P tgtKind p
  rw [List.get_eq_getElem, List.getElem_map, List.getElem_finRange]
  exact congrArg (pair_tgtVertex hw P tgtKind) (Fin.ext rfl)

theorem pair_kind_tgt' (p : Fin w) :
    (pairCircuit hw P tgtKind).kind (pair_tgtVertex hw P tgtKind p).val = tgtKind p := by
  change (if (w + p.val) < w then _ else tgtKind ⟨(w + p.val) % w, Nat.mod_lt _ hw⟩) = tgtKind p
  rw [if_neg (by omega)]
  congr 1
  apply Fin.ext
  change (w + p.val) % w = p.val
  rw [Nat.add_mod_left, Nat.mod_eq_of_lt p.isLt]

theorem vertCoord_eval' (u : Fin w) :
    vertCoord (pairCircuit hw P tgtKind) (pairCylinder hw P tgtKind base)
      (pairCircuit_totalWidth hw P tgtKind) (pair_srcVertex hw P tgtKind u) = u := by
  have hext : (vertCoord (pairCircuit hw P tgtKind) (pairCylinder hw P tgtKind base)
      (pairCircuit_totalWidth hw P tgtKind) (pair_srcVertex hw P tgtKind u)).val = u.val := by
    dsimp [vertCoord, FullLayerIndexing, subtypeUnivEquiv, Equiv.trans]
    set H := (pairCylinder hw P tgtKind base).layerOrder 0 with hH
    have h_len : u.val < H.entries.length := by
      rw [hH]
      change u.val < ((List.finRange w).map (pair_srcVertex hw P tgtKind)).length
      simp
    have heq : H.entries.get ⟨u.val, h_len⟩ = pair_srcVertex hw P tgtKind u := by
      change ((List.finRange w).map (pair_srcVertex hw P tgtKind)).get ⟨u.val, _⟩ = _
      simp
    have h1 : (List.Nodup.getEquiv H.entries H.nodup) ⟨u.val, h_len⟩
        = ⟨pair_srcVertex hw P tgtKind u, H.complete _⟩ := Subtype.ext heq
    have h2 : ((List.Nodup.getEquiv H.entries H.nodup).symm
        ⟨pair_srcVertex hw P tgtKind u, H.complete _⟩) = ⟨u.val, h_len⟩ := by
      rw [← h1]; simp
    exact congrArg Fin.val h2
  exact Fin.ext hext

theorem pair_edge_src' (p : Fin w) (u : Fin (pairCircuit hw P tgtKind).gateCount)
    (hu : (pairCircuit hw P tgtKind).edge u (pair_tgtVertex hw P tgtKind p).val = true) :
    ∃ q : Fin w, q ∈ P p ∧ u = (pair_srcVertex hw P tgtKind q).val := by
  obtain ⟨hu1, -, hρ⟩ := (pairCircuit_edge_iff hw P tgtKind).mp hu
  refine ⟨⟨u.val % w, Nat.mod_lt _ hw⟩, ?_, ?_⟩
  · have hpp : (⟨(pair_tgtVertex hw P tgtKind p).val.val % w, Nat.mod_lt _ hw⟩ : Fin w) = p := by
      apply Fin.ext
      change (w + p.val) % w = p.val
      rw [Nat.add_mod_left, Nat.mod_eq_of_lt p.isLt]
    rw [hpp] at hρ
    exact hρ
  · apply Fin.ext
    change u.val = u.val % w
    rw [Nat.mod_eq_of_lt hu1]

theorem vertCoord_of_src' (q : Fin w) (u : Fin (pairCircuit hw P tgtKind).gateCount)
    (hlu : (pairCircuit hw P tgtKind).layer u = 0)
    (hueq : u = (pair_srcVertex hw P tgtKind q).val) :
    vertCoord (pairCircuit hw P tgtKind) (pairCylinder hw P tgtKind base)
      (pairCircuit_totalWidth hw P tgtKind) ⟨u, hlu⟩ = q := by
  have hvv : (⟨u, hlu⟩ : LayerVertex (pairCircuit hw P tgtKind) 0)
      = pair_srcVertex hw P tgtKind q := Subtype.ext hueq
  rw [hvv]
  exact vertCoord_eval' hw P tgtKind base q

theorem pairLayer_and (h_comp : ∀ p, (tgtKind p).isComputation) (p : Fin w)
    (hk : tgtKind p = ADRGate.andGate) (z : Config w) :
    runTrans (pairLayerTrans hw P tgtKind base) z p = (P p).all (fun q => z q) := by
  set c := pairCircuit hw P tgtKind with hc_def
  set cert := pairCylinder hw P tgtKind base with hcert_def
  have hc : WellFormedADR c := pairCircuit_wellFormed hw P tgtKind h_comp
  have hW : TotalWidthAtMost c w := pairCircuit_totalWidth hw P tgtKind
  have hp : p.val < (cert.layerOrder (0 + 1)).entries.length := by
    rw [hcert_def, pairCyl_len_one hw P tgtKind base]; exact p.isLt
  have hvtx : (FullLayerIndexing c cert (0 + 1)).symm ⟨p.val, hp⟩
      = pair_tgtVertex hw P tgtKind p := pair_tgt_symm' hw P tgtKind base p hp
  have hkind : c.kind ((FullLayerIndexing c cert (0 + 1)).symm ⟨p.val, hp⟩).val
      = ADRGate.andGate := by
    rw [hvtx, pair_kind_tgt' hw P tgtKind p]; exact hk
  apply bool_eq_of_iff
  rw [List.all_eq_true]
  have hrun : runTrans (pairLayerTrans hw P tgtKind base) z p
      = layerTransMap c cert (fun _ => true) 0 z p := rfl
  rw [hrun, layerTransMap_and_true_iff c cert hc hW (fun _ => true) z hp hkind]
  constructor
  · intro hall q hq
    have hedge : c.edge (pair_srcVertex hw P tgtKind q).val
        ((FullLayerIndexing c cert (0 + 1)).symm ⟨p.val, hp⟩).val = true := by
      rw [hvtx]
      exact pairCircuit_edge_of hw P tgtKind p q hq
    have h1 := hall _ hedge
    rwa [vertCoord_of_src' hw P tgtKind base q _ _ rfl] at h1
  · intro hall u hu
    rw [hvtx] at hu
    obtain ⟨q, hqmem, hueq⟩ := pair_edge_src' hw P tgtKind p u hu
    rw [vertCoord_of_src' hw P tgtKind base q u _ hueq]
    exact hall q hqmem

theorem pairLayer_or (h_comp : ∀ p, (tgtKind p).isComputation) (p : Fin w)
    (hk : tgtKind p = ADRGate.orGate) (z : Config w) :
    runTrans (pairLayerTrans hw P tgtKind base) z p = (P p).any (fun q => z q) := by
  set c := pairCircuit hw P tgtKind with hc_def
  set cert := pairCylinder hw P tgtKind base with hcert_def
  have hc : WellFormedADR c := pairCircuit_wellFormed hw P tgtKind h_comp
  have hW : TotalWidthAtMost c w := pairCircuit_totalWidth hw P tgtKind
  have hp : p.val < (cert.layerOrder (0 + 1)).entries.length := by
    rw [hcert_def, pairCyl_len_one hw P tgtKind base]; exact p.isLt
  have hvtx : (FullLayerIndexing c cert (0 + 1)).symm ⟨p.val, hp⟩
      = pair_tgtVertex hw P tgtKind p := pair_tgt_symm' hw P tgtKind base p hp
  have hkind : c.kind ((FullLayerIndexing c cert (0 + 1)).symm ⟨p.val, hp⟩).val
      = ADRGate.orGate := by
    rw [hvtx, pair_kind_tgt' hw P tgtKind p]; exact hk
  apply bool_eq_of_iff
  rw [List.any_eq_true]
  have hrun : runTrans (pairLayerTrans hw P tgtKind base) z p
      = layerTransMap c cert (fun _ => true) 0 z p := rfl
  rw [hrun, layerTransMap_or_true_iff c cert hc hW (fun _ => true) z hp hkind]
  constructor
  · rintro ⟨u, hu, hval⟩
    rw [hvtx] at hu
    obtain ⟨q, hqmem, hueq⟩ := pair_edge_src' hw P tgtKind p u hu
    rw [vertCoord_of_src' hw P tgtKind base q u _ hueq] at hval
    exact ⟨q, hqmem, hval⟩
  · rintro ⟨q, hqmem, hval⟩
    have hedge : c.edge (pair_srcVertex hw P tgtKind q).val
        ((FullLayerIndexing c cert (0 + 1)).symm ⟨p.val, hp⟩).val = true := by
      rw [hvtx]
      exact pairCircuit_edge_of hw P tgtKind p q hqmem
    exact ⟨_, hedge, by rw [vertCoord_of_src' hw P tgtKind base q _ _ rfl]; exact hval⟩

theorem pairLayerTrans_memCF (h_comp : ∀ p, (tgtKind p).isComputation)
    (hne : ∀ p, P p ≠ []) (hlen : ∀ p, (P p).length ≤ 2) :
    pairLayerTrans hw P tgtKind base ∈ NonCrossingCF w := by
  apply Submonoid.subset_closure
  refine ⟨1, pairCircuit hw P tgtKind, pairCylinder hw P tgtKind base, 0, (fun _ => true),
    pairCircuit_hmvNormal hw P tgtKind h_comp hlen,
    pairCircuit_totalWidth hw P tgtKind, ?_,
    pairCircuit_constantFreeLayer hw P tgtKind h_comp
      (fun p => fun hlen0 => hne p (List.eq_nil_of_length_eq_zero hlen0)), rfl⟩
  change ((pair_tgtListing hw P tgtKind).entries).length = w
  simp [pair_tgtListing]

end Semantics

/-- **The general constant-free layer.**  A cyclically source-sorted
predecessor assignment with one or two predecessors per target is realised by an
element of `NonCrossingCF w` computing the prescribed AND (`K p = true`) or OR
(`K p = false`) of its predecessor slots. -/
theorem exists_memCF_of_cycSorted (hw : 0 < w) (P : Fin w → List (Fin w)) (K : Fin w → Bool)
    (hne : ∀ p, P p ≠ []) (hlen : ∀ p, (P p).length ≤ 2) (hnd : ∀ p, (P p).Nodup)
    (hsort : CycSortedSrc (arcPairWord P)) :
    ∃ g : TransMonoid w, g ∈ NonCrossingCF w ∧
      (∀ (z : Config w) (p : Fin w), K p = true →
          runTrans g z p = (P p).all (fun q => z q)) ∧
      (∀ (z : Config w) (p : Fin w), K p = false →
          runTrans g z p = (P p).any (fun q => z q)) := by
  classical
  set tgtKind : Fin w → ADRGate 1 :=
    fun p => if K p then ADRGate.andGate else ADRGate.orGate with htk
  have h_comp : ∀ p, (tgtKind p).isComputation := by
    intro p
    change (if K p = true then ADRGate.andGate else ADRGate.orGate).isComputation = true
    split <;> rfl
  obtain ⟨base⟩ := exists_base_cert hw P tgtKind hnd hsort
  refine ⟨pairLayerTrans hw P tgtKind base,
    pairLayerTrans_memCF hw P tgtKind base h_comp hne hlen, ?_, ?_⟩
  · intro z p hK
    refine pairLayer_and hw P tgtKind base h_comp p ?_ z
    rw [htk]
    simp [hK]
  · intro z p hK
    refine pairLayer_or hw P tgtKind base h_comp p ?_ z
    rw [htk]
    simp [hK]

end AllenderOQ3.Internal
