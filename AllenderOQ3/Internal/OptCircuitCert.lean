import AllenderOQ3.Internal.OptCircuit

/-!
# Certificates and semantics for the single-fan-in layers

The generic half of the certificate machinery for `optCircuit`
(`docs/LOCAL_DIVISOR_PLAN.md` §9): given per-vertex outgoing/incoming arc
lists whose source-major and target-major concatenations coincide, the circuit
is incidence-cylindrical with the canonical listings (`optCylinder`), its
layer-0 transition computes exactly the intended map `optTrans ρ β`
(`optCylinder_layerTrans`), and the intended map lies in `NonCrossing w`
(`optTrans_mem_nonCrossing`).

The instance words (freeze / adjacent duplication) are built in
`OptCircuitInstances.lean`.  Everything here is `sorry`-free.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace AllenderOQ3
namespace Internal

attribute [local instance] Classical.propDecidable

variable {w : Nat}

section Cert

variable (hw : 0 < w) (ρ : Fin w → Option (Fin w)) (β : Fin w → Bool)

/-! ## The listing family and the empty upper transitions -/

/-- Layers `≥ 2` of the witness circuit are empty. -/
noncomputable def emptyListing (m : Nat) :
    CyclicListing (LayerVertex (optCircuit w hw ρ β) (m + 2)) where
  entries := []
  nodup := List.nodup_nil
  complete := by
    intro a
    exfalso
    have h1 : (optCircuit w hw ρ β).layer a.val = m + 2 := a.2
    have h2 := optCircuit_layer_le hw ρ β a.val
    omega

/-- The canonical listing family. -/
noncomputable def optOrders :
    ∀ ell, CyclicListing (LayerVertex (optCircuit w hw ρ β) ell)
  | 0 => srcListing hw ρ β
  | 1 => tgtListing hw ρ β
  | (m + 2) => emptyListing hw ρ β m

/-- There are no arcs above the base transition. -/
theorem no_arc_above (ell : Nat)
    (e : TransitionArc (optCircuit w hw ρ β) (ell + 1)) : False := by
  obtain ⟨⟨u, v⟩, hedge, hlu, hlv⟩ := e
  obtain ⟨hu, -, -⟩ := (optCircuit_edge_iff hw ρ β).mp hedge
  have h0 : (optCircuit w hw ρ β).layer u = 0 := Nat.div_eq_of_lt hu
  rw [h0] at hlu
  omega

/-- The empty certificate for any transition above the base. -/
noncomputable def emptyTransition (ell : Nat)
    (O₁ : CyclicListing (LayerVertex (optCircuit w hw ρ β) (ell + 1)))
    (O₂ : CyclicListing (LayerVertex (optCircuit w hw ρ β) (ell + 2))) :
    ArcOrderCertificate (optCircuit w hw ρ β) (ell + 1) O₁ O₂ :=
  arcOrderCertificate_of_eq (fun _ => []) (fun _ => [])
    (fun _ => List.nodup_nil) (fun _ => List.nodup_nil)
    (fun _ e => (no_arc_above hw ρ β ell e).elim)
    (fun _ e => (no_arc_above hw ρ β ell e).elim)
    (by rw [flatMap_const_nil, flatMap_const_nil])

/-! ## Arcs of the base transition -/

/-- Index recovery at a target vertex. -/
theorem tgt_index (p : Fin w) :
    (⟨(tgtVertex hw ρ β p).val.val % w, Nat.mod_lt _ hw⟩ : Fin w) = p := by
  apply Fin.ext
  change (w + p.val) % w = p.val
  rw [Nat.add_mod_left, Nat.mod_eq_of_lt p.isLt]

/-- Index recovery at a source vertex. -/
theorem src_index (q : Fin w) :
    (⟨(srcVertex hw ρ β q).val.val % w, Nat.mod_lt _ hw⟩ : Fin w) = q := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt q.isLt

/-- The edge from source position `q` to target position `p`. -/
theorem optCircuit_edge_of (p q : Fin w) (h : ρ p = some q) :
    (optCircuit w hw ρ β).edge (srcVertex hw ρ β q).val (tgtVertex hw ρ β p).val
      = true := by
  refine decide_eq_true ⟨q.isLt, by change w ≤ w + p.val; omega, ?_⟩
  rw [tgt_index hw ρ β p, src_index hw ρ β q]
  exact h

/-- The transition arc from source position `q` to target position `p`. -/
noncomputable def optArc (p q : Fin w) (h : ρ p = some q) :
    TransitionArc (optCircuit w hw ρ β) 0 :=
  ⟨((srcVertex hw ρ β q).val, (tgtVertex hw ρ β p).val),
    optCircuit_edge_of hw ρ β p q h, (srcVertex hw ρ β q).2, (tgtVertex hw ρ β p).2⟩

theorem optArc_source (p q : Fin w) (h : ρ p = some q) :
    arcSource (optArc hw ρ β p q h) = srcVertex hw ρ β q :=
  Subtype.ext rfl

theorem optArc_target (p q : Fin w) (h : ρ p = some q) :
    arcTarget (optArc hw ρ β p q h) = tgtVertex hw ρ β p :=
  Subtype.ext rfl

/-- Every arc of the base transition is an `optArc`. -/
theorem arc_cases (e : TransitionArc (optCircuit w hw ρ β) 0) :
    ∃ (p q : Fin w) (h : ρ p = some q), e = optArc hw ρ β p q h := by
  obtain ⟨⟨u, v⟩, hedge, hlu, hlv⟩ := e
  obtain ⟨hu, hv, hρ⟩ := (optCircuit_edge_iff hw ρ β).mp hedge
  have hv2 : v.val < 2 * w := v.isLt
  have hpw : v.val - w < w := by omega
  set p : Fin w := ⟨v.val - w, hpw⟩ with hp
  set q : Fin w := ⟨u.val, hu⟩ with hq
  have hmodv : v.val % w = v.val - w := by
    rw [Nat.mod_eq_sub_mod hv, Nat.mod_eq_of_lt (by omega)]
  have hindexv : (⟨v.val % w, Nat.mod_lt _ hw⟩ : Fin w) = p := by
    apply Fin.ext
    exact hmodv
  have hindexu : (⟨u.val % w, Nat.mod_lt _ hw⟩ : Fin w) = q := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt hu
  rw [hindexv, hindexu] at hρ
  refine ⟨p, q, hρ, ?_⟩
  apply Subtype.ext
  change (u, v) = ((srcVertex hw ρ β q).val, (tgtVertex hw ρ β p).val)
  have h1 : u = (srcVertex hw ρ β q).val := by
    apply Fin.ext
    rfl
  have h2 : v = (tgtVertex hw ρ β p).val := by
    apply Fin.ext
    change v.val = w + (v.val - w)
    have hge : w ≤ v.val := hv
    omega
  rw [← h1, ← h2]

/-! ## The cylinder from matching arc words -/

/-- The incidence certificate of the witness circuit, from per-vertex arc
lists whose source-major and target-major concatenations coincide. -/
noncomputable def optCylinder
    (out : LayerVertex (optCircuit w hw ρ β) 0 →
      List (TransitionArc (optCircuit w hw ρ β) 0))
    (inc : LayerVertex (optCircuit w hw ρ β) 1 →
      List (TransitionArc (optCircuit w hw ρ β) 0))
    (hout_nd : ∀ u, (out u).Nodup) (hinc_nd : ∀ v, (inc v).Nodup)
    (hout_ex : ∀ u e, e ∈ out u ↔ e.1.1 = u.1)
    (hinc_ex : ∀ v e, e ∈ inc v ↔ e.1.2 = v.1)
    (heq : (srcListing hw ρ β).entries.flatMap out
      = (tgtListing hw ρ β).entries.flatMap inc) :
    IncidenceCylinder (optCircuit w hw ρ β) where
  layerOrder := optOrders hw ρ β
  transitionOrder := fun ell => match ell with
    | 0 => arcOrderCertificate_of_eq out inc hout_nd hinc_nd hout_ex hinc_ex heq
    | (m + 1) => emptyTransition hw ρ β m (optOrders hw ρ β (m + 1))
        (optOrders hw ρ β (m + 2))

theorem optCylinder_canonical
    (out : LayerVertex (optCircuit w hw ρ β) 0 →
      List (TransitionArc (optCircuit w hw ρ β) 0))
    (inc : LayerVertex (optCircuit w hw ρ β) 1 →
      List (TransitionArc (optCircuit w hw ρ β) 0))
    (hout_nd : ∀ u, (out u).Nodup) (hinc_nd : ∀ v, (inc v).Nodup)
    (hout_ex : ∀ u e, e ∈ out u ↔ e.1.1 = u.1)
    (hinc_ex : ∀ v e, e ∈ inc v ↔ e.1.2 = v.1)
    (heq : (srcListing hw ρ β).entries.flatMap out
      = (tgtListing hw ρ β).entries.flatMap inc) :
    CanonicalOrders hw ρ β
      (optCylinder hw ρ β out inc hout_nd hinc_nd hout_ex hinc_ex heq) :=
  ⟨rfl, rfl⟩

/-! ## Semantics of the base transition -/

section Semantics

variable {cert : IncidenceCylinder (optCircuit w hw ρ β)}

/-- The gate at target position `p` has the prescribed kind. -/
theorem canonical_kind (hC : CanonicalOrders hw ρ β cert) (p : Fin w) :
    (optCircuit w hw ρ β).kind
        (vtxAt (optCircuit w hw ρ β) cert (0 + 1)
          (canonical_tgt_length hw ρ β hC) p).val
      = match ρ p with
        | some _ => ADRGate.andGate
        | none => ADRGate.literal ⟨0, Nat.zero_lt_one⟩ (!(β p)) := by
  rw [canonical_vtxAt hw ρ β hC p]
  change (if (tgtVertex hw ρ β p).val.val < w then _ else _) = _
  rw [if_neg (by change ¬ (w + p.val) < w; omega)]
  rw [tgt_index hw ρ β p]
  rfl

/-- Sources of edges into target position `p` are the prescribed one. -/
theorem canonical_edge_char (hC : CanonicalOrders hw ρ β cert) {p q : Fin w}
    (hρp : ρ p = some q) (u : LayerVertex (optCircuit w hw ρ β) 0)
    (hu : (optCircuit w hw ρ β).edge u.val
      (vtxAt (optCircuit w hw ρ β) cert (0 + 1)
        (canonical_tgt_length hw ρ β hC) p).val = true) :
    u = srcVertex hw ρ β q := by
  rw [canonical_vtxAt hw ρ β hC p] at hu
  obtain ⟨hu1, -, hρ⟩ := (optCircuit_edge_iff hw ρ β).mp hu
  have h1 : (⟨(tgtVertex hw ρ β p).val.val % w, Nat.mod_lt _ hw⟩ : Fin w) = p :=
    tgt_index hw ρ β p
  have h2 : (⟨u.val.val % w, Nat.mod_lt _ hw⟩ : Fin w) = ⟨u.val.val, hu1⟩ := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt hu1
  rw [h1, h2] at hρ
  rw [hρp] at hρ
  have h3 : q = ⟨u.val.val, hu1⟩ := Option.some.inj hρ
  apply Subtype.ext
  apply Fin.ext
  exact (congrArg Fin.val h3).symm

/-- **The base transition computes the intended map.** -/
theorem canonical_layerTrans (hC : CanonicalOrders hw ρ β cert) :
    layerTrans (optCircuit w hw ρ β) cert (fun _ => true) 0 = optTrans ρ β := by
  apply transMonoid_ext
  intro z
  funext p
  have hlen2 := canonical_tgt_length hw ρ β hC
  have hlen1 := (canonical_src_length hw ρ β hC).le
  have hrun : runTrans (layerTrans (optCircuit w hw ρ β) cert (fun _ => true) 0) z p
      = layerTransMap (optCircuit w hw ρ β) cert (fun _ => true) 0 z p := rfl
  have hgoal : runTrans (optTrans ρ β) z p
      = match ρ p with | some q => z q | none => β p := rfl
  rw [hrun, hgoal]
  cases hρp : ρ p with
  | none =>
    change _ = β p
    have hk : (optCircuit w hw ρ β).kind
        (vtxAt (optCircuit w hw ρ β) cert (0 + 1) hlen2 p).val
          = ADRGate.literal ⟨0, Nat.zero_lt_one⟩ (!(β p)) := by
      rw [canonical_kind hw ρ β hC p, hρp]
    rw [layerTransMap_literal (x := fun _ => true) hlen2 z p hk]
    cases β p <;> rfl
  | some q =>
    change _ = z q
    have hk : (optCircuit w hw ρ β).kind
        (vtxAt (optCircuit w hw ρ β) cert (0 + 1) hlen2 p).val
          = ADRGate.andGate := by
      rw [canonical_kind hw ρ β hC p, hρp]
    have hiff := layerTransMap_and (x := fun _ => true) hlen1 hlen2
      (optCircuit_wellFormed hw ρ β) z p hk
    have hedge : (optCircuit w hw ρ β).edge (srcVertex hw ρ β q).val
        (vtxAt (optCircuit w hw ρ β) cert (0 + 1) hlen2 p).val = true := by
      rw [canonical_vtxAt hw ρ β hC p]
      exact optCircuit_edge_of hw ρ β p q hρp
    cases hzq : z q with
    | true =>
      have hall : ∀ u : LayerVertex (optCircuit w hw ρ β) 0,
          (optCircuit w hw ρ β).edge u.val
            (vtxAt (optCircuit w hw ρ β) cert (0 + 1) hlen2 p).val = true →
          z (idxOfVtx (optCircuit w hw ρ β) cert 0 hlen1 u) = true := by
        intro u hu
        rw [canonical_edge_char hw ρ β hC hρp u hu,
          canonical_idxOfVtx hw ρ β hC q]
        exact hzq
      exact hiff.mpr hall
    | false =>
      cases hval : layerTransMap (optCircuit w hw ρ β) cert (fun _ => true) 0 z p with
      | false => rfl
      | true =>
        exfalso
        have h := hiff.mp hval (srcVertex hw ρ β q) hedge
        rw [canonical_idxOfVtx hw ρ β hC q] at h
        rw [hzq] at h
        exact Bool.false_ne_true h

end Semantics

/-- **Membership of the intended map**, from any canonical certificate. -/
theorem optTrans_mem_nonCrossing
    (cert : IncidenceCylinder (optCircuit w hw ρ β))
    (hC : CanonicalOrders hw ρ β cert) :
    optTrans ρ β ∈ NonCrossing w := by
  rw [← canonical_layerTrans hw ρ β hC]
  exact layerTrans_mem_nonCrossing _ cert _ 0
    (optCircuit_hmvNormal hw ρ β) (optCircuit_totalWidth hw ρ β)

end Cert

end Internal
end AllenderOQ3
