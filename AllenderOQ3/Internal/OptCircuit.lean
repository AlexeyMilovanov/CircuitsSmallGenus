import AllenderOQ3.Internal.NonCrossingDefs
import AllenderOQ3.Internal.NonCrossingUnits
import AllenderOQ3.Internal.IncidenceToolkit

/-!
# Single-fan-in layers with prescribed copy/constant outputs

The generic circuit family behind the clamp and fan-fill layers of T5a
(`docs/LOCAL_DIVISOR_PLAN.md` §9): a two-layer certified circuit whose target
position `p` either copies a prescribed source position (`ρ p = some q`) or
outputs a prescribed constant bit (`ρ p = none`, bit `β p`).

* `optCircuit` — the circuit: `2 w` gates, layers `g / w`, dummy literals on
  the source layer, an `AND` of the single prescribed predecessor or a literal
  on the target layer;
* well-formedness, HMV normality, total width (adapted from `constCircuit`);
* `srcListing`/`tgtListing` — the canonical layer listings;
* `canonical_vtxAt` / `canonical_idxOfVtx` — for ANY incidence certificate
  whose layer-0/1 listings agree entrywise with the canonical ones, positions
  align with gate indices.

Certificates themselves are built per instance (freeze/dup layers) in the
sequel; the semantics lemma and the membership corollary live there too.

Everything here is `sorry`-free.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace AllenderOQ3
namespace Internal

attribute [local instance] Classical.propDecidable

variable {w : Nat}

/-- The intended semantics: copy `ρ p` or output the constant `β p`. -/
noncomputable def optMap (ρ : Fin w → Option (Fin w)) (β : Fin w → Bool)
    (z : Config w) : Config w :=
  fun p => match ρ p with
    | some q => z q
    | none => β p

/-- The intended transition. -/
noncomputable def optTrans (ρ : Fin w → Option (Fin w)) (β : Fin w → Bool) :
    TransMonoid w :=
  ofConfigMap (optMap ρ β)

@[simp] theorem runTrans_optTrans (ρ : Fin w → Option (Fin w)) (β : Fin w → Bool)
    (z : Config w) : runTrans (optTrans ρ β) z = optMap ρ β z := rfl

/-- The two-layer single-fan-in witness circuit. -/
def optCircuit (w : Nat) (hw : 0 < w) (ρ : Fin w → Option (Fin w))
    (β : Fin w → Bool) : ADRCircuit 1 where
  gateCount := 2 * w
  output := ⟨0, by omega⟩
  kind := fun g =>
    if g.val < w then ADRGate.literal ⟨0, Nat.zero_lt_one⟩ false
    else match ρ ⟨g.val % w, Nat.mod_lt _ hw⟩ with
      | some _ => ADRGate.andGate
      | none => ADRGate.literal ⟨0, Nat.zero_lt_one⟩ (!(β ⟨g.val % w, Nat.mod_lt _ hw⟩))
  layer := fun g => g.val / w
  edge := fun u v => decide (u.val < w ∧ w ≤ v.val ∧
    ρ ⟨v.val % w, Nat.mod_lt _ hw⟩ = some ⟨u.val % w, Nat.mod_lt _ hw⟩)

section Basic

variable (hw : 0 < w) (ρ : Fin w → Option (Fin w)) (β : Fin w → Bool)

theorem optCircuit_edge_iff {u v : Fin (optCircuit w hw ρ β).gateCount} :
    (optCircuit w hw ρ β).edge u v = true ↔
      u.val < w ∧ w ≤ v.val ∧
        ρ ⟨v.val % w, Nat.mod_lt _ hw⟩ = some ⟨u.val % w, Nat.mod_lt _ hw⟩ := by
  constructor
  · intro h
    exact of_decide_eq_true h
  · intro h
    exact decide_eq_true h

theorem optCircuit_wellFormed : WellFormedADR (optCircuit w hw ρ β) := by
  constructor
  · intro u v h
    obtain ⟨hu, hv, -⟩ := (optCircuit_edge_iff hw ρ β).mp h
    have hv2 : v.val < 2 * w := v.isLt
    have h1 : (optCircuit w hw ρ β).layer u = 0 := Nat.div_eq_of_lt hu
    have h2 : (optCircuit w hw ρ β).layer v = 1 := by
      change v.val / w = 1
      have hd : v.val / w < 2 := by
        by_contra hcon
        push_neg at hcon
        have h3 : 2 * w ≤ (v.val / w) * w := Nat.mul_le_mul_right w hcon
        have h4 : (v.val / w) * w ≤ v.val := Nat.div_mul_le_self v.val w
        omega
      have hd2 : 1 ≤ v.val / w := (Nat.one_le_div_iff hw).mpr hv
      omega
    rw [h1, h2]
  · intro g hg h
    cases hval : (optCircuit w hw ρ β).edge h g with
    | false => rfl
    | true =>
      exfalso
      obtain ⟨-, hg2, hρ⟩ := (optCircuit_edge_iff hw ρ β).mp hval
      obtain ⟨i, b, hkind⟩ := hg
      by_cases hglt : g.val < w
      · omega
      · have hk2 : (optCircuit w hw ρ β).kind g = ADRGate.andGate := by
          change (if g.val < w then _ else _) = _
          rw [if_neg hglt, hρ]
        rw [hkind] at hk2
        simp at hk2

theorem optCircuit_hmvNormal : HMVNormal (optCircuit w hw ρ β) := by
  refine ⟨optCircuit_wellFormed hw ρ β, ?_⟩
  intro g hg
  classical
  have hcard : (Finset.univ.filter
      (fun h : Fin (optCircuit w hw ρ β).gateCount =>
        (optCircuit w hw ρ β).edge h g = true)).card ≤ 1 := by
    refine Finset.card_le_one.mpr ?_
    intro a ha b hb
    obtain ⟨-, ha2⟩ := Finset.mem_filter.mp ha
    obtain ⟨-, hb2⟩ := Finset.mem_filter.mp hb
    obtain ⟨halt, -, haρ⟩ := (optCircuit_edge_iff hw ρ β).mp ha2
    obtain ⟨hblt, -, hbρ⟩ := (optCircuit_edge_iff hw ρ β).mp hb2
    rw [haρ] at hbρ
    have h1 : (⟨a.val % w, Nat.mod_lt _ hw⟩ : Fin w)
        = ⟨b.val % w, Nat.mod_lt _ hw⟩ :=
      Option.some.inj hbρ
    have h2 : a.val % w = b.val % w := congrArg Fin.val h1
    rw [Nat.mod_eq_of_lt halt, Nat.mod_eq_of_lt hblt] at h2
    exact Fin.ext h2
  calc predecessorCount (optCircuit w hw ρ β) g ≤ 1 := hcard
    _ ≤ 2 := by omega

theorem optCircuit_layer_le (g : Fin (optCircuit w hw ρ β).gateCount) :
    (optCircuit w hw ρ β).layer g ≤ 1 := by
  by_contra hcon
  push_neg at hcon
  have h2 : 2 ≤ g.val / w := hcon
  have h3 : 2 * w ≤ (g.val / w) * w := Nat.mul_le_mul_right w h2
  have h4 : (g.val / w) * w ≤ g.val := Nat.div_mul_le_self g.val w
  have h5 : g.val < 2 * w := g.isLt
  omega

theorem optCircuit_totalWidth : TotalWidthAtMost (optCircuit w hw ρ β) w := by
  intro ell
  by_cases hell : ell ≤ 1
  · have hinj : Set.InjOn
        (fun g : Fin (optCircuit w hw ρ β).gateCount =>
          (⟨g.val % w, Nat.mod_lt _ hw⟩ : Fin w))
        ↑(Finset.univ.filter (fun g : Fin (optCircuit w hw ρ β).gateCount =>
          (optCircuit w hw ρ β).layer g = ell)) := by
      intro a ha b hb hab
      have hla : a.val / w = ell :=
        (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2
      have hlb : b.val / w = ell :=
        (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).2
      have hmod : a.val % w = b.val % w := congrArg Fin.val hab
      have ha' : a.val = w * (a.val / w) + a.val % w := (Nat.div_add_mod a.val w).symm
      have hb' : b.val = w * (b.val / w) + b.val % w := (Nat.div_add_mod b.val w).symm
      rw [hla] at ha'
      rw [hlb] at hb'
      apply Fin.ext
      omega
    have hcard := Finset.card_le_card_of_injOn
      (fun g : Fin (optCircuit w hw ρ β).gateCount =>
        (⟨g.val % w, Nat.mod_lt _ hw⟩ : Fin w))
      (fun a _ => Finset.mem_univ _) hinj
    calc (Finset.univ.filter (fun g : Fin (optCircuit w hw ρ β).gateCount =>
            (optCircuit w hw ρ β).layer g = ell)).card
        ≤ (Finset.univ : Finset (Fin w)).card := hcard
      _ = w := by simp
  · have hempty : (Finset.univ.filter
        (fun g : Fin (optCircuit w hw ρ β).gateCount =>
          (optCircuit w hw ρ β).layer g = ell)) = ∅ := by
      apply Finset.filter_false_of_mem
      intro g _
      have := optCircuit_layer_le hw ρ β g
      omega
    rw [hempty]
    simp

/-! ## The canonical layer listings -/

/-- The source-layer vertex at position `p`. -/
def srcVertex (p : Fin w) : LayerVertex (optCircuit w hw ρ β) 0 :=
  ⟨⟨p.val, by change p.val < 2 * w; omega⟩, Nat.div_eq_of_lt p.isLt⟩

/-- The target-layer vertex at position `p`. -/
def tgtVertex (p : Fin w) : LayerVertex (optCircuit w hw ρ β) 1 :=
  ⟨⟨w + p.val, by change w + p.val < 2 * w; omega⟩, by
    change (w + p.val) / w = 1
    rw [Nat.add_comm, Nat.add_div_right _ hw, Nat.div_eq_of_lt p.isLt]⟩

theorem srcVertex_injective : Function.Injective (srcVertex hw ρ β) := by
  intro a b hab
  have h1 := Fin.ext_iff.mp (Subtype.ext_iff.mp hab)
  exact Fin.ext h1

theorem tgtVertex_injective : Function.Injective (tgtVertex hw ρ β) := by
  intro a b hab
  have h1 := Fin.ext_iff.mp (Subtype.ext_iff.mp hab)
  have h2 : w + a.val = w + b.val := h1
  exact Fin.ext (by omega)

/-- The canonical source listing. -/
noncomputable def srcListing : CyclicListing (LayerVertex (optCircuit w hw ρ β) 0) where
  entries := (List.finRange w).map (srcVertex hw ρ β)
  nodup := List.Nodup.map (srcVertex_injective hw ρ β) (List.nodup_finRange w)
  complete := by
    intro a
    have ha : a.val.val < w := by
      have h1 : a.val.val / w = 0 := a.2
      have h2 : a.val.val < 2 * w := a.val.isLt
      by_contra hcon
      push_neg at hcon
      have h3 : 1 ≤ a.val.val / w := (Nat.one_le_div_iff hw).mpr hcon
      omega
    have heq : a = srcVertex hw ρ β ⟨a.val.val, ha⟩ := by
      apply Subtype.ext
      apply Fin.ext
      rfl
    rw [heq]
    exact List.mem_map_of_mem (List.mem_finRange _)

/-- The canonical target listing. -/
noncomputable def tgtListing : CyclicListing (LayerVertex (optCircuit w hw ρ β) 1) where
  entries := (List.finRange w).map (tgtVertex hw ρ β)
  nodup := List.Nodup.map (tgtVertex_injective hw ρ β) (List.nodup_finRange w)
  complete := by
    intro a
    have h1 : a.val.val / w = 1 := a.2
    have h2 : a.val.val < 2 * w := a.val.isLt
    have ha : w ≤ a.val.val := by
      by_contra hcon
      push_neg at hcon
      have h3 : a.val.val / w = 0 := Nat.div_eq_of_lt hcon
      omega
    have hb : a.val.val - w < w := by omega
    have heq : a = tgtVertex hw ρ β ⟨a.val.val - w, hb⟩ := by
      apply Subtype.ext
      apply Fin.ext
      change a.val.val = w + (a.val.val - w)
      omega
    rw [heq]
    exact List.mem_map_of_mem (List.mem_finRange _)

theorem srcListing_length :
    (srcListing hw ρ β).entries.length = w := by
  change ((List.finRange w).map (srcVertex hw ρ β)).length = w
  rw [List.length_map, List.length_finRange]

theorem tgtListing_length :
    (tgtListing hw ρ β).entries.length = w := by
  change ((List.finRange w).map (tgtVertex hw ρ β)).length = w
  rw [List.length_map, List.length_finRange]

/-- Listings agreeing entrywise with the canonical ones. -/
def CanonicalOrders (cert : IncidenceCylinder (optCircuit w hw ρ β)) : Prop :=
  (cert.layerOrder 0).entries = (srcListing hw ρ β).entries ∧
    (cert.layerOrder 1).entries = (tgtListing hw ρ β).entries

end Basic

/-! ## Position alignment for canonical certificates -/

/-- `vtxAt` is the listing entry at the given position, for any circuit. -/
theorem vtxAt_eq_get {n : Nat} {c : ADRCircuit n} (cert : IncidenceCylinder c)
    (ell : Nat) (h : (cert.layerOrder ell).entries.length = w) (j : Fin w) :
    vtxAt c cert ell h j
      = (cert.layerOrder ell).entries.get ⟨j.val, by rw [h]; exact j.isLt⟩ := by
  have h1 : (FullLayerIndexing c cert ell)
      ((cert.layerOrder ell).entries.get ⟨j.val, by rw [h]; exact j.isLt⟩)
        = ⟨j.val, by rw [h]; exact j.isLt⟩ := by
    change ((cert.layerOrder ell).nodup.getEquiv).symm
      ⟨(cert.layerOrder ell).entries.get ⟨j.val, _⟩,
        (cert.layerOrder ell).complete _⟩ = _
    rw [Equiv.symm_apply_eq]
    apply Subtype.ext
    rfl
  change (FullLayerIndexing c cert ell).symm _ = _
  rw [Equiv.symm_apply_eq]
  exact h1.symm

section Alignment

variable (hw : 0 < w) (ρ : Fin w → Option (Fin w)) (β : Fin w → Bool)
variable {cert : IncidenceCylinder (optCircuit w hw ρ β)}

theorem canonical_tgt_length (hC : CanonicalOrders hw ρ β cert) :
    (cert.layerOrder (0 + 1)).entries.length = w := by
  change (cert.layerOrder 1).entries.length = w
  rw [hC.2]
  exact tgtListing_length hw ρ β

theorem canonical_src_length (hC : CanonicalOrders hw ρ β cert) :
    (cert.layerOrder 0).entries.length = w := by
  rw [hC.1]
  exact srcListing_length hw ρ β

/-- Entry computation for a listing that equals a `finRange`-map. -/
theorem get_of_entries_eq {α : Type} {l : List α} {f : Fin w → α}
    (hl : l = (List.finRange w).map f) {j : Fin w} (hj : j.val < l.length) :
    l.get ⟨j.val, hj⟩ = f j := by
  subst hl
  rw [List.get_eq_getElem, List.getElem_map]
  congr 1
  apply Fin.ext
  simp

/-- The vertex at target position `p` of a canonical certificate. -/
theorem canonical_vtxAt (hC : CanonicalOrders hw ρ β cert) (p : Fin w) :
    vtxAt (optCircuit w hw ρ β) cert (0 + 1) (canonical_tgt_length hw ρ β hC) p
      = tgtVertex hw ρ β p := by
  rw [vtxAt_eq_get]
  exact get_of_entries_eq hC.2 _

/-- The vertex at source position `q` of a canonical certificate. -/
theorem canonical_src_vtxAt (hC : CanonicalOrders hw ρ β cert) (q : Fin w) :
    vtxAt (optCircuit w hw ρ β) cert 0 (canonical_src_length hw ρ β hC) q
      = srcVertex hw ρ β q := by
  rw [vtxAt_eq_get]
  exact get_of_entries_eq hC.1 _

/-- The position of source vertex `q` in a canonical certificate. -/
theorem canonical_idxOfVtx (hC : CanonicalOrders hw ρ β cert) (q : Fin w) :
    idxOfVtx (optCircuit w hw ρ β) cert 0 (canonical_src_length hw ρ β hC).le
      (srcVertex hw ρ β q) = q := by
  have h3 := congrArg
    (idxOfVtx (optCircuit w hw ρ β) cert 0 (canonical_src_length hw ρ β hC).le)
    (canonical_src_vtxAt hw ρ β hC q)
  rw [idxOfVtx_vtxAt] at h3
  exact h3.symm

end Alignment

end Internal
end AllenderOQ3
