import AllenderOQ3.Incidence
import AllenderOQ3.Internal.Prune
import AllenderOQ3.Internal.LayerCompress
import AllenderOQ3.Internal.StateChain
import AllenderOQ3.Internal.IncidenceToolkit

set_option autoImplicit false
set_option linter.unusedVariables false

namespace AllenderOQ3
namespace Internal

open AllenderOQ3

theorem predecessorCount_restrict {n : Nat} {c : ADRCircuit n} {m : Nat}
    (f : SubEmbedding c m) (out : Fin m) (a : Fin m) :
    predecessorCount (restrict c f out) a = predecessorCount c (f.toFun a) := by
  classical
  unfold predecessorCount
  let F : (Fin m) ↪ (Fin c.gateCount) := ⟨f.toFun, f.inj⟩
  have hsub : (Finset.univ.filter (fun h => (restrict c f out).edge h a = true)).card =
      (Finset.univ.filter (fun h => c.edge h (f.toFun a) = true)).card := by
    rw [← Finset.card_map F]
    congr 1
    ext u
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hu
      obtain ⟨x, hx⟩ := f.predClosed a u hu
      refine ⟨x, ?_, hx⟩
      change c.edge (f.toFun x) (f.toFun a) = true
      rw [hx]
      exact hu
  exact hsub

theorem hmvNormal_restrict {n : Nat} {c : ADRCircuit n} (hc : HMVNormal c)
    {m : Nat} (f : SubEmbedding c m) (out : Fin m) :
    HMVNormal (restrict c f out) := by
  constructor
  · exact wellFormed_restrict hc.1 f out
  · intro g hg
    rw [restrict_kind] at hg
    rw [predecessorCount_restrict]
    exact hc.2 (f.toFun g) hg

theorem hmvNormal_prunedCircuit {n : Nat} {c : ADRCircuit n} (hc : HMVNormal c) :
    HMVNormal (prunedCircuit c) :=
  hmvNormal_restrict hc (ancestorEmbedding c) (ancestorOutput c)

theorem hmvNormal_shiftLayers {n : Nat} {c : ADRCircuit n} (hc : HMVNormal c)
    {m : Nat} (hm : ∀ g, m ≤ c.layer g) : HMVNormal (shiftLayers c m) := by
  constructor
  · exact wellFormed_shiftLayers hc.1 hm
  · intro g hg
    have : ((shiftLayers c m).kind g) = c.kind g := rfl
    rw [this] at hg
    have hpre : predecessorCount (shiftLayers c m) g = predecessorCount c g := rfl
    rw [hpre]
    exact hc.2 g hg

def shiftLayerVertex {n : Nat} (c : ADRCircuit n) (m : Nat) (ell : Nat)
    (hm : ∀ g, m ≤ c.layer g)
    (v : LayerVertex (shiftLayers c m) ell) : LayerVertex c (ell + m) :=
  ⟨v.val, by
    have h1 : c.layer v.val - m = ell := v.property
    have h2 : m ≤ c.layer v.val := hm v.val
    revert h1 h2
    generalize c.layer v.val = L
    intro h1 h2
    change L = ell + m
    omega⟩

def shiftLayerVertexInv {n : Nat} (c : ADRCircuit n) (m : Nat) (ell : Nat)
    (hm : ∀ g, m ≤ c.layer g)
    (v : LayerVertex c (ell + m)) : LayerVertex (shiftLayers c m) ell :=
  ⟨v.val, by
    change c.layer v.val - m = ell
    have h1 : c.layer v.val = ell + m := v.property
    revert h1
    generalize c.layer v.val = L
    intro h1
    omega⟩

def shiftTransitionArc {n : Nat} (c : ADRCircuit n) (m : Nat) (ell : Nat)
    (hm : ∀ g, m ≤ c.layer g)
    (e : TransitionArc (shiftLayers c m) ell) : TransitionArc c (ell + m) :=
  ⟨e.val, e.property.1, by
    have h1 : c.layer e.val.1 - m = ell := e.property.2.1
    have h2 : m ≤ c.layer e.val.1 := hm e.val.1
    revert h1 h2
    generalize c.layer e.val.1 = L
    intro h1 h2
    change L = ell + m
    omega,
  by
    have h1 : c.layer e.val.2 - m = ell + 1 := e.property.2.2
    have h2 : m ≤ c.layer e.val.2 := hm e.val.2
    revert h1 h2
    generalize c.layer e.val.2 = L
    intro h1 h2
    change L = ell + m + 1
    omega⟩

def shiftTransitionArcInv {n : Nat} (c : ADRCircuit n) (m : Nat) (ell : Nat)
    (hm : ∀ g, m ≤ c.layer g)
    (e : TransitionArc c (ell + m)) : TransitionArc (shiftLayers c m) ell :=
  ⟨e.val, e.property.1, by
    change c.layer e.val.1 - m = ell
    have h1 : c.layer e.val.1 = ell + m := e.property.2.1
    revert h1
    generalize c.layer e.val.1 = L
    intro h1
    omega,
  by
    change c.layer e.val.2 - m = ell + 1
    have h1 : c.layer e.val.2 = ell + m + 1 := e.property.2.2
    revert h1
    generalize c.layer e.val.2 = L
    intro h1
    omega⟩
theorem shiftLayerVertex_inv {n : Nat} {c : ADRCircuit n} {m : Nat} {ell : Nat}
    {hm : ∀ g, m ≤ c.layer g} (v : LayerVertex c (ell + m)) :
    shiftLayerVertex c m ell hm (shiftLayerVertexInv c m ell hm v) = v := by
  apply Subtype.ext
  rfl

theorem shiftLayerVertexInv_inv {n : Nat} {c : ADRCircuit n} {m : Nat} {ell : Nat}
    {hm : ∀ g, m ≤ c.layer g} (v : LayerVertex (shiftLayers c m) ell) :
    shiftLayerVertexInv c m ell hm (shiftLayerVertex c m ell hm v) = v := by
  apply Subtype.ext
  rfl

theorem shiftTransitionArc_inv {n : Nat} {c : ADRCircuit n} {m : Nat} {ell : Nat}
    {hm : ∀ g, m ≤ c.layer g} (e : TransitionArc c (ell + m)) :
    shiftTransitionArc c m ell hm (shiftTransitionArcInv c m ell hm e) = e := by
  apply Subtype.ext
  rfl

theorem shiftTransitionArcInv_inv {n : Nat} {c : ADRCircuit n} {m : Nat} {ell : Nat}
    {hm : ∀ g, m ≤ c.layer g} (e : TransitionArc (shiftLayers c m) ell) :
    shiftTransitionArcInv c m ell hm (shiftTransitionArc c m ell hm e) = e := by
  apply Subtype.ext
  rfl
theorem cyclic_rotation_map {α β : Type} (xs ys : List α) (f : α → β)
  (h : CyclicRotation xs ys) :
  CyclicRotation (xs.map f) (ys.map f) := by
  rcases h with ⟨p, q, h1, h2⟩
  use p.map f, q.map f
  rw [h1, h2]
  exact ⟨by simp, by simp⟩

def mapCyclicListing {α β : Type} [DecidableEq α] [DecidableEq β]
    (cl : CyclicListing α) (f : α → β) (g : β → α)
    (h_inv : ∀ a, g (f a) = a) (h_inv2 : ∀ b, f (g b) = b) :
    CyclicListing β where
  entries := cl.entries.map f
  nodup := by
    apply List.Nodup.map
    · intro a1 a2 h
      have : g (f a1) = g (f a2) := by rw [h]
      rw [h_inv, h_inv] at this
      exact this
    · exact cl.nodup
  complete := by
    intro b
    have : b = f (g b) := (h_inv2 b).symm
    rw [this]
    apply List.mem_map_of_mem
    exact cl.complete (g b)

def mapArcOrderCertificate {n : Nat} {c1 c2 : ADRCircuit n}
    {ell1 ell2 : Nat}
    (sourceOrder1 : CyclicListing (LayerVertex c1 ell1))
    (targetOrder1 : CyclicListing (LayerVertex c1 (ell1 + 1)))
    (cert : ArcOrderCertificate c1 ell1 sourceOrder1 targetOrder1)
    (f_v : LayerVertex c1 ell1 → LayerVertex c2 ell2)
    (f_v_inv : LayerVertex c2 ell2 → LayerVertex c1 ell1)
    (h_f_v_inv : ∀ v, f_v_inv (f_v v) = v)
    (h_f_v_inv2 : ∀ v, f_v (f_v_inv v) = v)
    (f_w : LayerVertex c1 (ell1 + 1) → LayerVertex c2 (ell2 + 1))
    (f_w_inv : LayerVertex c2 (ell2 + 1) → LayerVertex c1 (ell1 + 1))
    (h_f_w_inv : ∀ w, f_w_inv (f_w w) = w)
    (h_f_w_inv2 : ∀ w, f_w (f_w_inv w) = w)
    (f_e : TransitionArc c1 ell1 → TransitionArc c2 ell2)
    (f_e_inv : TransitionArc c2 ell2 → TransitionArc c1 ell1)
    (h_f_e_inv : ∀ e, f_e_inv (f_e e) = e)
    (h_f_e_inv2 : ∀ e, f_e (f_e_inv e) = e)
    (h_outgoing_compat : ∀ u e, (f_e e).1.1 = (f_v u).1 ↔ e.1.1 = u.1)
    (h_incoming_compat : ∀ v e, (f_e e).1.2 = (f_w v).1 ↔ e.1.2 = v.1)
    : ArcOrderCertificate c2 ell2
        (mapCyclicListing sourceOrder1 f_v f_v_inv h_f_v_inv h_f_v_inv2)
        (mapCyclicListing targetOrder1 f_w f_w_inv h_f_w_inv h_f_w_inv2) where
  outgoing := fun u => (cert.outgoing (f_v_inv u)).map f_e
  incoming := fun v => (cert.incoming (f_w_inv v)).map f_e
  outgoing_nodup := by
    intro u
    apply List.Nodup.map
    · intro e1 e2 h
      have : f_e_inv (f_e e1) = f_e_inv (f_e e2) := by rw [h]
      rw [h_f_e_inv, h_f_e_inv] at this
      exact this
    · exact cert.outgoing_nodup (f_v_inv u)
  incoming_nodup := by
    intro v
    apply List.Nodup.map
    · intro e1 e2 h
      have : f_e_inv (f_e e1) = f_e_inv (f_e e2) := by rw [h]
      rw [h_f_e_inv, h_f_e_inv] at this
      exact this
    · exact cert.incoming_nodup (f_w_inv v)
  outgoing_exact := by
    intro u e2
    simp only [List.mem_map]
    constructor
    · rintro ⟨e1, h1, h2⟩
      rw [← h2]
      have : (f_e e1).1.1 = (f_v (f_v_inv u)).1 ↔ e1.1.1 = (f_v_inv u).1 :=
        h_outgoing_compat (f_v_inv u) e1
      rw [h_f_v_inv2 u] at this
      rw [this]
      exact (cert.outgoing_exact (f_v_inv u) e1).mp h1
    · intro h
      use f_e_inv e2
      constructor
      · apply (cert.outgoing_exact (f_v_inv u) (f_e_inv e2)).mpr
        have : (f_e (f_e_inv e2)).1.1 = (f_v (f_v_inv u)).1 ↔ (f_e_inv e2).1.1 = (f_v_inv u).1 :=
          h_outgoing_compat (f_v_inv u) (f_e_inv e2)
        rw [h_f_e_inv2, h_f_v_inv2] at this
        exact this.mp h
      · exact h_f_e_inv2 e2
  incoming_exact := by
    intro v e2
    simp only [List.mem_map]
    constructor
    · rintro ⟨e1, h1, h2⟩
      rw [← h2]
      have : (f_e e1).1.2 = (f_w (f_w_inv v)).1 ↔ e1.1.2 = (f_w_inv v).1 :=
        h_incoming_compat (f_w_inv v) e1
      rw [h_f_w_inv2 v] at this
      rw [this]
      exact (cert.incoming_exact (f_w_inv v) e1).mp h1
    · intro h
      use f_e_inv e2
      constructor
      · apply (cert.incoming_exact (f_w_inv v) (f_e_inv e2)).mpr
        have : (f_e (f_e_inv e2)).1.2 = (f_w (f_w_inv v)).1 ↔ (f_e_inv e2).1.2 = (f_w_inv v).1 :=
          h_incoming_compat (f_w_inv v) (f_e_inv e2)
        rw [h_f_e_inv2, h_f_w_inv2] at this
        exact this.mp h
      · exact h_f_e_inv2 e2
  commonArcWord := by
    have h_source :
        (mapCyclicListing sourceOrder1 f_v f_v_inv h_f_v_inv h_f_v_inv2).entries
          = sourceOrder1.entries.map f_v := rfl
    have h_target :
        (mapCyclicListing targetOrder1 f_w f_w_inv h_f_w_inv h_f_w_inv2).entries
          = targetOrder1.entries.map f_w := rfl
    rw [h_source, h_target]
    have h1 :
        (sourceOrder1.entries.map f_v).flatMap
            (fun u => (cert.outgoing (f_v_inv u)).map f_e)
          = (sourceOrder1.entries.flatMap cert.outgoing).map f_e := by
      rw [List.flatMap_map f_v (fun u => (cert.outgoing (f_v_inv u)).map f_e)]
      have : (fun (x : LayerVertex c1 ell1) =>
            List.map f_e (cert.outgoing (f_v_inv (f_v x))))
          = (fun x => List.map f_e (cert.outgoing x)) := by
        funext x
        rw [h_f_v_inv]
      rw [this]
      exact List.map_flatMap.symm
    have h2 :
        (targetOrder1.entries.map f_w).flatMap
            (fun v => (cert.incoming (f_w_inv v)).map f_e)
          = (targetOrder1.entries.flatMap cert.incoming).map f_e := by
      rw [List.flatMap_map f_w (fun v => (cert.incoming (f_w_inv v)).map f_e)]
      have : (fun (x : LayerVertex c1 (ell1 + 1)) =>
            List.map f_e (cert.incoming (f_w_inv (f_w x))))
          = (fun x => List.map f_e (cert.incoming x)) := by
        funext x
        rw [h_f_w_inv]
      rw [this]
      exact List.map_flatMap.symm
    rw [h1, h2]
    exact cyclic_rotation_map _ _ _ cert.commonArcWord

/-!
### Layer shift

The shift is indexed as `m + ell` rather than `ell + m`; with that convention
the successor layer `m + (ell + 1)` is *definitionally* `(m + ell) + 1`, so the
source/target listings of the transported certificate line up on the nose.
-/

def shiftLV {n : Nat} (c : ADRCircuit n) (m ell : Nat) (hm : ∀ g, m ≤ c.layer g)
    (v : LayerVertex c (m + ell)) : LayerVertex (shiftLayers c m) ell :=
  ⟨v.val, by
    have h1 : c.layer v.val = m + ell := v.property
    have h2 : m ≤ c.layer v.val := hm v.val
    change c.layer v.val - m = ell
    omega⟩

def shiftLVinv {n : Nat} (c : ADRCircuit n) (m ell : Nat) (hm : ∀ g, m ≤ c.layer g)
    (v : LayerVertex (shiftLayers c m) ell) : LayerVertex c (m + ell) :=
  ⟨v.val, by
    have h1 : c.layer v.val - m = ell := v.property
    have h2 : m ≤ c.layer v.val := hm v.val
    change c.layer v.val = m + ell
    omega⟩

theorem shiftLV_inv {n : Nat} {c : ADRCircuit n} {m ell : Nat}
    {hm : ∀ g, m ≤ c.layer g} (v : LayerVertex c (m + ell)) :
    shiftLVinv c m ell hm (shiftLV c m ell hm v) = v := Subtype.ext rfl

theorem shiftLVinv_inv {n : Nat} {c : ADRCircuit n} {m ell : Nat}
    {hm : ∀ g, m ≤ c.layer g} (v : LayerVertex (shiftLayers c m) ell) :
    shiftLV c m ell hm (shiftLVinv c m ell hm v) = v := Subtype.ext rfl

def shiftTA {n : Nat} (c : ADRCircuit n) (m ell : Nat) (hm : ∀ g, m ≤ c.layer g)
    (e : TransitionArc c (m + ell)) : TransitionArc (shiftLayers c m) ell :=
  ⟨e.val, e.property.1, by
    have h1 : c.layer e.val.1 = m + ell := e.property.2.1
    have h2 : m ≤ c.layer e.val.1 := hm e.val.1
    change c.layer e.val.1 - m = ell
    omega,
   by
    have h1 : c.layer e.val.2 = m + ell + 1 := e.property.2.2
    have h2 : m ≤ c.layer e.val.2 := hm e.val.2
    change c.layer e.val.2 - m = ell + 1
    omega⟩

def shiftTAinv {n : Nat} (c : ADRCircuit n) (m ell : Nat) (hm : ∀ g, m ≤ c.layer g)
    (e : TransitionArc (shiftLayers c m) ell) : TransitionArc c (m + ell) :=
  ⟨e.val, e.property.1, by
    have h1 : c.layer e.val.1 - m = ell := e.property.2.1
    have h2 : m ≤ c.layer e.val.1 := hm e.val.1
    change c.layer e.val.1 = m + ell
    omega,
   by
    have h1 : c.layer e.val.2 - m = ell + 1 := e.property.2.2
    have h2 : m ≤ c.layer e.val.2 := hm e.val.2
    change c.layer e.val.2 = m + ell + 1
    omega⟩

theorem shiftTA_inv {n : Nat} {c : ADRCircuit n} {m ell : Nat}
    {hm : ∀ g, m ≤ c.layer g} (e : TransitionArc c (m + ell)) :
    shiftTAinv c m ell hm (shiftTA c m ell hm e) = e := Subtype.ext rfl

theorem shiftTAinv_inv {n : Nat} {c : ADRCircuit n} {m ell : Nat}
    {hm : ∀ g, m ≤ c.layer g} (e : TransitionArc (shiftLayers c m) ell) :
    shiftTA c m ell hm (shiftTAinv c m ell hm e) = e := Subtype.ext rfl

/-- Transport of an incidence cylinder along a uniform downward layer shift. -/
def incidenceCylinder_shiftLayers {n : Nat} {c : ADRCircuit n}
    (cyl : IncidenceCylinder c) {m : Nat} (hm : ∀ g, m ≤ c.layer g) :
    IncidenceCylinder (shiftLayers c m) where
  layerOrder ell := mapCyclicListing (cyl.layerOrder (m + ell))
    (shiftLV c m ell hm) (shiftLVinv c m ell hm)
    (fun v => shiftLV_inv (c := c) (m := m) (ell := ell) (hm := hm) v)
    (fun v => shiftLVinv_inv (c := c) (m := m) (ell := ell) (hm := hm) v)
  transitionOrder ell :=
    mapArcOrderCertificate _ _ (cyl.transitionOrder (m + ell))
      (shiftLV c m ell hm) (shiftLVinv c m ell hm)
      (fun v => shiftLV_inv (c := c) (m := m) (ell := ell) (hm := hm) v)
      (fun v => shiftLVinv_inv (c := c) (m := m) (ell := ell) (hm := hm) v)
      (shiftLV c m (ell + 1) hm) (shiftLVinv c m (ell + 1) hm)
      (fun v => shiftLV_inv (c := c) (m := m) (ell := ell + 1) (hm := hm) v)
      (fun v => shiftLVinv_inv (c := c) (m := m) (ell := ell + 1) (hm := hm) v)
      (shiftTA c m ell hm) (shiftTAinv c m ell hm)
      (fun e => shiftTA_inv (c := c) (m := m) (ell := ell) (hm := hm) e)
      (fun e => shiftTAinv_inv (c := c) (m := m) (ell := ell) (hm := hm) e)
      (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl)

/-!
### Generic list combinatorics for filtered transport
-/

theorem cyclicRotation_filterMap {α β : Type} (xs ys : List α) (f : α → Option β)
    (h : CyclicRotation xs ys) :
    CyclicRotation (xs.filterMap f) (ys.filterMap f) := by
  obtain ⟨p, q, h1, h2⟩ := h
  refine ⟨p.filterMap f, q.filterMap f, ?_, ?_⟩
  · rw [h1, List.filterMap_append]
  · rw [h2, List.filterMap_append]

theorem filterMap_flatMap_eq {α β γ : Type} (l : List α) (g : α → List β)
    (f : β → Option γ) :
    (l.flatMap g).filterMap f = l.flatMap (fun x => (g x).filterMap f) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      simp only [List.flatMap_cons, List.filterMap_append, ih]

theorem flatMap_filterMap_eq {α β δ : Type} (l : List α) (t : α → Option β)
    (G : β → List δ) (H : α → List δ)
    (hsome : ∀ a b, t a = some b → G b = H a)
    (hnone : ∀ a, t a = none → H a = []) :
    (l.filterMap t).flatMap G = l.flatMap H := by
  induction l with
  | nil => rfl
  | cons a tl ih =>
      cases hta : t a with
      | none =>
          rw [List.filterMap_cons_none hta, ih, List.flatMap_cons, hnone a hta,
            List.nil_append]
      | some b =>
          rw [List.filterMap_cons_some hta, List.flatMap_cons, List.flatMap_cons,
            ih, hsome a b hta]

/-!
### Certificate transport through a predecessor-closed restriction

`restrict c f out` keeps exactly the gates in the range of `f`.  Transporting an
incidence certificate is *not* a bijection: a layer's vertex set shrinks to its
retained sublist, so the construction is a `filterMap`, not a `map`.

The two facts that make it work are:

* every arc *into* a retained vertex has a retained tail (`SubEmbedding.predClosed`),
  so a non-retained tail contributes an empty outgoing block, and
* filtering both sides of a `CyclicRotation` by the same partial map preserves it.
-/

section RestrictTransport

variable {n : Nat} {c : ADRCircuit n} {m : Nat}

/-- The layer vertex of `c` underlying a layer vertex of the restriction. -/
def embLV (f : SubEmbedding c m) (out : Fin m) (ell : Nat)
    (a : LayerVertex (restrict c f out) ell) : LayerVertex c ell :=
  ⟨f.toFun a.val, a.property⟩

/-- The transition arc of `c` underlying a transition arc of the restriction. -/
def embTA (f : SubEmbedding c m) (out : Fin m) (ell : Nat)
    (e : TransitionArc (restrict c f out) ell) : TransitionArc c ell :=
  ⟨(f.toFun e.val.1, f.toFun e.val.2), e.property.1, e.property.2.1, e.property.2.2⟩

/-- Partial inverse of `embLV`: a layer vertex of `c` is retained iff it is in
the range of the embedding. -/
noncomputable def restrictLV (f : SubEmbedding c m) (out : Fin m) (ell : Nat)
    (v : LayerVertex c ell) : Option (LayerVertex (restrict c f out) ell) :=
  if h : ∃ a : Fin m, f.toFun a = v.val then
    some ⟨h.choose, by
      change c.layer (f.toFun h.choose) = ell
      rw [h.choose_spec]
      exact v.property⟩
  else none

/-- Partial inverse of `embTA`. -/
noncomputable def restrictTA (f : SubEmbedding c m) (out : Fin m) (ell : Nat)
    (e : TransitionArc c ell) : Option (TransitionArc (restrict c f out) ell) :=
  if h : ∃ p : Fin m × Fin m, f.toFun p.1 = e.val.1 ∧ f.toFun p.2 = e.val.2 then
    some ⟨h.choose,
      by
        change c.edge (f.toFun h.choose.1) (f.toFun h.choose.2) = true
        rw [h.choose_spec.1, h.choose_spec.2]
        exact e.property.1,
      by
        change c.layer (f.toFun h.choose.1) = ell
        rw [h.choose_spec.1]
        exact e.property.2.1,
      by
        change c.layer (f.toFun h.choose.2) = ell + 1
        rw [h.choose_spec.2]
        exact e.property.2.2⟩
  else none

theorem restrictLV_embLV (f : SubEmbedding c m) (out : Fin m) (ell : Nat)
    (a : LayerVertex (restrict c f out) ell) :
    restrictLV f out ell (embLV f out ell a) = some a := by
  have h : ∃ b : Fin m, f.toFun b = (embLV f out ell a).val := ⟨a.val, rfl⟩
  rw [restrictLV, dif_pos h]
  exact congrArg some (Subtype.ext (f.inj h.choose_spec))

theorem embLV_of_restrictLV (f : SubEmbedding c m) (out : Fin m) (ell : Nat)
    {v : LayerVertex c ell} {a : LayerVertex (restrict c f out) ell}
    (hv : restrictLV f out ell v = some a) : embLV f out ell a = v := by
  rw [restrictLV] at hv
  split at hv
  · rename_i h
    have hav : a = ⟨h.choose, _⟩ := (Option.some.inj hv).symm
    apply Subtype.ext
    change f.toFun a.val = v.val
    rw [hav]
    exact h.choose_spec
  · exact absurd hv (by simp)

theorem restrictLV_eq_none_iff (f : SubEmbedding c m) (out : Fin m) (ell : Nat)
    (v : LayerVertex c ell) :
    restrictLV f out ell v = none ↔ ¬ ∃ a : Fin m, f.toFun a = v.val := by
  rw [restrictLV]
  split <;> simp_all

theorem restrictTA_embTA (f : SubEmbedding c m) (out : Fin m) (ell : Nat)
    (e : TransitionArc (restrict c f out) ell) :
    restrictTA f out ell (embTA f out ell e) = some e := by
  have h : ∃ p : Fin m × Fin m,
      f.toFun p.1 = (embTA f out ell e).val.1 ∧
      f.toFun p.2 = (embTA f out ell e).val.2 := ⟨e.val, rfl, rfl⟩
  rw [restrictTA, dif_pos h]
  refine congrArg some (Subtype.ext ?_)
  have h1 : h.choose.1 = e.val.1 := f.inj h.choose_spec.1
  have h2 : h.choose.2 = e.val.2 := f.inj h.choose_spec.2
  change h.choose = e.val
  have hp : (h.choose.1, h.choose.2) = (e.val.1, e.val.2) := by rw [h1, h2]
  simpa using hp

theorem embTA_of_restrictTA (f : SubEmbedding c m) (out : Fin m) (ell : Nat)
    {e : TransitionArc c ell} {e' : TransitionArc (restrict c f out) ell}
    (he : restrictTA f out ell e = some e') : embTA f out ell e' = e := by
  rw [restrictTA] at he
  split at he
  · rename_i h
    have hval : h.choose = e'.val := congrArg Subtype.val (Option.some.inj he)
    apply Subtype.ext
    change (f.toFun e'.val.1, f.toFun e'.val.2) = e.val
    rw [← hval, h.choose_spec.1, h.choose_spec.2]
  · exact absurd he (by simp)

theorem restrictTA_eq_none_of_tail (f : SubEmbedding c m) (out : Fin m) (ell : Nat)
    (e : TransitionArc c ell) (h : ¬ ∃ a : Fin m, f.toFun a = e.val.1) :
    restrictTA f out ell e = none := by
  rw [restrictTA, dif_neg]
  rintro ⟨p, hp1, -⟩
  exact h ⟨p.1, hp1⟩

theorem restrictTA_eq_none_of_head (f : SubEmbedding c m) (out : Fin m) (ell : Nat)
    (e : TransitionArc c ell) (h : ¬ ∃ b : Fin m, f.toFun b = e.val.2) :
    restrictTA f out ell e = none := by
  rw [restrictTA, dif_neg]
  rintro ⟨p, -, hp2⟩
  exact h ⟨p.2, hp2⟩

/-- The retained part of a layer listing. -/
noncomputable def restrictListing (f : SubEmbedding c m) (out : Fin m) (ell : Nat)
    (cl : CyclicListing (LayerVertex c ell)) :
    CyclicListing (LayerVertex (restrict c f out) ell) where
  entries := cl.entries.filterMap (restrictLV f out ell)
  nodup := by
    refine List.Nodup.filterMap ?_ cl.nodup
    intro a a' b hb hb'
    have h1 := embLV_of_restrictLV f out ell hb
    have h2 := embLV_of_restrictLV f out ell hb'
    rw [← h1, ← h2]
  complete := by
    intro a
    refine List.mem_filterMap.mpr ⟨embLV f out ell a, cl.complete _, ?_⟩
    exact restrictLV_embLV f out ell a

/-- Transport of an incidence cylinder through a predecessor-closed restriction. -/
noncomputable def incidenceCylinder_restrict (f : SubEmbedding c m) (out : Fin m)
    (cyl : IncidenceCylinder c) : IncidenceCylinder (restrict c f out) where
  layerOrder ell := restrictListing f out ell (cyl.layerOrder ell)
  transitionOrder ell :=
    { outgoing := fun u =>
        ((cyl.transitionOrder ell).outgoing (embLV f out ell u)).filterMap
          (restrictTA f out ell)
      incoming := fun v =>
        ((cyl.transitionOrder ell).incoming (embLV f out (ell + 1) v)).filterMap
          (restrictTA f out ell)
      outgoing_nodup := by
        intro u
        refine List.Nodup.filterMap ?_ ((cyl.transitionOrder ell).outgoing_nodup _)
        intro e e' e0 h1 h2
        rw [← embTA_of_restrictTA f out ell h1, ← embTA_of_restrictTA f out ell h2]
      incoming_nodup := by
        intro v
        refine List.Nodup.filterMap ?_ ((cyl.transitionOrder ell).incoming_nodup _)
        intro e e' e0 h1 h2
        rw [← embTA_of_restrictTA f out ell h1, ← embTA_of_restrictTA f out ell h2]
      outgoing_exact := by
        intro u e
        constructor
        · intro hmem
          obtain ⟨e0, h0, h1⟩ := List.mem_filterMap.mp hmem
          have h2 := ((cyl.transitionOrder ell).outgoing_exact _ e0).mp h0
          have h3 : embTA f out ell e = e0 := embTA_of_restrictTA f out ell h1
          apply f.inj
          change f.toFun e.val.1 = f.toFun u.val
          have hfe : f.toFun e.val.1 = e0.val.1 := congrArg (fun z => z.val.1) h3
          rw [hfe, h2]
          rfl
        · intro hu
          refine List.mem_filterMap.mpr ⟨embTA f out ell e, ?_, ?_⟩
          · refine ((cyl.transitionOrder ell).outgoing_exact _ _).mpr ?_
            change f.toFun e.val.1 = f.toFun u.val
            rw [hu]
          · exact restrictTA_embTA f out ell e
      incoming_exact := by
        intro v e
        constructor
        · intro hmem
          obtain ⟨e0, h0, h1⟩ := List.mem_filterMap.mp hmem
          have h2 := ((cyl.transitionOrder ell).incoming_exact _ e0).mp h0
          have h3 : embTA f out ell e = e0 := embTA_of_restrictTA f out ell h1
          apply f.inj
          change f.toFun e.val.2 = f.toFun v.val
          have hfe : f.toFun e.val.2 = e0.val.2 := congrArg (fun z => z.val.2) h3
          rw [hfe, h2]
          rfl
        · intro hv
          refine List.mem_filterMap.mpr ⟨embTA f out ell e, ?_, ?_⟩
          · refine ((cyl.transitionOrder ell).incoming_exact _ _).mpr ?_
            change f.toFun e.val.2 = f.toFun v.val
            rw [hv]
          · exact restrictTA_embTA f out ell e
      commonArcWord := by
        have hsrc :
            (restrictListing f out ell (cyl.layerOrder ell)).entries.flatMap
              (fun u => ((cyl.transitionOrder ell).outgoing
                (embLV f out ell u)).filterMap (restrictTA f out ell))
              = ((cyl.layerOrder ell).entries.flatMap
                  (cyl.transitionOrder ell).outgoing).filterMap
                  (restrictTA f out ell) := by
          rw [filterMap_flatMap_eq]
          refine flatMap_filterMap_eq _ _ _ _ ?_ ?_
          · intro v a hva
            rw [embLV_of_restrictLV f out ell hva]
          · intro v hv
            refine List.filterMap_eq_nil_iff.mpr ?_
            intro e he
            have hev := ((cyl.transitionOrder ell).outgoing_exact v e).mp he
            refine restrictTA_eq_none_of_tail f out ell e ?_
            rintro ⟨a, ha⟩
            exact ((restrictLV_eq_none_iff f out ell v).mp hv) ⟨a, by rw [ha, hev]⟩
        have htgt :
            (restrictListing f out (ell + 1) (cyl.layerOrder (ell + 1))).entries.flatMap
              (fun v => ((cyl.transitionOrder ell).incoming
                (embLV f out (ell + 1) v)).filterMap (restrictTA f out ell))
              = ((cyl.layerOrder (ell + 1)).entries.flatMap
                  (cyl.transitionOrder ell).incoming).filterMap
                  (restrictTA f out ell) := by
          rw [filterMap_flatMap_eq]
          refine flatMap_filterMap_eq _ _ _ _ ?_ ?_
          · intro v a hva
            rw [embLV_of_restrictLV f out (ell + 1) hva]
          · intro v hv
            refine List.filterMap_eq_nil_iff.mpr ?_
            intro e he
            have hev := ((cyl.transitionOrder ell).incoming_exact v e).mp he
            refine restrictTA_eq_none_of_head f out ell e ?_
            rintro ⟨b, hb⟩
            exact ((restrictLV_eq_none_iff f out (ell + 1) v).mp hv)
              ⟨b, by rw [hb, hev]⟩
        rw [hsrc, htgt]
        exact cyclicRotation_filterMap _ _ _
          (cyl.transitionOrder ell).commonArcWord }

end RestrictTransport

/-- Transport of an incidence cylinder through ancestor pruning. -/
noncomputable def incidenceCylinder_prunedCircuit {n : Nat} {c : ADRCircuit n}
    (cyl : IncidenceCylinder c) : IncidenceCylinder (prunedCircuit c) :=
  incidenceCylinder_restrict (ancestorEmbedding c) (ancestorOutput c) cyl

/-- `Nonempty` form of `incidenceCylinder_restrict`. -/
theorem nonempty_incidenceCylinder_restrict {n : Nat} {c : ADRCircuit n} {m : Nat}
    (f : SubEmbedding c m) (out : Fin m) (h : Nonempty (IncidenceCylinder c)) :
    Nonempty (IncidenceCylinder (restrict c f out)) :=
  h.elim fun cyl => ⟨incidenceCylinder_restrict f out cyl⟩

/-- `Nonempty` form of `incidenceCylinder_prunedCircuit`. -/
theorem nonempty_incidenceCylinder_prunedCircuit {n : Nat} {c : ADRCircuit n}
    (h : Nonempty (IncidenceCylinder c)) :
    Nonempty (IncidenceCylinder (prunedCircuit c)) :=
  h.elim fun cyl => ⟨incidenceCylinder_prunedCircuit cyl⟩

/-- `Nonempty` form of `incidenceCylinder_shiftLayers`. -/
theorem nonempty_incidenceCylinder_shiftLayers {n : Nat} {c : ADRCircuit n} {m : Nat}
    (hm : ∀ g, m ≤ c.layer g) (h : Nonempty (IncidenceCylinder c)) :
    Nonempty (IncidenceCylinder (shiftLayers c m)) :=
  h.elim fun cyl => ⟨incidenceCylinder_shiftLayers cyl hm⟩

end Internal
end AllenderOQ3
