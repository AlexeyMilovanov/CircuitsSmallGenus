import AllenderOQ3.Incidence
import AllenderOQ3.Base
import AllenderOQ3.Internal.IncidenceToolkit

set_option autoImplicit false

namespace AllenderOQ3.Internal

/-!
# Building an `ADRCircuit` from an abstract finite gate type

`ADRCircuit` indexes its gates by `Fin gateCount`.  Every construction that
*builds* a circuit (the incidence refinement N4 of `docs/INCIDENCE_REFINEMENT.md`
above all) is far easier to describe on a structured finite gate type -- a sum of
old gates, fresh ports, copy rails and fold nodes -- than on a numeral interval.

This file provides the bridge.  An `ADRSpec n G` is the circuit data on an
arbitrary finite gate type `G`; `ofSpec` transports it to an honest
`ADRCircuit n` along `Fintype.equivFin G`, and the lemmas below translate every
property used by the refinement interface -- well-formedness, fan-in,
total width, gate count, valuations -- back and forth.  Consequently a
construction may be carried out, and verified, entirely on `G`.

Everything here is `sorry`-free.
-/

/-- Circuit data on an arbitrary gate type. -/
structure ADRSpec (n : Nat) (G : Type) where
  /-- The output gate. -/
  output : G
  /-- The gate labels. -/
  kind : G → ADRGate n
  /-- The layer of each gate. -/
  layer : G → Nat
  /-- The wire relation. -/
  edge : G → G → Bool

variable {n : Nat} {G : Type} [Fintype G]

/-- The gate type transported into `Fin (Fintype.card G)`. -/
noncomputable def specIndex (G : Type) [Fintype G] : G ≃ Fin (Fintype.card G) :=
  Fintype.equivFin G

/-- The circuit described by a spec. -/
noncomputable def ofSpec (s : ADRSpec n G) : ADRCircuit n where
  gateCount := Fintype.card G
  output := specIndex G s.output
  kind := fun i => s.kind ((specIndex G).symm i)
  layer := fun i => s.layer ((specIndex G).symm i)
  edge := fun i j => s.edge ((specIndex G).symm i) ((specIndex G).symm j)

@[simp] theorem ofSpec_gateCount (s : ADRSpec n G) :
    (ofSpec s).gateCount = Fintype.card G := rfl

/-- The embedding of the abstract gate type into the gates of `ofSpec s`. -/
noncomputable def specEmb (s : ADRSpec n G) (g : G) : Fin (ofSpec s).gateCount :=
  specIndex G g

@[simp] theorem specEmb_symm (s : ADRSpec n G) (g : G) :
    (specIndex G).symm (specEmb s g) = g :=
  (specIndex G).symm_apply_apply g

theorem specEmb_injective (s : ADRSpec n G) : Function.Injective (specEmb s) :=
  fun _ _ h => (specIndex G).injective h

theorem specEmb_surjective (s : ADRSpec n G) : Function.Surjective (specEmb s) :=
  fun i => ⟨(specIndex G).symm i, (specIndex G).apply_symm_apply i⟩

@[simp] theorem ofSpec_kind (s : ADRSpec n G) (g : G) :
    (ofSpec s).kind (specEmb s g) = s.kind g := by
  simp [ofSpec, specEmb]

@[simp] theorem ofSpec_layer (s : ADRSpec n G) (g : G) :
    (ofSpec s).layer (specEmb s g) = s.layer g := by
  simp [ofSpec, specEmb]

@[simp] theorem ofSpec_edge (s : ADRSpec n G) (g h : G) :
    (ofSpec s).edge (specEmb s g) (specEmb s h) = s.edge g h := by
  simp [ofSpec, specEmb]

@[simp] theorem ofSpec_output (s : ADRSpec n G) :
    (ofSpec s).output = specEmb s s.output := rfl

/-! ## Counting -/

/-- Cardinalities of index sets computed on `G` transfer to `ofSpec s`. -/
theorem card_filter_ofSpec (s : ADRSpec n G) (p : G → Prop) [DecidablePred p] :
    (Finset.univ.filter fun i : Fin (ofSpec s).gateCount =>
        p ((specIndex G).symm i)).card
      = (Finset.univ.filter p).card := by
  classical
  refine (Finset.card_equiv (specIndex G) ?_).symm
  intro g
  simp

/-! ## Well-formedness, fan-in, width -/

/-- Well-formedness stated on the abstract gate type. -/
def SpecWellFormed (s : ADRSpec n G) : Prop :=
  (∀ u v, s.edge u v = true → s.layer u + 1 = s.layer v) ∧
  (∀ g, (∃ (i : Fin n) (b : Bool), s.kind g = .literal i b) →
    ∀ h, s.edge h g = false)

theorem wellFormed_ofSpec {s : ADRSpec n G} (h : SpecWellFormed s) :
    WellFormedADR (ofSpec s) := by
  classical
  refine ⟨fun u v huv => ?_, fun g hg h' => ?_⟩
  · have := h.1 ((specIndex G).symm u) ((specIndex G).symm v) huv
    simpa [ofSpec] using this
  · exact h.2 ((specIndex G).symm g) (by simpa [ofSpec] using hg) ((specIndex G).symm h')

/-- The fan-in of a gate of `ofSpec s`, computed on `G`. -/
theorem predecessorCount_ofSpec (s : ADRSpec n G) (g : G) :
    predecessorCount (ofSpec s) (specEmb s g)
      = (Finset.univ.filter fun h => s.edge h g = true).card := by
  classical
  have := card_filter_ofSpec s (fun h => s.edge h g = true)
  simpa [predecessorCount, ofSpec, specEmb] using this

/-- Fan-in bounds transfer. -/
theorem fanin_ofSpec {s : ADRSpec n G} {F : Nat}
    (h : ∀ g, (Finset.univ.filter fun h => s.edge h g = true).card ≤ F) :
    ∀ i, predecessorCount (ofSpec s) i ≤ F := by
  intro i
  obtain ⟨g, rfl⟩ := specEmb_surjective s i
  rw [predecessorCount_ofSpec]
  exact h g

theorem hmvNormal_ofSpec {s : ADRSpec n G} (hwf : SpecWellFormed s)
    (h : ∀ g, (s.kind g).isComputation = true →
      (Finset.univ.filter fun h => s.edge h g = true).card ≤ 2) :
    HMVNormal (ofSpec s) := by
  refine ⟨wellFormed_ofSpec hwf, fun i hi => ?_⟩
  obtain ⟨g, rfl⟩ := specEmb_surjective s i
  rw [predecessorCount_ofSpec]
  exact h g (by simpa using hi)

/-- Total width bounds transfer. -/
theorem totalWidth_ofSpec {s : ADRSpec n G} {W : Nat}
    (h : ∀ ell, (Finset.univ.filter fun g => s.layer g = ell).card ≤ W) :
    TotalWidthAtMost (ofSpec s) W := by
  classical
  intro ell
  have hcard := card_filter_ofSpec s (fun g => s.layer g = ell)
  have : (Finset.univ.filter fun i : Fin (ofSpec s).gateCount =>
      (ofSpec s).layer i = ell).card
      = (Finset.univ.filter fun g => s.layer g = ell).card := by
    simpa [ofSpec] using hcard
  rw [this]
  exact h ell

/-! ## Semantics -/

/-- Universal quantification over the predecessors of `specEmb s g` transfers to `G`. -/
theorem ofSpec_forall_pred (s : ADRSpec n G) (g : G)
    (P : Fin (ofSpec s).gateCount → Prop) :
    (∀ i, (ofSpec s).edge i (specEmb s g) = true → P i)
      ↔ ∀ h : G, s.edge h g = true → P (specEmb s h) := by
  constructor
  · intro H h hh
    exact H _ (by simpa using hh)
  · intro H i hi
    obtain ⟨h, rfl⟩ := specEmb_surjective s i
    exact H h (by simpa using hi)

/-- Existential quantification over the predecessors of `specEmb s g` transfers to `G`. -/
theorem ofSpec_exists_pred (s : ADRSpec n G) (g : G)
    (P : Fin (ofSpec s).gateCount → Prop) :
    (∃ i, (ofSpec s).edge i (specEmb s g) = true ∧ P i)
      ↔ ∃ h : G, s.edge h g = true ∧ P (specEmb s h) := by
  constructor
  · rintro ⟨i, hi, hP⟩
    obtain ⟨h, rfl⟩ := specEmb_surjective s i
    exact ⟨h, by simpa using hi, hP⟩
  · rintro ⟨h, hh, hP⟩
    exact ⟨specEmb s h, by simpa using hh, hP⟩

/-- The valuation condition on the abstract gate type. -/
def SpecValuation (s : ADRSpec n G) (x : Fin n → Bool) (value : G → Bool) : Prop :=
  ∀ g, match s.kind g with
    | .literal i negated =>
        value g = if negated then !(x i) else x i
    | .andGate =>
        (value g = true ↔ ∀ h, s.edge h g = true → value h = true)
    | .orGate =>
        (value g = true ↔ ∃ h, s.edge h g = true ∧ value h = true)

/-- Valuations of `ofSpec s` are exactly the abstract valuations of `s`. -/
theorem adrValuation_ofSpec_iff (s : ADRSpec n G) (x : Fin n → Bool)
    (value : Fin (ofSpec s).gateCount → Bool) :
    ADRValuation (ofSpec s) x value ↔ SpecValuation s x (fun g => value (specEmb s g)) := by
  constructor
  · intro h g
    have hg := h (specEmb s g)
    rw [ofSpec_kind] at hg
    cases hk : s.kind g with
    | literal i b =>
        rw [hk] at hg
        exact hg
    | andGate =>
        rw [hk] at hg
        exact hg.trans (ofSpec_forall_pred s g (fun i => value i = true))
    | orGate =>
        rw [hk] at hg
        exact hg.trans (ofSpec_exists_pred s g (fun i => value i = true))
  · intro h i
    obtain ⟨g, rfl⟩ := specEmb_surjective s i
    have hg := h g
    rw [ofSpec_kind]
    cases hk : s.kind g with
    | literal i b =>
        rw [hk] at hg
        exact hg
    | andGate =>
        rw [hk] at hg
        exact hg.trans (ofSpec_forall_pred s g (fun i => value i = true)).symm
    | orGate =>
        rw [hk] at hg
        exact hg.trans (ofSpec_exists_pred s g (fun i => value i = true)).symm

/-! ## Incidence certificates -/

section Incidence

variable [DecidableEq G]

/-- A vertex of layer `ell`, on the abstract gate type. -/
def SpecLayerVertex (s : ADRSpec n G) (ell : Nat) := {g : G // s.layer g = ell}

instance (s : ADRSpec n G) (ell : Nat) : DecidableEq (SpecLayerVertex s ell) :=
  inferInstanceAs (DecidableEq {g : G // s.layer g = ell})

/-- An arc of the transition out of layer `ell`, on the abstract gate type. -/
def SpecTransitionArc (s : ADRSpec n G) (ell : Nat) :=
  {e : G × G // s.edge e.1 e.2 = true ∧ s.layer e.1 = ell ∧ s.layer e.2 = ell + 1}

instance (s : ADRSpec n G) (ell : Nat) : DecidableEq (SpecTransitionArc s ell) :=
  inferInstanceAs (DecidableEq {p : G × G //
    s.edge p.1 p.2 = true ∧ s.layer p.1 = ell ∧ s.layer p.2 = ell + 1})

/-- The source endpoint of an abstract transition arc. -/
def specArcSource {s : ADRSpec n G} {ell : Nat} (e : SpecTransitionArc s ell) :
    SpecLayerVertex s ell := ⟨e.1.1, e.2.2.1⟩

/-- The target endpoint of an abstract transition arc. -/
def specArcTarget {s : ADRSpec n G} {ell : Nat} (e : SpecTransitionArc s ell) :
    SpecLayerVertex s (ell + 1) := ⟨e.1.2, e.2.2.2⟩

/-- Abstract layer vertices are the layer vertices of `ofSpec s`. -/
noncomputable def specLayerVertexEquiv (s : ADRSpec n G) (ell : Nat) :
    SpecLayerVertex s ell ≃ LayerVertex (ofSpec s) ell where
  toFun g := ⟨specEmb s g.1, by simpa using g.2⟩
  invFun v := ⟨(specIndex G).symm v.1, v.2⟩
  left_inv g := by apply Subtype.ext; simp [specEmb]
  right_inv v := by apply Subtype.ext; simp [specEmb]

/-- Abstract transition arcs are the transition arcs of `ofSpec s`. -/
noncomputable def specTransitionArcEquiv (s : ADRSpec n G) (ell : Nat) :
    SpecTransitionArc s ell ≃ TransitionArc (ofSpec s) ell where
  toFun e := ⟨(specEmb s e.1.1, specEmb s e.1.2),
    by refine ⟨by simpa using e.2.1, by simpa using e.2.2.1, by simpa using e.2.2.2⟩⟩
  invFun e := ⟨((specIndex G).symm e.1.1, (specIndex G).symm e.1.2), e.2⟩
  left_inv e := by
    apply Subtype.ext
    simp [specEmb]
  right_inv e := by
    apply Subtype.ext
    simp [specEmb]

omit [DecidableEq G] in
@[simp] theorem specTransitionArcEquiv_source (s : ADRSpec n G) (ell : Nat)
    (e : SpecTransitionArc s ell) :
    arcSource (specTransitionArcEquiv s ell e) = specLayerVertexEquiv s ell (specArcSource e) :=
  rfl

omit [DecidableEq G] in
@[simp] theorem specTransitionArcEquiv_target (s : ADRSpec n G) (ell : Nat)
    (e : SpecTransitionArc s ell) :
    arcTarget (specTransitionArcEquiv s ell e)
      = specLayerVertexEquiv s (ell + 1) (specArcTarget e) :=
  rfl

/-- **Incidence certificates may be built on the abstract gate type.**  One arc word per
transition, listing every abstract arc exactly once and grouped both along the source
layer order and along the target layer order, makes `ofSpec s` incidence-cylindrical. -/
theorem incidenceCylinder_ofSpec (s : ADRSpec n G)
    (order : ∀ ell, CyclicListing (SpecLayerVertex s ell))
    (word : ∀ ell, List (SpecTransitionArc s ell))
    (hnodup : ∀ ell, (word ell).Nodup)
    (hcomplete : ∀ ell (e : SpecTransitionArc s ell), e ∈ word ell)
    (hS : ∀ ell, GroupedAlong specArcSource (order ell).entries (word ell))
    (hT : ∀ ell, GroupedAlong specArcTarget (order (ell + 1)).entries (word ell)) :
    Nonempty (IncidenceCylinder (ofSpec s)) := by
  classical
  refine incidenceCylinder_of_words
    (fun ell => { entries := (order ell).entries.map (specLayerVertexEquiv s ell)
                  nodup := (order ell).nodup.map (specLayerVertexEquiv s ell).injective
                  complete := fun v => by
                    obtain ⟨g, rfl⟩ := (specLayerVertexEquiv s ell).surjective v
                    exact List.mem_map_of_mem ((order ell).complete g) })
    (fun ell => (word ell).map (specTransitionArcEquiv s ell))
    (fun ell => (hnodup ell).map (specTransitionArcEquiv s ell).injective)
    (fun ell e => ?_) (fun ell => ?_) (fun ell => ?_)
  · obtain ⟨a, rfl⟩ := (specTransitionArcEquiv s ell).surjective e
    exact List.mem_map_of_mem (hcomplete ell a)
  · exact groupedAlong_map specArcSource arcSource (specTransitionArcEquiv s ell)
      (specLayerVertexEquiv s ell) (specLayerVertexEquiv s ell).injective
      (fun _ => rfl) _ _ (hS ell)
  · exact groupedAlong_map specArcTarget arcTarget (specTransitionArcEquiv s ell)
      (specLayerVertexEquiv s (ell + 1)) (specLayerVertexEquiv s (ell + 1)).injective
      (fun _ => rfl) _ _ (hT ell)

end Incidence

end AllenderOQ3.Internal
