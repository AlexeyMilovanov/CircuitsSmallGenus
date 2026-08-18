import AllenderOQ3.Model
import AllenderOQ3.Internal.OrbitCount
import AllenderOQ3.Internal.Subcircuit
import AllenderOQ3.Internal.CountInvariance
import AllenderOQ3.Internal.DeleteEdge

set_option autoImplicit false
namespace AllenderOQ3.Internal

/-- Deleting an edge never increases the rotation genus. -/
theorem genus_deleteEdge_le {n : Nat} (c : ADRCircuit n) (u v : Fin c.gateCount) :
    orientableCircuitGenus (deleteEdge c u v) ≤ orientableCircuitGenus c := by
  by_cases h : c.edge u v = false ∨ c.edge v u = true ∨ u = v
  · exact (genus_deleteEdge_eq_of_adj_eq c u v
      (adj_deleteEdge_iff_of_degenerate c u v h)).le
  · push_neg at h
    obtain ⟨huv, hvu, hne⟩ := h
    exact genus_deleteEdge_le_of_present (by simpa using huv) (by simpa using hvu) hne

theorem dart_in_image_left {n : Nat} (c : ADRCircuit n) {m : Nat}
    (f : SubEmbedding c m)
    (h_isolated : ∀ g : Fin c.gateCount, (∀ a, f.toFun a ≠ g) →
      ∀ h, c.edge g h = false ∧ c.edge h g = false)
    (u v : Fin c.gateCount) (h_adj : UnderlyingAdj c u v) :
    ∃ a, f.toFun a = u := by
  dsimp [UnderlyingAdj] at h_adj
  by_contra h_not
  have h_is := h_isolated u (fun a h => h_not ⟨a, h⟩)
  rcases h_adj.1 with he | he
  · have hf := (h_is v).1; rw [he] at hf; contradiction
  · have hf := (h_is v).2; rw [he] at hf; contradiction

theorem dart_in_image_right {n : Nat} (c : ADRCircuit n) {m : Nat}
    (f : SubEmbedding c m)
    (h_isolated : ∀ g : Fin c.gateCount, (∀ a, f.toFun a ≠ g) →
      ∀ h, c.edge g h = false ∧ c.edge h g = false)
    (u v : Fin c.gateCount) (h_adj : UnderlyingAdj c u v) :
    ∃ b, f.toFun b = v := by
  dsimp [UnderlyingAdj] at h_adj
  by_contra h_not
  have h_is := h_isolated v (fun b h => h_not ⟨b, h⟩)
  rcases h_adj.1 with he | he
  · have hf := (h_is u).2; rw [he] at hf; contradiction
  · have hf := (h_is u).1; rw [he] at hf; contradiction

noncomputable def restrictDartEquiv {n : Nat} (c : ADRCircuit n) {m : Nat}
    (f : SubEmbedding c m) (out : Fin m)
    (h_isolated : ∀ g : Fin c.gateCount, (∀ a, f.toFun a ≠ g) →
      ∀ h, c.edge g h = false ∧ c.edge h g = false) :
    CircuitDart (restrict c f out) ≃ CircuitDart c where
  toFun d := ⟨(f.toFun d.1.1, f.toFun d.1.2), by
    have h_adj := d.2
    dsimp [UnderlyingAdj, restrict] at h_adj ⊢
    obtain ⟨h1, h2⟩ := h_adj
    exact ⟨h1, fun heq => h2 (f.inj heq)⟩⟩
  invFun d := ⟨
    (Classical.choose (dart_in_image_left c f h_isolated d.1.1 d.1.2 d.2),
     Classical.choose (dart_in_image_right c f h_isolated d.1.1 d.1.2 d.2)),
    by
      dsimp [UnderlyingAdj, restrict]
      have h_adj := d.2
      dsimp [UnderlyingAdj] at h_adj
      have ha := Classical.choose_spec (dart_in_image_left c f h_isolated d.1.1 d.1.2 d.2)
      have hb := Classical.choose_spec (dart_in_image_right c f h_isolated d.1.1 d.1.2 d.2)
      have h_or : c.edge (f.toFun (Classical.choose
        (dart_in_image_left c f h_isolated d.1.1 d.1.2 d.property)))
        (f.toFun (Classical.choose
        (dart_in_image_right c f h_isolated d.1.1 d.1.2 d.property))) = true ∨
        c.edge (f.toFun (Classical.choose
        (dart_in_image_right c f h_isolated d.1.1 d.1.2 d.property)))
        (f.toFun (Classical.choose
        (dart_in_image_left c f h_isolated d.1.1 d.1.2 d.property))) = true := by
        rw [ha, hb]
        exact h_adj.1
      have h_neq : Classical.choose
        (dart_in_image_left c f h_isolated d.1.1 d.1.2 d.property) ≠
        Classical.choose (dart_in_image_right c f h_isolated d.1.1 d.1.2 d.property) := by
        intro heq
        have h_eq2 : f.toFun (Classical.choose
          (dart_in_image_left c f h_isolated d.1.1 d.1.2 d.property)) =
          f.toFun (Classical.choose
          (dart_in_image_right c f h_isolated d.1.1 d.1.2 d.property)) := by rw [heq]
        rw [ha, hb] at h_eq2
        exact h_adj.2 h_eq2
      exact ⟨h_or, h_neq⟩⟩
  left_inv d := by
    apply Subtype.ext; apply Prod.ext <;> dsimp
    · apply f.inj
      have h_adj : UnderlyingAdj c (f.toFun d.1.1) (f.toFun d.1.2) := by
        have h := d.2
        dsimp [UnderlyingAdj, restrict] at h ⊢
        exact ⟨h.1, fun heq => h.2 (f.inj heq)⟩
      have ha := Classical.choose_spec
        (dart_in_image_left c f h_isolated (f.toFun d.1.1) (f.toFun d.1.2) h_adj)
      exact ha
    · apply f.inj
      have h_adj : UnderlyingAdj c (f.toFun d.1.1) (f.toFun d.1.2) := by
        have h := d.2
        dsimp [UnderlyingAdj, restrict] at h ⊢
        exact ⟨h.1, fun heq => h.2 (f.inj heq)⟩
      have hb := Classical.choose_spec
        (dart_in_image_right c f h_isolated (f.toFun d.1.1) (f.toFun d.1.2) h_adj)
      exact hb
  right_inv d := by
    apply Subtype.ext; apply Prod.ext <;> dsimp
    · have ha := Classical.choose_spec (dart_in_image_left c f h_isolated d.1.1 d.1.2 d.2)
      exact ha
    · have hb := Classical.choose_spec (dart_in_image_right c f h_isolated d.1.1 d.1.2 d.2)
      exact hb

@[simp]
theorem restrictDartEquiv_source {n : Nat} (c : ADRCircuit n) {m : Nat}
    (f : SubEmbedding c m) (out : Fin m)
    (h_isolated : ∀ g : Fin c.gateCount, (∀ a, f.toFun a ≠ g) →
      ∀ h, c.edge g h = false ∧ c.edge h g = false)
    (d : CircuitDart (restrict c f out)) :
    (restrictDartEquiv c f out h_isolated d).source = f.toFun d.source := rfl

noncomputable def restrictRotation {n : Nat} (c : ADRCircuit n) {m : Nat}
    (f : SubEmbedding c m) (out : Fin m)
    (h_isolated : ∀ g : Fin c.gateCount, (∀ a, f.toFun a ≠ g) →
      ∀ h, c.edge g h = false ∧ c.edge h g = false)
    (r : OrientableRotation c) : OrientableRotation (restrict c f out) where
  rotation := (restrictDartEquiv c f out h_isolated).trans
    (r.rotation.trans (restrictDartEquiv c f out h_isolated).symm)
  preservesSource := by
    intro d
    apply f.inj
    have h1 := restrictDartEquiv_source c f out h_isolated
    rw [← h1, ← h1]
    change (restrictDartEquiv c f out h_isolated ((restrictDartEquiv c f out h_isolated).symm
      (r.rotation (restrictDartEquiv c f out h_isolated d)))).source = _
    rw [Equiv.apply_symm_apply]
    exact r.preservesSource _
  cyclicAtVertex := by
    intro d e hde
    have hsrc : (restrictDartEquiv c f out h_isolated d).source =
        (restrictDartEquiv c f out h_isolated e).source := by
      rw [restrictDartEquiv_source, restrictDartEquiv_source, hde]
    obtain ⟨k, hk⟩ := r.cyclicAtVertex _ _ hsrc
    refine ⟨k, ?_⟩
    rw [pow_conj_apply, hk, Equiv.symm_apply_apply]

theorem underlyingAdj_restrict_iff {n : Nat} (c : ADRCircuit n) {m : Nat}
    (f : SubEmbedding c m) (out : Fin m) (a b : Fin m) :
    UnderlyingAdj (restrict c f out) a b ↔ UnderlyingAdj c (f.toFun a) (f.toFun b) := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun heq => h2 (f.inj heq)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun heq => h2 (by rw [heq])⟩

theorem restrictDartEquiv_source_iff {n : Nat} (c : ADRCircuit n) {m : Nat}
    (f : SubEmbedding c m) (out : Fin m)
    (h_isolated : ∀ g : Fin c.gateCount, (∀ a, f.toFun a ≠ g) →
      ∀ h, c.edge g h = false ∧ c.edge h g = false)
    (d e : CircuitDart (restrict c f out)) :
    (restrictDartEquiv c f out h_isolated d).source
        = (restrictDartEquiv c f out h_isolated e).source ↔ d.source = e.source := by
  rw [restrictDartEquiv_source, restrictDartEquiv_source]
  exact ⟨fun h => f.inj h, fun h => by rw [h]⟩

theorem restrictDartEquiv_reverse {n : Nat} (c : ADRCircuit n) {m : Nat}
    (f : SubEmbedding c m) (out : Fin m)
    (h_isolated : ∀ g : Fin c.gateCount, (∀ a, f.toFun a ≠ g) →
      ∀ h, c.edge g h = false ∧ c.edge h g = false)
    (d : CircuitDart (restrict c f out)) :
    restrictDartEquiv c f out h_isolated (dartReverse (restrict c f out) d)
      = dartReverse c (restrictDartEquiv c f out h_isolated d) := rfl

/-- The gates outside the image of a `SubEmbedding`. -/
def missingGates {n : Nat} (c : ADRCircuit n) {m : Nat} (f : SubEmbedding c m) :
    Finset (Fin c.gateCount) :=
  Finset.univ.filter (fun g => ∀ a, f.toFun a ≠ g)

theorem gateCount_eq_add_missing {n : Nat} (c : ADRCircuit n) {m : Nat}
    (f : SubEmbedding c m) : c.gateCount = m + (missingGates c f).card := by
  classical
  have h1 : missingGates c f = Finset.univ \ (Finset.univ.image f.toFun) := by
    ext g
    simp [missingGates, Finset.mem_sdiff, eq_comm]
  have h2 : (Finset.univ.image f.toFun).card = m := by
    rw [Finset.card_image_of_injective _ f.inj]
    simp
  have h4 := Finset.card_sdiff_add_card_eq_card
    (Finset.subset_univ (Finset.univ.image f.toFun))
  simp only [Finset.card_univ, Fintype.card_fin, h2] at h4
  rw [h1]
  omega

theorem underlyingEdgeCount_restrict {n : Nat} (c : ADRCircuit n) {m : Nat}
    (f : SubEmbedding c m) (out : Fin m)
    (h_isolated : ∀ g : Fin c.gateCount, (∀ a, f.toFun a ≠ g) →
      ∀ h, c.edge g h = false ∧ c.edge h g = false) :
    underlyingEdgeCount (restrict c f out) = underlyingEdgeCount c := by
  have h1 := two_mul_underlyingEdgeCount (restrict c f out)
  have h2 := two_mul_underlyingEdgeCount c
  have h3 : Fintype.card (CircuitDart (restrict c f out)) = Fintype.card (CircuitDart c) :=
    Fintype.card_congr (restrictDartEquiv c f out h_isolated)
  omega

theorem isolatedVertexCount_restrict {n : Nat} (c : ADRCircuit n) {m : Nat}
    (f : SubEmbedding c m) (out : Fin m)
    (h_isolated : ∀ g : Fin c.gateCount, (∀ a, f.toFun a ≠ g) →
      ∀ h, c.edge g h = false ∧ c.edge h g = false) :
    isolatedVertexCount c
      = isolatedVertexCount (restrict c f out) + (missingGates c f).card := by
  classical
  have hset : (Finset.univ.filter (fun u : Fin c.gateCount => ∀ v, ¬ UnderlyingAdj c u v))
      = ((Finset.univ.filter
            (fun a : Fin m => ∀ b, ¬ UnderlyingAdj (restrict c f out) a b)).image f.toFun)
        ∪ missingGates c f := by
    ext g
    simp only [missingGates, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_image]
    constructor
    · intro hg
      by_cases hex : ∃ a, f.toFun a = g
      · obtain ⟨a, rfl⟩ := hex
        refine Or.inl ⟨a, ?_, rfl⟩
        intro b hb
        exact hg (f.toFun b) ((underlyingAdj_restrict_iff c f out a b).mp hb)
      · exact Or.inr (fun a ha => hex ⟨a, ha⟩)
    · rintro (⟨a, ha, rfl⟩ | hg)
      · intro v hv
        obtain ⟨b, rfl⟩ := dart_in_image_right c f h_isolated _ v hv
        exact ha b ((underlyingAdj_restrict_iff c f out a b).mpr hv)
      · intro v hv
        rcases hv.1 with he | he
        · have := (h_isolated g hg v).1
          rw [he] at this; exact Bool.noConfusion this
        · have := (h_isolated g hg v).2
          rw [he] at this; exact Bool.noConfusion this
  have hdisj : Disjoint ((Finset.univ.filter
      (fun a : Fin m => ∀ b, ¬ UnderlyingAdj (restrict c f out) a b)).image f.toFun)
      (missingGates c f) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_image, Finset.mem_filter] at hx
    simp only [missingGates, Finset.mem_filter] at hx'
    obtain ⟨a, -, rfl⟩ := hx
    exact hx'.2 a rfl
  unfold isolatedVertexCount
  rw [hset, Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ f.inj]
  congr 1

theorem reach_of_reach_restrict {n : Nat} (c : ADRCircuit n) {m : Nat}
    (f : SubEmbedding c m) (out : Fin m) {a b : Fin m}
    (h : VertexReachable (restrict c f out) a b) :
    VertexReachable c (f.toFun a) (f.toFun b) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hyz ih => exact ih.tail ((underlyingAdj_restrict_iff c f out _ _).mp hyz)

theorem reach_restrict_of_reach {n : Nat} (c : ADRCircuit n) {m : Nat}
    (f : SubEmbedding c m) (out : Fin m)
    (h_isolated : ∀ g : Fin c.gateCount, (∀ a, f.toFun a ≠ g) →
      ∀ h, c.edge g h = false ∧ c.edge h g = false)
    {a : Fin m} {x : Fin c.gateCount} (h : VertexReachable c (f.toFun a) x) :
    ∃ b, f.toFun b = x ∧ VertexReachable (restrict c f out) a b := by
  induction h with
  | refl => exact ⟨a, rfl, Relation.ReflTransGen.refl⟩
  | tail _ hyz ih =>
      obtain ⟨b, rfl, hb⟩ := ih
      obtain ⟨b', rfl⟩ := dart_in_image_right c f h_isolated _ _ hyz
      exact ⟨b', rfl, hb.tail ((underlyingAdj_restrict_iff c f out b b').mpr hyz)⟩

/-- A gate outside the image is isolated, so it reaches only itself. -/
theorem missing_reach_eq {n : Nat} (c : ADRCircuit n) {m : Nat}
    (f : SubEmbedding c m)
    (h_isolated : ∀ g : Fin c.gateCount, (∀ a, f.toFun a ≠ g) →
      ∀ h, c.edge g h = false ∧ c.edge h g = false)
    {g x : Fin c.gateCount} (hg : ∀ a, f.toFun a ≠ g)
    (h : VertexReachable c g x) : x = g := by
  induction h with
  | refl => rfl
  | tail _ hyz ih =>
      subst ih
      rcases hyz.1 with he | he
      · rw [(h_isolated _ hg _).1] at he; exact Bool.noConfusion he
      · rw [(h_isolated _ hg _).2] at he; exact Bool.noConfusion he

theorem componentCount_restrict {n : Nat} (c : ADRCircuit n) {m : Nat}
    (f : SubEmbedding c m) (out : Fin m)
    (h_isolated : ∀ g : Fin c.gateCount, (∀ a, f.toFun a ≠ g) →
      ∀ h, c.edge g h = false ∧ c.edge h g = false) :
    componentCount c
      = componentCount (restrict c f out) + (missingGates c f).card := by
  classical
  have hmiss : (missingGates c f).card
      = Nat.card {g : Fin c.gateCount // ∀ a, f.toFun a ≠ g} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rfl
  have hll : ∀ a b : Fin m, Quot.mk (VertexReachable c) (f.toFun a)
      = Quot.mk (VertexReachable c) (f.toFun b) →
      Quot.mk (VertexReachable (restrict c f out)) a
        = Quot.mk (VertexReachable (restrict c f out)) b := by
    intro a b hab
    have hr : VertexReachable c (f.toFun a) (f.toFun b) :=
      ((vertexReachable_equiv c).eqvGen_iff).mp (Quot.eq.mp hab)
    obtain ⟨b', hb', hreach⟩ := reach_restrict_of_reach c f out h_isolated hr
    have hbb : b' = b := f.inj hb'
    subst hbb
    exact Quot.sound hreach
  have hlr : ∀ (a : Fin m) (g : Fin c.gateCount), (∀ x, f.toFun x ≠ g) →
      Quot.mk (VertexReachable c) (f.toFun a) ≠ Quot.mk (VertexReachable c) g := by
    intro a g hg heq
    have hr : VertexReachable c (f.toFun a) g :=
      ((vertexReachable_equiv c).eqvGen_iff).mp (Quot.eq.mp heq)
    have hr' : VertexReachable c g (f.toFun a) := (vertexReachable_equiv c).symm hr
    exact hg a (missing_reach_eq c f h_isolated hg hr')
  have hrr : ∀ g g' : Fin c.gateCount, (∀ x, f.toFun x ≠ g) →
      Quot.mk (VertexReachable c) g = Quot.mk (VertexReachable c) g' → g = g' := by
    intro g g' hg heq
    have hr : VertexReachable c g g' :=
      ((vertexReachable_equiv c).eqvGen_iff).mp (Quot.eq.mp heq)
    exact (missing_reach_eq c f h_isolated hg hr).symm
  set G : Quot (VertexReachable (restrict c f out)) ⊕ {g : Fin c.gateCount // ∀ a, f.toFun a ≠ g}
      → Quot (VertexReachable c) :=
    Sum.elim (Quot.lift (fun a => Quot.mk (VertexReachable c) (f.toFun a))
        (fun a b hab => Quot.sound (reach_of_reach_restrict c f out hab)))
      (fun g => Quot.mk (VertexReachable c) g.1) with hG
  have hbij : Function.Bijective G := by
    constructor
    · rintro (q | ⟨g, hg⟩) (q' | ⟨g', hg'⟩) heq
      · revert heq
        induction q using Quot.ind with
        | _ a =>
          induction q' using Quot.ind with
          | _ b =>
            intro heq
            exact congrArg Sum.inl (hll a b heq)
      · revert heq
        induction q using Quot.ind with
        | _ a =>
          intro heq
          exact absurd heq (hlr a g' hg')
      · revert heq
        induction q' using Quot.ind with
        | _ b =>
          intro heq
          exact absurd heq.symm (hlr b g hg)
      · exact congrArg Sum.inr (Subtype.ext (hrr g g' hg heq))
    · intro q
      induction q using Quot.ind with
      | _ x =>
        by_cases hex : ∃ a, f.toFun a = x
        · obtain ⟨a, rfl⟩ := hex
          exact ⟨Sum.inl (Quot.mk _ a), rfl⟩
        · exact ⟨Sum.inr ⟨x, fun a ha => hex ⟨a, ha⟩⟩, rfl⟩
  rw [componentCount_eq_natCard_quot, componentCount_eq_natCard_quot, hmiss,
    ← Nat.card_sum, Nat.card_eq_of_bijective G hbij]

/-- Deleting a vertex (by restriction) that has no incident edges does not change genus. -/
theorem genus_restrict_isolated {n : Nat} (c : ADRCircuit n) {m : Nat}
    (f : SubEmbedding c m) (out : Fin m)
    (h_isolated : ∀ g : Fin c.gateCount, (∀ a, f.toFun a ≠ g) →
      ∀ h, c.edge g h = false ∧ c.edge h g = false) :
    orientableCircuitGenus (restrict c f out) = orientableCircuitGenus c := by
  classical
  set phi := restrictDartEquiv c f out h_isolated with hphi
  have hs := restrictDartEquiv_source_iff c f out h_isolated
  have hrev := restrictDartEquiv_reverse c f out h_isolated
  have hs' : ∀ d e : CircuitDart c,
      (phi.symm d).source = (phi.symm e).source ↔ d.source = e.source := by
    intro d e
    have h := hs (phi.symm d) (phi.symm e)
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
    exact h.symm
  have hrev' : ∀ d : CircuitDart c,
      phi.symm (dartReverse c d) = dartReverse (restrict c f out) (phi.symm d) := by
    intro d
    apply phi.injective
    rw [Equiv.apply_symm_apply, hrev, Equiv.apply_symm_apply]
  have harith : ∀ F : Nat,
      (2 * componentCount (restrict c f out) + underlyingEdgeCount (restrict c f out)
          - (restrict c f out).gateCount - (F + isolatedVertexCount (restrict c f out))) / 2
        = (2 * componentCount c + underlyingEdgeCount c - c.gateCount
          - (F + isolatedVertexCount c)) / 2 := by
    intro F
    have hC := componentCount_restrict c f out h_isolated
    have hI := isolatedVertexCount_restrict c f out h_isolated
    have hE := underlyingEdgeCount_restrict c f out h_isolated
    have hV := gateCount_eq_add_missing c f
    have hg : (restrict c f out).gateCount = m := rfl
    omega
  have hfwd : ∀ r : OrientableRotation c,
      rotationGenus (restrictRotation c f out h_isolated r) = rotationGenus r := by
    intro r
    have heq : restrictRotation c f out h_isolated r = transportRotation phi hs r := rfl
    have hface : permCycleCount (facePermutation (restrictRotation c f out h_isolated r))
        = permCycleCount (facePermutation r) := by
      rw [heq]
      exact permCycleCount_facePermutation_transport phi hs hrev r
    unfold rotationGenus
    simp only [hface]
    exact harith _
  have hbwd : ∀ r' : OrientableRotation (restrict c f out),
      rotationGenus (transportRotation phi.symm hs' r') = rotationGenus r' := by
    intro r'
    have hface : permCycleCount (facePermutation (transportRotation phi.symm hs' r'))
        = permCycleCount (facePermutation r') :=
      permCycleCount_facePermutation_transport phi.symm hs' hrev' r'
    unfold rotationGenus
    simp only [hface]
    exact (harith _).symm
  unfold orientableCircuitGenus
  congr 1
  ext g
  constructor
  · rintro ⟨r', hr'⟩
    exact ⟨transportRotation phi.symm hs' r', by rw [hbwd]; exact hr'⟩
  · rintro ⟨r, hr⟩
    exact ⟨restrictRotation c f out h_isolated r, by rw [hfwd]; exact hr⟩

end AllenderOQ3.Internal
