import AllenderOQ3.Internal.MinRep
import AllenderOQ3.Internal.Subcircuit

/-!
# Counting invariants under restriction to a predecessor-closed subfamily

When every gate outside the image of a `SubEmbedding` is isolated (has no
incident edge at all), restricting the circuit removes exactly
`c.gateCount - m` isolated singleton components.  This file records the
resulting vertex, component and edge counts.
-/

set_option autoImplicit false

namespace AllenderOQ3.Internal

/-- Adjacency in a restricted circuit is adjacency of the images. -/
theorem adj_restrict_iff {n : Nat} (c : ADRCircuit n) {m : Nat}
    (f : SubEmbedding c m) (out : Fin m) (a b : Fin m) :
    UnderlyingAdj (restrict c f out) a b ↔ UnderlyingAdj c (f.toFun a) (f.toFun b) := by
  unfold UnderlyingAdj
  simp only [restrict_edge]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun heq => h2 (f.inj heq)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun heq => h2 (by rw [heq])⟩

/-- A gate outside the image of an isolating `SubEmbedding` is adjacent to nothing. -/
theorem not_adj_of_not_mem_image {n : Nat} (c : ADRCircuit n) {m : Nat}
    (f : SubEmbedding c m)
    (h_isolated : ∀ g : Fin c.gateCount, (∀ a, f.toFun a ≠ g) →
      ∀ h, c.edge g h = false ∧ c.edge h g = false)
    (u : Fin c.gateCount) (hu : ∀ a, f.toFun a ≠ u) (v : Fin c.gateCount) :
    ¬ UnderlyingAdj c u v := by
  intro hadj
  have h := h_isolated u hu v
  rcases hadj.1 with he | he
  · rw [(h).1] at he; exact Bool.noConfusion he
  · rw [(h).2] at he; exact Bool.noConfusion he

/-- The source of a dart lies in the image of an isolating `SubEmbedding`. -/
theorem dart_in_image_left {n : Nat} (c : ADRCircuit n) {m : Nat}
    (f : SubEmbedding c m)
    (h_isolated : ∀ g : Fin c.gateCount, (∀ a, f.toFun a ≠ g) →
      ∀ h, c.edge g h = false ∧ c.edge h g = false)
    (u v : Fin c.gateCount) (h_adj : UnderlyingAdj c u v) :
    ∃ a, f.toFun a = u := by
  by_contra h_not
  exact not_adj_of_not_mem_image c f h_isolated u (fun a ha => h_not ⟨a, ha⟩) v h_adj

/-- The target of a dart lies in the image of an isolating `SubEmbedding`. -/
theorem dart_in_image_right {n : Nat} (c : ADRCircuit n) {m : Nat}
    (f : SubEmbedding c m)
    (h_isolated : ∀ g : Fin c.gateCount, (∀ a, f.toFun a ≠ g) →
      ∀ h, c.edge g h = false ∧ c.edge h g = false)
    (u v : Fin c.gateCount) (h_adj : UnderlyingAdj c u v) :
    ∃ b, f.toFun b = v := by
  by_contra h_not
  exact not_adj_of_not_mem_image c f h_isolated v (fun b hb => h_not ⟨b, hb⟩) u
    ⟨h_adj.1.elim Or.inr Or.inl, Ne.symm h_adj.2⟩

/-- Reachability from an isolated gate is trivial. -/
theorem reach_eq_of_isolated {n : Nat} (c : ADRCircuit n) (u : Fin c.gateCount)
    (hu : ∀ v, ¬ UnderlyingAdj c u v) (v : Fin c.gateCount)
    (h : VertexReachable c u v) : u = v := by
  rcases Relation.ReflTransGen.cases_head h with h1 | ⟨y, hy, _⟩
  · exact h1
  · exact absurd hy (hu y)

/-- Reachability in the restricted circuit implies reachability of the images. -/
theorem reach_restrict_image {n : Nat} (c : ADRCircuit n) {m : Nat}
    (f : SubEmbedding c m) (out : Fin m) {a b : Fin m}
    (h : VertexReachable (restrict c f out) a b) :
    VertexReachable c (f.toFun a) (f.toFun b) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail h1 h2 ih =>
      exact ih.tail ((adj_restrict_iff c f out _ _).mp h2)

/-- Reachability in `c` starting from a gate in the image stays in the image and
lifts to the restricted circuit. -/
theorem reach_lift_of_isolated {n : Nat} (c : ADRCircuit n) {m : Nat}
    (f : SubEmbedding c m) (out : Fin m)
    (h_isolated : ∀ g : Fin c.gateCount, (∀ a, f.toFun a ≠ g) →
      ∀ h, c.edge g h = false ∧ c.edge h g = false)
    {u v : Fin c.gateCount} (h : VertexReachable c u v) (a : Fin m) (ha : f.toFun a = u) :
    ∃ b, f.toFun b = v ∧ VertexReachable (restrict c f out) a b := by
  induction h with
  | refl => exact ⟨a, ha, Relation.ReflTransGen.refl⟩
  | @tail y z _h1 h2 ih =>
      obtain ⟨b, hb, hab⟩ := ih
      obtain ⟨d, hd⟩ := dart_in_image_right c f h_isolated y z h2
      refine ⟨d, hd, hab.tail ?_⟩
      refine (adj_restrict_iff c f out b d).mpr ?_
      rw [hb, hd]
      exact h2

/-- Split a cardinality along the image of an injection, when everything outside
the image satisfies the predicate. -/
theorem card_filter_split_image {N m : Nat} (g : Fin m → Fin N)
    (hg : Function.Injective g) (P : Fin N → Prop)
    (hP : ∀ u, (∀ a, g a ≠ u) → P u) [DecidablePred P]
    [DecidablePred (fun u => (∃ a, g a = u) ∧ P u)] :
    (Finset.univ.filter P).card
      = (Finset.univ.filter (fun u => (∃ a, g a = u) ∧ P u)).card + (N - m) := by
  classical
  have hsplit : Finset.univ.filter P
      = (Finset.univ.filter (fun u => (∃ a, g a = u) ∧ P u))
        ∪ (Finset.univ.filter (fun u => ¬ ∃ a, g a = u)) := by
    ext u
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      by_cases hi : ∃ a, g a = u
      · exact Or.inl ⟨hi, h⟩
      · exact Or.inr hi
    · rintro (⟨_, h⟩ | h)
      · exact h
      · exact hP u (fun a ha => h ⟨a, ha⟩)
  have hdisj : Disjoint (Finset.univ.filter (fun u => (∃ a, g a = u) ∧ P u))
      (Finset.univ.filter (fun u => ¬ ∃ a, g a = u)) := by
    rw [Finset.disjoint_left]
    intro u hu hu'
    exact (Finset.mem_filter.mp hu').2 (Finset.mem_filter.mp hu).2.1
  rw [hsplit, Finset.card_union_of_disjoint hdisj]
  congr 1
  have himg : Finset.univ.filter (fun u => ¬ ∃ a, g a = u)
      = (Finset.univ.image g)ᶜ := by
    ext u
    simp
  rw [himg, Finset.card_compl, Finset.card_image_of_injective _ hg]
  simp

/-- Restricting away isolated gates removes exactly the discarded gates from the
isolated-vertex count. -/
theorem isolatedVertexCount_restrict_dup {n : Nat} (c : ADRCircuit n) {m : Nat}
    (f : SubEmbedding c m) (out : Fin m)
    (h_isolated : ∀ g : Fin c.gateCount, (∀ a, f.toFun a ≠ g) →
      ∀ h, c.edge g h = false ∧ c.edge h g = false) :
    isolatedVertexCount c
      = isolatedVertexCount (restrict c f out) + (c.gateCount - m) := by
  classical
  unfold isolatedVertexCount
  rw [card_filter_split_image f.toFun f.inj (fun u => ∀ v, ¬ UnderlyingAdj c u v)
    (fun u hu v => not_adj_of_not_mem_image c f h_isolated u hu v)]
  congr 1
  have himg : (Finset.univ.filter
      (fun u => (∃ a, f.toFun a = u) ∧ ∀ v, ¬ UnderlyingAdj c u v))
      = (Finset.univ.filter
        (fun a : Fin m => ∀ b, ¬ UnderlyingAdj (restrict c f out) a b)).image f.toFun := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨⟨a, rfl⟩, hiso⟩
      refine ⟨a, ?_, rfl⟩
      intro b hb
      exact hiso _ ((adj_restrict_iff c f out a b).mp hb)
    · rintro ⟨a, ha, rfl⟩
      refine ⟨⟨a, rfl⟩, ?_⟩
      intro v hv
      obtain ⟨b, hb⟩ := dart_in_image_right c f h_isolated _ v hv
      refine ha b ((adj_restrict_iff c f out a b).mpr ?_)
      rw [hb]
      exact hv
  rw [himg, Finset.card_image_of_injective _ f.inj]
  congr 1

/-- Restricting away isolated gates removes exactly the discarded gates from the
component count. -/
theorem componentCount_restrict {n : Nat} (c : ADRCircuit n) {m : Nat}
    (f : SubEmbedding c m) (out : Fin m)
    (h_isolated : ∀ g : Fin c.gateCount, (∀ a, f.toFun a ≠ g) →
      ∀ h, c.edge g h = false ∧ c.edge h g = false) :
    componentCount c = componentCount (restrict c f out) + (c.gateCount - m) := by
  classical
  unfold componentCount
  rw [card_filter_split_image f.toFun f.inj
    (fun u => ∀ v, VertexReachable c u v → u.val ≤ v.val) ?_]
  · congr 1
    refine (minRepSet_card_congr_inj (vertexReachable_equiv (restrict c f out))
      (vertexReachable_equiv c) (fun a : Fin m => a.val)
      (fun u : Fin c.gateCount => u.val) (fun x y h => Fin.ext h) (fun x y h => Fin.ext h)
      f.toFun ?_ ?_).symm
    · intro a b
      constructor
      · intro h; exact reach_restrict_image c f out h
      · intro h
        obtain ⟨b', hb', hab⟩ := reach_lift_of_isolated c f out h_isolated h a rfl
        have : b' = b := f.inj hb'
        rwa [this] at hab
    · intro a v h
      obtain ⟨b, hb, _⟩ := reach_lift_of_isolated c f out h_isolated h a rfl
      exact ⟨b, hb⟩
  · intro u hu v hv
    have := reach_eq_of_isolated c u
      (fun v => not_adj_of_not_mem_image c f h_isolated u hu v) v hv
    rw [this]

/-- Two filters with pointwise equivalent predicates have the same cardinality.
The decidability instances are explicit arguments so that the lemma applies to
filters coming from classical definitions. -/
theorem card_filter_congr_pred {N : Nat} (P Q : Fin N → Prop) (instP : DecidablePred P)
    (instQ : DecidablePred Q) (h : ∀ x, P x ↔ Q x) :
    (@Finset.filter _ P instP Finset.univ).card
      = (@Finset.filter _ Q instQ Finset.univ).card :=
  Finset.card_bij (fun x _ => x)
    (fun a ha => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (h a).mp (Finset.mem_filter.mp ha).2⟩)
    (fun _ _ _ _ hab => hab)
    (fun b hb => ⟨b, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (h b).mpr (Finset.mem_filter.mp hb).2⟩, rfl⟩)

/-- Adjacency in the underlying graph is symmetric. -/
theorem underlyingAdj_symm {n : Nat} (c : ADRCircuit n) (u v : Fin c.gateCount) :
    UnderlyingAdj c u v ↔ UnderlyingAdj c v u := by
  unfold UnderlyingAdj
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1.elim Or.inr Or.inl, Ne.symm h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1.elim Or.inr Or.inl, Ne.symm h2⟩

/-- The number of darts is twice the number of undirected edges. -/
theorem twice_underlyingEdgeCount {n : Nat} (c : ADRCircuit n) :
    2 * underlyingEdgeCount c = Fintype.card (CircuitDart c) := by
  classical
  have hdart : Fintype.card (CircuitDart c)
      = ∑ u : Fin c.gateCount, ∑ v : Fin c.gateCount,
          (if UnderlyingAdj c u v then 1 else 0) := by
    rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type]
  have hE : underlyingEdgeCount c
      = ∑ u : Fin c.gateCount, ∑ v : Fin c.gateCount,
          (if u.val < v.val ∧ UnderlyingAdj c u v then 1 else 0) := by
    unfold underlyingEdgeCount
    simp only [Finset.card_filter]
  have hswap : ∑ u : Fin c.gateCount, ∑ v : Fin c.gateCount,
        (if v.val < u.val ∧ UnderlyingAdj c u v then 1 else 0)
      = ∑ u : Fin c.gateCount, ∑ v : Fin c.gateCount,
        (if u.val < v.val ∧ UnderlyingAdj c u v then 1 else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun v _ => ?_))
    exact if_congr (and_congr_right (fun _ => underlyingAdj_symm c v u)) rfl rfl
  have hkey : ∀ u v : Fin c.gateCount,
      (if UnderlyingAdj c u v then 1 else 0)
        = (if u.val < v.val ∧ UnderlyingAdj c u v then (1 : Nat) else 0)
          + (if v.val < u.val ∧ UnderlyingAdj c u v then 1 else 0) := by
    intro u v
    by_cases h : UnderlyingAdj c u v
    · have hne : u.val ≠ v.val := fun hh => h.2 (Fin.ext hh)
      rcases Nat.lt_or_ge u.val v.val with hlt | hge
      · rw [if_pos h, if_pos ⟨hlt, h⟩,
          if_neg (fun hc => absurd hc.1 (by omega))]
      · have hlt : v.val < u.val := by omega
        rw [if_pos h, if_neg (fun hc => absurd hc.1 (by omega)),
          if_pos ⟨hlt, h⟩]
    · rw [if_neg h, if_neg (fun hc => h hc.2), if_neg (fun hc => h hc.2)]
  have hsum : ∑ u : Fin c.gateCount, ∑ v : Fin c.gateCount,
        (if UnderlyingAdj c u v then 1 else 0)
      = (∑ u : Fin c.gateCount, ∑ v : Fin c.gateCount,
          (if u.val < v.val ∧ UnderlyingAdj c u v then 1 else 0))
        + (∑ u : Fin c.gateCount, ∑ v : Fin c.gateCount,
          (if v.val < u.val ∧ UnderlyingAdj c u v then 1 else 0)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun v _ => hkey u v)
  rw [hdart, hsum, hswap, hE, two_mul]

end AllenderOQ3.Internal
