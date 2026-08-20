import AllenderOQ3.Internal.Surgery

/-!
# Masking edges and additivity of the genus over separated blocks

This file provides the combinatorial core of the §3 genus packing statement.

* `maskCircuit c keep` keeps only the edges selected by `keep`; since it is an
  iterated `deleteEdge`, it never increases the rotation genus
  (`genus_maskCircuit_le`).
* If no edge of `c` joins a vertex set `A` to its complement (`SeparatedBy c A`),
  the circuit splits into the two blocks `blockIn c A` (only the edges inside
  `A`) and `blockOut c A` (only the edges outside `A`).  All four ingredients of
  the genus formula are additive over such a split: edges, isolated vertices,
  components, and — for a fixed rotation system — faces.
* Consequently, `r` pairwise disjoint vertex sets whose induced subgraphs are all
  non-rotation-planar force the genus to be at least `r`
  (`length_le_genus_of_blocks`).

Everything here is elementary bookkeeping on top of the surgery machinery of
`AllenderOQ3.Internal.Surgery`; no external assumption is used.
-/

set_option autoImplicit false

namespace AllenderOQ3.Internal

variable {n : Nat}

/-! ## Two elementary helpers -/

/-- Two filters with pointwise equivalent predicates have the same cardinality.
The decidability instances are explicit arguments so that the lemma applies to
filters coming from classical definitions. -/
theorem card_filter_congr_of_iff {N : Nat} (P Q : Fin N → Prop) (instP : DecidablePred P)
    (instQ : DecidablePred Q) (h : ∀ x, P x ↔ Q x) :
    (@Finset.filter _ P instP Finset.univ).card
      = (@Finset.filter _ Q instQ Finset.univ).card :=
  Finset.card_bij (fun x _ => x)
    (fun a ha => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (h a).mp (Finset.mem_filter.mp ha).2⟩)
    (fun _ _ _ _ hab => hab)
    (fun b hb => ⟨b, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (h b).mpr (Finset.mem_filter.mp hb).2⟩, rfl⟩)

/-- Adjacency in the underlying graph is symmetric. -/
theorem underlyingAdj_comm {c : ADRCircuit n} (u v : Fin c.gateCount) :
    UnderlyingAdj c u v ↔ UnderlyingAdj c v u := by
  unfold UnderlyingAdj
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1.elim Or.inr Or.inl, Ne.symm h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1.elim Or.inr Or.inl, Ne.symm h2⟩

/-! ## Masking a set of edges -/

/-- Keep only the edges selected by `keep`. -/
def maskCircuit (c : ADRCircuit n) (keep : Fin c.gateCount → Fin c.gateCount → Bool) :
    ADRCircuit n :=
  { c with edge := fun a b => if keep a b then c.edge a b else false }

@[simp] theorem maskCircuit_gateCount (c : ADRCircuit n)
    (keep : Fin c.gateCount → Fin c.gateCount → Bool) :
    (maskCircuit c keep).gateCount = c.gateCount := rfl

@[simp] theorem maskCircuit_output (c : ADRCircuit n)
    (keep : Fin c.gateCount → Fin c.gateCount → Bool) :
    (maskCircuit c keep).output = c.output := rfl

@[simp] theorem maskCircuit_kind (c : ADRCircuit n)
    (keep : Fin c.gateCount → Fin c.gateCount → Bool) (g : Fin c.gateCount) :
    (maskCircuit c keep).kind g = c.kind g := rfl

@[simp] theorem maskCircuit_layer (c : ADRCircuit n)
    (keep : Fin c.gateCount → Fin c.gateCount → Bool) (g : Fin c.gateCount) :
    (maskCircuit c keep).layer g = c.layer g := rfl

@[simp] theorem maskCircuit_edge (c : ADRCircuit n)
    (keep : Fin c.gateCount → Fin c.gateCount → Bool) (a b : Fin c.gateCount) :
    (maskCircuit c keep).edge a b = if keep a b then c.edge a b else false := rfl

/-- Two masks that agree pointwise give the same circuit. -/
theorem maskCircuit_congr (c : ADRCircuit n)
    (k₁ k₂ : Fin c.gateCount → Fin c.gateCount → Bool) (h : ∀ a b, k₁ a b = k₂ a b) :
    maskCircuit c k₁ = maskCircuit c k₂ := by
  unfold maskCircuit
  congr 1
  funext a b
  rw [h a b]

/-- Masking with a mask that keeps everything changes nothing. -/
theorem maskCircuit_eq_self (c : ADRCircuit n)
    (keep : Fin c.gateCount → Fin c.gateCount → Bool) (h : ∀ a b, keep a b = true) :
    maskCircuit c keep = c := by
  unfold maskCircuit
  have : (fun a b => if keep a b then c.edge a b else false) = c.edge := by
    funext a b
    rw [h a b, if_pos rfl]
  rw [this]

/-- Turning one further mask entry off is deleting one edge. -/
theorem maskCircuit_update (c : ADRCircuit n)
    (keep : Fin c.gateCount → Fin c.gateCount → Bool) (u v : Fin c.gateCount) :
    maskCircuit c (fun a b => keep a b && !(decide (a = u ∧ b = v)))
      = deleteEdge (maskCircuit c keep) u v := by
  unfold maskCircuit deleteEdge
  congr 1
  funext a b
  by_cases h : a = u ∧ b = v
  · simp [h]
  · simp [h]

/-- Masking never increases the rotation genus: it is an iterated edge deletion. -/
theorem genus_maskCircuit_le (c : ADRCircuit n)
    (keep : Fin c.gateCount → Fin c.gateCount → Bool) :
    orientableCircuitGenus (maskCircuit c keep) ≤ orientableCircuitGenus c := by
  classical
  suffices H : ∀ (m : Nat) (k : Fin c.gateCount → Fin c.gateCount → Bool),
      (Finset.univ.filter
        (fun p : Fin c.gateCount × Fin c.gateCount => k p.1 p.2 = false)).card ≤ m →
      orientableCircuitGenus (maskCircuit c k) ≤ orientableCircuitGenus c by
    exact H _ keep le_rfl
  intro m
  induction m with
  | zero =>
      intro k hk
      have hall : ∀ a b, k a b = true := by
        intro a b
        by_contra hab
        have hmem : ((a, b) : Fin c.gateCount × Fin c.gateCount) ∈
            Finset.univ.filter (fun p : Fin c.gateCount × Fin c.gateCount => k p.1 p.2 = false) :=
              by
          have hab' : k a b = false := by simpa using hab
          simp [hab']
        have := Finset.card_pos.mpr ⟨_, hmem⟩
        omega
      rw [maskCircuit_eq_self c k hall]
  | succ m ih =>
      intro k hk
      by_cases hall : ∀ a b, k a b = true
      · rw [maskCircuit_eq_self c k hall]
      · push_neg at hall
        obtain ⟨u, v, huv⟩ := hall
        have huv' : k u v = false := by simpa using huv
        set k' : Fin c.gateCount → Fin c.gateCount → Bool :=
          fun a b => k a b || decide (a = u ∧ b = v) with hk'def
        have hssub : (Finset.univ.filter
              (fun p : Fin c.gateCount × Fin c.gateCount => k' p.1 p.2 = false)) ⊂
            (Finset.univ.filter
              (fun p : Fin c.gateCount × Fin c.gateCount => k p.1 p.2 = false)) := by
          constructor
          · intro p hp
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, hk'def,
              Bool.or_eq_false_iff] at hp ⊢
            exact hp.1
          · intro hcon
            have hmem : ((u, v) : Fin c.gateCount × Fin c.gateCount) ∈
                Finset.univ.filter
                  (fun p : Fin c.gateCount × Fin c.gateCount => k p.1 p.2 = false) := by
              simp [huv']
            have hmem' := hcon hmem
            simp [hk'def] at hmem'
        have hcard : (Finset.univ.filter
            (fun p : Fin c.gateCount × Fin c.gateCount => k' p.1 p.2 = false)).card ≤ m := by
          have := Finset.card_lt_card hssub
          omega
        have heq : maskCircuit c k = deleteEdge (maskCircuit c k') u v := by
          rw [← maskCircuit_update c k' u v]
          refine maskCircuit_congr c k _ (fun a b => ?_)
          by_cases h : a = u ∧ b = v
          · obtain ⟨rfl, rfl⟩ := h
            simp [hk'def, huv']
          · simp [hk'def, h]
        rw [heq]
        exact le_trans (genus_deleteEdge_le (maskCircuit c k') u v) (ih k' hcard)

/-! ## Separated blocks -/

/-- No edge of `c` joins `A` to its complement. -/
def SeparatedBy (c : ADRCircuit n) (A : Finset (Fin c.gateCount)) : Prop :=
  ∀ a b, c.edge a b = true → (a ∈ A ↔ b ∈ A)

/-- The block of `c` spanned by the edges inside `A`. -/
def blockIn (c : ADRCircuit n) (A : Finset (Fin c.gateCount)) : ADRCircuit n :=
  maskCircuit c (fun a b => decide (a ∈ A) && decide (b ∈ A))

/-- The block of `c` spanned by the edges outside `A`. -/
def blockOut (c : ADRCircuit n) (A : Finset (Fin c.gateCount)) : ADRCircuit n :=
  maskCircuit c (fun a b => !decide (a ∈ A) && !decide (b ∈ A))

@[simp] theorem blockIn_gateCount (c : ADRCircuit n) (A : Finset (Fin c.gateCount)) :
    (blockIn c A).gateCount = c.gateCount := rfl

@[simp] theorem blockOut_gateCount (c : ADRCircuit n) (A : Finset (Fin c.gateCount)) :
    (blockOut c A).gateCount = c.gateCount := rfl

@[simp] theorem blockIn_edge (c : ADRCircuit n) (A : Finset (Fin c.gateCount))
    (a b : Fin c.gateCount) :
    (blockIn c A).edge a b = if a ∈ A ∧ b ∈ A then c.edge a b else false := by
  by_cases h : a ∈ A ∧ b ∈ A
  · simp [blockIn, maskCircuit, h.1, h.2]
  · rw [if_neg h]
    have : ¬ (a ∈ A ∧ b ∈ A) := h
    simp only [blockIn, maskCircuit_edge, Bool.and_eq_true, decide_eq_true_eq]
    rw [if_neg this]

@[simp] theorem blockOut_edge (c : ADRCircuit n) (A : Finset (Fin c.gateCount))
    (a b : Fin c.gateCount) :
    (blockOut c A).edge a b = if a ∉ A ∧ b ∉ A then c.edge a b else false := by
  by_cases h : a ∉ A ∧ b ∉ A
  · simp [blockOut, maskCircuit, h.1, h.2]
  · rw [if_neg h]
    simp only [blockOut, maskCircuit_edge, Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not]
    rw [if_neg h]

/-- An edge of the first block is an edge of `c` inside `A`. -/
theorem blockIn_edge_true {c : ADRCircuit n} {A : Finset (Fin c.gateCount)}
    {a b : Fin c.gateCount} (h : (blockIn c A).edge a b = true) :
    c.edge a b = true ∧ a ∈ A ∧ b ∈ A := by
  by_cases hc : a ∈ A ∧ b ∈ A
  · rw [blockIn_edge, if_pos hc] at h
    exact ⟨h, hc.1, hc.2⟩
  · rw [blockIn_edge, if_neg hc] at h
    exact absurd h (by simp)

/-- An edge of the second block is an edge of `c` outside `A`. -/
theorem blockOut_edge_true {c : ADRCircuit n} {A : Finset (Fin c.gateCount)}
    {a b : Fin c.gateCount} (h : (blockOut c A).edge a b = true) :
    c.edge a b = true ∧ a ∉ A ∧ b ∉ A := by
  by_cases hc : a ∉ A ∧ b ∉ A
  · rw [blockOut_edge, if_pos hc] at h
    exact ⟨h, hc.1, hc.2⟩
  · rw [blockOut_edge, if_neg hc] at h
    exact absurd h (by simp)

/-- Adjacency inside the first block. -/
theorem underlyingAdj_blockIn {c : ADRCircuit n} {A : Finset (Fin c.gateCount)}
    (hsep : SeparatedBy c A) (u v : Fin c.gateCount) :
    UnderlyingAdj (blockIn c A) u v ↔ (UnderlyingAdj c u v ∧ u ∈ A) := by
  constructor
  · rintro ⟨h1, hne⟩
    rcases h1 with h | h
    · obtain ⟨he, ha, _⟩ := blockIn_edge_true h
      exact ⟨⟨Or.inl he, hne⟩, ha⟩
    · obtain ⟨he, _, ha⟩ := blockIn_edge_true h
      exact ⟨⟨Or.inr he, hne⟩, ha⟩
  · rintro ⟨⟨h1, hne⟩, hu⟩
    refine ⟨?_, hne⟩
    rcases h1 with h | h
    · have hv : v ∈ A := (hsep u v h).mp hu
      exact Or.inl (by rw [blockIn_edge, if_pos ⟨hu, hv⟩]; exact h)
    · have hv : v ∈ A := (hsep v u h).mpr hu
      exact Or.inr (by rw [blockIn_edge, if_pos ⟨hv, hu⟩]; exact h)

/-- Adjacency inside the second block. -/
theorem underlyingAdj_blockOut {c : ADRCircuit n} {A : Finset (Fin c.gateCount)}
    (hsep : SeparatedBy c A) (u v : Fin c.gateCount) :
    UnderlyingAdj (blockOut c A) u v ↔ (UnderlyingAdj c u v ∧ u ∉ A) := by
  constructor
  · rintro ⟨h1, hne⟩
    rcases h1 with h | h
    · obtain ⟨he, ha, _⟩ := blockOut_edge_true h
      exact ⟨⟨Or.inl he, hne⟩, ha⟩
    · obtain ⟨he, _, ha⟩ := blockOut_edge_true h
      exact ⟨⟨Or.inr he, hne⟩, ha⟩
  · rintro ⟨⟨h1, hne⟩, hu⟩
    refine ⟨?_, hne⟩
    rcases h1 with h | h
    · have hv : v ∉ A := fun hv => hu ((hsep u v h).mpr hv)
      exact Or.inl (by rw [blockOut_edge, if_pos ⟨hu, hv⟩]; exact h)
    · have hv : v ∉ A := fun hv => hu ((hsep v u h).mp hv)
      exact Or.inr (by rw [blockOut_edge, if_pos ⟨hv, hu⟩]; exact h)

/-! ## The darts of the two blocks -/

/-- The darts of the first block are the darts of `c` whose source lies in `A`. -/
def blockDartIn {c : ADRCircuit n} {A : Finset (Fin c.gateCount)} (hsep : SeparatedBy c A) :
    CircuitDart (blockIn c A) ≃ {d : CircuitDart c // d.source ∈ A} where
  toFun d := ⟨⟨d.1, ((underlyingAdj_blockIn hsep d.1.1 d.1.2).mp d.2).1⟩,
    ((underlyingAdj_blockIn hsep d.1.1 d.1.2).mp d.2).2⟩
  invFun d := ⟨d.1.1, (underlyingAdj_blockIn hsep d.1.1.1 d.1.1.2).mpr ⟨d.1.2, d.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The darts of the second block are the darts of `c` whose source lies outside `A`. -/
def blockDartOut {c : ADRCircuit n} {A : Finset (Fin c.gateCount)} (hsep : SeparatedBy c A) :
    CircuitDart (blockOut c A) ≃ {d : CircuitDart c // ¬ (d.source ∈ A)} where
  toFun d := ⟨⟨d.1, ((underlyingAdj_blockOut hsep d.1.1 d.1.2).mp d.2).1⟩,
    ((underlyingAdj_blockOut hsep d.1.1 d.1.2).mp d.2).2⟩
  invFun d := ⟨d.1.1, (underlyingAdj_blockOut hsep d.1.1.1 d.1.1.2).mpr ⟨d.1.2, d.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The darts split between the two blocks. -/
theorem card_dart_block {c : ADRCircuit n} {A : Finset (Fin c.gateCount)}
    (hsep : SeparatedBy c A) :
    Fintype.card (CircuitDart (blockIn c A)) + Fintype.card (CircuitDart (blockOut c A))
      = Fintype.card (CircuitDart c) := by
  classical
  rw [Fintype.card_congr (blockDartIn hsep), Fintype.card_congr (blockDartOut hsep),
    ← Fintype.card_sum,
    Fintype.card_congr (Equiv.sumCompl (fun d : CircuitDart c => d.source ∈ A))]

/-! ## Additivity of the four counts -/

/-- The edges split between the two blocks. -/
theorem underlyingEdgeCount_block {c : ADRCircuit n} {A : Finset (Fin c.gateCount)}
    (hsep : SeparatedBy c A) :
    underlyingEdgeCount (blockIn c A) + underlyingEdgeCount (blockOut c A)
      = underlyingEdgeCount c := by
  have h1 := two_mul_underlyingEdgeCount (blockIn c A)
  have h2 := two_mul_underlyingEdgeCount (blockOut c A)
  have h3 := two_mul_underlyingEdgeCount c
  have h4 := card_dart_block hsep
  omega

/-- Splitting a count along a set: the two "one side or the property" filters. -/
theorem card_filter_side_pair {N : Nat} (R : Fin N → Prop) [DecidablePred R]
    (A : Finset (Fin N)) :
    (Finset.univ.filter (fun u => u ∉ A ∨ R u)).card
        + (Finset.univ.filter (fun u => u ∈ A ∨ R u)).card
      = (Finset.univ.filter R).card + N := by
  classical
  have hkey := Finset.card_union_add_card_inter
    (Finset.univ.filter (fun u : Fin N => u ∉ A ∨ R u))
    (Finset.univ.filter (fun u : Fin N => u ∈ A ∨ R u))
  have hunion : (Finset.univ.filter (fun u : Fin N => u ∉ A ∨ R u))
      ∪ (Finset.univ.filter (fun u : Fin N => u ∈ A ∨ R u)) = Finset.univ := by
    ext u
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    by_cases hu : u ∈ A
    · exact Or.inr (Or.inl hu)
    · exact Or.inl (Or.inl hu)
  have hinter : (Finset.univ.filter (fun u : Fin N => u ∉ A ∨ R u))
      ∩ (Finset.univ.filter (fun u : Fin N => u ∈ A ∨ R u)) = Finset.univ.filter R := by
    ext u
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1 | h1, h2 | h2⟩
      · exact absurd h2 h1
      · exact h2
      · exact h1
      · exact h1
    · intro h
      exact ⟨Or.inr h, Or.inr h⟩
  rw [hunion, hinter, Finset.card_univ, Fintype.card_fin] at hkey
  omega

/-- Each block turns the vertices of the other block into isolated vertices. -/
theorem isolatedVertexCount_block {c : ADRCircuit n} {A : Finset (Fin c.gateCount)}
    (hsep : SeparatedBy c A) :
    isolatedVertexCount (blockIn c A) + isolatedVertexCount (blockOut c A)
      = isolatedVertexCount c + c.gateCount := by
  classical
  have hIn : isolatedVertexCount (blockIn c A)
      = (Finset.univ.filter
          (fun u : Fin c.gateCount => u ∉ A ∨ ∀ v, ¬ UnderlyingAdj c u v)).card := by
    unfold isolatedVertexCount
    refine card_filter_congr_of_iff (N := c.gateCount) _ _ _ _ (fun u => ?_)
    constructor
    · intro h
      by_cases hu : u ∈ A
      · exact Or.inr (fun v hv => h v ((underlyingAdj_blockIn hsep u v).mpr ⟨hv, hu⟩))
      · exact Or.inl hu
    · rintro (hu | h) v hv
      · exact hu ((underlyingAdj_blockIn hsep u v).mp hv).2
      · exact h v ((underlyingAdj_blockIn hsep u v).mp hv).1
  have hOut : isolatedVertexCount (blockOut c A)
      = (Finset.univ.filter
          (fun u : Fin c.gateCount => u ∈ A ∨ ∀ v, ¬ UnderlyingAdj c u v)).card := by
    unfold isolatedVertexCount
    refine card_filter_congr_of_iff (N := c.gateCount) _ _ _ _ (fun u => ?_)
    constructor
    · intro h
      by_cases hu : u ∈ A
      · exact Or.inl hu
      · exact Or.inr (fun v hv => h v ((underlyingAdj_blockOut hsep u v).mpr ⟨hv, hu⟩))
    · rintro (hu | h) v hv
      · exact ((underlyingAdj_blockOut hsep u v).mp hv).2 hu
      · exact h v ((underlyingAdj_blockOut hsep u v).mp hv).1
  have hc : isolatedVertexCount c
      = (Finset.univ.filter (fun u : Fin c.gateCount => ∀ v, ¬ UnderlyingAdj c u v)).card := by
    unfold isolatedVertexCount
    exact card_filter_congr_of_iff (N := c.gateCount) _ _ _ _ (fun _ => Iff.rfl)
  rw [hIn, hOut, hc]
  exact card_filter_side_pair (fun u : Fin c.gateCount => ∀ v, ¬ UnderlyingAdj c u v) A

/-! ## Reachability inside a block -/

/-- Reachability in the first block implies reachability in `c`. -/
theorem reach_of_reach_blockIn {c : ADRCircuit n} {A : Finset (Fin c.gateCount)}
    (hsep : SeparatedBy c A) {u v : Fin c.gateCount}
    (h : VertexReachable (blockIn c A) u v) : VertexReachable c u v := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hadj ih => exact ih.tail ((underlyingAdj_blockIn hsep _ _).mp hadj).1

/-- Reachability in the second block implies reachability in `c`. -/
theorem reach_of_reach_blockOut {c : ADRCircuit n} {A : Finset (Fin c.gateCount)}
    (hsep : SeparatedBy c A) {u v : Fin c.gateCount}
    (h : VertexReachable (blockOut c A) u v) : VertexReachable c u v := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hadj ih => exact ih.tail ((underlyingAdj_blockOut hsep _ _).mp hadj).1

/-- Starting inside `A`, reachability in `c` stays inside `A` and is realised in the
first block. -/
theorem reach_blockIn_of_reach {c : ADRCircuit n} {A : Finset (Fin c.gateCount)}
    (hsep : SeparatedBy c A) {u v : Fin c.gateCount} (hu : u ∈ A)
    (h : VertexReachable c u v) : VertexReachable (blockIn c A) u v ∧ v ∈ A := by
  induction h with
  | refl => exact ⟨Relation.ReflTransGen.refl, hu⟩
  | @tail w z _ hadj ih =>
      have hstep : UnderlyingAdj (blockIn c A) w z :=
        (underlyingAdj_blockIn hsep w z).mpr ⟨hadj, ih.2⟩
      have hz : z ∈ A :=
        ((underlyingAdj_blockIn hsep z w).mp
          ((underlyingAdj_comm (c := blockIn c A) w z).mp hstep)).2
      exact ⟨ih.1.tail hstep, hz⟩

/-- Starting outside `A`, reachability in `c` stays outside `A` and is realised in the
second block. -/
theorem reach_blockOut_of_reach {c : ADRCircuit n} {A : Finset (Fin c.gateCount)}
    (hsep : SeparatedBy c A) {u v : Fin c.gateCount} (hu : u ∉ A)
    (h : VertexReachable c u v) : VertexReachable (blockOut c A) u v ∧ v ∉ A := by
  induction h with
  | refl => exact ⟨Relation.ReflTransGen.refl, hu⟩
  | @tail w z _ hadj ih =>
      have hstep : UnderlyingAdj (blockOut c A) w z :=
        (underlyingAdj_blockOut hsep w z).mpr ⟨hadj, ih.2⟩
      have hz : z ∉ A :=
        ((underlyingAdj_blockOut hsep z w).mp
          ((underlyingAdj_comm (c := blockOut c A) w z).mp hstep)).2
      exact ⟨ih.1.tail hstep, hz⟩

/-- Each block turns the vertices of the other block into singleton components. -/
theorem componentCount_block {c : ADRCircuit n} {A : Finset (Fin c.gateCount)}
    (hsep : SeparatedBy c A) :
    componentCount (blockIn c A) + componentCount (blockOut c A)
      = componentCount c + c.gateCount := by
  classical
  have hIn : componentCount (blockIn c A)
      = (Finset.univ.filter (fun u : Fin c.gateCount =>
          u ∉ A ∨ ∀ v, VertexReachable c u v → u.val ≤ v.val)).card := by
    unfold componentCount
    refine card_filter_congr_of_iff (N := c.gateCount) _ _ _ _ (fun u => ?_)
    by_cases hu : u ∈ A
    · constructor
      · intro h
        exact Or.inr (fun v hv => h v (reach_blockIn_of_reach hsep hu hv).1)
      · rintro (hcon | h)
        · exact absurd hu hcon
        · exact fun v hv => h v (reach_of_reach_blockIn hsep hv)
    · constructor
      · intro _
        exact Or.inl hu
      · intro _ v hv
        rcases Relation.ReflTransGen.cases_head hv with rfl | ⟨y, hy, _⟩
        · exact Nat.le_refl _
        · exact absurd ((underlyingAdj_blockIn hsep u y).mp hy).2 hu
  have hOut : componentCount (blockOut c A)
      = (Finset.univ.filter (fun u : Fin c.gateCount =>
          u ∈ A ∨ ∀ v, VertexReachable c u v → u.val ≤ v.val)).card := by
    unfold componentCount
    refine card_filter_congr_of_iff (N := c.gateCount) _ _ _ _ (fun u => ?_)
    by_cases hu : u ∈ A
    · constructor
      · intro _
        exact Or.inl hu
      · intro _ v hv
        rcases Relation.ReflTransGen.cases_head hv with rfl | ⟨y, hy, _⟩
        · exact Nat.le_refl _
        · exact absurd hu ((underlyingAdj_blockOut hsep u y).mp hy).2
    · constructor
      · intro h
        exact Or.inr (fun v hv => h v (reach_blockOut_of_reach hsep hu hv).1)
      · rintro (hcon | h)
        · exact absurd hcon hu
        · exact fun v hv => h v (reach_of_reach_blockOut hsep hv)
  have hc : componentCount c
      = (Finset.univ.filter (fun u : Fin c.gateCount =>
          ∀ v, VertexReachable c u v → u.val ≤ v.val)).card := by
    unfold componentCount
    exact card_filter_congr_of_iff (N := c.gateCount) _ _ _ _ (fun _ => Iff.rfl)
  rw [hIn, hOut, hc]
  exact card_filter_side_pair
    (fun u : Fin c.gateCount => ∀ v, VertexReachable c u v → u.val ≤ v.val) A

/-! ## Splitting a rotation system -/

/-- Transporting a permutation along an equivalence with an invariant subtype does
not change its cycle count. -/
theorem permCycleCount_of_subtype_transport {D E : Type} [Fintype D] [DecidableEq D]
    [Fintype E] [DecidableEq E] (P : Equiv.Perm D) (S : D → Prop) [DecidablePred S]
    (h : ∀ x, S (P x) ↔ S x) (phi : E ≃ {x : D // S x}) (Q : Equiv.Perm E)
    (hQ : ∀ e, (phi (Q e)).1 = P (phi e).1) :
    permCycleCount Q = permCycleCount (P.subtypePerm h) := by
  have hQeq : Q = phi.trans ((P.subtypePerm h).trans phi.symm) := by
    apply Equiv.ext
    intro e
    apply phi.injective
    rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.apply_symm_apply]
    exact Subtype.ext (hQ e)
  rw [hQeq, permCycleCount_conj_quot]

/-- Both endpoints of a dart lie on the same side of a separating set. -/
theorem dart_source_mem_iff {c : ADRCircuit n} {A : Finset (Fin c.gateCount)}
    (hsep : SeparatedBy c A) (d : CircuitDart c) : d.source ∈ A ↔ d.target ∈ A := by
  rcases d.2.1 with he | he
  · exact hsep _ _ he
  · exact (hsep _ _ he).symm

/-- The rotation preserves the side of a dart. -/
theorem rot_source_mem_invariant {c : ADRCircuit n} {A : Finset (Fin c.gateCount)}
    (rot : OrientableRotation c) (d : CircuitDart c) :
    ((rot.rotation d).source ∈ A) ↔ (d.source ∈ A) := by
  rw [rot.preservesSource d]

/-- The face permutation preserves the side of a dart. -/
theorem face_source_mem_invariant {c : ADRCircuit n} {A : Finset (Fin c.gateCount)}
    (hsep : SeparatedBy c A) (rot : OrientableRotation c) (d : CircuitDart c) :
    ((facePermutation rot d).source ∈ A) ↔ (d.source ∈ A) := by
  have h1 : (facePermutation rot d).source = (dartReverse c d).source :=
    rot.preservesSource _
  rw [h1]
  exact (dart_source_mem_iff hsep d).symm

/-- The rotation system induced on the first block. -/
noncomputable def blockRotationIn {c : ADRCircuit n} {A : Finset (Fin c.gateCount)}
    (hsep : SeparatedBy c A) (rot : OrientableRotation c) :
    OrientableRotation (blockIn c A) where
  rotation := (blockDartIn hsep).trans
    (((rot.rotation).subtypePerm (fun d => rot_source_mem_invariant rot d)).trans
      (blockDartIn hsep).symm)
  preservesSource := by
    intro d
    change (rot.rotation ((blockDartIn hsep) d).1).source = d.source
    rw [rot.preservesSource]
    rfl
  cyclicAtVertex := by
    intro d e hde
    obtain ⟨k, hk⟩ := rot.cyclicAtVertex ((blockDartIn hsep) d).1 ((blockDartIn hsep) e).1 hde
    refine ⟨k, ?_⟩
    rw [pow_conj_apply (blockDartIn hsep) _ k d, Equiv.Perm.subtypePerm_pow]
    exact (Equiv.symm_apply_eq _).mpr (Subtype.ext hk)

/-- The rotation system induced on the second block. -/
noncomputable def blockRotationOut {c : ADRCircuit n} {A : Finset (Fin c.gateCount)}
    (hsep : SeparatedBy c A) (rot : OrientableRotation c) :
    OrientableRotation (blockOut c A) where
  rotation := (blockDartOut hsep).trans
    (((rot.rotation).subtypePerm
        (fun d => not_congr (rot_source_mem_invariant rot d))).trans
      (blockDartOut hsep).symm)
  preservesSource := by
    intro d
    change (rot.rotation ((blockDartOut hsep) d).1).source = d.source
    rw [rot.preservesSource]
    rfl
  cyclicAtVertex := by
    intro d e hde
    obtain ⟨k, hk⟩ := rot.cyclicAtVertex ((blockDartOut hsep) d).1 ((blockDartOut hsep) e).1 hde
    refine ⟨k, ?_⟩
    rw [pow_conj_apply (blockDartOut hsep) _ k d, Equiv.Perm.subtypePerm_pow]
    exact (Equiv.symm_apply_eq _).mpr (Subtype.ext hk)

/-- A rotation system of a separated circuit splits into rotation systems of the
two blocks, and the faces split accordingly. -/
theorem exists_block_rotations {c : ADRCircuit n} {A : Finset (Fin c.gateCount)}
    (hsep : SeparatedBy c A) (rot : OrientableRotation c) :
    ∃ (rIn : OrientableRotation (blockIn c A)) (rOut : OrientableRotation (blockOut c A)),
      permCycleCount (facePermutation rIn) + permCycleCount (facePermutation rOut)
        = permCycleCount (facePermutation rot) := by
  classical
  refine ⟨blockRotationIn hsep rot, blockRotationOut hsep rot, ?_⟩
  have hface := face_source_mem_invariant hsep rot
  have hsplit := permCycleCount_split (facePermutation rot)
    (fun d : CircuitDart c => d.source ∈ A) hface
  have hIn : permCycleCount (facePermutation (blockRotationIn hsep rot))
      = permCycleCount ((facePermutation rot).subtypePerm
          (p := fun d : CircuitDart c => d.source ∈ A) hface) := by
    refine permCycleCount_of_subtype_transport (facePermutation rot)
      (fun d : CircuitDart c => d.source ∈ A) hface (blockDartIn hsep) _ (fun e => ?_)
    rfl
  have hOut : permCycleCount (facePermutation (blockRotationOut hsep rot))
      = permCycleCount ((facePermutation rot).subtypePerm
          (p := fun d : CircuitDart c => ¬ (d.source ∈ A)) (fun x => not_congr (hface x))) := by
    refine permCycleCount_of_subtype_transport (facePermutation rot)
      (fun d : CircuitDart c => ¬ (d.source ∈ A)) (fun x => not_congr (hface x))
      (blockDartOut hsep) _ (fun e => ?_)
    rfl
  rw [hIn, hOut, hsplit]

/-! ## The packing bound -/

/-- The Euler defect of a rotation system, i.e. twice its genus. -/
theorem two_mul_rotationGenus_le {c : ADRCircuit n} (rot : OrientableRotation c) {k : Nat}
    (h : 2 * k + (c.gateCount + permCycleCount (facePermutation rot) + isolatedVertexCount c)
      ≤ 2 * componentCount c + underlyingEdgeCount c) :
    k ≤ rotationGenus rot := by
  change k ≤ (2 * componentCount c + underlyingEdgeCount c - c.gateCount -
    (permCycleCount (facePermutation rot) + isolatedVertexCount c)) / 2
  omega

/-- A non-rotation-planar circuit has Euler defect at least two for every
rotation system. -/
theorem defect_ge_two_of_not_planar {c : ADRCircuit n} (h : ¬ RotationPlanar c)
    (rot : OrientableRotation c) :
    2 + (c.gateCount + permCycleCount (facePermutation rot) + isolatedVertexCount c)
      ≤ 2 * componentCount c + underlyingEdgeCount c := by
  by_contra hcon
  apply h
  refine ⟨rot, ?_⟩
  change (2 * componentCount c + underlyingEdgeCount c - c.gateCount -
    (permCycleCount (facePermutation rot) + isolatedVertexCount c)) / 2 = 0
  omega

/-- A block taken inside a set disjoint from `A` does not see the deletion of the
edges inside `A`. -/
theorem blockIn_blockOut_of_disjoint {c : ADRCircuit n} {A B : Finset (Fin c.gateCount)}
    (hd : Disjoint A B) : blockIn (blockOut c A) B = blockIn c B := by
  unfold blockIn blockOut maskCircuit
  congr 1
  funext a b
  by_cases hab : a ∈ B ∧ b ∈ B
  · have ha : a ∉ A := fun h => (Finset.disjoint_left.mp hd h) hab.1
    have hb : b ∉ A := fun h => (Finset.disjoint_left.mp hd h) hab.2
    simp [hab.1, hab.2, ha, hb]
  · simp only [Bool.and_eq_true, decide_eq_true_eq]
    rw [if_neg hab, if_neg hab]

/-- All four counts of an edgeless circuit. -/
theorem counts_of_no_adj {c : ADRCircuit n} (h : ∀ u v, ¬ UnderlyingAdj c u v)
    (rot : OrientableRotation c) :
    isolatedVertexCount c = c.gateCount ∧ componentCount c = c.gateCount ∧
      underlyingEdgeCount c = 0 ∧ permCycleCount (facePermutation rot) = 0 := by
  classical
  have hI : isolatedVertexCount c = c.gateCount := by
    unfold isolatedVertexCount
    rw [Finset.filter_true_of_mem (fun u _ => h u), Finset.card_univ, Fintype.card_fin]
  have hC : componentCount c = c.gateCount := by
    unfold componentCount
    rw [Finset.filter_true_of_mem (fun u _ => ?_), Finset.card_univ, Fintype.card_fin]
    intro v hv
    rcases Relation.ReflTransGen.cases_head hv with rfl | ⟨y, hy, _⟩
    · exact Nat.le_refl _
    · exact absurd hy (h _ _)
  have hE : underlyingEdgeCount c = 0 := by
    unfold underlyingEdgeCount
    refine Finset.sum_eq_zero (fun u _ => ?_)
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro v _
    exact fun hc => (h u v) hc.2
  have hdart : Fintype.card (CircuitDart c) = 0 := by
    have := two_mul_underlyingEdgeCount c
    omega
  have hF : permCycleCount (facePermutation rot) = 0 := by
    unfold permCycleCount
    have hle := Finset.card_filter_le (Finset.univ : Finset (CircuitDart c))
      (fun x => ∀ y, (∃ k : Nat, ((facePermutation rot) ^ k) x = y) →
        (Fintype.equivFin (CircuitDart c) x).val ≤ (Fintype.equivFin (CircuitDart c) y).val)
    have hcard : (Finset.univ : Finset (CircuitDart c)).card = 0 := by
      rw [Finset.card_univ]
      exact hdart
    omega
  exact ⟨hI, hC, hE, hF⟩

/-- An edgeless circuit has Euler defect zero. -/
theorem defect_of_no_adj {c : ADRCircuit n} (h : ∀ u v, ¬ UnderlyingAdj c u v)
    (rot : OrientableRotation c) :
    c.gateCount + permCycleCount (facePermutation rot) + isolatedVertexCount c
      ≤ 2 * componentCount c + underlyingEdgeCount c := by
  obtain ⟨hI, hC, hE, hF⟩ := counts_of_no_adj h rot
  omega

/-- Packing bound, defect form: if every edge of `c` lies inside one of the
pairwise disjoint sets of `l`, and every one of those sets induces a
non-rotation-planar block, then every rotation system of `c` has Euler defect at
least `2 * l.length`. -/
theorem packing_defect (k : Nat) :
    ∀ (c : ADRCircuit n) (l : List (Finset (Fin c.gateCount))), l.length = k →
      l.Pairwise Disjoint →
      (∀ A ∈ l, ¬ RotationPlanar (blockIn c A)) →
      (∀ a b, c.edge a b = true → ∃ A ∈ l, a ∈ A ∧ b ∈ A) →
      ∀ rot : OrientableRotation c,
        2 * k + (c.gateCount + permCycleCount (facePermutation rot) + isolatedVertexCount c)
          ≤ 2 * componentCount c + underlyingEdgeCount c := by
  induction k with
  | zero =>
      intro c l hlen _ _ hedge rot
      have hnil : l = [] := List.eq_nil_of_length_eq_zero hlen
      subst hnil
      have hno : ∀ u v, ¬ UnderlyingAdj c u v := by
        intro u v hadj
        rcases hadj.1 with he | he
        · obtain ⟨A, hA, _⟩ := hedge _ _ he
          exact absurd hA (List.not_mem_nil)
        · obtain ⟨A, hA, _⟩ := hedge _ _ he
          exact absurd hA (List.not_mem_nil)
      have := defect_of_no_adj hno rot
      omega
  | succ k ih =>
      intro c l hlen hdisj hnp hedge rot
      match l, hlen with
      | A :: rest, hlen =>
      have hrestlen : rest.length = k := by
        simpa using hlen
      have hdisjA : ∀ B ∈ rest, Disjoint A B := (List.pairwise_cons.mp hdisj).1
      have hdisjrest : rest.Pairwise Disjoint := (List.pairwise_cons.mp hdisj).2
      have hsep : SeparatedBy c A := by
        intro a b hab
        obtain ⟨B, hB, haB, hbB⟩ := hedge a b hab
        rcases List.mem_cons.mp hB with rfl | hBrest
        · exact iff_of_true haB hbB
        · have hd := hdisjA B hBrest
          have ha : a ∉ A := fun h => (Finset.disjoint_left.mp hd h) haB
          have hb : b ∉ A := fun h => (Finset.disjoint_left.mp hd h) hbB
          exact iff_of_false ha hb
      obtain ⟨rIn, rOut, hF⟩ := exists_block_rotations hsep rot
      have hA := defect_ge_two_of_not_planar (hnp A (List.mem_cons_self ..)) rIn
      have hedgeOut : ∀ a b, (blockOut c A).edge a b = true → ∃ B ∈ rest, a ∈ B ∧ b ∈ B := by
        intro a b hab
        obtain ⟨he, ha, _⟩ := blockOut_edge_true hab
        obtain ⟨B, hB, haB, hbB⟩ := hedge a b he
        rcases List.mem_cons.mp hB with rfl | hBrest
        · exact absurd haB ha
        · exact ⟨B, hBrest, haB, hbB⟩
      have hnpOut : ∀ B ∈ rest, ¬ RotationPlanar (blockIn (blockOut c A) B) := by
        intro B hB
        rw [blockIn_blockOut_of_disjoint (hdisjA B hB)]
        exact hnp B (List.mem_cons_of_mem _ hB)
      have hIH := ih (blockOut c A) rest hrestlen hdisjrest hnpOut hedgeOut rOut
      have hC := componentCount_block hsep
      have hI := isolatedVertexCount_block hsep
      have hE := underlyingEdgeCount_block hsep
      simp only [blockIn_gateCount, blockOut_gateCount] at hA hIH
      omega

/-- Genus packing, list form: pairwise disjoint vertex sets with non-planar
induced blocks force the genus up. -/
theorem length_le_genus_of_blocks (c : ADRCircuit n) (l : List (Finset (Fin c.gateCount)))
    (hdisj : l.Pairwise Disjoint)
    (hnp : ∀ A ∈ l, ¬ RotationPlanar (blockIn c A)) :
    l.length ≤ orientableCircuitGenus c := by
  classical
  set keep : Fin c.gateCount → Fin c.gateCount → Bool :=
    fun a b => decide (∃ A ∈ l, a ∈ A ∧ b ∈ A) with hkeep
  have hedge : ∀ a b, (maskCircuit c keep).edge a b = true → ∃ A ∈ l, a ∈ A ∧ b ∈ A := by
    intro a b hab
    by_cases h : keep a b = true
    · simpa [hkeep] using h
    · rw [maskCircuit_edge, if_neg h] at hab
      exact absurd hab (by simp)
  have hblock : ∀ A ∈ l, blockIn (maskCircuit c keep) A = blockIn c A := by
    intro A hA
    unfold blockIn maskCircuit
    congr 1
    funext a b
    by_cases hab : a ∈ A ∧ b ∈ A
    · have hk : keep a b = true := by
        simp only [hkeep, decide_eq_true_eq]
        exact ⟨A, hA, hab.1, hab.2⟩
      simp [hab.1, hab.2, hk]
    · simp only [Bool.and_eq_true, decide_eq_true_eq]
      rw [if_neg hab, if_neg hab]
  have hnp' : ∀ A ∈ l, ¬ RotationPlanar (blockIn (maskCircuit c keep) A) := by
    intro A hA
    rw [hblock A hA]
    exact hnp A hA
  obtain ⟨rot, hrot⟩ := exists_rotation_genus_eq (maskCircuit c keep)
  have hdef := packing_defect l.length (maskCircuit c keep) l rfl hdisj hnp' hedge rot
  have hge : l.length ≤ rotationGenus rot := two_mul_rotationGenus_le rot hdef
  calc l.length ≤ rotationGenus rot := hge
    _ = orientableCircuitGenus (maskCircuit c keep) := hrot
    _ ≤ orientableCircuitGenus c := genus_maskCircuit_le c keep

end AllenderOQ3.Internal
