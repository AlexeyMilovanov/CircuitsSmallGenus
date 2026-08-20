import AllenderOQ3.Internal.ACCBuild

/-!
# Unbounded fan-in joins of a finite family of ACC circuits

The depth-two blocking formula of §9 (an `OR` over exponentially many state
sequences of an `AND` over the blocks) and the beta ports of §7.3 both need a
combinator that takes a *finite family* `f : Fin k → ACCCircuit n m` of ACC
circuits over the same inputs and the same modulus, places all of them side by
side, and attaches a single fresh **root** gate fed by every block output.

Crucially the root has fan-in `k`, not fan-in two: a binary tree would add
`Θ(log k)` to the depth, which is exactly what an `ACC0` bound cannot afford.

The gate set of the join is
`((i : Fin k) × Fin (f i).gateCount) ⊕ Fin 1`, transported to
`Fin ((∑ i, (f i).gateCount) + 1)` along the equivalence `joinEquiv`.

Main results:

* `wellFormedACC_accJoin` — well-formedness is preserved, provided every block
  is well formed, all block layers are `≤ d`, and the root is neither a literal
  nor a `NOT` gate;
* `accJoin_layer_le` — the join has depth `d + 1`;
* `accJoin_edge_to_block` / `accJoin_edge_to_root` — the edge relation;
* `accValuation_accJoin` — gluing valuations of the blocks with a root value
  that satisfies the root's own gate condition;
* `accAccepts_accJoin_or` — an `OR` root accepts iff *some* block accepts;
* `accAccepts_accJoin_and` — an `AND` root accepts iff *every* block accepts;
* `accOrAnd` and `accAccepts_accOrAnd` — the depth-two, unbounded fan-in
  `OR`-of-`AND`s over a doubly indexed family, which is the shape produced by
  the blocking argument of §9.

Everything is `sorry`-free.
-/

set_option autoImplicit false

namespace AllenderOQ3.Internal

variable {n m : Nat}

/-! ## The index equivalence -/

/-- The gate index type of a `k`-ary join — a gate of one of the blocks, or the
fresh root — identified with `Fin ((∑ i, (f i).gateCount) + 1)`. -/
def joinEquiv {k : Nat} (f : Fin k → ACCCircuit n m) :
    (((i : Fin k) × Fin (f i).gateCount) ⊕ Fin 1) ≃ Fin ((∑ i, (f i).gateCount) + 1) :=
  (Equiv.sumCongr finSigmaFinEquiv (Equiv.refl (Fin 1))).trans finSumFinEquiv

/-! ## Edges inside the blocks -/

/-- Edges internal to the blocks: an edge exists only between two gates of the
same block, where it is the block's own edge. -/
def blockEdge {k : Nat} (f : Fin k → ACCCircuit n m)
    (s t : (i : Fin k) × Fin (f i).gateCount) : Bool :=
  if h : s.1 = t.1 then (f t.1).edge (h ▸ s.2) t.2 else false

@[simp] theorem blockEdge_same {k : Nat} (f : Fin k → ACCCircuit n m) (i : Fin k)
    (a b : Fin (f i).gateCount) :
    blockEdge f ⟨i, a⟩ ⟨i, b⟩ = (f i).edge a b := by
  simp [blockEdge]

theorem blockEdge_ne {k : Nat} (f : Fin k → ACCCircuit n m) {i j : Fin k}
    (hij : i ≠ j) (a : Fin (f i).gateCount) (b : Fin (f j).gateCount) :
    blockEdge f ⟨i, a⟩ ⟨j, b⟩ = false := by
  simp [blockEdge, hij]

/-- Characterisation of the edges into a block gate. -/
theorem blockEdge_to {k : Nat} {f : Fin k → ACCCircuit n m}
    {s : (i : Fin k) × Fin (f i).gateCount} {j : Fin k} {b : Fin (f j).gateCount} :
    blockEdge f s ⟨j, b⟩ = true ↔ ∃ a, s = ⟨j, a⟩ ∧ (f j).edge a b = true := by
  obtain ⟨i, a⟩ := s
  by_cases hij : i = j
  · subst hij
    simp only [blockEdge_same]
    constructor
    · intro h; exact ⟨a, rfl, h⟩
    · rintro ⟨a', ha', h⟩
      rw [Sigma.mk.injEq] at ha'
      obtain ⟨-, ha'⟩ := ha'
      cases ha'
      exact h
  · simp only [blockEdge_ne f hij, Bool.false_eq_true, false_iff, not_exists]
    rintro a' ⟨ha', -⟩
    exact hij (congrArg Sigma.fst ha')

/-! ## The join circuit -/

/-- The `k`-ary join: all blocks side by side, plus one fresh root gate of kind
`root` at layer `d + 1`, fed by the output gate of every block. -/
def accJoin {k : Nat} (f : Fin k → ACCCircuit n m) (d : Nat) (root : ACCGate n m) :
    ACCCircuit n m where
  gateCount := (∑ i, (f i).gateCount) + 1
  output := joinEquiv f (Sum.inr 0)
  kind := fun g =>
    Sum.elim (fun s => (f s.1).kind s.2) (fun _ => root) ((joinEquiv f).symm g)
  layer := fun g =>
    Sum.elim (fun s => (f s.1).layer s.2) (fun _ => d + 1) ((joinEquiv f).symm g)
  edge := fun u v =>
    Sum.elim
      (fun s =>
        Sum.elim (fun t => blockEdge f s t)
          (fun _ => decide (s.2 = (f s.1).output)) ((joinEquiv f).symm v))
      (fun _ => false) ((joinEquiv f).symm u)

variable {k : Nat} {f : Fin k → ACCCircuit n m} {d : Nat} {root : ACCGate n m}

@[simp] theorem accJoin_gateCount :
    (accJoin f d root).gateCount = (∑ i, (f i).gateCount) + 1 := rfl

@[simp] theorem accJoin_output :
    (accJoin f d root).output = joinEquiv f (Sum.inr 0) := rfl

@[simp] theorem accJoin_kind_block (i : Fin k) (a : Fin (f i).gateCount) :
    (accJoin f d root).kind (joinEquiv f (Sum.inl ⟨i, a⟩)) = (f i).kind a := by
  simp [accJoin]

@[simp] theorem accJoin_kind_root (j : Fin 1) :
    (accJoin f d root).kind (joinEquiv f (Sum.inr j)) = root := by
  simp [accJoin]

@[simp] theorem accJoin_layer_block (i : Fin k) (a : Fin (f i).gateCount) :
    (accJoin f d root).layer (joinEquiv f (Sum.inl ⟨i, a⟩)) = (f i).layer a := by
  simp [accJoin]

@[simp] theorem accJoin_layer_root (j : Fin 1) :
    (accJoin f d root).layer (joinEquiv f (Sum.inr j)) = d + 1 := by
  simp [accJoin]

@[simp] theorem accJoin_edge_bb (s t : (i : Fin k) × Fin (f i).gateCount) :
    (accJoin f d root).edge (joinEquiv f (Sum.inl s)) (joinEquiv f (Sum.inl t))
      = blockEdge f s t := by
  simp [accJoin]

@[simp] theorem accJoin_edge_br (s : (i : Fin k) × Fin (f i).gateCount) (j : Fin 1) :
    (accJoin f d root).edge (joinEquiv f (Sum.inl s)) (joinEquiv f (Sum.inr j))
      = decide (s.2 = (f s.1).output) := by
  simp [accJoin]

@[simp] theorem accJoin_edge_r (j : Fin 1) (v : Fin (accJoin f d root).gateCount) :
    (accJoin f d root).edge (joinEquiv f (Sum.inr j)) v = false := by
  simp [accJoin]

/-- Every gate of the join is either a block gate or the root. -/
theorem accJoin_cases {P : Fin (accJoin f d root).gateCount → Prop}
    (hb : ∀ (i : Fin k) (a : Fin (f i).gateCount), P (joinEquiv f (Sum.inl ⟨i, a⟩)))
    (hr : ∀ j : Fin 1, P (joinEquiv f (Sum.inr j))) :
    ∀ g, P g := by
  intro g
  obtain ⟨y, rfl⟩ := (joinEquiv f).surjective g
  cases y with
  | inl s => obtain ⟨i, a⟩ := s; exact hb i a
  | inr j => exact hr j

/-- Edges into a block gate come from the same block. -/
theorem accJoin_edge_to_block {j : Fin k} {b : Fin (f j).gateCount}
    {h : Fin (accJoin f d root).gateCount} :
    (accJoin f d root).edge h (joinEquiv f (Sum.inl ⟨j, b⟩)) = true ↔
      ∃ a, h = joinEquiv f (Sum.inl ⟨j, a⟩) ∧ (f j).edge a b = true := by
  induction h using accJoin_cases with
  | hb i a =>
      rw [accJoin_edge_bb, blockEdge_to]
      constructor
      · rintro ⟨a', ha', he⟩
        exact ⟨a', congrArg _ (congrArg Sum.inl ha'), he⟩
      · rintro ⟨a', ha', he⟩
        refine ⟨a', ?_, he⟩
        have := (joinEquiv f).injective ha'
        exact Sum.inl.inj this
  | hr j' =>
      simp only [accJoin_edge_r, Bool.false_eq_true, false_iff, not_exists]
      rintro a ⟨ha, -⟩
      simpa using (joinEquiv f).injective ha

/-- Edges into the root come from the output gates of the blocks. -/
theorem accJoin_edge_to_root {j : Fin 1} {h : Fin (accJoin f d root).gateCount} :
    (accJoin f d root).edge h (joinEquiv f (Sum.inr j)) = true ↔
      ∃ i, h = joinEquiv f (Sum.inl ⟨i, (f i).output⟩) := by
  induction h using accJoin_cases with
  | hb i a =>
      rw [accJoin_edge_br]
      constructor
      · intro ha
        exact ⟨i, congrArg _ (congrArg Sum.inl (by simp_all))⟩
      · rintro ⟨i', hi'⟩
        have := Sum.inl.inj ((joinEquiv f).injective hi')
        rw [Sigma.mk.injEq] at this
        obtain ⟨heq, hval⟩ := this
        subst heq
        simpa using hval
  | hr j' =>
      simp only [accJoin_edge_r, Bool.false_eq_true, false_iff, not_exists]
      intro i hi
      simpa using (joinEquiv f).injective hi

/-! ## Well-formedness -/

theorem accJoin_layer_le (hd : ∀ (i : Fin k) (a : Fin (f i).gateCount), (f i).layer a ≤ d) :
    ∀ g, (accJoin f d root).layer g ≤ d + 1 := by
  refine accJoin_cases ?_ ?_
  · intro i a; rw [accJoin_layer_block]; exact le_trans (hd i a) (Nat.le_succ d)
  · intro j; rw [accJoin_layer_root]

theorem wellFormedACC_accJoin (hf : ∀ i, WellFormedACC (f i))
    (hd : ∀ (i : Fin k) (a : Fin (f i).gateCount), (f i).layer a ≤ d)
    (hlit : ∀ (i : Fin n) (b : Bool), root ≠ .literal i b)
    (hnot : root ≠ .notGate) :
    WellFormedACC (accJoin f d root) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u v huv
    induction v using accJoin_cases with
    | hb j b =>
        obtain ⟨a, rfl, he⟩ := accJoin_edge_to_block.mp huv
        rw [accJoin_layer_block, accJoin_layer_block]
        exact (hf j).1 a b he
    | hr j =>
        obtain ⟨i, rfl⟩ := accJoin_edge_to_root.mp huv
        rw [accJoin_layer_block, accJoin_layer_root]
        exact Nat.lt_succ_of_le (hd i _)
  · refine accJoin_cases ?_ ?_
    · intro i a
      rw [accJoin_layer_block, accJoin_kind_block]
      exact (hf i).2.1 a
    · intro j
      rw [accJoin_layer_root, accJoin_kind_root]
      simp only [Nat.succ_ne_zero, false_iff, not_exists]
      exact hlit
  · refine accJoin_cases ?_ ?_
    · intro i a hg
      rw [accJoin_kind_block] at hg
      obtain ⟨h', hh', huniq⟩ := (hf i).2.2 a hg
      refine ⟨joinEquiv f (Sum.inl ⟨i, h'⟩), accJoin_edge_to_block.mpr ⟨h', rfl, hh'⟩, ?_⟩
      intro y hy
      obtain ⟨a', rfl, hy'⟩ := accJoin_edge_to_block.mp hy
      exact congrArg _ (congrArg Sum.inl (by rw [huniq a' hy']))
    · intro j hg
      rw [accJoin_kind_root] at hg
      exact absurd hg hnot

/-! ## Semantics -/

/-- The valuation of the join obtained from valuations of the blocks together
with a value `r` for the root. -/
def joinValue (f : Fin k → ACCCircuit n m) (d : Nat) (root : ACCGate n m)
    (v : (i : Fin k) → Fin (f i).gateCount → Bool) (r : Bool) :
    Fin (accJoin f d root).gateCount → Bool :=
  fun g => Sum.elim (fun s => v s.1 s.2) (fun _ => r) ((joinEquiv f).symm g)

@[simp] theorem joinValue_block (v : (i : Fin k) → Fin (f i).gateCount → Bool) (r : Bool)
    (i : Fin k) (a : Fin (f i).gateCount) :
    joinValue f d root v r (joinEquiv f (Sum.inl ⟨i, a⟩)) = v i a := by
  simp [joinValue]

@[simp] theorem joinValue_root (v : (i : Fin k) → Fin (f i).gateCount → Bool) (r : Bool)
    (j : Fin 1) :
    joinValue f d root v r (joinEquiv f (Sum.inr j)) = r := by
  simp [joinValue]

/-- The inputs of a block gate in the join biject with its inputs in the block. -/
theorem accJoin_card_block (V : Fin (accJoin f d root).gateCount → Bool)
    {j : Fin k} {b : Fin (f j).gateCount} :
    (Finset.univ.filter (fun h : Fin (accJoin f d root).gateCount =>
        (accJoin f d root).edge h (joinEquiv f (Sum.inl ⟨j, b⟩)) = true ∧ V h = true)).card
      = (Finset.univ.filter (fun a : Fin (f j).gateCount =>
          (f j).edge a b = true ∧ V (joinEquiv f (Sum.inl ⟨j, a⟩)) = true)).card := by
  refine (Finset.card_bij (fun a _ => joinEquiv f (Sum.inl ⟨j, a⟩)) ?_ ?_ ?_).symm
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact ⟨accJoin_edge_to_block.mpr ⟨a, rfl, ha.1⟩, ha.2⟩
  · intro a₁ _ a₂ _ hEq
    have := Sum.inl.inj ((joinEquiv f).injective hEq)
    rw [Sigma.mk.injEq] at this
    exact eq_of_heq this.2
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    obtain ⟨a, rfl, ha⟩ := accJoin_edge_to_block.mp hy.1
    exact ⟨a, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨ha, hy.2⟩, rfl⟩

/-- The inputs of the root biject with the block indices. -/
theorem accJoin_card_root (v : (i : Fin k) → Fin (f i).gateCount → Bool) (r : Bool)
    {j : Fin 1} :
    (Finset.univ.filter (fun h : Fin (accJoin f d root).gateCount =>
        (accJoin f d root).edge h (joinEquiv f (Sum.inr j)) = true ∧
          joinValue f d root v r h = true)).card
      = (Finset.univ.filter (fun i : Fin k => v i (f i).output = true)).card := by
  refine (Finset.card_bij (fun i _ => joinEquiv f (Sum.inl ⟨i, (f i).output⟩)) ?_ ?_ ?_).symm
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact ⟨accJoin_edge_to_root.mpr ⟨i, rfl⟩, by simpa using hi⟩
  · intro i₁ _ i₂ _ hEq
    have := Sum.inl.inj ((joinEquiv f).injective hEq)
    exact congrArg Sigma.fst this
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    obtain ⟨i, rfl⟩ := accJoin_edge_to_root.mp hy.1
    refine ⟨i, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simpa using hy.2

/-- The condition the root's value must satisfy, given the outputs of the blocks. -/
def RootSpec (f : Fin k → ACCCircuit n m) (root : ACCGate n m) (x : Fin n → Bool)
    (v : (i : Fin k) → Fin (f i).gateCount → Bool) (r : Bool) : Prop :=
  match root with
  | .literal i b => r = if b then !(x i) else x i
  | .andGate => (r = true ↔ ∀ i, v i (f i).output = true)
  | .orGate => (r = true ↔ ∃ i, v i (f i).output = true)
  | .notGate => (r = true ↔ ∃ i, v i (f i).output = false)
  | .modGate =>
      (r = true ↔ (Finset.univ.filter (fun i => v i (f i).output = true)).card % m = 0)

/-- Gluing valuations of the blocks with a root value satisfying the root's own
gate condition gives a valuation of the join. -/
theorem accValuation_accJoin {x : Fin n → Bool}
    {v : (i : Fin k) → Fin (f i).gateCount → Bool} {r : Bool}
    (hv : ∀ i, ACCValuation (f i) x (v i)) (hr : RootSpec f root x v r) :
    ACCValuation (accJoin f d root) x (joinValue f d root v r) := by
  refine accJoin_cases ?_ ?_
  · intro i a
    have hg := hv i a
    rw [accJoin_kind_block]
    cases hk : (f i).kind a with
    | literal idx bneg =>
        simp only [hk] at hg
        simpa using hg
    | andGate =>
        simp only [hk] at hg
        rw [joinValue_block, hg]
        constructor
        · intro H y hy
          obtain ⟨a', rfl, he⟩ := accJoin_edge_to_block.mp hy
          simpa using H a' he
        · intro H a' he
          simpa using H _ (accJoin_edge_to_block.mpr ⟨a', rfl, he⟩)
    | orGate =>
        simp only [hk] at hg
        rw [joinValue_block, hg]
        constructor
        · rintro ⟨a', he, hva⟩
          exact ⟨_, accJoin_edge_to_block.mpr ⟨a', rfl, he⟩, by simpa using hva⟩
        · rintro ⟨y, hy, hvy⟩
          obtain ⟨a', rfl, he⟩ := accJoin_edge_to_block.mp hy
          exact ⟨a', he, by simpa using hvy⟩
    | notGate =>
        simp only [hk] at hg
        rw [joinValue_block, hg]
        constructor
        · rintro ⟨a', he, hva⟩
          exact ⟨_, accJoin_edge_to_block.mpr ⟨a', rfl, he⟩, by simpa using hva⟩
        · rintro ⟨y, hy, hvy⟩
          obtain ⟨a', rfl, he⟩ := accJoin_edge_to_block.mp hy
          exact ⟨a', he, by simpa using hvy⟩
    | modGate =>
        simp only [hk] at hg
        rw [joinValue_block, hg, accJoin_card_block]
        simp
  · intro j
    rw [accJoin_kind_root]
    cases hk : root with
    | literal idx bneg =>
        simp only [hk, RootSpec] at hr
        simpa using hr
    | andGate =>
        simp only [hk, RootSpec] at hr
        rw [joinValue_root, hr]
        constructor
        · intro H y hy
          obtain ⟨i, rfl⟩ := accJoin_edge_to_root.mp hy
          simpa using H i
        · intro H i
          simpa using H _ (accJoin_edge_to_root.mpr ⟨i, rfl⟩)
    | orGate =>
        simp only [hk, RootSpec] at hr
        rw [joinValue_root, hr]
        constructor
        · rintro ⟨i, hi⟩
          exact ⟨_, accJoin_edge_to_root.mpr ⟨i, rfl⟩, by simpa using hi⟩
        · rintro ⟨y, hy, hvy⟩
          obtain ⟨i, rfl⟩ := accJoin_edge_to_root.mp hy
          exact ⟨i, by simpa using hvy⟩
    | notGate =>
        simp only [hk, RootSpec] at hr
        rw [joinValue_root, hr]
        constructor
        · rintro ⟨i, hi⟩
          exact ⟨_, accJoin_edge_to_root.mpr ⟨i, rfl⟩, by simpa using hi⟩
        · rintro ⟨y, hy, hvy⟩
          obtain ⟨i, rfl⟩ := accJoin_edge_to_root.mp hy
          exact ⟨i, by simpa using hvy⟩
    | modGate =>
        simp only [hk, RootSpec] at hr
        dsimp only
        rw [joinValue_root, hr, accJoin_card_root]

/-! ## Acceptance -/

theorem evalACC_accJoin_block (hf : ∀ i, WellFormedACC (f i))
    (hd : ∀ (i : Fin k) (a : Fin (f i).gateCount), (f i).layer a ≤ d)
    (hlit : ∀ (i : Fin n) (b : Bool), root ≠ .literal i b) (hnot : root ≠ .notGate)
    (x : Fin n → Bool) {r : Bool}
    (hr : RootSpec f root x (fun i => evalACC (f i) (hf i) x) r) :
    evalACC (accJoin f d root) (wellFormedACC_accJoin hf hd hlit hnot) x
      = joinValue f d root (fun i => evalACC (f i) (hf i) x) r := by
  have hval := accValuation_accJoin (f := f) (d := d) (root := root)
    (v := fun i => evalACC (f i) (hf i) x) (r := r)
    (fun i => (accValuation_iff_eq_evalACC (hf i)).mpr rfl) hr
  exact ((accValuation_iff_eq_evalACC (wellFormedACC_accJoin hf hd hlit hnot)).mp hval).symm

/-- An `OR` root accepts exactly when some block accepts. -/
theorem accAccepts_accJoin_or (hf : ∀ i, WellFormedACC (f i))
    (hd : ∀ (i : Fin k) (a : Fin (f i).gateCount), (f i).layer a ≤ d)
    (x : Fin n → Bool) :
    ACCAccepts (accJoin f d .orGate) x ↔ ∃ i, ACCAccepts (f i) x := by
  have hlit : ∀ (i : Fin n) (b : Bool), (ACCGate.orGate : ACCGate n m) ≠ .literal i b := by
    intro i b; simp
  have hnot : (ACCGate.orGate : ACCGate n m) ≠ .notGate := by simp
  classical
  set r : Bool := decide (∃ i, evalACC (f i) (hf i) x (f i).output = true) with hrdef
  have hr : RootSpec f (ACCGate.orGate : ACCGate n m) x (fun i => evalACC (f i) (hf i) x) r := by
    rw [RootSpec, hrdef]; simp
  have hr' : (r = true ↔ ∃ i, evalACC (f i) (hf i) x (f i).output = true) := by
    rw [hrdef]; simp
  rw [accAccepts_iff (wellFormedACC_accJoin hf hd hlit hnot) x]
  rw [evalACC_accJoin_block hf hd hlit hnot x (r := r) hr]
  rw [accJoin_output, joinValue_root]
  rw [hr']
  exact exists_congr fun i => (accAccepts_iff (hf i) x).symm

/-- An `AND` root accepts exactly when every block accepts. -/
theorem accAccepts_accJoin_and (hf : ∀ i, WellFormedACC (f i))
    (hd : ∀ (i : Fin k) (a : Fin (f i).gateCount), (f i).layer a ≤ d)
    (x : Fin n → Bool) :
    ACCAccepts (accJoin f d .andGate) x ↔ ∀ i, ACCAccepts (f i) x := by
  have hlit : ∀ (i : Fin n) (b : Bool), (ACCGate.andGate : ACCGate n m) ≠ .literal i b := by
    intro i b; simp
  have hnot : (ACCGate.andGate : ACCGate n m) ≠ .notGate := by simp
  classical
  set r : Bool := decide (∀ i, evalACC (f i) (hf i) x (f i).output = true) with hrdef
  have hr : RootSpec f (ACCGate.andGate : ACCGate n m) x (fun i => evalACC (f i) (hf i) x) r := by
    rw [RootSpec, hrdef]; simp
  have hr' : (r = true ↔ ∀ i, evalACC (f i) (hf i) x (f i).output = true) := by
    rw [hrdef]; simp
  rw [accAccepts_iff (wellFormedACC_accJoin hf hd hlit hnot) x]
  rw [evalACC_accJoin_block hf hd hlit hnot x (r := r) hr]
  rw [accJoin_output, joinValue_root]
  rw [hr']
  exact forall_congr' fun i => (accAccepts_iff (hf i) x).symm

open Classical in
/-- A `MOD` root accepts exactly when the number of accepting blocks is 0 modulo m. -/
theorem accAccepts_accJoin_mod (hf : ∀ i, WellFormedACC (f i))
    (hd : ∀ (i : Fin k) (a : Fin (f i).gateCount), (f i).layer a ≤ d)
    (x : Fin n → Bool) :
    ACCAccepts (accJoin f d .modGate) x ↔ (Finset.univ.filter fun i => ACCAccepts (f i) x).card % m
      = 0 := by
  have hlit : ∀ (i : Fin n) (b : Bool), (ACCGate.modGate : ACCGate n m) ≠ .literal i b := by
    intro i b; simp
  have hnot : (ACCGate.modGate : ACCGate n m) ≠ .notGate := by simp
  classical
  set r : Bool := decide
    ((Finset.univ.filter fun i => evalACC (f i) (hf i) x (f i).output = true).card % m = 0) with
    hrdef
  have hr : RootSpec f (ACCGate.modGate : ACCGate n m) x (fun i => evalACC (f i) (hf i) x) r := by
    rw [RootSpec, hrdef]; simp
  have hr' :
    (r = true ↔ (Finset.univ.filter fun i => evalACC (f i) (hf i) x (f i).output = true).card % m =
    0) := by
    rw [hrdef]; simp
  rw [accAccepts_iff (wellFormedACC_accJoin hf hd hlit hnot) x]
  rw [evalACC_accJoin_block hf hd hlit hnot x (r := r) hr]
  rw [accJoin_output, joinValue_root]
  rw [hr']
  have eq_filter : (Finset.univ.filter fun i => evalACC (f i) (hf i) x (f i).output = true) =
    Finset.univ.filter fun i => ACCAccepts (f i) x := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (accAccepts_iff (hf i) x).symm
  rw [eq_filter]

/-! ## Depth-two OR of ANDs -/

section OrAnd

variable {kk : Fin k → Nat}

/-- The depth-two, unbounded fan-in `OR`-of-`AND`s over a doubly indexed family
of ACC circuits: this is the shape produced by the blocking argument of §9. -/
def accOrAnd (g : (i : Fin k) → Fin (kk i) → ACCCircuit n m) (d : Nat) : ACCCircuit n m :=
  accJoin (fun i => accJoin (g i) d .andGate) (d + 1) .orGate

@[simp] theorem accOrAnd_gateCount (g : (i : Fin k) → Fin (kk i) → ACCCircuit n m) (d : Nat) :
    (accOrAnd g d).gateCount = (∑ i, ((∑ j, (g i j).gateCount) + 1)) + 1 := rfl

theorem wellFormedACC_accOrAnd {g : (i : Fin k) → Fin (kk i) → ACCCircuit n m}
    (hg : ∀ i j, WellFormedACC (g i j))
    (hd : ∀ i j (a : Fin (g i j).gateCount), (g i j).layer a ≤ d) :
    WellFormedACC (accOrAnd g d) := by
  have hlitA : ∀ (i : Fin n) (b : Bool), (ACCGate.andGate : ACCGate n m) ≠ .literal i b := by
    intro i b; simp
  have hnotA : (ACCGate.andGate : ACCGate n m) ≠ .notGate := by simp
  have hlitO : ∀ (i : Fin n) (b : Bool), (ACCGate.orGate : ACCGate n m) ≠ .literal i b := by
    intro i b; simp
  have hnotO : (ACCGate.orGate : ACCGate n m) ≠ .notGate := by simp
  exact wellFormedACC_accJoin
    (fun i => wellFormedACC_accJoin (hg i) (hd i) hlitA hnotA)
    (fun i => accJoin_layer_le (hd i)) hlitO hnotO

theorem accOrAnd_layer_le {g : (i : Fin k) → Fin (kk i) → ACCCircuit n m}
    (hd : ∀ i j (a : Fin (g i j).gateCount), (g i j).layer a ≤ d) :
    ∀ a, (accOrAnd g d).layer a ≤ d + 2 :=
  accJoin_layer_le (fun i => accJoin_layer_le (hd i))

/-- The depth-two `OR`-of-`AND`s accepts exactly when some `i` has all of its
conjuncts accepting. -/
theorem accAccepts_accOrAnd {g : (i : Fin k) → Fin (kk i) → ACCCircuit n m}
    (hg : ∀ i j, WellFormedACC (g i j))
    (hd : ∀ i j (a : Fin (g i j).gateCount), (g i j).layer a ≤ d) (x : Fin n → Bool) :
    ACCAccepts (accOrAnd g d) x ↔ ∃ i, ∀ j, ACCAccepts (g i j) x := by
  have hlitA : ∀ (i : Fin n) (b : Bool), (ACCGate.andGate : ACCGate n m) ≠ .literal i b := by
    intro i b; simp
  have hnotA : (ACCGate.andGate : ACCGate n m) ≠ .notGate := by simp
  rw [accOrAnd, accAccepts_accJoin_or
    (fun i => wellFormedACC_accJoin (hg i) (hd i) hlitA hnotA)
    (fun i => accJoin_layer_le (hd i)) x]
  exact exists_congr fun i => accAccepts_accJoin_and (hg i) (hd i) x

end OrAnd

end AllenderOQ3.Internal
