import AllenderOQ3.Internal.ACCSemantics

/-!
# ACC building blocks: the disjoint union combinator

This file provides the first assembly combinator on the ACC side: the *disjoint
union* `accUnion a b` of two ACC circuits with the same input arity and the same
modulus.  Gates of `a` are embedded on the left (`Fin.castAdd`), gates of `b` on
the right (`Fin.natAdd`), and no edge crosses between the two sides.  Layers are
inherited unchanged, so the layer-zero-iff-literal condition of `WellFormedACC`
holds on both sides simultaneously and no shifting is required.

The results here are:

* `wellFormedACC_accUnion` — well-formedness is preserved;
* `accUnion_layer_le` — the depth of the union is the max of the two depths;
* `accValuation_accUnion` — a valuation of the union is exactly a pair of
  valuations of the two sides;
* `evalACC_accUnion_left` / `evalACC_accUnion_right` — the canonical valuation of
  the union restricts to the canonical valuations of the sides;
* `accAccepts_accUnion` — the union (whose output is the output of `a`) accepts
  exactly the inputs accepted by `a`.

Everything is `sorry`-free.
-/

set_option autoImplicit false

namespace AllenderOQ3.Internal

variable {n m : Nat}

/-- The disjoint union of two ACC circuits: gates of `a` are placed on the left,
gates of `b` on the right, with no edges between the two sides.  The output gate
is the output gate of `a`. -/
def accUnion (a b : ACCCircuit n m) : ACCCircuit n m where
  gateCount := a.gateCount + b.gateCount
  output := Fin.castAdd b.gateCount a.output
  kind := Fin.addCases a.kind b.kind
  layer := Fin.addCases a.layer b.layer
  edge := fun u v =>
    Fin.addCases (motive := fun _ => Bool)
      (fun u' =>
        Fin.addCases (motive := fun _ => Bool)
          (fun v' => a.edge u' v') (fun _ => false) v)
      (fun u' =>
        Fin.addCases (motive := fun _ => Bool)
          (fun _ => false) (fun v' => b.edge u' v') v)
      u

@[simp] theorem accUnion_gateCount (a b : ACCCircuit n m) :
    (accUnion a b).gateCount = a.gateCount + b.gateCount := rfl

@[simp] theorem accUnion_output (a b : ACCCircuit n m) :
    (accUnion a b).output = Fin.castAdd b.gateCount a.output := rfl

@[simp] theorem accUnion_kind_left (a b : ACCCircuit n m) (g : Fin a.gateCount) :
    (accUnion a b).kind (Fin.castAdd b.gateCount g) = a.kind g := by
  simp [accUnion]

@[simp] theorem accUnion_kind_right (a b : ACCCircuit n m) (g : Fin b.gateCount) :
    (accUnion a b).kind (Fin.natAdd a.gateCount g) = b.kind g := by
  simp [accUnion]

@[simp] theorem accUnion_layer_left (a b : ACCCircuit n m) (g : Fin a.gateCount) :
    (accUnion a b).layer (Fin.castAdd b.gateCount g) = a.layer g := by
  simp [accUnion]

@[simp] theorem accUnion_layer_right (a b : ACCCircuit n m) (g : Fin b.gateCount) :
    (accUnion a b).layer (Fin.natAdd a.gateCount g) = b.layer g := by
  simp [accUnion]

@[simp] theorem accUnion_edge_ll (a b : ACCCircuit n m) (u v : Fin a.gateCount) :
    (accUnion a b).edge (Fin.castAdd b.gateCount u) (Fin.castAdd b.gateCount v)
      = a.edge u v := by
  simp [accUnion]

@[simp] theorem accUnion_edge_rr (a b : ACCCircuit n m) (u v : Fin b.gateCount) :
    (accUnion a b).edge (Fin.natAdd a.gateCount u) (Fin.natAdd a.gateCount v)
      = b.edge u v := by
  simp [accUnion]

@[simp] theorem accUnion_edge_lr (a b : ACCCircuit n m)
    (u : Fin a.gateCount) (v : Fin b.gateCount) :
    (accUnion a b).edge (Fin.castAdd b.gateCount u) (Fin.natAdd a.gateCount v)
      = false := by
  simp [accUnion]

@[simp] theorem accUnion_edge_rl (a b : ACCCircuit n m)
    (u : Fin b.gateCount) (v : Fin a.gateCount) :
    (accUnion a b).edge (Fin.natAdd a.gateCount u) (Fin.castAdd b.gateCount v)
      = false := by
  simp [accUnion]

/-- Incoming edges of a left gate come exactly from left gates. -/
theorem accUnion_edge_to_left {a b : ACCCircuit n m} {g : Fin a.gateCount}
    {h : Fin (accUnion a b).gateCount} :
    (accUnion a b).edge h (Fin.castAdd b.gateCount g) = true ↔
      ∃ h', h = Fin.castAdd b.gateCount h' ∧ a.edge h' g = true := by
  induction h using Fin.addCases with
  | left h' =>
      simp only [accUnion_edge_ll]
      constructor
      · intro he; exact ⟨h', rfl, he⟩
      · rintro ⟨h'', hEq, he⟩
        have : h'' = h' := by
          have := congrArg Fin.val hEq
          simpa [Fin.ext_iff] using this.symm
        subst this; exact he
  | right h' =>
      simp only [accUnion_edge_rl]
      constructor
      · intro he; exact absurd he (by simp)
      · rintro ⟨h'', hEq, _⟩
        exact absurd (congrArg Fin.val hEq) (by simp; omega)

/-- Incoming edges of a right gate come exactly from right gates. -/
theorem accUnion_edge_to_right {a b : ACCCircuit n m} {g : Fin b.gateCount}
    {h : Fin (accUnion a b).gateCount} :
    (accUnion a b).edge h (Fin.natAdd a.gateCount g) = true ↔
      ∃ h', h = Fin.natAdd a.gateCount h' ∧ b.edge h' g = true := by
  induction h using Fin.addCases with
  | left h' =>
      simp only [accUnion_edge_lr]
      constructor
      · intro he; exact absurd he (by simp)
      · rintro ⟨h'', hEq, _⟩
        exact absurd (congrArg Fin.val hEq) (by simp; omega)
  | right h' =>
      simp only [accUnion_edge_rr]
      constructor
      · intro he; exact ⟨h', rfl, he⟩
      · rintro ⟨h'', hEq, he⟩
        have : h'' = h' := by
          have := congrArg Fin.val hEq
          simpa [Fin.ext_iff] using this.symm
        subst this; exact he

/-- Well-formedness is preserved by disjoint union. -/
theorem wellFormedACC_accUnion {a b : ACCCircuit n m}
    (ha : WellFormedACC a) (hb : WellFormedACC b) : WellFormedACC (accUnion a b) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u v huv
    induction v using Fin.addCases with
    | left v' =>
        obtain ⟨u', rfl, he⟩ := accUnion_edge_to_left.mp huv
        simpa using ha.1 u' v' he
    | right v' =>
        obtain ⟨u', rfl, he⟩ := accUnion_edge_to_right.mp huv
        simpa using hb.1 u' v' he
  · intro g
    induction g using Fin.addCases with
    | left g' =>
        simpa using ha.2.1 g'
    | right g' =>
        simpa using hb.2.1 g'
  · intro g hg
    induction g using Fin.addCases with
    | left g' =>
        rw [accUnion_kind_left] at hg
        obtain ⟨h', hh', huniq⟩ := ha.2.2 g' hg
        refine ⟨Fin.castAdd b.gateCount h', by simpa using hh', ?_⟩
        intro y hy
        obtain ⟨y', rfl, hy'⟩ := accUnion_edge_to_left.mp hy
        exact congrArg _ (huniq y' hy')
    | right g' =>
        rw [accUnion_kind_right] at hg
        obtain ⟨h', hh', huniq⟩ := hb.2.2 g' hg
        refine ⟨Fin.natAdd a.gateCount h', by simpa using hh', ?_⟩
        intro y hy
        obtain ⟨y', rfl, hy'⟩ := accUnion_edge_to_right.mp hy
        exact congrArg _ (huniq y' hy')

/-- The depth of a disjoint union is bounded by a common bound for the two
sides. -/
theorem accUnion_layer_le {a b : ACCCircuit n m} {d : Nat}
    (hda : ∀ g, a.layer g ≤ d) (hdb : ∀ g, b.layer g ≤ d) :
    ∀ g, (accUnion a b).layer g ≤ d := by
  intro g
  induction g using Fin.addCases with
  | left g' => simpa using hda g'
  | right g' => simpa using hdb g'

/-- The inputs of a left `modGate` on the union are in bijection with its inputs
on the left circuit, so the two counts agree. -/
theorem accUnion_card_left {a b : ACCCircuit n m} {g : Fin a.gateCount}
    (va : Fin a.gateCount → Bool) (vb : Fin b.gateCount → Bool) :
    (Finset.univ.filter (fun h : Fin (accUnion a b).gateCount =>
        (accUnion a b).edge h (Fin.castAdd b.gateCount g) = true ∧
          Fin.addCases va vb h = true)).card
      = (Finset.univ.filter (fun h : Fin a.gateCount =>
          a.edge h g = true ∧ va h = true)).card := by
  refine (Finset.card_bij (fun h _ => Fin.castAdd b.gateCount h) ?_ ?_ ?_).symm
  · intro h hh
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hh ⊢
    simpa using hh
  · intro h₁ _ h₂ _ hEq
    have := congrArg Fin.val hEq
    simpa [Fin.ext_iff] using this
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    obtain ⟨y', rfl, hy'⟩ := accUnion_edge_to_left.mp hy.1
    refine ⟨y', ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hy', ?_⟩
    simpa using hy.2

/-- The inputs of a right `modGate` on the union are in bijection with its inputs
on the right circuit, so the two counts agree. -/
theorem accUnion_card_right {a b : ACCCircuit n m} {g : Fin b.gateCount}
    (va : Fin a.gateCount → Bool) (vb : Fin b.gateCount → Bool) :
    (Finset.univ.filter (fun h : Fin (accUnion a b).gateCount =>
        (accUnion a b).edge h (Fin.natAdd a.gateCount g) = true ∧
          Fin.addCases va vb h = true)).card
      = (Finset.univ.filter (fun h : Fin b.gateCount =>
          b.edge h g = true ∧ vb h = true)).card := by
  refine (Finset.card_bij (fun h _ => Fin.natAdd a.gateCount h) ?_ ?_ ?_).symm
  · intro h hh
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hh ⊢
    simpa using hh
  · intro h₁ _ h₂ _ hEq
    have := congrArg Fin.val hEq
    simpa [Fin.ext_iff] using this
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    obtain ⟨y', rfl, hy'⟩ := accUnion_edge_to_right.mp hy.1
    refine ⟨y', ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hy', ?_⟩
    simpa using hy.2

/-- Gluing two valuations gives a valuation of the disjoint union. -/
theorem accValuation_accUnion {a b : ACCCircuit n m} {x : Fin n → Bool}
    {va : Fin a.gateCount → Bool} {vb : Fin b.gateCount → Bool}
    (hva : ACCValuation a x va) (hvb : ACCValuation b x vb) :
    ACCValuation (accUnion a b) x (Fin.addCases va vb) := by
  intro g
  induction g using Fin.addCases with
  | left g' =>
      have hg := hva g'
      rw [accUnion_kind_left]
      cases hk : a.kind g' with
      | literal i bneg =>
          simp only [hk] at hg
          simpa using hg
      | andGate =>
          simp only [hk] at hg
          simp only [Fin.addCases_left]
          rw [hg]
          constructor
          · intro H y hy
            obtain ⟨y', rfl, hy'⟩ := accUnion_edge_to_left.mp hy
            simpa using H y' hy'
          · intro H y' hy'
            have := H (Fin.castAdd b.gateCount y') (by simpa using hy')
            simpa using this
      | orGate =>
          simp only [hk] at hg
          simp only [Fin.addCases_left]
          rw [hg]
          constructor
          · rintro ⟨y', hy', hv⟩
            exact ⟨Fin.castAdd b.gateCount y', by simpa using hy', by simpa using hv⟩
          · rintro ⟨y, hy, hv⟩
            obtain ⟨y', rfl, hy'⟩ := accUnion_edge_to_left.mp hy
            exact ⟨y', hy', by simpa using hv⟩
      | notGate =>
          simp only [hk] at hg
          simp only [Fin.addCases_left]
          rw [hg]
          constructor
          · rintro ⟨y', hy', hv⟩
            exact ⟨Fin.castAdd b.gateCount y', by simpa using hy', by simpa using hv⟩
          · rintro ⟨y, hy, hv⟩
            obtain ⟨y', rfl, hy'⟩ := accUnion_edge_to_left.mp hy
            exact ⟨y', hy', by simpa using hv⟩
      | modGate =>
          simp only [hk] at hg
          simp only [Fin.addCases_left]
          rw [hg, accUnion_card_left va vb]
  | right g' =>
      have hg := hvb g'
      rw [accUnion_kind_right]
      cases hk : b.kind g' with
      | literal i bneg =>
          simp only [hk] at hg
          simpa using hg
      | andGate =>
          simp only [hk] at hg
          simp only [Fin.addCases_right]
          rw [hg]
          constructor
          · intro H y hy
            obtain ⟨y', rfl, hy'⟩ := accUnion_edge_to_right.mp hy
            simpa using H y' hy'
          · intro H y' hy'
            have := H (Fin.natAdd a.gateCount y') (by simpa using hy')
            simpa using this
      | orGate =>
          simp only [hk] at hg
          simp only [Fin.addCases_right]
          rw [hg]
          constructor
          · rintro ⟨y', hy', hv⟩
            exact ⟨Fin.natAdd a.gateCount y', by simpa using hy', by simpa using hv⟩
          · rintro ⟨y, hy, hv⟩
            obtain ⟨y', rfl, hy'⟩ := accUnion_edge_to_right.mp hy
            exact ⟨y', hy', by simpa using hv⟩
      | notGate =>
          simp only [hk] at hg
          simp only [Fin.addCases_right]
          rw [hg]
          constructor
          · rintro ⟨y', hy', hv⟩
            exact ⟨Fin.natAdd a.gateCount y', by simpa using hy', by simpa using hv⟩
          · rintro ⟨y, hy, hv⟩
            obtain ⟨y', rfl, hy'⟩ := accUnion_edge_to_right.mp hy
            exact ⟨y', hy', by simpa using hv⟩
      | modGate =>
          simp only [hk] at hg
          simp only [Fin.addCases_right]
          rw [hg, accUnion_card_right va vb]

/-- The canonical valuation of the union restricts to that of the left side. -/
theorem evalACC_accUnion_left {a b : ACCCircuit n m}
    (ha : WellFormedACC a) (hb : WellFormedACC b) (x : Fin n → Bool)
    (g : Fin a.gateCount) :
    evalACC (accUnion a b) (wellFormedACC_accUnion ha hb) x
        (Fin.castAdd b.gateCount g) = evalACC a ha x g := by
  have hval := accValuation_accUnion
    (Classical.choose_spec (accValuation_exists a ha x))
    (Classical.choose_spec (accValuation_exists b hb x))
  have heq := (accValuation_iff_eq_evalACC (wellFormedACC_accUnion ha hb)).mp hval
  have := congrFun heq (Fin.castAdd b.gateCount g)
  simpa [evalACC] using this.symm

/-- The canonical valuation of the union restricts to that of the right side. -/
theorem evalACC_accUnion_right {a b : ACCCircuit n m}
    (ha : WellFormedACC a) (hb : WellFormedACC b) (x : Fin n → Bool)
    (g : Fin b.gateCount) :
    evalACC (accUnion a b) (wellFormedACC_accUnion ha hb) x
        (Fin.natAdd a.gateCount g) = evalACC b hb x g := by
  have hval := accValuation_accUnion
    (Classical.choose_spec (accValuation_exists a ha x))
    (Classical.choose_spec (accValuation_exists b hb x))
  have heq := (accValuation_iff_eq_evalACC (wellFormedACC_accUnion ha hb)).mp hval
  have := congrFun heq (Fin.natAdd a.gateCount g)
  simpa [evalACC] using this.symm

/-- Since the output of the union is the output of `a`, the union accepts exactly
what `a` accepts. -/
theorem accAccepts_accUnion {a b : ACCCircuit n m}
    (ha : WellFormedACC a) (hb : WellFormedACC b) (x : Fin n → Bool) :
    ACCAccepts (accUnion a b) x ↔ ACCAccepts a x := by
  rw [accAccepts_iff (wellFormedACC_accUnion ha hb) x, accAccepts_iff ha x,
    accUnion_output, evalACC_accUnion_left ha hb x]

/-- Shift layers of an ACC circuit by a constant, leaving literals at layer 0. -/
def accShiftLayers (c : ACCCircuit n m) (shift : Nat) : ACCCircuit n m where
  gateCount := c.gateCount
  output := c.output
  kind := c.kind
  layer := fun g => if c.layer g = 0 then 0 else c.layer g + shift
  edge := c.edge

@[simp] theorem accShiftLayers_gateCount (c : ACCCircuit n m) (shift : Nat) :
    (accShiftLayers c shift).gateCount = c.gateCount := rfl

@[simp] theorem accShiftLayers_output (c : ACCCircuit n m) (shift : Nat) :
    (accShiftLayers c shift).output = c.output := rfl

@[simp] theorem accShiftLayers_kind (c : ACCCircuit n m) (shift : Nat) (g : Fin c.gateCount) :
    (accShiftLayers c shift).kind g = c.kind g := rfl

@[simp] theorem accShiftLayers_layer (c : ACCCircuit n m) (shift : Nat) (g : Fin c.gateCount) :
    (accShiftLayers c shift).layer g = if c.layer g = 0 then 0 else c.layer g + shift := rfl

@[simp] theorem accShiftLayers_edge (c : ACCCircuit n m) (shift : Nat) (u v : Fin c.gateCount) :
    (accShiftLayers c shift).edge u v = c.edge u v := rfl

theorem wellFormedACC_accShiftLayers {c : ACCCircuit n m} (hc : WellFormedACC c) (shift : Nat) :
    WellFormedACC (accShiftLayers c shift) := by
  obtain ⟨h1, h2, h3⟩ := hc
  refine ⟨?_, ?_, ?_⟩
  · intro u v huv
    have hlt := h1 u v huv
    simp only [accShiftLayers_layer]
    split <;> split <;> omega
  · intro g
    rw [accShiftLayers_layer, accShiftLayers_kind]
    constructor
    · intro h
      apply (h2 g).mp
      by_contra hl
      rw [if_neg hl] at h
      omega
    · intro h
      rw [if_pos ((h2 g).mpr h)]
  · intro g hg
    simp only [accShiftLayers_kind] at hg
    simpa only [accShiftLayers_edge] using h3 g hg

theorem accShiftLayers_layer_le {c : ACCCircuit n m} {d : Nat} (hc : ∀ g, c.layer g ≤ d)
  (shift : Nat) :
    ∀ g, (accShiftLayers c shift).layer g ≤ d + shift := by
  intro g
  rw [accShiftLayers_layer]
  have := hc g
  split <;> omega

theorem evalACC_accShiftLayers {c : ACCCircuit n m} (hc : WellFormedACC c) (shift : Nat)
    (x : Fin n → Bool) (g : Fin c.gateCount) :
    evalACC (accShiftLayers c shift) (wellFormedACC_accShiftLayers hc shift) x g = evalACC c hc x g
      := by
  have hval : ACCValuation (accShiftLayers c shift) x (evalACC c hc x) :=
    Classical.choose_spec (accValuation_exists c hc x)
  have heq := (accValuation_iff_eq_evalACC (wellFormedACC_accShiftLayers hc shift)).mp hval
  exact congrFun heq.symm g

theorem accAccepts_accShiftLayers {c : ACCCircuit n m} (hc : WellFormedACC c) (shift : Nat)
  (x : Fin n → Bool) :
    ACCAccepts (accShiftLayers c shift) x ↔ ACCAccepts c x := by
  rw [accAccepts_iff (wellFormedACC_accShiftLayers hc shift) x, accAccepts_iff hc x,
    accShiftLayers_output, evalACC_accShiftLayers hc shift x]

/-- Relabel variables in an ACC circuit. -/
def accRelabel {n' : Nat} (c : ACCCircuit n m) (f : Fin n → Fin n') : ACCCircuit n' m where
  gateCount := c.gateCount
  output := c.output
  kind := fun g => match c.kind g with
    | .literal i b => .literal (f i) b
    | .andGate => .andGate
    | .orGate => .orGate
    | .notGate => .notGate
    | .modGate => .modGate
  layer := c.layer
  edge := c.edge

@[simp] theorem accRelabel_gateCount {n' : Nat} (c : ACCCircuit n m) (f : Fin n → Fin n') :
    (accRelabel c f).gateCount = c.gateCount := rfl

@[simp] theorem accRelabel_output {n' : Nat} (c : ACCCircuit n m) (f : Fin n → Fin n') :
    (accRelabel c f).output = c.output := rfl

@[simp] theorem accRelabel_layer {n' : Nat} (c : ACCCircuit n m) (f : Fin n → Fin n')
  (g : Fin c.gateCount) :
    (accRelabel c f).layer g = c.layer g := rfl

@[simp] theorem accRelabel_edge {n' : Nat} (c : ACCCircuit n m) (f : Fin n → Fin n')
  (u v : Fin c.gateCount) :
    (accRelabel c f).edge u v = c.edge u v := rfl

/-- Relabelling turns a `notGate` into a `notGate` and nothing else. -/
theorem accRelabel_kind_notGate {n' : Nat} (c : ACCCircuit n m) (f : Fin n → Fin n')
    (g : Fin c.gateCount) :
    (accRelabel c f).kind g = .notGate ↔ c.kind g = .notGate := by
  constructor
  · intro h
    rcases hk : c.kind g with ⟨i, b⟩ | _ | _ | _ | _ <;>
      simp only [accRelabel, hk] at h ⊢ <;> simp_all
  · intro h; simp only [accRelabel, h]

/-- Relabelling turns literals into literals and nothing else. -/
theorem accRelabel_kind_literal {n' : Nat} (c : ACCCircuit n m) (f : Fin n → Fin n')
    (g : Fin c.gateCount) :
    (∃ (i : Fin n') (b : Bool), (accRelabel c f).kind g = .literal i b) ↔
      ∃ (i : Fin n) (b : Bool), c.kind g = .literal i b := by
  constructor
  · rintro ⟨i, b, h⟩
    rcases hk : c.kind g with ⟨i', b'⟩ | _ | _ | _ | _ <;>
      simp only [accRelabel, hk] at h <;> simp_all
  · rintro ⟨i, b, h⟩
    exact ⟨f i, b, by simp only [accRelabel, h]⟩

theorem wellFormedACC_accRelabel {n' : Nat} {c : ACCCircuit n m} (hc : WellFormedACC c)
  (f : Fin n → Fin n') :
    WellFormedACC (accRelabel c f) := by
  refine ⟨hc.1, ?_, ?_⟩
  · intro g
    rw [accRelabel_layer, accRelabel_kind_literal]
    exact hc.2.1 g
  · intro g hg
    exact hc.2.2 g ((accRelabel_kind_notGate c f g).mp hg)

theorem accRelabel_layer_le {n' : Nat} {c : ACCCircuit n m} {d : Nat} (hc : ∀ g, c.layer g ≤ d)
  (f : Fin n → Fin n') :
    ∀ g, (accRelabel c f).layer g ≤ d := by
  intro g
  rw [accRelabel_layer]
  exact hc g

/-- A valuation of `c` on the relabelled input `x ∘ f` is a valuation of `accRelabel c f` on `x`. -/
theorem accValuation_accRelabel {n' : Nat} {c : ACCCircuit n m} (f : Fin n → Fin n')
    (x : Fin n' → Bool) (v : Fin c.gateCount → Bool) (hv : ACCValuation c (x ∘ f) v) :
    ACCValuation (accRelabel c f) x v := by
  intro g
  have hg := hv g
  rcases hk : c.kind g with ⟨i, b⟩ | _ | _ | _ | _ <;>
    simp only [hk] at hg <;> simp only [accRelabel, hk] <;>
    simpa [Function.comp] using hg

theorem evalACC_accRelabel {n' : Nat} {c : ACCCircuit n m} (hc : WellFormedACC c)
  (f : Fin n → Fin n')
    (x : Fin n' → Bool) (g : Fin c.gateCount) :
    evalACC (accRelabel c f) (wellFormedACC_accRelabel hc f) x g = evalACC c hc (x ∘ f) g := by
  have hval : ACCValuation (accRelabel c f) x (evalACC c hc (x ∘ f)) :=
    accValuation_accRelabel f x _ (Classical.choose_spec (accValuation_exists c hc (x ∘ f)))
  have heq := (accValuation_iff_eq_evalACC (wellFormedACC_accRelabel hc f)).mp hval
  exact congrFun heq.symm g

theorem accAccepts_accRelabel {n' : Nat} {c : ACCCircuit n m} (hc : WellFormedACC c)
  (f : Fin n → Fin n') (x : Fin n' → Bool) :
    ACCAccepts (accRelabel c f) x ↔ ACCAccepts c (x ∘ f) := by
  rw [accAccepts_iff (wellFormedACC_accRelabel hc f) x, accAccepts_iff hc (x ∘ f),
    accRelabel_output, evalACC_accRelabel hc f x]

/-- Output-for-literal substitution. Replaces occurrences of `u` as an input in `c` with
  `b.output`. -/
def accGraft (c b : ACCCircuit n m) (u : Fin c.gateCount) : ACCCircuit n m where
  gateCount := c.gateCount + b.gateCount
  output := Fin.castAdd b.gateCount c.output
  kind := Fin.addCases c.kind b.kind
  layer := Fin.addCases c.layer b.layer
  edge := fun x y =>
    Fin.addCases (motive := fun _ => Bool)
      (fun x' => Fin.addCases (motive := fun _ => Bool)
        (fun y' => if x' = u then false else c.edge x' y')
        (fun _ => false) y)
      (fun x' => Fin.addCases (motive := fun _ => Bool)
        (fun y' => if x' = b.output then c.edge u y' else false)
        (fun y' => b.edge x' y') y)
      x

@[simp] theorem accGraft_gateCount (c b : ACCCircuit n m) (u : Fin c.gateCount) :
    (accGraft c b u).gateCount = c.gateCount + b.gateCount := rfl

@[simp] theorem accGraft_output (c b : ACCCircuit n m) (u : Fin c.gateCount) :
    (accGraft c b u).output = Fin.castAdd b.gateCount c.output := rfl

@[simp] theorem accGraft_kind_left (c b : ACCCircuit n m) (u g : Fin c.gateCount) :
    (accGraft c b u).kind (Fin.castAdd b.gateCount g) = c.kind g := by simp [accGraft]

@[simp] theorem accGraft_kind_right (c b : ACCCircuit n m) (u : Fin c.gateCount)
    (g : Fin b.gateCount) :
    (accGraft c b u).kind (Fin.natAdd c.gateCount g) = b.kind g := by simp [accGraft]

@[simp] theorem accGraft_layer_left (c b : ACCCircuit n m) (u g : Fin c.gateCount) :
    (accGraft c b u).layer (Fin.castAdd b.gateCount g) = c.layer g := by simp [accGraft]

@[simp] theorem accGraft_layer_right (c b : ACCCircuit n m) (u : Fin c.gateCount)
    (g : Fin b.gateCount) :
    (accGraft c b u).layer (Fin.natAdd c.gateCount g) = b.layer g := by simp [accGraft]

@[simp] theorem accGraft_edge_ll (c b : ACCCircuit n m) (u x y : Fin c.gateCount) :
    (accGraft c b u).edge (Fin.castAdd b.gateCount x) (Fin.castAdd b.gateCount y)
      = if x = u then false else c.edge x y := by simp [accGraft]

@[simp] theorem accGraft_edge_lr (c b : ACCCircuit n m) (u x : Fin c.gateCount)
    (y : Fin b.gateCount) :
    (accGraft c b u).edge (Fin.castAdd b.gateCount x) (Fin.natAdd c.gateCount y) = false := by
  simp [accGraft]

@[simp] theorem accGraft_edge_rl (c b : ACCCircuit n m) (u : Fin c.gateCount) (x : Fin b.gateCount)
    (y : Fin c.gateCount) :
    (accGraft c b u).edge (Fin.natAdd c.gateCount x) (Fin.castAdd b.gateCount y)
      = if x = b.output then c.edge u y else false := by simp [accGraft]

@[simp] theorem accGraft_edge_rr (c b : ACCCircuit n m) (u : Fin c.gateCount)
    (x y : Fin b.gateCount) :
    (accGraft c b u).edge (Fin.natAdd c.gateCount x) (Fin.natAdd c.gateCount y) = b.edge x y := by
  simp [accGraft]

/-- Incoming edges of a left gate: either an old edge of `c` not coming from `u`, or the new
edge coming from the output of the grafted circuit `b` (in place of an edge from `u`). -/
theorem accGraft_edge_to_left {c b : ACCCircuit n m} {u : Fin c.gateCount} {g : Fin c.gateCount}
    {h : Fin (accGraft c b u).gateCount} :
    (accGraft c b u).edge h (Fin.castAdd b.gateCount g) = true ↔
      (∃ h', h = Fin.castAdd b.gateCount h' ∧ h' ≠ u ∧ c.edge h' g = true) ∨
        (h = Fin.natAdd c.gateCount b.output ∧ c.edge u g = true) := by
  induction h using Fin.addCases with
  | left h' =>
      simp only [accGraft_edge_ll]
      constructor
      · intro he
        split at he
        · exact absurd he (by simp)
        · exact Or.inl ⟨h', rfl, by assumption, he⟩
      · rintro (⟨h'', hEq, hne, he⟩ | ⟨hEq, _⟩)
        · have : h'' = h' := by
            have := congrArg Fin.val hEq
            simpa [Fin.ext_iff] using this.symm
          subst this
          rw [if_neg hne]; exact he
        · exact absurd (congrArg Fin.val hEq) (by simp; omega)
  | right h' =>
      simp only [accGraft_edge_rl]
      constructor
      · intro he
        split at he
        · refine Or.inr ⟨?_, he⟩
          subst_vars; rfl
        · exact absurd he (by simp)
      · rintro (⟨h'', hEq, _, _⟩ | ⟨hEq, he⟩)
        · exact absurd (congrArg Fin.val hEq) (by simp; omega)
        · have : h' = b.output := by
            have := congrArg Fin.val hEq
            simpa [Fin.ext_iff] using this
          subst this
          rw [if_pos rfl]; exact he

/-- Incoming edges of a right gate come exactly from right gates. -/
theorem accGraft_edge_to_right {c b : ACCCircuit n m} {u : Fin c.gateCount} {g : Fin b.gateCount}
    {h : Fin (accGraft c b u).gateCount} :
    (accGraft c b u).edge h (Fin.natAdd c.gateCount g) = true ↔
      ∃ h', h = Fin.natAdd c.gateCount h' ∧ b.edge h' g = true := by
  induction h using Fin.addCases with
  | left h' =>
      simp only [accGraft_edge_lr]
      constructor
      · intro he; exact absurd he (by simp)
      · rintro ⟨h'', hEq, _⟩
        exact absurd (congrArg Fin.val hEq) (by simp; omega)
  | right h' =>
      simp only [accGraft_edge_rr]
      constructor
      · intro he; exact ⟨h', rfl, he⟩
      · rintro ⟨h'', hEq, he⟩
        have : h'' = h' := by
          have := congrArg Fin.val hEq
          simpa [Fin.ext_iff] using this.symm
        subst this; exact he

theorem wellFormedACC_accGraft {c b : ACCCircuit n m} (hc : WellFormedACC c) (hb : WellFormedACC b)
    (u : Fin c.gateCount) (h_layer : ∀ y, c.edge u y = true → b.layer b.output < c.layer y) :
    WellFormedACC (accGraft c b u) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy
    induction y using Fin.addCases with
    | left y' =>
        rcases accGraft_edge_to_left.mp hxy with ⟨x', rfl, _, he⟩ | ⟨rfl, he⟩
        · simpa using hc.1 x' y' he
        · simpa using h_layer y' he
    | right y' =>
        obtain ⟨x', rfl, he⟩ := accGraft_edge_to_right.mp hxy
        simpa using hb.1 x' y' he
  · intro g
    induction g using Fin.addCases with
    | left g' => simpa using hc.2.1 g'
    | right g' => simpa using hb.2.1 g'
  · intro g hg
    induction g using Fin.addCases with
    | left g' =>
        rw [accGraft_kind_left] at hg
        obtain ⟨h', hh', huniq⟩ := hc.2.2 g' hg
        by_cases hu : h' = u
        · subst hu
          refine
            ⟨Fin.natAdd c.gateCount b.output, accGraft_edge_to_left.mpr (Or.inr ⟨rfl, hh'⟩), ?_⟩
          intro y hy
          rcases accGraft_edge_to_left.mp hy with ⟨y', rfl, hne, hey⟩ | ⟨rfl, _⟩
          · exact absurd (huniq y' hey) hne
          · rfl
        · refine ⟨Fin.castAdd b.gateCount h',
            accGraft_edge_to_left.mpr (Or.inl ⟨h', rfl, hu, hh'⟩), ?_⟩
          intro y hy
          rcases accGraft_edge_to_left.mp hy with ⟨y', rfl, _, hey⟩ | ⟨rfl, hey⟩
          · exact congrArg _ (huniq y' hey)
          · exact absurd (huniq u hey) (fun h => hu h.symm)
    | right g' =>
        rw [accGraft_kind_right] at hg
        obtain ⟨h', hh', huniq⟩ := hb.2.2 g' hg
        refine ⟨Fin.natAdd c.gateCount h', accGraft_edge_to_right.mpr ⟨h', rfl, hh'⟩, ?_⟩
        intro y hy
        obtain ⟨y', rfl, hy'⟩ := accGraft_edge_to_right.mp hy
        exact congrArg _ (huniq y' hy')

theorem accGraft_layer_le {c b : ACCCircuit n m} {d : Nat}
    (hc : ∀ g, c.layer g ≤ d) (hb : ∀ g, b.layer g ≤ d) (u : Fin c.gateCount) :
    ∀ g, (accGraft c b u).layer g ≤ d := by
  intro g
  induction g using Fin.addCases with
  | left g' => simpa [accGraft] using hc g'
  | right g' => simpa [accGraft] using hb g'

/-- Counting inputs of a right gate of a graft: they are exactly the inputs inside `b`. -/
theorem accGraft_card_right {c b : ACCCircuit n m} {u : Fin c.gateCount} {g : Fin b.gateCount}
    (V : Fin (accGraft c b u).gateCount → Bool) :
    (Finset.univ.filter (fun h : Fin (accGraft c b u).gateCount =>
        (accGraft c b u).edge h (Fin.natAdd c.gateCount g) = true ∧ V h = true)).card
      = (Finset.univ.filter (fun h : Fin b.gateCount =>
          b.edge h g = true ∧ V (Fin.natAdd c.gateCount h) = true)).card := by
  refine (Finset.card_bij (fun h _ => Fin.natAdd c.gateCount h) ?_ ?_ ?_).symm
  · intro h hh
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hh ⊢
    simpa using hh
  · intro h₁ _ h₂ _ hEq
    have := congrArg Fin.val hEq
    simpa [Fin.ext_iff] using this
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    obtain ⟨y', rfl, hy'⟩ := accGraft_edge_to_right.mp hy.1
    exact ⟨y', by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hy', hy.2⟩, rfl⟩

/-- Counting inputs of a left gate of a graft: the input `u` is replaced by `b.output`, whose
value agrees with that of `u` by hypothesis, so the count is unchanged. -/
theorem accGraft_card_left {c b : ACCCircuit n m} {u : Fin c.gateCount} {g : Fin c.gateCount}
    {vc : Fin c.gateCount → Bool} {vb : Fin b.gateCount → Bool} (hx : vc u = vb b.output) :
    (Finset.univ.filter (fun h : Fin (accGraft c b u).gateCount =>
        (accGraft c b u).edge h (Fin.castAdd b.gateCount g) = true ∧
          Fin.addCases vc vb h = true)).card
      = (Finset.univ.filter (fun h : Fin c.gateCount =>
          c.edge h g = true ∧ vc h = true)).card := by
  refine (Finset.card_bij
    (fun h _ => if h = u then Fin.natAdd c.gateCount b.output else Fin.castAdd b.gateCount h)
    ?_ ?_ ?_).symm
  · intro h hh
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hh ⊢
    by_cases hu : h = u
    · subst hu
      simp only
      refine ⟨accGraft_edge_to_left.mpr (Or.inr ⟨rfl, hh.1⟩), ?_⟩
      simpa [← hx] using hh.2
    · simp only [if_neg hu]
      exact ⟨accGraft_edge_to_left.mpr (Or.inl ⟨h, rfl, hu, hh.1⟩), by simpa using hh.2⟩
  · intro h₁ _ h₂ _ hEq
    dsimp only at hEq
    by_cases h1u : h₁ = u <;> by_cases h2u : h₂ = u
    · rw [h1u, h2u]
    · rw [if_pos h1u, if_neg h2u] at hEq
      exact absurd (congrArg Fin.val hEq) (by simp; omega)
    · rw [if_neg h1u, if_pos h2u] at hEq
      exact absurd (congrArg Fin.val hEq) (by simp; omega)
    · rw [if_neg h1u, if_neg h2u] at hEq
      have := congrArg Fin.val hEq
      simpa [Fin.ext_iff] using this
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    rcases accGraft_edge_to_left.mp hy.1 with ⟨y', rfl, hne, hey⟩ | ⟨rfl, hey⟩
    · refine ⟨y', ?_, by simp [hne]⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hey, by simpa using hy.2⟩
    · refine ⟨u, ?_, by simp⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hey, ?_⟩
      rw [hx]
      simpa using hy.2

/-- Gluing a valuation of `c` and a valuation of `b` that agree at the graft point gives a
valuation of the graft. -/
theorem accValuation_accGraft {c b : ACCCircuit n m} {u : Fin c.gateCount} {x : Fin n → Bool}
    {vc : Fin c.gateCount → Bool} {vb : Fin b.gateCount → Bool}
    (hvc : ACCValuation c x vc) (hvb : ACCValuation b x vb) (hx : vc u = vb b.output) :
    ACCValuation (accGraft c b u) x (Fin.addCases vc vb) := by
  intro G
  induction G using Fin.addCases with
  | left g =>
      have hg := hvc g
      rw [accGraft_kind_left]
      cases hk : c.kind g with
      | literal i bneg =>
          simp only [hk] at hg
          simpa using hg
      | andGate =>
          simp only [hk] at hg
          simp only [Fin.addCases_left]
          rw [hg]
          constructor
          · intro H y hy
            rcases accGraft_edge_to_left.mp hy with ⟨y', rfl, _, hey⟩ | ⟨rfl, hey⟩
            · simpa using H y' hey
            · simpa [← hx] using H u hey
          · intro H y' hy'
            by_cases hu : y' = u
            · subst hu
              have := H (Fin.natAdd c.gateCount b.output)
                (accGraft_edge_to_left.mpr (Or.inr ⟨rfl, hy'⟩))
              simpa [hx] using this
            · have := H (Fin.castAdd b.gateCount y')
                (accGraft_edge_to_left.mpr (Or.inl ⟨y', rfl, hu, hy'⟩))
              simpa using this
      | orGate =>
          simp only [hk] at hg
          simp only [Fin.addCases_left]
          rw [hg]
          constructor
          · rintro ⟨y', hy', hv⟩
            by_cases hu : y' = u
            · subst hu
              exact ⟨Fin.natAdd c.gateCount b.output,
                accGraft_edge_to_left.mpr (Or.inr ⟨rfl, hy'⟩), by simpa [← hx] using hv⟩
            · exact ⟨Fin.castAdd b.gateCount y',
                accGraft_edge_to_left.mpr (Or.inl ⟨y', rfl, hu, hy'⟩), by simpa using hv⟩
          · rintro ⟨y, hy, hv⟩
            rcases accGraft_edge_to_left.mp hy with ⟨y', rfl, _, hey⟩ | ⟨rfl, hey⟩
            · exact ⟨y', hey, by simpa using hv⟩
            · exact ⟨u, hey, by simpa [hx] using hv⟩
      | notGate =>
          simp only [hk] at hg
          simp only [Fin.addCases_left]
          rw [hg]
          constructor
          · rintro ⟨y', hy', hv⟩
            by_cases hu : y' = u
            · subst hu
              exact ⟨Fin.natAdd c.gateCount b.output,
                accGraft_edge_to_left.mpr (Or.inr ⟨rfl, hy'⟩), by simpa [← hx] using hv⟩
            · exact ⟨Fin.castAdd b.gateCount y',
                accGraft_edge_to_left.mpr (Or.inl ⟨y', rfl, hu, hy'⟩), by simpa using hv⟩
          · rintro ⟨y, hy, hv⟩
            rcases accGraft_edge_to_left.mp hy with ⟨y', rfl, _, hey⟩ | ⟨rfl, hey⟩
            · exact ⟨y', hey, by simpa using hv⟩
            · exact ⟨u, hey, by simpa [hx] using hv⟩
      | modGate =>
          simp only [hk] at hg
          simp only [Fin.addCases_left]
          rw [hg, accGraft_card_left hx]
  | right g =>
      have hg := hvb g
      rw [accGraft_kind_right]
      cases hk : b.kind g with
      | literal i bneg =>
          simp only [hk] at hg
          simpa using hg
      | andGate =>
          simp only [hk] at hg
          simp only [Fin.addCases_right]
          rw [hg]
          constructor
          · intro H y hy
            obtain ⟨y', rfl, hey⟩ := accGraft_edge_to_right.mp hy
            simpa using H y' hey
          · intro H y' hy'
            have := H (Fin.natAdd c.gateCount y') (accGraft_edge_to_right.mpr ⟨y', rfl, hy'⟩)
            simpa using this
      | orGate =>
          simp only [hk] at hg
          simp only [Fin.addCases_right]
          rw [hg]
          constructor
          · rintro ⟨y', hy', hv⟩
            exact ⟨Fin.natAdd c.gateCount y', accGraft_edge_to_right.mpr ⟨y', rfl, hy'⟩,
              by simpa using hv⟩
          · rintro ⟨y, hy, hv⟩
            obtain ⟨y', rfl, hey⟩ := accGraft_edge_to_right.mp hy
            exact ⟨y', hey, by simpa using hv⟩
      | notGate =>
          simp only [hk] at hg
          simp only [Fin.addCases_right]
          rw [hg]
          constructor
          · rintro ⟨y', hy', hv⟩
            exact ⟨Fin.natAdd c.gateCount y', accGraft_edge_to_right.mpr ⟨y', rfl, hy'⟩,
              by simpa using hv⟩
          · rintro ⟨y, hy, hv⟩
            obtain ⟨y', rfl, hey⟩ := accGraft_edge_to_right.mp hy
            exact ⟨y', hey, by simpa using hv⟩
      | modGate =>
          simp only [hk] at hg
          simp only [Fin.addCases_right]
          rw [hg, accGraft_card_right (Fin.addCases vc vb)]
          simp

/-- Any valuation of a graft restricts to a valuation of the grafted circuit `b`. -/
theorem accValuation_accGraft_right {c b : ACCCircuit n m} {u : Fin c.gateCount} {x : Fin n → Bool}
    {V : Fin (accGraft c b u).gateCount → Bool} (hV : ACCValuation (accGraft c b u) x V) :
    ACCValuation b x (fun g => V (Fin.natAdd c.gateCount g)) := by
  intro g
  have hg := hV (Fin.natAdd c.gateCount g)
  rw [accGraft_kind_right] at hg
  cases hk : b.kind g with
  | literal i bneg =>
      simp only [hk] at hg ⊢
      exact hg
  | andGate =>
      simp only [hk] at hg ⊢
      rw [hg]
      constructor
      · intro H y' hy'
        exact H _ (accGraft_edge_to_right.mpr ⟨y', rfl, hy'⟩)
      · intro H y hy
        obtain ⟨y', rfl, hey⟩ := accGraft_edge_to_right.mp hy
        exact H y' hey
  | orGate =>
      simp only [hk] at hg ⊢
      rw [hg]
      constructor
      · rintro ⟨y, hy, hv⟩
        obtain ⟨y', rfl, hey⟩ := accGraft_edge_to_right.mp hy
        exact ⟨y', hey, hv⟩
      · rintro ⟨y', hy', hv⟩
        exact ⟨_, accGraft_edge_to_right.mpr ⟨y', rfl, hy'⟩, hv⟩
  | notGate =>
      simp only [hk] at hg ⊢
      rw [hg]
      constructor
      · rintro ⟨y, hy, hv⟩
        obtain ⟨y', rfl, hey⟩ := accGraft_edge_to_right.mp hy
        exact ⟨y', hey, hv⟩
      · rintro ⟨y', hy', hv⟩
        exact ⟨_, accGraft_edge_to_right.mpr ⟨y', rfl, hy'⟩, hv⟩
  | modGate =>
      simp only [hk] at hg ⊢
      rw [hg, accGraft_card_right V]

theorem evalACC_accGraft_left {c b : ACCCircuit n m} (hc : WellFormedACC c) (hb : WellFormedACC b)
    (u : Fin c.gateCount) (h_layer : ∀ y, c.edge u y = true → b.layer b.output < c.layer y)
    (x : Fin n → Bool) (g : Fin c.gateCount)
    (hx : evalACC c hc x u = evalACC b hb x b.output) :
    evalACC (accGraft c b u) (wellFormedACC_accGraft hc hb u h_layer) x (Fin.castAdd b.gateCount g)
      = evalACC c hc x g := by
  have hval := accValuation_accGraft
    (Classical.choose_spec (accValuation_exists c hc x))
    (Classical.choose_spec (accValuation_exists b hb x)) hx
  have heq := (accValuation_iff_eq_evalACC (wellFormedACC_accGraft hc hb u h_layer)).mp hval
  have := congrFun heq (Fin.castAdd b.gateCount g)
  simpa [evalACC] using this.symm

theorem evalACC_accGraft_right {c b : ACCCircuit n m} (hc : WellFormedACC c) (hb : WellFormedACC b)
    (u : Fin c.gateCount) (h_layer : ∀ y, c.edge u y = true → b.layer b.output < c.layer y)
    (x : Fin n → Bool) (g : Fin b.gateCount) :
    evalACC (accGraft c b u) (wellFormedACC_accGraft hc hb u h_layer) x (Fin.natAdd c.gateCount g)
      = evalACC b hb x g := by
  have hV := Classical.choose_spec
    (accValuation_exists (accGraft c b u) (wellFormedACC_accGraft hc hb u h_layer) x)
  have heq := (accValuation_iff_eq_evalACC hb).mp (accValuation_accGraft_right hV)
  exact congrFun heq g

theorem accAccepts_accGraft {c b : ACCCircuit n m} (hc : WellFormedACC c) (hb : WellFormedACC b)
    (u : Fin c.gateCount) (h_layer : ∀ y, c.edge u y = true → b.layer b.output < c.layer y)
    (x : Fin n → Bool) (hx : evalACC c hc x u = evalACC b hb x b.output) :
    ACCAccepts (accGraft c b u) x ↔ ACCAccepts c x := by
  rw [accAccepts_iff (wellFormedACC_accGraft hc hb u h_layer) x, accAccepts_iff hc x,
    accGraft_output, evalACC_accGraft_left hc hb u h_layer x c.output hx]

end AllenderOQ3.Internal
