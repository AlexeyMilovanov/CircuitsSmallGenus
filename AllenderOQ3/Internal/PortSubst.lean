import AllenderOQ3.Internal.ACCBuild

set_option autoImplicit false
set_option linter.style.longLine false
namespace AllenderOQ3.Internal

variable {n p m : Nat}

/-!
# Beta port substitution

`accPortSubst c beta` replaces the `p` *ports* of a wrapper circuit
`c : ACCCircuit (n + p) m` — that is, its literal gates over the upper `p` input
variables — by the outputs of the family `beta : Fin p → ACCCircuit n m`.

The gate set is the disjoint union of the gates of `c` (kept in place, on the
left) with the gates of all the `beta i` (on the right, indexed through
`finSigmaFinEquiv`).  A port literal gate of `c` over the port `i` is turned into
a one-input `orGate` (or `notGate`, if the literal was negated) fed by the output
gate of `beta i`; every other gate of `c` keeps its kind and its incoming edges.

Layers: the gates of the `beta i` keep their layers, the port gates sit just
above them at `betaDepth beta + 1`, ordinary literal gates of `c` stay at layer
`0`, and the remaining gates of `c` are shifted up by `betaDepth beta + 1`.
-/

/-- The maximal layer occurring in a family of ACC circuits. -/
def betaDepth (beta : Fin p → ACCCircuit n m) : Nat :=
  Finset.univ.sup (fun i => Finset.univ.sup (beta i).layer)

theorem betaDepth_ge (beta : Fin p → ACCCircuit n m) (i : Fin p) (g : Fin (beta i).gateCount) :
    (beta i).layer g ≤ betaDepth beta :=
  le_trans (Finset.le_sup (f := (beta i).layer) (Finset.mem_univ g))
    (Finset.le_sup (f := fun i => Finset.univ.sup (beta i).layer) (Finset.mem_univ i))

/-- Edges inside the disjoint family `beta`: only gates of the same member are joined. -/
def betaEdge (beta : Fin p → ACCCircuit n m) :
    ((i : Fin p) × Fin (beta i).gateCount) → ((i : Fin p) × Fin (beta i).gateCount) → Bool :=
  fun a b => if e : a.1 = b.1 then
    (beta b.1).edge (Fin.cast (congrArg (fun k => (beta k).gateCount) e) a.2) b.2 else false

@[simp] theorem betaEdge_same (beta : Fin p → ACCCircuit n m) (i : Fin p)
    (g h : Fin (beta i).gateCount) : betaEdge beta ⟨i, g⟩ ⟨i, h⟩ = (beta i).edge g h := by
  simp [betaEdge]

theorem betaEdge_ne (beta : Fin p → ACCCircuit n m) {i j : Fin p}
    (g : Fin (beta i).gateCount) (h : Fin (beta j).gateCount) (hij : i ≠ j) :
    betaEdge beta ⟨i, g⟩ ⟨j, h⟩ = false := by
  simp [betaEdge, hij]

/-- The edge relation from a gate of the beta block into a gate of the wrapper: only the
output gate of `beta i` feeds the port literal gates of `c` over the port `i`. -/
def portSubstEdgeRL (c : ACCCircuit (n + p) m) (beta : Fin p → ACCCircuit n m)
    (a : (i : Fin p) × Fin (beta i).gateCount) (v : Fin c.gateCount) : Bool :=
  decide (a.2 = (beta a.1).output) &&
    (match c.kind v with
      | .literal j _ => decide (j = Fin.natAdd n a.1)
      | _ => false)

theorem portSubstEdgeRL_eq_true_iff (c : ACCCircuit (n + p) m) (beta : Fin p → ACCCircuit n m)
    (i : Fin p) (g : Fin (beta i).gateCount) (v : Fin c.gateCount) :
    portSubstEdgeRL c beta ⟨i, g⟩ v = true ↔
      g = (beta i).output ∧ ∃ bneg : Bool, c.kind v = .literal (Fin.natAdd n i) bneg := by
  simp only [portSubstEdgeRL, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hg, hv⟩
    refine ⟨hg, ?_⟩
    revert hv
    cases hk : c.kind v with
    | literal j bneg =>
        intro hv
        simp only [decide_eq_true_eq] at hv
        exact ⟨bneg, by rw [hv]⟩
    | andGate => simp
    | orGate => simp
    | notGate => simp
    | modGate => simp
  · rintro ⟨hg, bneg, hv⟩
    exact ⟨hg, by rw [hv]; simp⟩

/-- Beta port substitution: replaces ports (the upper `p` inputs of a wrapper circuit)
with the outputs of a family of `beta` circuits. -/
noncomputable def accPortSubst (c : ACCCircuit (n + p) m) (beta : Fin p → ACCCircuit n m) :
    ACCCircuit n m where
  gateCount := c.gateCount + ∑ i, (beta i).gateCount
  output := Fin.castAdd _ c.output
  kind := Fin.addCases
    (fun g => match c.kind g with
      | .literal j bneg =>
          Fin.addCases (motive := fun _ => ACCGate n m)
            (fun j' => .literal j' bneg) (fun _ => if bneg then .notGate else .orGate) j
      | .andGate => .andGate
      | .orGate => .orGate
      | .notGate => .notGate
      | .modGate => .modGate)
    (fun s => (beta (finSigmaFinEquiv.symm s).1).kind (finSigmaFinEquiv.symm s).2)
  layer := Fin.addCases
    (fun g => match c.kind g with
      | .literal j _ =>
          Fin.addCases (motive := fun _ => Nat) (fun _ => 0) (fun _ => betaDepth beta + 1) j
      | _ => c.layer g + betaDepth beta + 1)
    (fun s => (beta (finSigmaFinEquiv.symm s).1).layer (finSigmaFinEquiv.symm s).2)
  edge := fun U V =>
    Fin.addCases (motive := fun _ => Bool)
      (fun u => Fin.addCases (motive := fun _ => Bool) (fun v => c.edge u v) (fun _ => false) V)
      (fun s => Fin.addCases (motive := fun _ => Bool)
        (fun v => portSubstEdgeRL c beta (finSigmaFinEquiv.symm s) v)
        (fun t => betaEdge beta (finSigmaFinEquiv.symm s) (finSigmaFinEquiv.symm t)) V)
      U


theorem betaDepth_le {beta : Fin p → ACCCircuit n m} {d : Nat}
    (h : ∀ i g, (beta i).layer g ≤ d) : betaDepth beta ≤ d :=
  Finset.sup_le fun i _ => Finset.sup_le fun g _ => h i g

/-- Every gate index of the beta block is the image of a pair `(i, g)`. -/
theorem exists_sigma_repr (beta : Fin p → ACCCircuit n m)
    (s : Fin (∑ i, (beta i).gateCount)) :
    ∃ (i : Fin p) (g : Fin (beta i).gateCount), s = finSigmaFinEquiv ⟨i, g⟩ :=
  ⟨(finSigmaFinEquiv.symm s).1, (finSigmaFinEquiv.symm s).2, by
    rw [Sigma.eta, Equiv.apply_symm_apply]⟩

@[simp] theorem accPortSubst_gateCount (c : ACCCircuit (n + p) m) (beta : Fin p → ACCCircuit n m) :
    (accPortSubst c beta).gateCount = c.gateCount + ∑ i, (beta i).gateCount := rfl

@[simp] theorem accPortSubst_output (c : ACCCircuit (n + p) m) (beta : Fin p → ACCCircuit n m) :
    (accPortSubst c beta).output = Fin.castAdd _ c.output := rfl

theorem accPortSubst_kind_left (c : ACCCircuit (n + p) m) (beta : Fin p → ACCCircuit n m)
    (g : Fin c.gateCount) :
    (accPortSubst c beta).kind (Fin.castAdd _ g) =
      match c.kind g with
      | .literal j bneg =>
          Fin.addCases (motive := fun _ => ACCGate n m)
            (fun j' => .literal j' bneg) (fun _ => if bneg then .notGate else .orGate) j
      | .andGate => .andGate
      | .orGate => .orGate
      | .notGate => .notGate
      | .modGate => .modGate := by
  simp only [accPortSubst, Fin.addCases_left]

@[simp] theorem accPortSubst_kind_right (c : ACCCircuit (n + p) m) (beta : Fin p → ACCCircuit n m)
    (i : Fin p) (g : Fin (beta i).gateCount) :
    (accPortSubst c beta).kind (Fin.natAdd c.gateCount (finSigmaFinEquiv ⟨i, g⟩))
      = (beta i).kind g := by
  have ha : finSigmaFinEquiv.symm
      (finSigmaFinEquiv (⟨i, g⟩ : (k : Fin p) × Fin (beta k).gateCount)) = ⟨i, g⟩ :=
    Equiv.symm_apply_apply _ _
  simp only [accPortSubst, Fin.addCases_right]
  exact congrArg (fun X : (k : Fin p) × Fin (beta k).gateCount => (beta X.1).kind X.2) ha

theorem accPortSubst_layer_left (c : ACCCircuit (n + p) m) (beta : Fin p → ACCCircuit n m)
    (g : Fin c.gateCount) :
    (accPortSubst c beta).layer (Fin.castAdd _ g) =
      match c.kind g with
      | .literal j _ =>
          Fin.addCases (motive := fun _ => Nat) (fun _ => 0) (fun _ => betaDepth beta + 1) j
      | _ => c.layer g + betaDepth beta + 1 := by
  simp only [accPortSubst, Fin.addCases_left]

@[simp] theorem accPortSubst_layer_right (c : ACCCircuit (n + p) m) (beta : Fin p → ACCCircuit n m)
    (i : Fin p) (g : Fin (beta i).gateCount) :
    (accPortSubst c beta).layer (Fin.natAdd c.gateCount (finSigmaFinEquiv ⟨i, g⟩))
      = (beta i).layer g := by
  have ha : finSigmaFinEquiv.symm
      (finSigmaFinEquiv (⟨i, g⟩ : (k : Fin p) × Fin (beta k).gateCount)) = ⟨i, g⟩ :=
    Equiv.symm_apply_apply _ _
  simp only [accPortSubst, Fin.addCases_right]
  exact congrArg (fun X : (k : Fin p) × Fin (beta k).gateCount => (beta X.1).layer X.2) ha

@[simp] theorem accPortSubst_edge_ll (c : ACCCircuit (n + p) m) (beta : Fin p → ACCCircuit n m)
    (u v : Fin c.gateCount) :
    (accPortSubst c beta).edge (Fin.castAdd _ u) (Fin.castAdd _ v) = c.edge u v := by
  simp only [accPortSubst, Fin.addCases_left]

@[simp] theorem accPortSubst_edge_lr (c : ACCCircuit (n + p) m) (beta : Fin p → ACCCircuit n m)
    (u : Fin c.gateCount) (s : Fin (∑ i, (beta i).gateCount)) :
    (accPortSubst c beta).edge (Fin.castAdd _ u) (Fin.natAdd c.gateCount s) = false := by
  simp only [accPortSubst, Fin.addCases_left, Fin.addCases_right]

@[simp] theorem accPortSubst_edge_rl (c : ACCCircuit (n + p) m) (beta : Fin p → ACCCircuit n m)
    (i : Fin p) (g : Fin (beta i).gateCount) (v : Fin c.gateCount) :
    (accPortSubst c beta).edge (Fin.natAdd c.gateCount (finSigmaFinEquiv ⟨i, g⟩))
        (Fin.castAdd _ v)
      = portSubstEdgeRL c beta ⟨i, g⟩ v := by
  have ha : finSigmaFinEquiv.symm
      (finSigmaFinEquiv (⟨i, g⟩ : (k : Fin p) × Fin (beta k).gateCount)) = ⟨i, g⟩ :=
    Equiv.symm_apply_apply _ _
  simp only [accPortSubst, Fin.addCases_left, Fin.addCases_right, ha]

@[simp] theorem accPortSubst_edge_rr (c : ACCCircuit (n + p) m) (beta : Fin p → ACCCircuit n m)
    (i : Fin p) (g : Fin (beta i).gateCount) (j : Fin p) (h : Fin (beta j).gateCount) :
    (accPortSubst c beta).edge (Fin.natAdd c.gateCount (finSigmaFinEquiv ⟨i, g⟩))
        (Fin.natAdd c.gateCount (finSigmaFinEquiv ⟨j, h⟩))
      = betaEdge beta ⟨i, g⟩ ⟨j, h⟩ := by
  have ha : finSigmaFinEquiv.symm
      (finSigmaFinEquiv (⟨i, g⟩ : (k : Fin p) × Fin (beta k).gateCount)) = ⟨i, g⟩ :=
    Equiv.symm_apply_apply _ _
  have hb : finSigmaFinEquiv.symm
      (finSigmaFinEquiv (⟨j, h⟩ : (k : Fin p) × Fin (beta k).gateCount)) = ⟨j, h⟩ :=
    Equiv.symm_apply_apply _ _
  simp only [accPortSubst, Fin.addCases_right, ha, hb]

/-- Incoming edges of a wrapper gate: either an old edge of `c`, or the new edge from the
output gate of `beta i` into a port literal gate over the port `i`. -/
theorem accPortSubst_edge_to_left {c : ACCCircuit (n + p) m} {beta : Fin p → ACCCircuit n m}
    {g : Fin c.gateCount} {U : Fin (accPortSubst c beta).gateCount} :
    (accPortSubst c beta).edge U (Fin.castAdd _ g) = true ↔
      (∃ u, U = Fin.castAdd _ u ∧ c.edge u g = true) ∨
        (∃ (i : Fin p) (bneg : Bool),
          U = Fin.natAdd c.gateCount (finSigmaFinEquiv ⟨i, (beta i).output⟩) ∧
            c.kind g = .literal (Fin.natAdd n i) bneg) := by
  induction U using Fin.addCases with
  | left u =>
      rw [accPortSubst_edge_ll]
      constructor
      · intro he; exact Or.inl ⟨u, rfl, he⟩
      · rintro (⟨u', hEq, he⟩ | ⟨i, bneg, hEq, _⟩)
        · have : u' = u := by
            have := congrArg Fin.val hEq
            simpa [Fin.ext_iff] using this.symm
          subst this; exact he
        · exact absurd (congrArg Fin.val hEq) (by simp; omega)
  | right s =>
      obtain ⟨i, g', rfl⟩ := exists_sigma_repr beta s
      rw [accPortSubst_edge_rl, portSubstEdgeRL_eq_true_iff]
      constructor
      · rintro ⟨rfl, bneg, hk⟩
        exact Or.inr ⟨i, bneg, rfl, hk⟩
      · rintro (⟨u, hEq, _⟩ | ⟨i', bneg, hEq, hk⟩)
        · exact absurd (congrArg Fin.val hEq) (by simp; omega)
        · have hs : (finSigmaFinEquiv (⟨i, g'⟩ : (k : Fin p) × Fin (beta k).gateCount))
              = finSigmaFinEquiv ⟨i', (beta i').output⟩ := by
            apply Fin.ext
            have := congrArg Fin.val hEq
            simpa using this
          have hsig := finSigmaFinEquiv.injective hs
          rw [Sigma.mk.injEq] at hsig
          obtain ⟨rfl, hg⟩ := hsig
          refine ⟨?_, bneg, hk⟩
          simpa using hg

/-- Incoming edges of a gate of the beta block come exactly from the same beta circuit. -/
theorem accPortSubst_edge_to_right {c : ACCCircuit (n + p) m} {beta : Fin p → ACCCircuit n m}
    {i : Fin p} {g : Fin (beta i).gateCount} {U : Fin (accPortSubst c beta).gateCount} :
    (accPortSubst c beta).edge U (Fin.natAdd c.gateCount (finSigmaFinEquiv ⟨i, g⟩)) = true ↔
      ∃ h, U = Fin.natAdd c.gateCount (finSigmaFinEquiv ⟨i, h⟩) ∧ (beta i).edge h g = true := by
  induction U using Fin.addCases with
  | left u =>
      rw [accPortSubst_edge_lr]
      constructor
      · intro he; exact absurd he (by simp)
      · rintro ⟨h, hEq, _⟩
        exact absurd (congrArg Fin.val hEq) (by simp; omega)
  | right s =>
      obtain ⟨j, h, rfl⟩ := exists_sigma_repr beta s
      rw [accPortSubst_edge_rr]
      constructor
      · intro he
        by_cases hij : j = i
        · subst hij
          rw [betaEdge_same] at he
          exact ⟨h, rfl, he⟩
        · rw [betaEdge_ne beta h g hij] at he
          exact absurd he (by simp)
      · rintro ⟨h', hEq, he⟩
        have hs : (finSigmaFinEquiv (⟨j, h⟩ : (k : Fin p) × Fin (beta k).gateCount))
            = finSigmaFinEquiv ⟨i, h'⟩ := by
          apply Fin.ext
          have := congrArg Fin.val hEq
          simpa using this
        have hsig := finSigmaFinEquiv.injective hs
        rw [Sigma.mk.injEq] at hsig
        obtain ⟨rfl, hh⟩ := hsig
        have : h = h' := by simpa using hh
        subst this
        rw [betaEdge_same]
        exact he

theorem accPortSubst_layer_left_le (c : ACCCircuit (n + p) m) (beta : Fin p → ACCCircuit n m)
    (g : Fin c.gateCount) :
    (accPortSubst c beta).layer (Fin.castAdd _ g) ≤ c.layer g + betaDepth beta + 1 := by
  rw [accPortSubst_layer_left]
  cases hk : c.kind g with
  | literal j b =>
      induction j using Fin.addCases with
      | left j' => simp
      | right i => simp
  | andGate => change c.layer g + betaDepth beta + 1 ≤ _; omega
  | orGate => change c.layer g + betaDepth beta + 1 ≤ _; omega
  | notGate => change c.layer g + betaDepth beta + 1 ≤ _; omega
  | modGate => change c.layer g + betaDepth beta + 1 ≤ _; omega

theorem accPortSubst_layer_left_of_port (c : ACCCircuit (n + p) m) (beta : Fin p → ACCCircuit n m)
    {g : Fin c.gateCount} {i : Fin p} {b : Bool} (hk : c.kind g = .literal (Fin.natAdd n i) b) :
    (accPortSubst c beta).layer (Fin.castAdd _ g) = betaDepth beta + 1 := by
  rw [accPortSubst_layer_left, hk]
  simp

theorem accPortSubst_layer_left_of_real (c : ACCCircuit (n + p) m) (beta : Fin p → ACCCircuit n m)
    {g : Fin c.gateCount} {j : Fin n} {b : Bool} (hk : c.kind g = .literal (Fin.castAdd p j) b) :
    (accPortSubst c beta).layer (Fin.castAdd _ g) = 0 := by
  rw [accPortSubst_layer_left, hk]
  simp

theorem accPortSubst_kind_left_of_port (c : ACCCircuit (n + p) m) (beta : Fin p → ACCCircuit n m)
    {g : Fin c.gateCount} {i : Fin p} {b : Bool} (hk : c.kind g = .literal (Fin.natAdd n i) b) :
    (accPortSubst c beta).kind (Fin.castAdd _ g) = if b then .notGate else .orGate := by
  rw [accPortSubst_kind_left, hk]
  simp

theorem accPortSubst_kind_left_of_real (c : ACCCircuit (n + p) m) (beta : Fin p → ACCCircuit n m)
    {g : Fin c.gateCount} {j : Fin n} {b : Bool} (hk : c.kind g = .literal (Fin.castAdd p j) b) :
    (accPortSubst c beta).kind (Fin.castAdd _ g) = .literal j b := by
  rw [accPortSubst_kind_left, hk]
  simp

theorem accPortSubst_layer_left_of_not_literal (c : ACCCircuit (n + p) m)
    (beta : Fin p → ACCCircuit n m) {g : Fin c.gateCount}
    (hk : ∀ (j : Fin (n + p)) (b : Bool), c.kind g ≠ .literal j b) :
    (accPortSubst c beta).layer (Fin.castAdd _ g) = c.layer g + betaDepth beta + 1 := by
  rw [accPortSubst_layer_left]
  cases hkk : c.kind g with
  | literal j b => exact absurd hkk (hk j b)
  | andGate => rfl
  | orGate => rfl
  | notGate => rfl
  | modGate => rfl

theorem accPortSubst_kind_left_not_literal (c : ACCCircuit (n + p) m)
    (beta : Fin p → ACCCircuit n m) {g : Fin c.gateCount}
    (hk : ∀ (j : Fin (n + p)) (b : Bool), c.kind g ≠ .literal j b) :
    ∀ (j : Fin n) (b : Bool), (accPortSubst c beta).kind (Fin.castAdd _ g) ≠ .literal j b := by
  intro j b
  rw [accPortSubst_kind_left]
  cases hkk : c.kind g with
  | literal j' b' => exact absurd hkk (hk j' b')
  | andGate => simp
  | orGate => simp
  | notGate => simp
  | modGate => simp

/-- Port substitution preserves well-formedness. -/
theorem wellFormedACC_accPortSubst (c : ACCCircuit (n + p) m) (beta : Fin p → ACCCircuit n m)
    (hc : WellFormedACC c) (hbeta : ∀ g, WellFormedACC (beta g)) :
    WellFormedACC (accPortSubst c beta) := by
  obtain ⟨hc1, hc2, hc3⟩ := hc
  refine ⟨?_, ?_, ?_⟩
  · intro U V hUV
    induction V using Fin.addCases with
    | left g =>
        rcases accPortSubst_edge_to_left.mp hUV with ⟨u, rfl, he⟩ | ⟨i, bneg, rfl, hk⟩
        · have hlt := hc1 u g he
          have hgnl : ∀ (j : Fin (n + p)) (b : Bool), c.kind g ≠ .literal j b := by
            intro j b hkj
            have : c.layer g = 0 := (hc2 g).mpr ⟨j, b, hkj⟩
            omega
          rw [accPortSubst_layer_left_of_not_literal c beta hgnl]
          have := accPortSubst_layer_left_le c beta u
          omega
        · rw [accPortSubst_layer_left_of_port c beta hk, accPortSubst_layer_right]
          have := betaDepth_ge beta i (beta i).output
          omega
    | right s =>
        obtain ⟨i, g, rfl⟩ := exists_sigma_repr beta s
        obtain ⟨h, rfl, he⟩ := accPortSubst_edge_to_right.mp hUV
        rw [accPortSubst_layer_right, accPortSubst_layer_right]
        exact (hbeta i).1 h g he
  · intro G
    induction G using Fin.addCases with
    | left g =>
        by_cases hlit : ∃ (j : Fin (n + p)) (b : Bool), c.kind g = .literal j b
        · obtain ⟨j, b, hk⟩ := hlit
          induction j using Fin.addCases with
          | left j' =>
              rw [accPortSubst_layer_left_of_real c beta hk,
                accPortSubst_kind_left_of_real c beta hk]
              exact ⟨fun _ => ⟨j', b, rfl⟩, fun _ => rfl⟩
          | right i =>
              rw [accPortSubst_layer_left_of_port c beta hk,
                accPortSubst_kind_left_of_port c beta hk]
              cases b <;> simp
        · push_neg at hlit
          rw [accPortSubst_layer_left_of_not_literal c beta hlit]
          constructor
          · intro h; omega
          · rintro ⟨j', b', hb⟩
            exact absurd hb (accPortSubst_kind_left_not_literal c beta hlit j' b')
    | right s =>
        obtain ⟨i, g, rfl⟩ := exists_sigma_repr beta s
        rw [accPortSubst_layer_right, accPortSubst_kind_right]
        exact (hbeta i).2.1 g
  · intro G hG
    induction G using Fin.addCases with
    | left g =>
        by_cases hlit : ∃ (j : Fin (n + p)) (b : Bool), c.kind g = .literal j b
        · obtain ⟨j, b, hk⟩ := hlit
          have hg0 : c.layer g = 0 := (hc2 g).mpr ⟨j, b, hk⟩
          have hnoin : ∀ u, c.edge u g = false := by
            intro u
            by_contra hcon
            have := hc1 u g (by simpa using hcon)
            omega
          induction j using Fin.addCases with
          | left j' =>
              rw [accPortSubst_kind_left_of_real c beta hk] at hG
              exact absurd hG (by simp)
          | right i =>
              refine ⟨Fin.natAdd c.gateCount (finSigmaFinEquiv ⟨i, (beta i).output⟩), ?_, ?_⟩
              · exact accPortSubst_edge_to_left.mpr (Or.inr ⟨i, b, rfl, hk⟩)
              · intro U hU
                rcases accPortSubst_edge_to_left.mp hU with ⟨u, rfl, he⟩ | ⟨i', bneg, rfl, hk'⟩
                · exact absurd he (by simp [hnoin u])
                · rw [hk] at hk'
                  have hii : i = i' := by
                    simp only [ACCGate.literal.injEq] at hk'
                    simpa using hk'.1
                  subst hii
                  rfl
        · push_neg at hlit
          have hkg : c.kind g = .notGate := by
            cases hkk : c.kind g with
            | literal j b => exact absurd hkk (hlit j b)
            | andGate => simp [accPortSubst_kind_left, hkk] at hG
            | orGate => simp [accPortSubst_kind_left, hkk] at hG
            | notGate => rfl
            | modGate => simp [accPortSubst_kind_left, hkk] at hG
          obtain ⟨h, hh, huniq⟩ := hc3 g hkg
          refine ⟨Fin.castAdd _ h, ?_, ?_⟩
          · exact accPortSubst_edge_to_left.mpr (Or.inl ⟨h, rfl, hh⟩)
          · intro U hU
            rcases accPortSubst_edge_to_left.mp hU with ⟨u, rfl, he⟩ | ⟨i, bneg, rfl, hk'⟩
            · rw [huniq u he]
            · exact absurd hk' (hlit _ _)
    | right s =>
        obtain ⟨i, g, rfl⟩ := exists_sigma_repr beta s
        rw [accPortSubst_kind_right] at hG
        obtain ⟨h, hh, huniq⟩ := (hbeta i).2.2 g hG
        refine ⟨Fin.natAdd c.gateCount (finSigmaFinEquiv ⟨i, h⟩), ?_, ?_⟩
        · exact accPortSubst_edge_to_right.mpr ⟨h, rfl, hh⟩
        · intro U hU
          obtain ⟨h', rfl, he'⟩ := accPortSubst_edge_to_right.mp hU
          rw [huniq h' he']

/-- The depth of the substituted circuit is bounded by a constant shift above the beta depth. -/
theorem accPortSubst_layer_le {c : ACCCircuit (n + p) m} {beta : Fin p → ACCCircuit n m}
    {d_c d_beta : Nat} (hc : ∀ g, c.layer g ≤ d_c) (hbeta : ∀ i g, (beta i).layer g ≤ d_beta) :
    ∀ g, (accPortSubst c beta).layer g ≤ d_c + d_beta + 2 := by
  have hB : betaDepth beta ≤ d_beta := betaDepth_le hbeta
  intro G
  induction G using Fin.addCases with
  | left g =>
      rw [accPortSubst_layer_left]
      cases hk : c.kind g with
      | literal j bneg =>
          induction j using Fin.addCases with
          | left j' => simp
          | right j' => simp; omega
      | andGate =>
          change c.layer g + betaDepth beta + 1 ≤ _
          have := hc g
          omega
      | orGate =>
          change c.layer g + betaDepth beta + 1 ≤ _
          have := hc g
          omega
      | notGate =>
          change c.layer g + betaDepth beta + 1 ≤ _
          have := hc g
          omega
      | modGate =>
          change c.layer g + betaDepth beta + 1 ≤ _
          have := hc g
          omega
  | right s =>
      obtain ⟨i, g, rfl⟩ := exists_sigma_repr beta s
      rw [accPortSubst_layer_right]
      have := hbeta i g
      omega

/-- The size of the substituted circuit grows by at most a small constant factor of the wrapper size. -/
theorem accPortSubst_gateCount_le (c : ACCCircuit (n + p) m) (beta : Fin p → ACCCircuit n m) :
    (accPortSubst c beta).gateCount ≤ c.gateCount + (∑ i, (beta i).gateCount) + 2 * c.gateCount := by
  simp only [accPortSubst_gateCount]
  omega

/-- A well-formed circuit has no edge into a literal gate (literals sit on layer `0`). -/
theorem acc_no_edge_into_literal {N : Nat} {c : ACCCircuit N m} (hc : WellFormedACC c)
    {g : Fin c.gateCount} {j : Fin N} {b : Bool} (hk : c.kind g = .literal j b)
    (u : Fin c.gateCount) : c.edge u g = false := by
  have hg0 : c.layer g = 0 := hc.2.1 g |>.mpr ⟨j, b, hk⟩
  by_contra hcon
  have := hc.1 u g (by simpa using hcon)
  omega

/-- The glued valuation on the substituted circuit. -/
def portSubstValue (c : ACCCircuit (n + p) m) (beta : Fin p → ACCCircuit n m)
    (vc : Fin c.gateCount → Bool) (vb : (i : Fin p) → Fin (beta i).gateCount → Bool) :
    Fin (accPortSubst c beta).gateCount → Bool :=
  Fin.addCases (motive := fun _ => Bool) vc
    (fun s => vb (finSigmaFinEquiv.symm s).1 (finSigmaFinEquiv.symm s).2)

@[simp] theorem portSubstValue_left (c : ACCCircuit (n + p) m) (beta : Fin p → ACCCircuit n m)
    (vc : Fin c.gateCount → Bool) (vb : (i : Fin p) → Fin (beta i).gateCount → Bool)
    (g : Fin c.gateCount) :
    portSubstValue c beta vc vb (Fin.castAdd _ g) = vc g := by
  simp only [portSubstValue, Fin.addCases_left]

@[simp] theorem portSubstValue_right (c : ACCCircuit (n + p) m) (beta : Fin p → ACCCircuit n m)
    (vc : Fin c.gateCount → Bool) (vb : (i : Fin p) → Fin (beta i).gateCount → Bool)
    (i : Fin p) (g : Fin (beta i).gateCount) :
    portSubstValue c beta vc vb (Fin.natAdd c.gateCount (finSigmaFinEquiv ⟨i, g⟩)) = vb i g := by
  have ha : finSigmaFinEquiv.symm
      (finSigmaFinEquiv (⟨i, g⟩ : (k : Fin p) × Fin (beta k).gateCount)) = ⟨i, g⟩ :=
    Equiv.symm_apply_apply _ _
  simp only [portSubstValue, Fin.addCases_right]
  exact congrArg (fun X : (k : Fin p) × Fin (beta k).gateCount => vb X.1 X.2) ha

/-- Counting the inputs of a beta gate inside the substituted circuit. -/
theorem accPortSubst_card_right {c : ACCCircuit (n + p) m} {beta : Fin p → ACCCircuit n m}
    {i : Fin p} {g : Fin (beta i).gateCount}
    (V : Fin (accPortSubst c beta).gateCount → Bool) :
    (Finset.univ.filter (fun h : Fin (accPortSubst c beta).gateCount =>
        (accPortSubst c beta).edge h
            (Fin.natAdd c.gateCount (finSigmaFinEquiv ⟨i, g⟩)) = true ∧ V h = true)).card
      = (Finset.univ.filter (fun h : Fin (beta i).gateCount =>
          (beta i).edge h g = true ∧
            V (Fin.natAdd c.gateCount (finSigmaFinEquiv ⟨i, h⟩)) = true)).card := by
  refine (Finset.card_bij
    (fun h _ => Fin.natAdd c.gateCount (finSigmaFinEquiv ⟨i, h⟩)) ?_ ?_ ?_).symm
  · intro h hh
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hh ⊢
    exact ⟨accPortSubst_edge_to_right.mpr ⟨h, rfl, hh.1⟩, hh.2⟩
  · intro h₁ _ h₂ _ hEq
    have hs : (finSigmaFinEquiv (⟨i, h₁⟩ : (k : Fin p) × Fin (beta k).gateCount))
        = finSigmaFinEquiv ⟨i, h₂⟩ := by
      apply Fin.ext
      have := congrArg Fin.val hEq
      simpa using this
    have hsig := finSigmaFinEquiv.injective hs
    rw [Sigma.mk.injEq] at hsig
    exact eq_of_heq hsig.2
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    obtain ⟨h, rfl, he⟩ := accPortSubst_edge_to_right.mp hy.1
    exact ⟨h, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨he, hy.2⟩, rfl⟩

/-- Counting the inputs of a non-literal wrapper gate inside the substituted circuit. -/
theorem accPortSubst_card_left {c : ACCCircuit (n + p) m} {beta : Fin p → ACCCircuit n m}
    {g : Fin c.gateCount} (hlit : ∀ (j : Fin (n + p)) (b : Bool), c.kind g ≠ .literal j b)
    (V : Fin (accPortSubst c beta).gateCount → Bool) :
    (Finset.univ.filter (fun h : Fin (accPortSubst c beta).gateCount =>
        (accPortSubst c beta).edge h (Fin.castAdd _ g) = true ∧ V h = true)).card
      = (Finset.univ.filter (fun h : Fin c.gateCount =>
          c.edge h g = true ∧ V (Fin.castAdd _ h) = true)).card := by
  refine (Finset.card_bij (fun h _ => Fin.castAdd (∑ i, (beta i).gateCount) h) ?_ ?_ ?_).symm
  · intro h hh
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hh ⊢
    exact ⟨accPortSubst_edge_to_left.mpr (Or.inl ⟨h, rfl, hh.1⟩), hh.2⟩
  · intro h₁ _ h₂ _ hEq
    have := congrArg Fin.val hEq
    simpa [Fin.ext_iff] using this
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    rcases accPortSubst_edge_to_left.mp hy.1 with ⟨u, rfl, he⟩ | ⟨i, bneg, _, hk⟩
    · exact ⟨u, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨he, hy.2⟩, rfl⟩
    · exact absurd hk (hlit _ _)

/-- Gluing a valuation of the wrapper (on the extended input) with valuations of the
`beta` circuits gives a valuation of the substituted circuit. -/
theorem accValuation_accPortSubst {c : ACCCircuit (n + p) m} {beta : Fin p → ACCCircuit n m}
    (hc : WellFormedACC c) {x : Fin n → Bool}
    {vc : Fin c.gateCount → Bool} {vb : (i : Fin p) → Fin (beta i).gateCount → Bool}
    (hvb : ∀ i, ACCValuation (beta i) x (vb i))
    (hvc : ACCValuation c
      (Fin.addCases (motive := fun _ => Bool) x (fun i => vb i (beta i).output)) vc) :
    ACCValuation (accPortSubst c beta) x (portSubstValue c beta vc vb) := by
  intro G
  induction G using Fin.addCases with
  | left g =>
      have hg := hvc g
      cases hk : c.kind g with
      | literal j bneg =>
          simp only [hk] at hg
          induction j using Fin.addCases with
          | left j' =>
              simp only [accPortSubst_kind_left_of_real c beta hk, portSubstValue_left]
              simpa using hg
          | right i =>
              have hgv : vc g = (if bneg then !(vb i (beta i).output) else vb i (beta i).output) := by
                simpa using hg
              have hE : (accPortSubst c beta).edge
                  (Fin.natAdd c.gateCount (finSigmaFinEquiv ⟨i, (beta i).output⟩))
                  (Fin.castAdd (∑ k, (beta k).gateCount) g) = true :=
                accPortSubst_edge_to_left.mpr (Or.inr ⟨i, bneg, rfl, hk⟩)
              have hkey : ∀ (U : Fin (accPortSubst c beta).gateCount),
                  (accPortSubst c beta).edge U (Fin.castAdd (∑ k, (beta k).gateCount) g) = true →
                  portSubstValue c beta vc vb U = vb i (beta i).output := by
                intro U hU
                rcases accPortSubst_edge_to_left.mp hU with ⟨u, rfl, he⟩ | ⟨i', bneg', rfl, hk'⟩
                · exact absurd he (by simp [acc_no_edge_into_literal hc hk u])
                · rw [hk] at hk'
                  have hii : i = i' := by
                    simp only [ACCGate.literal.injEq] at hk'
                    simpa using hk'.1
                  subst hii
                  simp
              simp only [accPortSubst_kind_left_of_port c beta hk]
              cases bneg with
              | false =>
                  simp only [if_neg (by simp : ¬ (false = true))]
                  rw [portSubstValue_left, hgv]
                  simp only [if_neg (by simp : ¬ (false = true))]
                  constructor
                  · intro hv
                    exact ⟨_, hE, by rw [portSubstValue_right]; exact hv⟩
                  · rintro ⟨U, hU, hUv⟩
                    rw [hkey U hU] at hUv
                    exact hUv
              | true =>
                  rw [portSubstValue_left, hgv]
                  constructor
                  · intro hv
                    refine ⟨_, hE, ?_⟩
                    rw [portSubstValue_right]
                    cases hb : vb i (beta i).output with
                    | false => rfl
                    | true => rw [hb] at hv; simp at hv
                  · rintro ⟨U, hU, hUv⟩
                    rw [hkey U hU] at hUv
                    rw [hUv]
                    rfl
      | andGate =>
          have hlit : ∀ (j : Fin (n + p)) (b : Bool), c.kind g ≠ .literal j b := by
            intro j b hb; rw [hk] at hb; exact absurd hb (by simp)
          simp only [hk] at hg
          simp only [accPortSubst_kind_left, hk, portSubstValue_left]
          rw [hg]
          constructor
          · intro H U hU
            rcases accPortSubst_edge_to_left.mp hU with ⟨u, rfl, he⟩ | ⟨i, bneg, _, hk'⟩
            · rw [portSubstValue_left]; exact H u he
            · exact absurd hk' (hlit _ _)
          · intro H u he
            have := H (Fin.castAdd (∑ k, (beta k).gateCount) u)
              (accPortSubst_edge_to_left.mpr (Or.inl ⟨u, rfl, he⟩))
            rwa [portSubstValue_left] at this
      | orGate =>
          have hlit : ∀ (j : Fin (n + p)) (b : Bool), c.kind g ≠ .literal j b := by
            intro j b hb; rw [hk] at hb; exact absurd hb (by simp)
          simp only [hk] at hg
          simp only [accPortSubst_kind_left, hk, portSubstValue_left]
          rw [hg]
          constructor
          · rintro ⟨u, he, hv⟩
            exact ⟨Fin.castAdd _ u, accPortSubst_edge_to_left.mpr (Or.inl ⟨u, rfl, he⟩),
              by rw [portSubstValue_left]; exact hv⟩
          · rintro ⟨U, hU, hUv⟩
            rcases accPortSubst_edge_to_left.mp hU with ⟨u, rfl, he⟩ | ⟨i, bneg, _, hk'⟩
            · exact ⟨u, he, by rwa [portSubstValue_left] at hUv⟩
            · exact absurd hk' (hlit _ _)
      | notGate =>
          have hlit : ∀ (j : Fin (n + p)) (b : Bool), c.kind g ≠ .literal j b := by
            intro j b hb; rw [hk] at hb; exact absurd hb (by simp)
          simp only [hk] at hg
          simp only [accPortSubst_kind_left, hk, portSubstValue_left]
          rw [hg]
          constructor
          · rintro ⟨u, he, hv⟩
            exact ⟨Fin.castAdd _ u, accPortSubst_edge_to_left.mpr (Or.inl ⟨u, rfl, he⟩),
              by rw [portSubstValue_left]; exact hv⟩
          · rintro ⟨U, hU, hUv⟩
            rcases accPortSubst_edge_to_left.mp hU with ⟨u, rfl, he⟩ | ⟨i, bneg, _, hk'⟩
            · exact ⟨u, he, by rwa [portSubstValue_left] at hUv⟩
            · exact absurd hk' (hlit _ _)
      | modGate =>
          have hlit : ∀ (j : Fin (n + p)) (b : Bool), c.kind g ≠ .literal j b := by
            intro j b hb; rw [hk] at hb; exact absurd hb (by simp)
          simp only [hk] at hg
          simp only [accPortSubst_kind_left, hk, portSubstValue_left]
          rw [hg, accPortSubst_card_left hlit]
          simp only [portSubstValue_left]
  | right s =>
      obtain ⟨i, g, rfl⟩ := exists_sigma_repr beta s
      have hg := hvb i g
      cases hk : (beta i).kind g with
      | literal j bneg =>
          simp only [hk] at hg
          simp only [accPortSubst_kind_right, hk, portSubstValue_right]
          exact hg
      | andGate =>
          simp only [hk] at hg
          simp only [accPortSubst_kind_right, hk, portSubstValue_right]
          rw [hg]
          constructor
          · intro H U hU
            obtain ⟨h, rfl, he⟩ := accPortSubst_edge_to_right.mp hU
            rw [portSubstValue_right]
            exact H h he
          · intro H h he
            have := H _ (accPortSubst_edge_to_right.mpr ⟨h, rfl, he⟩)
            rwa [portSubstValue_right] at this
      | orGate =>
          simp only [hk] at hg
          simp only [accPortSubst_kind_right, hk, portSubstValue_right]
          rw [hg]
          constructor
          · rintro ⟨h, he, hv⟩
            exact ⟨_, accPortSubst_edge_to_right.mpr ⟨h, rfl, he⟩,
              by rw [portSubstValue_right]; exact hv⟩
          · rintro ⟨U, hU, hUv⟩
            obtain ⟨h, rfl, he⟩ := accPortSubst_edge_to_right.mp hU
            exact ⟨h, he, by rwa [portSubstValue_right] at hUv⟩
      | notGate =>
          simp only [hk] at hg
          simp only [accPortSubst_kind_right, hk, portSubstValue_right]
          rw [hg]
          constructor
          · rintro ⟨h, he, hv⟩
            exact ⟨_, accPortSubst_edge_to_right.mpr ⟨h, rfl, he⟩,
              by rw [portSubstValue_right]; exact hv⟩
          · rintro ⟨U, hU, hUv⟩
            obtain ⟨h, rfl, he⟩ := accPortSubst_edge_to_right.mp hU
            exact ⟨h, he, by rwa [portSubstValue_right] at hUv⟩
      | modGate =>
          simp only [hk] at hg
          simp only [accPortSubst_kind_right, hk, portSubstValue_right]
          rw [hg, accPortSubst_card_right]
          simp only [portSubstValue_right]

/-- Semantic substitution: the valuation of the substituted circuit matches
the wrapper evaluated on the inputs concatenated with the beta outputs. -/
theorem evalACC_accPortSubst {c : ACCCircuit (n + p) m} {beta : Fin p → ACCCircuit n m}
    (hc : WellFormedACC c) (hbeta : ∀ g, WellFormedACC (beta g))
    (x : Fin n → Bool) :
    let x_ext := Fin.addCases (motive := fun _ => Bool) x
      (fun i => evalACC (beta i) (hbeta i) x (beta i).output)
    ACCAccepts (accPortSubst c beta) x ↔ ACCAccepts c x_ext := by
  intro x_ext
  have hvb : ∀ i, ACCValuation (beta i) x (evalACC (beta i) (hbeta i) x) :=
    fun i => (accValuation_iff_eq_evalACC (hbeta i)).mpr rfl
  have hvc : ACCValuation c x_ext (evalACC c hc x_ext) :=
    (accValuation_iff_eq_evalACC hc).mpr rfl
  have hV := accValuation_accPortSubst (vb := fun i => evalACC (beta i) (hbeta i) x) hc hvb hvc
  constructor
  · rintro ⟨w, hw, hout⟩
    have hwe := accValuation_unique (wellFormedACC_accPortSubst c beta hc hbeta) hw hV
    rw [hwe, accPortSubst_output, portSubstValue_left] at hout
    exact ⟨evalACC c hc x_ext, hvc, hout⟩
  · rintro ⟨w, hw, hout⟩
    have hwe : w = evalACC c hc x_ext := (accValuation_iff_eq_evalACC hc).mp hw
    refine ⟨_, hV, ?_⟩
    rw [accPortSubst_output, portSubstValue_left, ← hwe]
    exact hout

end AllenderOQ3.Internal
