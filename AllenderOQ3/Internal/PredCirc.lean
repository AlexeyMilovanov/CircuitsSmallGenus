import AllenderOQ3.Internal.ACCGadgets
import AllenderOQ3.Internal.ModulusLift
import AllenderOQ3.Internal.BlockAssembly

/-!
# Predicate circuits: a bookkeeping layer over the ACC gadgets

Almost every circuit built in the local-divisor compression argument is used
only through the four data "well formed / depth at most `d` / size at most
`Sz` / accepts exactly the inputs satisfying `P`".  `PredCirc` bundles those
four facts and `HasPredCirc` existentially quantifies the circuit, so that the
combinators (conjunction, disjunction of conjunctions, modulus lifting,
predicates of a letter value) read as closure properties of a single
predicate.

Everything here is `sorry`-free.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace AllenderOQ3
namespace Internal

variable {n m : Nat}

/-- `a` decides `P` with depth budget `d` and size budget `Sz`. -/
structure PredCirc (n m d Sz : Nat) (P : (Fin n → Bool) → Prop) (a : ACCCircuit n m) : Prop where
  wf : WellFormedACC a
  lay : ∀ q, a.layer q ≤ d
  sz : a.gateCount ≤ Sz
  acc : ∀ x, ACCAccepts a x ↔ P x

/-- There is a circuit deciding `P` within the depth and size budget. -/
def HasPredCirc (n m d Sz : Nat) (P : (Fin n → Bool) → Prop) : Prop :=
  ∃ a : ACCCircuit n m, PredCirc n m d Sz P a

/-- Weakening the budgets and rewriting the predicate. -/
theorem HasPredCirc.mono {d d' Sz Sz' : Nat} {P Q : (Fin n → Bool) → Prop}
    (h : HasPredCirc n m d Sz P) (hd : d ≤ d') (hSz : Sz ≤ Sz')
    (hPQ : ∀ x, P x ↔ Q x) : HasPredCirc n m d' Sz' Q := by
  obtain ⟨a, ha⟩ := h
  exact ⟨a, ⟨ha.wf, fun q => le_trans (ha.lay q) hd, le_trans ha.sz hSz,
    fun x => (ha.acc x).trans (hPQ x)⟩⟩

/-- The constantly true predicate. -/
theorem hasPredCirc_true : HasPredCirc n m 1 1 (fun _ => True) := by
  refine ⟨accConst n m true, ⟨wellFormedACC_accConst n m true, ?_, ?_, ?_⟩⟩
  · intro q; simp [accConst_layer]
  · simp [accConst_gateCount]
  · intro x; simp [accAccepts_accConst]

/-- The constantly false predicate. -/
theorem hasPredCirc_false : HasPredCirc n m 1 1 (fun _ => False) := by
  refine ⟨accConst n m false, ⟨wellFormedACC_accConst n m false, ?_, ?_, ?_⟩⟩
  · intro q; simp [accConst_layer]
  · simp [accConst_gateCount]
  · intro x; simp [accAccepts_accConst]

/-- Lifting a predicate circuit to a larger modulus. -/
theorem HasPredCirc.lift {M' d Sz : Nat} {P : (Fin n → Bool) → Prop}
    (hdvd : m ∣ M') (hpos : 0 < M') (h : HasPredCirc n m d Sz P) :
    HasPredCirc n M' (2 * d + 2) ((M' + 2) * Sz) P := by
  obtain ⟨a, ha⟩ := h
  refine ⟨accModulusLift a hdvd, ⟨wellFormedACC_accModulusLift a hdvd ha.wf,
    accModulusLift_layer_le ha.lay, ?_, ?_⟩⟩
  · exact le_trans (accModulusLift_gateCount_le a hdvd) (Nat.mul_le_mul_left _ ha.sz)
  · intro x
    rw [evalACC_accModulusLift_of_pos hpos ha.wf x]
    exact ha.acc x

/-- The conjunction of a finite family of predicate circuits. -/
theorem hasPredCirc_bigAnd {K d Sz : Nat} {P : Fin K → (Fin n → Bool) → Prop}
    (h : ∀ i, HasPredCirc n m d Sz (P i)) :
    HasPredCirc n m (d + 2) (K * Sz + 2) (fun x => ∀ i, P i x) := by
  choose f hf using h
  obtain ⟨a, hawf, halay, hasz, haacc⟩ :=
    exists_acc_bigAnd (n := n) (m := m) f (fun i => (hf i).wf) (fun i q => (hf i).lay q)
      (fun i => (hf i).sz)
  exact ⟨a, ⟨hawf, halay, hasz,
    fun x => (haacc x).trans (forall_congr' fun i => (hf i).acc x)⟩⟩

/-- The disjunction over a finite guess type of conjunctions of a fixed number
of predicate circuits. -/
theorem hasPredCirc_orAnd {Gu : Type} [Fintype Gu] {K d Sz : Nat}
    {P : Gu → Fin K → (Fin n → Bool) → Prop}
    (h : ∀ u j, HasPredCirc n m d Sz (P u j)) :
    HasPredCirc n m (d + 2) (Fintype.card Gu * (K * Sz + 1) + 1)
      (fun x => ∃ u, ∀ j, P u j x) := by
  classical
  choose f hf using h
  set ee := Fintype.equivFin Gu with hee
  set blocks : Fin (Fintype.card Gu) → Fin K → ACCCircuit n m := fun i j => f (ee.symm i) j
    with hblocks
  have hbwf : ∀ i j, WellFormedACC (blocks i j) := fun i j => (hf _ _).wf
  have hblay : ∀ i j (q : Fin (blocks i j).gateCount), (blocks i j).layer q ≤ d :=
    fun i j q => (hf _ _).lay q
  refine ⟨accOrAnd blocks d, ⟨wellFormedACC_accOrAnd hbwf hblay, accOrAnd_layer_le hblay, ?_, ?_⟩⟩
  · simp only [accOrAnd_gateCount]
    have hinner : ∀ i : Fin (Fintype.card Gu), (∑ j, (blocks i j).gateCount) + 1 ≤ K * Sz + 1 := by
      intro i
      have hsum : (∑ j, (blocks i j).gateCount) ≤ K * Sz := by
        refine le_trans (Finset.sum_le_card_nsmul Finset.univ _ Sz (fun j _ => (hf _ _).sz)) ?_
        simp
      omega
    have hsum : (∑ i : Fin (Fintype.card Gu), ((∑ j, (blocks i j).gateCount) + 1))
        ≤ Fintype.card Gu * (K * Sz + 1) := by
      refine le_trans (Finset.sum_le_card_nsmul Finset.univ _ _ (fun i _ => hinner i)) ?_
      simp
    omega
  · intro x
    rw [accAccepts_accOrAnd hbwf hblay x]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨ee.symm i, fun j => ((hf _ _).acc x).mp (hi j)⟩
    · rintro ⟨u, hu⟩
      refine ⟨ee u, fun j => ?_⟩
      have : blocks (ee u) j = f u j := by simp [hblocks]
      rw [this]
      exact ((hf u j).acc x).mpr (hu j)

/-- The conjunction of two predicate circuits. -/
theorem hasPredCirc_and {d Sz : Nat} {P Q : (Fin n → Bool) → Prop}
    (hP : HasPredCirc n m d Sz P) (hQ : HasPredCirc n m d Sz Q) :
    HasPredCirc n m (d + 2) (2 * Sz + 2) (fun x => P x ∧ Q x) := by
  obtain ⟨p, hp⟩ := hP
  obtain ⟨q, hq⟩ := hQ
  obtain ⟨a, hawf, halay, hasz, haacc⟩ :=
    exists_acc_orPair (n := n) (m := m) (K := 1) (fun _ => p) (fun _ => q)
      (fun _ => hp.wf) (fun _ => hq.wf) (fun _ => hp.lay) (fun _ => hq.lay)
      (fun _ => hp.sz) (fun _ => hq.sz)
  refine ⟨a, ⟨hawf, halay, by omega, fun x => (haacc x).trans ?_⟩⟩
  constructor
  · rintro ⟨_, h1, h2⟩
    exact ⟨(hp.acc x).mp h1, (hq.acc x).mp h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨0, (hp.acc x).mpr h1, (hq.acc x).mpr h2⟩

/-- The disjunction over a finite guess type. -/
theorem hasPredCirc_exists {Gu : Type} [Fintype Gu] {d Sz : Nat}
    {P : Gu → (Fin n → Bool) → Prop} (h : ∀ u, HasPredCirc n m d Sz (P u)) :
    HasPredCirc n m (d + 2) (Fintype.card Gu * (Sz + 1) + 1) (fun x => ∃ u, P u x) := by
  have hor := hasPredCirc_orAnd (n := n) (m := m) (K := 1) (P := fun u (_ : Fin 1) => P u)
    (fun u _ => h u)
  refine hor.mono le_rfl (by simp) ?_
  intro x
  exact exists_congr fun u => ⟨fun hh => hh 0, fun hh _ => hh⟩

/-- An arbitrary predicate of the value of a letter, from exact recognisers for
that value. -/
theorem hasPredCirc_ofLetter {G : Type} [Fintype G] {d Sz : Nat}
    (p : (Fin n → Bool) → G) (L : G → ACCCircuit n m)
    (hL : ∀ g, PredCirc n m d Sz (fun x => p x = g) (L g)) (P : G → Prop) :
    HasPredCirc n m (max d 1 + 2) (Fintype.card G * (Sz + 2) + 1) (fun x => P (p x)) := by
  obtain ⟨a, hawf, halay, hasz, haacc⟩ :=
    exists_acc_letterPred (n := n) (m := m) L p P (fun g => (hL g).wf) (fun g q => (hL g).lay q)
      (fun g => (hL g).sz) (fun g x => (hL g).acc x)
  exact ⟨a, ⟨hawf, halay, hasz, haacc⟩⟩

/-! ## Reindexing a block product to relative coordinates -/

/-- A `List.range'` product reindexed to start at `0`. -/
theorem prod_range'_reindex {G : Type} [Monoid G] :
    ∀ (k s : Nat) (F : Nat → G),
      ((List.range' s k).map F).prod = ((List.range' 0 k).map (fun r => F (s + r))).prod := by
  intro k
  induction k with
  | zero => intro s F; simp
  | succ k ih =>
    intro s F
    have e1 : ((List.range' s (k + 1)).map F).prod = F s * ((List.range' (s + 1) k).map F).prod := by
      simp [List.range'_succ]
    have e2 : ((List.range' 0 (k + 1)).map (fun r => F (s + r))).prod
        = F (s + 0) * ((List.range' 1 k).map (fun r => F (s + r))).prod := by
      simp [List.range'_succ]
    rw [e1, e2, ih (s + 1) F, ih 1 (fun r => F (s + r))]
    simp only [Nat.add_zero]
    congr 1
    refine congrArg List.prod (List.map_congr_left ?_)
    intro r _
    congr 1
    omega

/-- Blocks in absolute coordinates are blocks of the shifted word in relative
coordinates. -/
theorem blockProd_start_shift {G : Type} [Monoid G] {n : Nat}
    (f : Nat → (Fin n → Bool) → G) (x : Fin n → Bool) (start a b : Nat) :
    blockProd f start a b x = blockProd (fun i x => f (start + i) x) 0 a b x := by
  unfold blockProd
  rw [prod_range'_reindex (b - a) (start + a) (fun i => f i x),
    prod_range'_reindex (b - a) (0 + a) (fun i => f (start + i) x)]
  refine congrArg List.prod (List.map_congr_left ?_)
  intro r _
  congr 1
  omega

end Internal
end AllenderOQ3
