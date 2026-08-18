import AllenderOQ3.Internal.OrbitCount

/-!
# Invariance of the combinatorial counts under isomorphism

`componentCount` and `permCycleCount` are both defined by counting the
`rank`-minimal representative of each class of an equivalence relation.  This
file identifies those counts with `Nat.card` of the corresponding quotient,
which makes them manifestly invariant under any relation-preserving bijection.
-/

set_option autoImplicit false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace AllenderOQ3.Internal

/-- Counting `rank`-minimal representatives counts the classes of `r`. -/
theorem card_minReps_eq_natCard_quot {α : Type} [Fintype α] {r : α → α → Prop}
    (hr : Equivalence r) (rank : α → Nat) (hrank : Function.Injective rank)
    [DecidablePred fun x => ∀ y, r x y → rank x ≤ rank y] :
    (Finset.univ.filter fun x => ∀ y, r x y → rank x ≤ rank y).card
      = Nat.card (Quot r) := by
  classical
  have hbij : Function.Bijective
      (fun x : {x : α // ∀ y, r x y → rank x ≤ rank y} => Quot.mk r x.1) := by
    constructor
    · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
      have hrxy : r x y := (hr.eqvGen_iff).mp (Quot.eq.mp hxy)
      exact Subtype.ext (minRep_unique hr rank hrank hrxy hx hy)
    · intro q
      induction q using Quot.ind with
      | _ a =>
        obtain ⟨x, hax, hx⟩ := exists_minRep hr rank a
        exact ⟨⟨x, hx⟩, (Quot.sound hax).symm⟩
  have h1 : Nat.card {x : α // ∀ y, r x y → rank x ≤ rank y} = Nat.card (Quot r) :=
    Nat.card_eq_of_bijective _ hbij
  rw [← h1, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- The number of classes only depends on the relation up to isomorphism. -/
theorem natCard_quot_congr {α β : Type} (e : α ≃ β) {r : α → α → Prop} {s : β → β → Prop}
    (h : ∀ a b, r a b ↔ s (e a) (e b)) : Nat.card (Quot r) = Nat.card (Quot s) :=
  Nat.card_congr (Quot.congr e h)

/-- Iterating a conjugated permutation is the conjugate of the iterate. -/
theorem pow_conj_apply {α β : Type} (phi : α ≃ β) (r : Equiv.Perm β) (k : Nat) (d : α) :
    ((phi.trans (r.trans phi.symm)) ^ k) d = phi.symm ((r ^ k) (phi d)) := by
  induction k generalizing d with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, Equiv.Perm.mul_apply, ih]
      simp [pow_succ, Equiv.Perm.mul_apply]

/-- The orbit relation of a permutation. -/
def OrbitRel {α : Type} (p : Equiv.Perm α) (x y : α) : Prop := ∃ k : Nat, (p ^ k) x = y

theorem orbitRel_equivalence {α : Type} [Fintype α] [DecidableEq α] (p : Equiv.Perm α) :
    Equivalence (OrbitRel p) := by
  constructor
  · intro x; exact ⟨0, rfl⟩
  · intro x y hxy; exact perm_forwardReach_symm p hxy
  · rintro x y z ⟨k1, hk1⟩ ⟨k2, hk2⟩
    exact ⟨k2 + k1, by rw [pow_add, Equiv.Perm.mul_apply, hk1, hk2]⟩

/-- `permCycleCount` counts the orbits of the permutation. -/
theorem permCycleCount_eq_natCard_quot {α : Type} [Fintype α] [DecidableEq α]
    (p : Equiv.Perm α) : permCycleCount p = Nat.card (Quot (OrbitRel p)) := by
  classical
  have hrank : Function.Injective (fun y : α => (Fintype.equivFin α y).val) := by
    intro x y hxy
    exact (Fintype.equivFin α).injective (Fin.ext hxy)
  have := card_minReps_eq_natCard_quot (orbitRel_equivalence p)
    (fun y : α => (Fintype.equivFin α y).val) hrank
  unfold permCycleCount
  simpa [OrbitRel] using this

/-- Conjugating a permutation by a bijection does not change its cycle count. -/
theorem permCycleCount_conj_quot {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (phi : α ≃ β) (p : Equiv.Perm β) :
    permCycleCount (phi.trans (p.trans phi.symm)) = permCycleCount p := by
  rw [permCycleCount_eq_natCard_quot, permCycleCount_eq_natCard_quot]
  refine natCard_quot_congr phi ?_
  intro a b
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have := congrArg phi hk
    rwa [pow_conj_apply phi p k a, Equiv.apply_symm_apply] at this
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [pow_conj_apply phi p k a, hk, Equiv.symm_apply_apply]

/-- `componentCount` counts the connected components of the underlying graph. -/
theorem componentCount_eq_natCard_quot {n : Nat} (c : ADRCircuit n) :
    componentCount c = Nat.card (Quot (VertexReachable c)) := by
  classical
  have := card_minReps_eq_natCard_quot (vertexReachable_equiv c) Fin.val Fin.val_injective
  unfold componentCount
  simpa using this

/-- Transport a rotation system along an isomorphism of dart sets that respects
the "same source" relation. -/
noncomputable def transportRotation {n : Nat} {c₁ c₂ : ADRCircuit n}
    (phi : CircuitDart c₁ ≃ CircuitDart c₂)
    (hs : ∀ d e : CircuitDart c₁, (phi d).source = (phi e).source ↔ d.source = e.source)
    (r : OrientableRotation c₂) : OrientableRotation c₁ where
  rotation := phi.trans (r.rotation.trans phi.symm)
  preservesSource := by
    intro d
    refine (hs _ d).mp ?_
    change (phi (phi.symm (r.rotation (phi d)))).source = (phi d).source
    rw [Equiv.apply_symm_apply]
    exact r.preservesSource _
  cyclicAtVertex := by
    intro d e hde
    obtain ⟨k, hk⟩ := r.cyclicAtVertex (phi d) (phi e) ((hs d e).mpr hde)
    exact ⟨k, by rw [pow_conj_apply, hk, Equiv.symm_apply_apply]⟩

/-- If the dart isomorphism also commutes with dart reversal, the transported
rotation has the conjugate face permutation, hence the same number of faces. -/
theorem permCycleCount_facePermutation_transport {n : Nat} {c₁ c₂ : ADRCircuit n}
    (phi : CircuitDart c₁ ≃ CircuitDart c₂)
    (hs : ∀ d e : CircuitDart c₁, (phi d).source = (phi e).source ↔ d.source = e.source)
    (hr : ∀ d, phi (dartReverse c₁ d) = dartReverse c₂ (phi d))
    (r : OrientableRotation c₂) :
    permCycleCount (facePermutation (transportRotation phi hs r))
      = permCycleCount (facePermutation r) := by
  classical
  have hface : facePermutation (transportRotation phi hs r)
      = phi.trans ((facePermutation r).trans phi.symm) := by
    apply Equiv.ext
    intro d
    change (transportRotation phi hs r).rotation (dartReverse c₁ d)
      = phi.symm (r.rotation (dartReverse c₂ (phi d)))
    change phi.symm (r.rotation (phi (dartReverse c₁ d)))
      = phi.symm (r.rotation (dartReverse c₂ (phi d)))
    rw [hr]
  rw [hface, permCycleCount_conj_quot]

/-- Handshake lemma: an undirected edge count is half the number of darts. -/
theorem two_mul_edgeCount {V : Type} [Fintype V] (rank : V → Nat)
    (hrank : Function.Injective rank) (Adj : V → V → Prop) [DecidableRel Adj]
    (hirr : ∀ u v, Adj u v → u ≠ v) (hsymm : ∀ u v, Adj u v → Adj v u) :
    2 * ∑ u : V, (Finset.univ.filter (fun v => rank u < rank v ∧ Adj u v)).card
      = Fintype.card {p : V × V // Adj p.1 p.2} := by
  classical
  have key : ∀ (Q : V → V → Prop) (_ : ∀ a b, Decidable (Q a b)),
      ∑ u : V, (Finset.univ.filter (fun v => Q u v)).card
        = Fintype.card {p : V × V // Q p.1 p.2} := by
    intro Q inst
    letI := inst
    rw [Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype Q), Fintype.card_sigma]
    simp [Fintype.card_subtype]
  have hA := key (fun a b => rank a < rank b ∧ Adj a b) inferInstance
  have hB := key (fun a b => rank b < rank a ∧ Adj a b) inferInstance
  have hAll := key (fun a b => Adj a b) inferInstance
  have hAB : Fintype.card {p : V × V // rank p.1 < rank p.2 ∧ Adj p.1 p.2}
      = Fintype.card {p : V × V // rank p.2 < rank p.1 ∧ Adj p.1 p.2} := by
    refine Fintype.card_congr ⟨fun p => ⟨p.1.swap, ⟨p.2.1, hsymm _ _ p.2.2⟩⟩,
      fun p => ⟨p.1.swap, ⟨p.2.1, hsymm _ _ p.2.2⟩⟩, ?_, ?_⟩ <;>
      · rintro ⟨⟨a, b⟩, h⟩; rfl
  have hsplit : ∀ u : V, (Finset.univ.filter (fun v => Adj u v)).card
      = (Finset.univ.filter (fun v => rank u < rank v ∧ Adj u v)).card
        + (Finset.univ.filter (fun v => rank v < rank u ∧ Adj u v)).card := by
    intro u
    have e1 : (Finset.univ.filter (fun v => Adj u v)).filter (fun v => rank u < rank v)
        = Finset.univ.filter (fun v => rank u < rank v ∧ Adj u v) := by
      ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact and_comm
    have e2 : (Finset.univ.filter (fun v => Adj u v)).filter (fun v => ¬ rank u < rank v)
        = Finset.univ.filter (fun v => rank v < rank u ∧ Adj u v) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hadj, hnot⟩
        have hne : rank u ≠ rank x := fun h => (hirr _ _ hadj) (hrank h)
        exact ⟨by omega, hadj⟩
      · rintro ⟨hlt, hadj⟩
        exact ⟨hadj, by omega⟩
    rw [← e1, ← e2, Finset.card_filter_add_card_filter_not]
  rw [← hAll, Finset.sum_congr rfl (fun u _ => hsplit u), Finset.sum_add_distrib, hA, hB, ← hAB]
  ring

/-- Twice the number of underlying edges is the number of darts. -/
theorem two_mul_underlyingEdgeCount {n : Nat} (c : ADRCircuit n) :
    2 * underlyingEdgeCount c = Fintype.card (CircuitDart c) := by
  classical
  have h := two_mul_edgeCount (V := Fin c.gateCount) Fin.val Fin.val_injective
    (UnderlyingAdj c) (fun u v h => h.2) (fun u v h => ⟨h.1.elim Or.inr Or.inl, Ne.symm h.2⟩)
  unfold underlyingEdgeCount
  simpa using h

end AllenderOQ3.Internal
