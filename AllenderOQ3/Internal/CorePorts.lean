import AllenderOQ3.Internal.Prune
import AllenderOQ3.Internal.BlockGenus
import AllenderOQ3.Internal.CoreExtract
import AllenderOQ3.Internal.GenusBudget
import AllenderOQ3.Internal.Surgery

set_option autoImplicit false

namespace AllenderOQ3.Internal

variable {n : Nat} (c : ADRCircuit n) (v o : Fin c.gateCount)

noncomputable def coreMask (a b : Fin c.gateCount) : Bool :=
  (a ∈ coreSet c v o) && (b ∈ coreSet c v o)

theorem coreSet_predClosed_in_mask :
    ∀ z ∈ coreSet c v o, ∀ (u : Fin c.gateCount),
      (maskCircuit c (coreMask c v o)).edge u z = true → u ∈ coreSet c v o := by
  intro z _ u hedge
  unfold maskCircuit coreMask at hedge
  dsimp only at hedge
  split at hedge
  · next h =>
    revert h
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    rintro ⟨ha, _⟩
    exact ha
  · contradiction

variable (hv : v ∈ coreSet c v o) (ho : o ∈ coreSet c v o)

noncomputable def coreWithPorts : ADRCircuit n :=
  restrict (maskCircuit c (coreMask c v o))
    (@subEmbeddingOfFinset n (maskCircuit c (coreMask c v o)) (coreSet c v o)
      (coreSet_predClosed_in_mask c v o))
    ((coreSet c v o).equivFin ⟨o, ho⟩)

@[simp] theorem coreWithPorts_gateCount : (coreWithPorts c v o ho).gateCount = (coreSet c v o).card
  := rfl

@[simp] theorem coreWithPorts_kind (g : Fin (coreSet c v o).card) :
    (coreWithPorts c v o ho).kind g = c.kind ((coreSet c v o).equivFin.symm g) := by
  rfl

@[simp] theorem coreWithPorts_layer (g : Fin (coreSet c v o).card) :
    (coreWithPorts c v o ho).layer g = c.layer ((coreSet c v o).equivFin.symm g) := by
  rfl

@[simp] theorem coreWithPorts_edge (g h : Fin (coreSet c v o).card) :
    (coreWithPorts c v o ho).edge g h = c.edge ((coreSet c v o).equivFin.symm g)
      ((coreSet c v o).equivFin.symm h) := by
  dsimp [coreWithPorts, subEmbeddingOfFinset, restrict]
  simp [coreMask, ((coreSet c v o).equivFin.symm g).2, ((coreSet c v o).equivFin.symm h).2]

theorem wellFormedADR_coreWithPorts (hwf : WellFormedADR c) :
    WellFormedADR (coreWithPorts c v o ho) := by
  constructor
  · intro u z hedge
    simp only [coreWithPorts_edge] at hedge
    exact hwf.1 _ _ hedge
  · intro g hkind h
    simp only [coreWithPorts_edge]
    have hkind' : ∃ i b, c.kind ((coreSet c v o).equivFin.symm g) = .literal i b := by
      rcases hkind with ⟨i, b, hg⟩
      simp only [coreWithPorts_kind] at hg
      exact ⟨i, b, hg⟩
    exact hwf.2 _ hkind' _

theorem rotationPlanar_coreWithPorts (hplanar : RotationPlanar c) :
    RotationPlanar (coreWithPorts c v o ho) := by
  rw [rotationPlanar_iff_genus_zero] at hplanar ⊢
  have h1 : orientableCircuitGenus (maskCircuit c (coreMask c v o)) ≤ orientableCircuitGenus c :=
    genus_maskCircuit_le c _
  have h2 : orientableCircuitGenus (coreWithPorts c v o ho) =
      orientableCircuitGenus (maskCircuit c (coreMask c v o)) := by
    apply genus_restrict_isolated
    intro g hnot h
    have hg_not_mem : g ∉ coreSet c v o := by
      intro hg
      have := hnot ((coreSet c v o).equivFin ⟨g, hg⟩)
      have hsimp :
        (@subEmbeddingOfFinset n (maskCircuit c (coreMask c v o)) (coreSet c v o)
        (coreSet_predClosed_in_mask c v o)).toFun ((coreSet c v o).equivFin ⟨g, hg⟩) = g := by
        dsimp [subEmbeddingOfFinset]
        rw [Equiv.symm_apply_apply]
      exact this hsimp
    simp [maskCircuit_edge, coreMask, hg_not_mem]
  omega

theorem isGraphSink_coreWithPorts_output (hwf : WellFormedADR c) :
    IsGraphSink (coreWithPorts c v o ho) (coreWithPorts c v o ho).output := by
  intro u
  have : (coreWithPorts c v o ho).output = ((coreSet c v o).equivFin ⟨o, ho⟩) := rfl
  rw [this]
  simp only [coreWithPorts_edge, Equiv.symm_apply_apply]
  cases h_edge : c.edge o ((coreSet c v o).equivFin.symm u).1
  · rfl
  · exfalso
    have hu_mem := ((coreSet c v o).equivFin.symm u).2
    have hu_reach : EdgeReach c ((coreSet c v o).equivFin.symm u).1 o := (mem_coreSet.mp hu_mem).2.2
    have hu_layer_le := edgeReach_layer_le hwf hu_reach
    have hedge_layer : c.layer o + 1 = c.layer ((coreSet c v o).equivFin.symm u).1 :=
      hwf.1 _ _ h_edge
    omega

theorem isGraphSource_coreWithPorts_v (hwf : WellFormedADR c) (hv : v ∈ coreSet c v o) :
    IsGraphSource (coreWithPorts c v o ho) ((coreSet c v o).equivFin ⟨v, hv⟩) := by
  intro u
  simp only [coreWithPorts_edge, Equiv.symm_apply_apply]
  cases h_edge : c.edge ((coreSet c v o).equivFin.symm u).1 v
  · rfl
  · exfalso
    have hu_mem := ((coreSet c v o).equivFin.symm u).2
    have hu_reach : EdgeReach c v ((coreSet c v o).equivFin.symm u).1 := (mem_coreSet.mp hu_mem).2.1
    have hv_layer_le := edgeReach_layer_le hwf hu_reach
    have hedge_layer : c.layer ((coreSet c v o).equivFin.symm u).1 + 1 = c.layer v :=
      hwf.1 _ _ h_edge
    omega

theorem totalWidthAtMost_coreWithPorts :
    TotalWidthAtMost (coreWithPorts c v o ho) c.gateCount := by
  intro ell
  dsimp [TotalWidthAtMost]
  have h1 :
    (Finset.univ.filter fun g : Fin (coreWithPorts c v o ho).gateCount =>
    (coreWithPorts c v o ho).layer g = ell).card ≤
    (Finset.univ : Finset (Fin (coreWithPorts c v o ho).gateCount)).card :=
    Finset.card_filter_le _ _
  have h_bound : (Finset.univ : Finset (Fin (coreWithPorts c v o ho).gateCount)).card ≤ c.gateCount
    := by
    simp only [coreWithPorts_gateCount, Finset.card_univ, Fintype.card_fin]
    have h_le := (coreSet c v o).card_le_univ
    simp only [Fintype.card_fin] at h_le
    exact h_le
  exact le_trans h1 h_bound

/-- Taking the core can only remove incoming edges. -/
theorem predecessorCount_coreWithPorts_le_orig (g : Fin (coreSet c v o).card) :
    predecessorCount (coreWithPorts c v o ho) g ≤
      predecessorCount c ((coreSet c v o).equivFin.symm g) := by
  dsimp [predecessorCount]
  apply Finset.card_le_card_of_injOn (fun h => ((coreSet c v o).equivFin.symm h).1)
  · intro h hh
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hh ⊢
    simp only [coreWithPorts_edge] at hh
    exact hh
  · intro a _ b _ heq
    have heq2 : ((coreSet c v o).equivFin.symm a) = ((coreSet c v o).equivFin.symm b) :=
      Subtype.ext heq
    exact Equiv.injective _ heq2

/-- A fanin bound on the computation gates of `c` is inherited by the extracted core. -/
theorem predecessorCount_coreWithPorts_le_fanin {F : Nat}
    (h_pred : ∀ g, (c.kind g).isComputation = true → predecessorCount c g ≤ F) :
    ∀ g, predecessorCount (coreWithPorts c v o ho) g ≤ F := by
  intro g
  have h_comp : (c.kind ((coreSet c v o).equivFin.symm g)).isComputation = true := by
    have hg := ((coreSet c v o).equivFin.symm g).2
    simp only [mem_coreSet] at hg
    exact hg.1
  exact le_trans (predecessorCount_coreWithPorts_le_orig c v o ho g) (h_pred _ h_comp)

theorem predecessorCount_coreWithPorts_le
  (h_pred : ∀ g, (c.kind g).isComputation = true → predecessorCount c g ≤ 2) :
    ∀ g, predecessorCount (coreWithPorts c v o ho) g ≤ 2 :=
  predecessorCount_coreWithPorts_le_fanin c v o ho h_pred

/-- Every non-source gate of the core has a predecessor inside the core. -/
theorem coreSet_exists_pred {n : Nat} {c : ADRCircuit n} (hc : WellFormedADR c)
    {v o z : Fin c.gateCount} (hv : v ∈ coreSet c v o) (hz : z ∈ coreSet c v o)
    (hzv : z ≠ v) :
    ∃ u ∈ coreSet c v o, c.edge u z = true := by
  obtain ⟨-, hvz, hzo⟩ := mem_coreSet.mp hz
  rcases Relation.ReflTransGen.cases_tail hvz with hrefl | ⟨d, hvd, hedge⟩
  · exact absurd hrefl hzv
  · refine ⟨d, mem_coreSet.mpr ⟨?_, hvd, Relation.ReflTransGen.head hedge hzo⟩, hedge⟩
    rcases Relation.ReflTransGen.cases_tail hvd with hrefl | ⟨b, -, hbd⟩
    · rw [hrefl]; exact (mem_coreSet.mp hv).1
    · exact isComputation_of_edge hc hbd

/-- Every non-sink gate of the core has a successor inside the core. -/
theorem coreSet_exists_succ {n : Nat} {c : ADRCircuit n} (hc : WellFormedADR c)
    {v o z : Fin c.gateCount} (hz : z ∈ coreSet c v o) (hzo : z ≠ o) :
    ∃ u ∈ coreSet c v o, c.edge z u = true := by
  obtain ⟨-, hvz, hzo'⟩ := mem_coreSet.mp hz
  rcases Relation.ReflTransGen.cases_head hzo' with hrefl | ⟨u, hedge, huo⟩
  · exact absurd hrefl hzo
  · exact ⟨u, mem_coreSet.mpr ⟨isComputation_of_edge hc hedge,
      Relation.ReflTransGen.tail hvz hedge, huo⟩, hedge⟩

/-- **Unique sink.**  The output of the extracted core is its only graph sink. -/
theorem uniqueSink_coreWithPorts (hwf : WellFormedADR c) :
    ∃! t, IsGraphSink (coreWithPorts c v o ho) t := by
  refine ⟨(coreWithPorts c v o ho).output, isGraphSink_coreWithPorts_output c v o ho hwf, ?_⟩
  intro t ht
  by_contra hne
  have hzo : ((coreSet c v o).equivFin.symm t).1 ≠ o := by
    intro hz
    apply hne
    have : (coreSet c v o).equivFin.symm t = ⟨o, ho⟩ := Subtype.ext hz
    have hout : (coreWithPorts c v o ho).output = (coreSet c v o).equivFin ⟨o, ho⟩ := rfl
    rw [hout, ← this, Equiv.apply_symm_apply]
  obtain ⟨u, hu, hedge⟩ :=
    coreSet_exists_succ hwf ((coreSet c v o).equivFin.symm t).2 hzo
  have hfalse := ht ((coreSet c v o).equivFin ⟨u, hu⟩)
  rw [coreWithPorts_edge, Equiv.symm_apply_apply] at hfalse
  rw [hedge] at hfalse
  exact Bool.noConfusion hfalse

/-- **Unique source.**  The entry gate `v` is the only graph source of the extracted core. -/
theorem uniqueSource_coreWithPorts (hwf : WellFormedADR c) (hv : v ∈ coreSet c v o) :
    ∃! s, IsGraphSource (coreWithPorts c v o ho) s := by
  refine ⟨(coreSet c v o).equivFin ⟨v, hv⟩,
    isGraphSource_coreWithPorts_v c v o ho hwf hv, ?_⟩
  intro t ht
  by_contra hne
  have hzv : ((coreSet c v o).equivFin.symm t).1 ≠ v := by
    intro hz
    apply hne
    have : (coreSet c v o).equivFin.symm t = ⟨v, hv⟩ := Subtype.ext hz
    rw [← this, Equiv.apply_symm_apply]
  obtain ⟨u, hu, hedge⟩ :=
    coreSet_exists_pred hwf hv ((coreSet c v o).equivFin.symm t).2 hzv
  have hfalse := ht ((coreSet c v o).equivFin ⟨u, hu⟩)
  rw [coreWithPorts_edge, Equiv.symm_apply_apply] at hfalse
  rw [hedge] at hfalse
  exact Bool.noConfusion hfalse

/-- **Core width bound.**  Every gate of the core is a computation gate of `c` on the same
layer, so the *total* width of the extracted core is bounded by the *computation* width
of `c`. -/
theorem totalWidthAtMost_coreWithPorts_of_widthAtMost {w : Nat}
    (hw : ADRHasWidthAtMost c w) :
    TotalWidthAtMost (coreWithPorts c v o ho) w := by
  classical
  intro ell
  refine le_trans (Finset.card_le_card_of_injOn
    (fun g => ((coreSet c v o).equivFin.symm g).1) ?_ ?_) (hw ell)
  · intro g hg
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and,
      coreWithPorts_layer] at hg
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and]
    exact ⟨hg, (mem_coreSet.mp ((coreSet c v o).equivFin.symm g).2).1⟩
  · intro a _ b _ heq
    exact Equiv.injective _ (Subtype.ext heq)

end AllenderOQ3.Internal
