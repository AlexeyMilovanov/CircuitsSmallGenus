import AllenderOQ3.Internal.Subcircuit

set_option autoImplicit false

namespace AllenderOQ3.Internal

/-- `isComputation` is `false` exactly for literal gates. -/
theorem isComputation_eq_false {n : Nat} : ∀ (x : ADRGate n),
    x.isComputation = false → ∃ i b, x = ADRGate.literal i b := by
  intro x hx
  cases x with
  | literal i b => exact ⟨i, b, rfl⟩
  | andGate => simp [ADRGate.isComputation] at hx
  | orGate => simp [ADRGate.isComputation] at hx

-- `hg` (that `g` is a literal) is not needed for the proof, but it documents
-- intent and matches the downstream caller; suppress the unused-variable lint.
set_option linter.unusedVariables false in
/-- A gate reached by an edge out of a non-computation (literal) gate is itself a
computation gate: literal gates have no incoming edges, so the target of an edge
cannot be a literal. -/
theorem literal_succ_isComputation {n : Nat} {c : ADRCircuit n} (hc : WellFormedADR c)
    {g h : Fin c.gateCount} (hg : (c.kind g).isComputation = false)
    (he : c.edge g h = true) : (c.kind h).isComputation = true := by
  have hcomp : (c.kind h).isComputation ≠ false := by
    intro hfalse
    obtain ⟨i, b, hib⟩ := isComputation_eq_false (c.kind h) hfalse
    have hno : c.edge g h = false := hc.2 h ⟨i, b, hib⟩ g
    rw [he] at hno
    exact Bool.noConfusion hno
  cases hb : (c.kind h).isComputation with
  | false => exact (hcomp hb).elim
  | true => rfl

theorem card_live_literals_le {n : Nat} {c : ADRCircuit n} (hc : WellFormedADR c) {w : Nat}
    (hw : ADRHasWidthAtMost c w)
    (hfan : ∀ g, (c.kind g).isComputation = true → predecessorCount c g ≤ 2)
    (l : Nat) :
    (Finset.univ.filter (fun g : Fin c.gateCount =>
      c.layer g = l ∧ (c.kind g).isComputation = false ∧
        ∃ h, c.edge g h = true)).card ≤ 2 * w := by
  classical
  set S := Finset.univ.filter (fun g : Fin c.gateCount =>
      c.layer g = l ∧ (c.kind g).isComputation = false ∧
        ∃ h, c.edge g h = true) with hS
  set f : Fin c.gateCount → Fin c.gateCount := fun g =>
    if hg : ∃ h, c.edge g h = true then Classical.choose hg else g with hf
  have hedge : ∀ g ∈ S, c.edge g (f g) = true := by
    intro g hg
    rw [hS, Finset.mem_filter] at hg
    obtain ⟨-, -, -, hex⟩ := hg
    simp only [hf, dif_pos hex]
    exact Classical.choose_spec hex
  have hfiber : ∀ b ∈ Finset.image f S, {a ∈ S | f a = b}.card ≤ 2 := by
    intro b hb
    rw [Finset.mem_image] at hb
    obtain ⟨a, ha, hab⟩ := hb
    have hacomp : (c.kind a).isComputation = false := by
      rw [hS, Finset.mem_filter] at ha; exact ha.2.2.1
    have hbcomp : (c.kind b).isComputation = true := by
      have := literal_succ_isComputation hc hacomp (hab ▸ hedge a ha)
      exact this
    refine le_trans (Finset.card_le_card ?_) (hfan b hbcomp)
    intro x hx
    rw [Finset.mem_filter] at hx
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ x, ?_⟩
    have := hedge x hx.1
    rw [hx.2] at this
    exact this
  have hcard := Finset.card_le_mul_card_image (f := f) S 2 hfiber
  have himg : (Finset.image f S).card ≤ w := by
    refine le_trans (Finset.card_le_card ?_) (hw (l + 1))
    intro b hb
    rw [Finset.mem_image] at hb
    obtain ⟨a, ha, hab⟩ := hb
    have ha' := ha
    rw [hS, Finset.mem_filter] at ha'
    obtain ⟨-, hlayer, hacomp, -⟩ := ha'
    have hedgea : c.edge a b = true := hab ▸ hedge a ha
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ b, ?_, literal_succ_isComputation hc hacomp hedgea⟩
    have := hc.1 a b hedgea
    omega
  omega

/-- In a properly layered circuit all predecessors of a gate `g` sit on the single layer
`c.layer g - 1`, so a bound on the *total* width of that layer is a fan-in bound. -/
theorem predecessorCount_le_of_totalWidth {n : Nat} {c : ADRCircuit n}
    (hc : ProperLayered c) {W : Nat} (hw : TotalWidthAtMost c W) (g : Fin c.gateCount) :
    predecessorCount c g ≤ W := by
  classical
  refine le_trans (Finset.card_le_card ?_) (hw (c.layer g - 1))
  intro h hh
  rw [Finset.mem_filter] at hh ⊢
  refine ⟨Finset.mem_univ h, ?_⟩
  have := hc h g hh.2
  omega

theorem totalWidth_of_computationWidth {n : Nat} {c : ADRCircuit n} (hc : WellFormedADR c) {w : Nat}
    (hw : ADRHasWidthAtMost c w)
    (hfan : ∀ g, (c.kind g).isComputation = true → predecessorCount c g ≤ 2)
    (hlive : ∀ g, (c.kind g).isComputation = false → g ≠ c.output →
      ∃ h, c.edge g h = true) :
    TotalWidthAtMost c (3 * w + 1) := by
  classical
  intro ell
  set A := Finset.univ.filter (fun g : Fin c.gateCount =>
    c.layer g = ell ∧ (c.kind g).isComputation = true)
  set B := Finset.univ.filter (fun g : Fin c.gateCount =>
    c.layer g = ell ∧ (c.kind g).isComputation = false ∧
      ∃ h, c.edge g h = true)
  have hsub : Finset.univ.filter (fun g : Fin c.gateCount => c.layer g = ell)
      ⊆ (A ∪ B) ∪ {c.output} := by
    intro g hg
    rw [Finset.mem_filter] at hg
    obtain ⟨-, hl⟩ := hg
    by_cases hcomp : (c.kind g).isComputation = true
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ g, hl, hcomp⟩))
    · have hcf : (c.kind g).isComputation = false := by
        simpa using Bool.eq_false_iff.mpr hcomp
      by_cases hgo : g = c.output
      · exact Finset.mem_union_right _ (Finset.mem_singleton.mpr hgo)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨Finset.mem_univ g, hl, hcf, hlive g hcf hgo⟩))
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le (A ∪ B) ({c.output} : Finset (Fin c.gateCount))
  have h3 := Finset.card_union_le A B
  have h4 : A.card ≤ w := hw ell
  have h5 : B.card ≤ 2 * w := card_live_literals_le hc hw hfan ell
  have h6 : ({c.output} : Finset (Fin c.gateCount)).card = 1 := Finset.card_singleton _
  omega

end AllenderOQ3.Internal
