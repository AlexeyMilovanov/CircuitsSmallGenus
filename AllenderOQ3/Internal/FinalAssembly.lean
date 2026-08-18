import AllenderOQ3.Statement
import AllenderOQ3.Internal.Assembly
import AllenderOQ3.Internal.PlanarBlock
import AllenderOQ3.Internal.PolylogCompose
import AllenderOQ3.Internal.ACCOneStep
import AllenderOQ3.Internal.ModulusLift
import AllenderOQ3.Internal.CutChain
import AllenderOQ3.Internal.LayerPlanarizer
import AllenderOQ3.Internal.ACCTruthTable
import AllenderOQ3.Internal.FamilyPackage
import AllenderOQ3.Internal.WidthDiagnostic
import AllenderOQ3.Internal.Glue

set_option autoImplicit false

namespace AllenderOQ3

open AllenderOQ3.Internal

/-- **The final assembly at one input length.**  Given the planar bridge with its
parameters `M, dB, eB` already fixed at computation width `width`, a well-formed circuit
`c` of computation width `≤ width`, polynomial size and genus `≤ gen`, whose output gate
is a computation gate, is simulated by a single `ACC[2M]` circuit of constant depth and
polynomial size, provided the input length is large enough for the §9 round count
(`2 * C ≤ ⌊log₂ (n+1)⌋` and `4 * gen + 3 ≤ C * ⌊log₂ (n+1)⌋ ^ k`).

The proof runs the whole Stream C pipeline: a slot assignment (`exists_layerIndexing_of_width`),
the §4 planarizer (`layerPlanarizer`), the §8 block relation (`planarBlockRelation_at`) and
the local relations (`ACCOneStep`) lifted to the common modulus `2 * M`, and finally the
§6/§9 chain collapse `exists_acc_adrAccepts`. -/
theorem acc_of_bridge_at_length {width M dB eB σ : Nat} (hw : 0 < width) (hM : 2 ≤ M)
    (hbridge : PlanarBridgeAt width M dB eB)
    {n : Nat} (c : ADRCircuit n) (hc : WellFormedADR c)
    (hwc : ADRHasWidthAtMost c width)
    (hsz : c.gateCount ≤ (n + 1) ^ σ)
    (h_out_comp : (c.kind c.output).isComputation = true)
    (gen C k : Nat) (hgen : orientableCircuitGenus c ≤ gen)
    (hlen : 4 * gen + 3 ≤ C * Nat.log2 (n + 1) ^ k)
    (hcut : 2 * C ≤ Nat.log2 (n + 1)) (hCpos : 1 ≤ C) (hn : 1 ≤ n) :
    ACCRealizes n (2 * M) (2 * dB + 18 + 2 * (k + 1))
      ((n + 1) ^ ((2 * width + 2) * (k + 1) + assemblySizeExp width M eB σ + 1))
      (fun x => ADRAccepts c x) := by
  classical
  obtain ⟨idx⟩ := exists_layerIndexing_of_width c hwc hw
  obtain ⟨P, hPcard, hPplanar⟩ := layerPlanarizer c hc gen hgen
  have hLpos : 0 < 2 * M := by omega
  have h2L : (2 : Nat) ∣ 2 * M := ⟨M, rfl⟩
  have hML : M ∣ 2 * M := ⟨2, by omega⟩
  set A := (2 * M + 2) * (10 * c.gateCount + 10) with hA
  set Bsz := (2 * M + 2) * (c.gateCount + 1) ^ (eB + (2 * width + 1)) with hBsz
  set Gm := A + Bsz with hGm
  set d := 2 * dB + 16 with hd
  set Gf := 2 ^ width * (2 * Gm + 1) + 1 with hGf
  have hGmGf : Gm ≤ Gf := by
    rw [hGf]
    calc Gm ≤ 2 * Gm + 1 := by omega
      _ = 1 * (2 * Gm + 1) := (Nat.one_mul _).symm
      _ ≤ 2 ^ width * (2 * Gm + 1) := Nat.mul_le_mul_right _ Nat.one_le_two_pow
      _ ≤ 2 ^ width * (2 * Gm + 1) + 1 := Nat.le_succ _
  have hAGm : A ≤ Gm := by rw [hGm]; exact Nat.le_add_right _ _
  have hBGm : Bsz ≤ Gm := by rw [hGm]; exact Nat.le_add_left _ _
  -- the local (`ACC[2]`) relations, lifted to the modulus `2 * M`
  have hstepGm : ∀ (l : Nat) (s t : State width),
      ACCRealizes n (2 * M) d Gm (fun x => OneStep idx x l s t) := by
    intro l s t
    obtain ⟨a, h1, h2, h3, h4⟩ := exists_acc_oneStep hc idx l s t
    have h0 : ACCRealizes n 2 3 (10 * c.gateCount + 10) (fun x => OneStep idx x l s t) :=
      ⟨a, h1, h2, h3, h4⟩
    exact accRealizes_mono (by omega) (le_trans (le_of_eq hA.symm) hAGm)
      (accRealizes_modulusLift h2L hLpos h0)
  have hinitGm : ∀ t : State width,
      ACCRealizes n (2 * M) d Gm (fun x => InitState idx x t) := by
    intro t
    obtain ⟨a, h1, h2, h3, h4⟩ := exists_acc_initState hc idx t
    have h0 : ACCRealizes n 2 3 (10 * c.gateCount + 10) (fun x => InitState idx x t) :=
      ⟨a, h1, h2, h3, h4⟩
    exact accRealizes_mono (by omega) (le_trans (le_of_eq hA.symm) hAGm)
      (accRealizes_modulusLift h2L hLpos h0)
  have houtGm : ∀ t : State width,
      ACCRealizes n (2 * M) d Gm (fun _ => t (idx.slot c.output) = true) := by
    intro t
    obtain ⟨a, h1, h2, h3, h4⟩ := exists_acc_outputState hc idx t
    have h0 : ACCRealizes n 2 3 (10 * c.gateCount + 10)
        (fun _ => t (idx.slot c.output) = true) := ⟨a, h1, h2, h3, h4⟩
    exact accRealizes_mono (by omega) (le_trans (le_of_eq hA.symm) hAGm)
      (accRealizes_modulusLift h2L hLpos h0)
  -- the §8 planar block relations, lifted to the modulus `2 * M`
  have hblkGm : ∀ (p q : Nat), p ≤ q → (∀ i, p ≤ i → i ≤ q → i ∉ P) → ∀ s t : State width,
      ACCRealizes n (2 * M) d Gm (fun x => Reach idx x p (q - p) s t) := by
    intro p q hpq hP s t
    obtain ⟨a, h1, h2, h3, h4⟩ :=
      planarBlockRelation_at (wc := width) hc idx P hPplanar hwc hbridge p q hpq hP s t
    have h0 : ACCRealizes n M (dB + 2) ((c.gateCount + 1) ^ (eB + (2 * width + 1)))
        (fun x => Reach idx x p (q - p) s t) := ⟨a, h1, h2, h3, h4⟩
    exact accRealizes_mono (by omega) (le_trans (le_of_eq hBsz.symm) hBGm)
      (accRealizes_modulusLift hML hLpos h0)
  -- everything at the common depth `d + 2` and size `Gf`
  have hstepF : ∀ (l : Nat) (s t : State width),
      ACCRealizes n (2 * M) (d + 2) Gf (fun x => OneStep idx x l s t) :=
    fun l s t => accRealizes_mono (by omega) hGmGf (hstepGm l s t)
  have hinitF : ∀ t : State width,
      ACCRealizes n (2 * M) (d + 2) Gf (fun x => InitState idx x t) :=
    fun t => accRealizes_mono (by omega) hGmGf (hinitGm t)
  have houtF : ∀ t : State width,
      ACCRealizes n (2 * M) (d + 2) Gf (fun _ => t (idx.slot c.output) = true) :=
    fun t => accRealizes_mono (by omega) hGmGf (houtGm t)
  -- the gap relations: a `P`-free block followed by one exceptional step
  have hgapF : ∀ p q : Nat, p < q → (∀ l, p < l → l < q → l ∉ cutSet P) →
      ∀ s t : State width,
        ACCRealizes n (2 * M) (d + 2) Gf (fun x => Reach idx x p (q - p) s t) := by
    intro p q hpq hnot s t
    rcases Nat.lt_or_ge (p + 1) q with hq2 | hq1
    · have hPfree : ∀ i, p ≤ i → i ≤ q - 1 → i ∉ P := notMem_of_gap (by omega) hnot
      have hcomp := accRealizes_composeStates
        (fun x (s t : State width) => Reach idx x p (q - 1 - p) s t)
        (fun x (s t : State width) => OneStep idx x (q - 1) s t)
        (hblkGm p (q - 1) (by omega) hPfree) (fun s t => hstepGm (q - 1) s t) s t
      refine accRealizes_congr (fun x => ?_) hcomp
      have hsplit : q - p = (q - 1 - p) + 1 := by omega
      have hmid : p + (q - 1 - p) = q - 1 := by omega
      rw [hsplit, reach_add idx x (q - 1 - p) 1 p s t, hmid]
      exact exists_congr fun u => and_congr Iff.rfl (reach_one_iff idx x (q - 1) u t).symm
    · have hq : q - p = 1 := by omega
      refine accRealizes_congr (fun x => ?_) (hstepF p s t)
      rw [hq]
      exact (reach_one_iff idx x p s t).symm
  -- the polynomial size bound
  have hT : 2 ≤ n + 1 := by omega
  have hS1 : c.gateCount + 1 ≤ (n + 1) ^ (σ + 1) := succ_le_pow_succ hT hsz
  have hAle : A ≤ (n + 1) ^ (10 * (2 * M + 2) + (σ + 1)) := by
    rw [hA]
    calc (2 * M + 2) * (10 * c.gateCount + 10)
        = (10 * (2 * M + 2)) * (c.gateCount + 1) := by ring
      _ ≤ (10 * (2 * M + 2)) * (n + 1) ^ (σ + 1) := Nat.mul_le_mul_left _ hS1
      _ ≤ (n + 1) ^ (10 * (2 * M + 2) + (σ + 1)) := const_mul_pow_le hT _ _
  have hBle : Bsz ≤ (n + 1) ^ ((2 * M + 2) + (σ + 1) * (eB + (2 * width + 1))) := by
    rw [hBsz]
    calc (2 * M + 2) * (c.gateCount + 1) ^ (eB + (2 * width + 1))
        ≤ (2 * M + 2) * ((n + 1) ^ (σ + 1)) ^ (eB + (2 * width + 1)) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hS1 _)
      _ = (2 * M + 2) * (n + 1) ^ ((σ + 1) * (eB + (2 * width + 1))) := by rw [← pow_mul]
      _ ≤ (n + 1) ^ ((2 * M + 2) + (σ + 1) * (eB + (2 * width + 1))) := const_mul_pow_le hT _ _
  set m := max (10 * (2 * M + 2) + (σ + 1))
    ((2 * M + 2) + (σ + 1) * (eB + (2 * width + 1))) + 1 with hm
  have hGmle : Gm ≤ (n + 1) ^ m := by
    rw [hGm, hm]
    exact le_trans (Nat.add_le_add hAle hBle) (pow_add_pow_le hT _ _)
  have hQ1 : 1 ≤ (n + 1) ^ m := Nat.one_le_pow _ _ (by omega)
  have hGfle : Gf ≤ (n + 1) ^ assemblySizeExp width M eB σ := by
    have hstep1 : 2 * Gm + 1 ≤ 3 * (n + 1) ^ m := by omega
    have hbig : 1 ≤ (n + 1) ^ (2 ^ width + (3 + m)) := Nat.one_le_pow _ _ (by omega)
    have : Gf ≤ (n + 1) ^ (2 + (2 ^ width + (3 + m))) := by
      calc Gf = 2 ^ width * (2 * Gm + 1) + 1 := hGf
        _ ≤ 2 ^ width * (3 * (n + 1) ^ m) + 1 :=
            Nat.add_le_add_right (Nat.mul_le_mul_left _ hstep1) 1
        _ ≤ 2 ^ width * (n + 1) ^ (3 + m) + 1 :=
            Nat.add_le_add_right (Nat.mul_le_mul_left _ (const_mul_pow_le hT 3 m)) 1
        _ ≤ (n + 1) ^ (2 ^ width + (3 + m)) + 1 :=
            Nat.add_le_add_right (const_mul_pow_le hT _ _) 1
        _ ≤ 2 * (n + 1) ^ (2 ^ width + (3 + m)) := by omega
        _ ≤ (n + 1) ^ (2 + (2 ^ width + (3 + m))) := const_mul_pow_le hT 2 _
    have heq : 2 + (2 ^ width + (3 + m)) = assemblySizeExp width M eB σ := by
      rw [assemblySizeExp, hm]
      omega
    rw [← heq]
    exact this
  -- the §6/§9 collapse
  have hB2 : 2 ≤ Nat.log2 (n + 1) := by omega
  have hlen' : 4 * P.card + 3 ≤ C * Nat.log2 (n + 1) ^ k := by omega
  obtain ⟨a, h1, h2, h3, h4⟩ :=
    exists_acc_adrAccepts (M := 2 * M) hc idx h_out_comp P (d + 2) Gf
      (assemblySizeExp width M eB σ) C k (by omega) (by rw [hGf]; omega) hGfle hn hB2 hcut hlen'
      (fun l _ s t => hstepF l s t) hgapF hinitF houtF
  exact accRealizes_mono (by omega) (le_refl _) ⟨a, h1, h2, h3, h4⟩

theorem conditional_of_bridge :
    PlanarBridgeStatement →
    AllenderOQ3ConditionalStatement := by
  intro hBridge _hRot _hHan _hQuant L hHyp
  classical
  obtain ⟨width, sizeExponent, logExponent, factor, threshold, family,
    hw, hf, hwf, hwidth, hsize, hgenus, hdec⟩ := hHyp
  obtain ⟨M, dB, eB, hM, hbridge⟩ := hBridge width
  refine inNonuniformACC0_of_large_inputs L (2 * M)
    (max threshold (2 ^ (2 * (4 * factor + 3))))
    (max (2 * dB + 18 + 2 * (logExponent + 1)) 2)
    (max ((2 * width + 2) * (logExponent + 1) +
      assemblySizeExp width M eB sizeExponent + 1) (2 * M + 2))
    (by omega) ?_
  intro n hn
  have hpow : 2 ^ (2 * (4 * factor + 3)) ≤ n := le_trans (le_max_right _ _) hn
  have hpow1 : 1 ≤ 2 ^ (2 * (4 * factor + 3)) := Nat.one_le_two_pow
  have hn1 : 1 ≤ n := by omega
  have hcut : 2 * (4 * factor + 3) ≤ Nat.log2 (n + 1) :=
    le_log2_succ_of_pow_le _ n hpow
  have hcirc : ACCRealizes n (2 * M)
      (max (2 * dB + 18 + 2 * (logExponent + 1)) 2)
      ((n + 1) ^ (max ((2 * width + 2) * (logExponent + 1) +
        assemblySizeExp width M eB sizeExponent + 1) (2 * M + 2)))
      (fun x => ADRAccepts (family n) x) := by
    by_cases hoc : ((family n).kind (family n).output).isComputation = true
    · have hlen : 4 * (factor * Nat.log2 (n + 1) ^ logExponent) + 3
          ≤ (4 * factor + 3) * Nat.log2 (n + 1) ^ logExponent := by
        have hBk : 1 ≤ Nat.log2 (n + 1) ^ logExponent := Nat.one_le_pow _ _ (by omega)
        have hring : (4 * factor + 3) * Nat.log2 (n + 1) ^ logExponent
            = 4 * (factor * Nat.log2 (n + 1) ^ logExponent)
              + 3 * Nat.log2 (n + 1) ^ logExponent := by ring
        omega
      have hcore := acc_of_bridge_at_length (σ := sizeExponent) hw hM hbridge
        (family n) (hwf n) (hwidth n) (hsize n) hoc
        (factor * Nat.log2 (n + 1) ^ logExponent) (4 * factor + 3) logExponent
        (hgenus n (le_trans (le_max_left _ _) hn)) hlen hcut (by omega) hn1
      exact accRealizes_mono (le_max_left _ _)
        (Nat.pow_le_pow_right (by omega) (le_max_left _ _)) hcore
    · have hlit : ∃ (i : Fin n) (b : Bool),
          (family n).kind (family n).output = ADRGate.literal i b := by
        rcases hkind : (family n).kind (family n).output with ⟨i, b⟩ | _ | _
        · exact ⟨i, b, rfl⟩
        · rw [hkind] at hoc; exact absurd rfl hoc
        · rw [hkind] at hoc; exact absurd rfl hoc
      obtain ⟨i, b, hlit⟩ := hlit
      have h0 : ACCRealizes n 2 0 1 (fun x => ADRAccepts (family n) x) :=
        ⟨literalACC n i b, wellFormedACC_literalACC i b, fun _ => le_refl 0,
          le_of_eq rfl, fun x => acc_of_literal_output (hwf n) hlit x⟩
      have h1 := accRealizes_modulusLift (show (2 : Nat) ∣ 2 * M from ⟨M, rfl⟩)
        (by omega) h0
      refine accRealizes_mono (le_max_right _ _) ?_ h1
      calc (2 * M + 2) * 1 = (2 * M + 2) * (n + 1) ^ 0 := by ring
        _ ≤ (n + 1) ^ ((2 * M + 2) + 0) := const_mul_pow_le (by omega) _ _
        _ ≤ (n + 1) ^ (max ((2 * width + 2) * (logExponent + 1) +
              assemblySizeExp width M eB sizeExponent + 1) (2 * M + 2)) :=
            Nat.pow_le_pow_right (by omega) (by simp)
  exact accRealizes_congr (fun x => hdec n x) hcirc

end AllenderOQ3
