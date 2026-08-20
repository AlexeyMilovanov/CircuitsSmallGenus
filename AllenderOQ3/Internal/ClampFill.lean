import AllenderOQ3.Internal.OptCircuitInstances

/-!
# T5a assembled: the clamp and fan-fill transitions

`clampTrans` is a product of freeze layers over `Jᶜ`, clamping every
non-`J` coordinate to the basepoint.  `fillTrans` is an ascending sweep of
forward duplication layers (each non-`J` coordinate above the minimum of `J`
picks up the value of the nearest `J`-coordinate below it) followed by a
descending sweep of backward duplication layers (the initial segment below
the minimum of `J` copies the minimum).  Both are products of the certified
single layers of `OptCircuitInstances`, hence certified.

`clamp_fill_layers` at the bottom is the statement of the open leaf
`exists_clamp_fill_layers` of `ConstantElimination.lean`.
-/

set_option autoImplicit false

namespace AllenderOQ3
namespace Internal

attribute [local instance] Classical.propDecidable

variable {w : Nat}

/-! ## Semantics of the three elementary layers -/

theorem runTrans_freezeTrans (k : Fin w) (b : Bool) (z : Config w) (p : Fin w) :
    runTrans (optTrans (freezeRho k) (freezeBeta b)) z p
      = if p = k then b else z p := by
  change (match freezeRho k p with
    | some q => z q
    | none => freezeBeta b p) = _
  by_cases hp : p = k
  · rw [show freezeRho k p = none from by
      change (if p = k then _ else _) = _
      rw [if_pos hp], if_pos hp]
    rfl
  · rw [show freezeRho k p = some p from by
      change (if p = k then _ else _) = _
      rw [if_neg hp], if_neg hp]

theorem runTrans_dupNextTrans (i : Fin w) (z : Config w) (p : Fin w) :
    runTrans (optTrans (dupNextRho i) (beta0 w)) z p
      = if p.val = i.val + 1 then z i else z p := by
  change (match dupNextRho i p with
    | some q => z q
    | none => beta0 w p) = _
  by_cases hp : p.val = i.val + 1
  · rw [show dupNextRho i p = some i from by
      change (if p.val = i.val + 1 then _ else _) = _
      rw [if_pos hp], if_pos hp]
  · rw [show dupNextRho i p = some p from by
      change (if p.val = i.val + 1 then _ else _) = _
      rw [if_neg hp], if_neg hp]

theorem runTrans_dupPrevTrans (i : Fin w) (hi : i.val + 1 < w)
    (z : Config w) (p : Fin w) :
    runTrans (optTrans (dupPrevRho i hi) (beta0 w)) z p
      = if p.val = i.val then z ⟨i.val + 1, hi⟩ else z p := by
  change (match dupPrevRho i hi p with
    | some q => z q
    | none => beta0 w p) = _
  by_cases hp : p.val = i.val
  · rw [show dupPrevRho i hi p = some ⟨i.val + 1, hi⟩ from by
      change (if p.val = i.val then _ else _) = _
      rw [if_pos hp], if_pos hp]
  · rw [show dupPrevRho i hi p = some p from by
      change (if p.val = i.val then _ else _) = _
      rw [if_neg hp], if_neg hp]

/-! ## The nearest `J`-coordinate at or below a position -/

/-- The largest `J`-coordinate at or below `i`, or `i` itself if none. -/
noncomputable def gsrc (J : Finset (Fin w)) (i : Fin w) : Fin w :=
  if h : (J.filter (fun j => j ≤ i)).Nonempty
  then (J.filter (fun j => j ≤ i)).max' h else i

theorem gsrc_of_mem {J : Finset (Fin w)} {i : Fin w} (hi : i ∈ J) :
    gsrc J i = i := by
  unfold gsrc
  have hne : (J.filter (fun j => j ≤ i)).Nonempty :=
    ⟨i, Finset.mem_filter.mpr ⟨hi, le_refl i⟩⟩
  rw [dif_pos hne]
  apply le_antisymm
  · exact Finset.max'_le _ _ _ (fun y hy => (Finset.mem_filter.mp hy).2)
  · exact Finset.le_max' _ i
      (show i ∈ J.filter (fun j => j ≤ i) from
        Finset.mem_filter.mpr ⟨hi, le_refl i⟩)

theorem gsrc_of_empty {J : Finset (Fin w)} {i : Fin w}
    (h : ¬ (J.filter (fun j => j ≤ i)).Nonempty) : gsrc J i = i := by
  unfold gsrc
  rw [dif_neg h]

theorem gsrc_mem {J : Finset (Fin w)} {i : Fin w}
    (h : (J.filter (fun j => j ≤ i)).Nonempty) : gsrc J i ∈ J := by
  unfold gsrc
  rw [dif_pos h]
  exact (Finset.mem_filter.mp (Finset.max'_mem _ h)).1

theorem gsrc_congr {J : Finset (Fin w)} {i i' : Fin w}
    (hne : (J.filter (fun j => j ≤ i')).Nonempty)
    (h : J.filter (fun j => j ≤ i) = J.filter (fun j => j ≤ i')) :
    gsrc J i = gsrc J i' := by
  have hne' : (J.filter (fun j => j ≤ i)).Nonempty := by
    rw [h]; exact hne
  unfold gsrc
  rw [dif_pos hne', dif_pos hne]
  apply le_antisymm
  · refine Finset.max'_le _ _ _ (fun y hy => Finset.le_max' _ y ?_)
    rw [← h]; exact hy
  · refine Finset.max'_le _ _ _ (fun y hy => Finset.le_max' _ y ?_)
    rw [h]; exact hy

/-! ## The clamp transition -/

/-- Freeze every coordinate outside `J` to the basepoint value. -/
noncomputable def clampTrans (x₀ : Config w) (J : Finset (Fin w)) :
    TransMonoid w :=
  (((Finset.univ \ J).toList).map
    (fun k => optTrans (freezeRho k) (freezeBeta (x₀ k)))).prod

theorem runTrans_freezeList (x₀ : Config w) (L : List (Fin w))
    (z : Config w) (p : Fin w) :
    runTrans ((L.map
        (fun k => optTrans (freezeRho k) (freezeBeta (x₀ k)))).prod) z p
      = if p ∈ L then x₀ p else z p := by
  induction L generalizing z with
  | nil =>
    rw [List.map_nil, List.prod_nil, runTrans_one, if_neg (by simp)]
  | cons k L ih =>
    rw [List.map_cons, List.prod_cons, runTrans_mul, ih]
    by_cases hpL : p ∈ L
    · rw [if_pos hpL, if_pos (List.mem_cons_of_mem _ hpL)]
    · rw [if_neg hpL, runTrans_freezeTrans]
      by_cases hpk : p = k
      · subst hpk
        rw [if_pos rfl, if_pos (List.mem_cons_self ..)]
      · rw [if_neg hpk, if_neg (by
          rw [List.mem_cons]
          exact fun hc => hc.elim hpk hpL)]

theorem clampTrans_mem (hw : 0 < w) (x₀ : Config w) (J : Finset (Fin w)) :
    clampTrans x₀ J ∈ NonCrossing w := by
  refine Submonoid.list_prod_mem _ ?_
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨k, _, rfl⟩ := hx
  exact freezeTrans_mem hw k (x₀ k)

theorem runTrans_clampTrans (x₀ : Config w) (J : Finset (Fin w))
    (z : Config w) (i : Fin w) :
    runTrans (clampTrans x₀ J) z i = if i ∈ J then z i else x₀ i := by
  unfold clampTrans
  rw [runTrans_freezeList]
  by_cases hi : i ∈ J
  · rw [if_pos hi, if_neg (by
      rw [Finset.mem_toList, Finset.mem_sdiff]
      exact fun hc => hc.2 hi)]
  · rw [if_neg hi, if_pos (by
      rw [Finset.mem_toList, Finset.mem_sdiff]
      exact ⟨Finset.mem_univ i, hi⟩)]

/-! ## The ascending duplication sweep -/

/-- The ascending layer at position `n`: copy onto `n` from `n - 1` when `n`
is outside `J` and has a `J`-coordinate strictly below it. -/
noncomputable def ascLayer (J : Finset (Fin w)) (n : Nat) : TransMonoid w :=
  if h : n < w then
    if (⟨n, h⟩ : Fin w) ∈ J ∨ ¬ (J.filter (fun j => j.val < n)).Nonempty
    then 1
    else optTrans (dupNextRho (⟨n - 1, by omega⟩ : Fin w)) (beta0 w)
  else 1

noncomputable def ascProd (J : Finset (Fin w)) : Nat → TransMonoid w
  | 0 => 1
  | n + 1 => ascProd J n * ascLayer J n

theorem ascLayer_mem (hw : 0 < w) (J : Finset (Fin w)) (n : Nat) :
    ascLayer J n ∈ NonCrossing w := by
  unfold ascLayer
  split
  · next h =>
    split
    · exact one_mem _
    · next hc =>
      push_neg at hc
      have hn0 : 0 < n := by
        obtain ⟨j, hj⟩ := hc.2
        have h2 : j.val < n := (Finset.mem_filter.mp hj).2
        omega
      exact dupNextTrans_mem hw ⟨n - 1, by omega⟩
        (show n - 1 + 1 < w by omega)
  · exact one_mem _

theorem ascProd_mem (hw : 0 < w) (J : Finset (Fin w)) (n : Nat) :
    ascProd J n ∈ NonCrossing w := by
  induction n with
  | zero => exact one_mem _
  | succ n ih => exact mul_mem ih (ascLayer_mem hw J n)

theorem runTrans_ascProd (J : Finset (Fin w)) (n : Nat) (z : Config w)
    (p : Fin w) :
    runTrans (ascProd J n) z p
      = if p.val < n then z (gsrc J p) else z p := by
  induction n generalizing p with
  | zero =>
    change runTrans (1 : TransMonoid w) z p = _
    rw [runTrans_one, if_neg (by omega)]
  | succ n ih =>
    change runTrans (ascProd J n * ascLayer J n) z p = _
    rw [runTrans_mul]
    unfold ascLayer
    split
    · next hnw =>
      split
      · next hC =>
        rw [runTrans_one, ih p]
        by_cases hpn : p.val < n
        · rw [if_pos hpn, if_pos (by omega)]
        · by_cases hpe : p.val = n
          · rw [if_neg hpn, if_pos (by omega)]
            by_cases hpJ : p ∈ J
            · rw [gsrc_of_mem hpJ]
            · have hpfin : p = ⟨n, hnw⟩ := Fin.ext hpe
              have hemp : ¬ (J.filter (fun j => j.val < n)).Nonempty := by
                rcases hC with hmem | hemp
                · exact absurd (by rw [hpfin]; exact hmem) hpJ
                · exact hemp
              have hgs : gsrc J p = p := by
                refine gsrc_of_empty (fun hne => ?_)
                obtain ⟨j, hj⟩ := hne
                have hj1 := Finset.mem_filter.mp hj
                apply hemp
                refine ⟨j, Finset.mem_filter.mpr ⟨hj1.1, ?_⟩⟩
                have hjp : j.val ≤ p.val := Fin.le_def.mp hj1.2
                rcases Nat.lt_or_ge j.val n with hlt | hge
                · exact hlt
                · exfalso
                  have hje : j = p := Fin.ext (by omega)
                  rw [hje] at hj1
                  exact hpJ hj1.1
              rw [hgs]
          · rw [if_neg hpn, if_neg (by omega)]
      · next hC =>
        push_neg at hC
        obtain ⟨hpJn, hfil⟩ := hC
        have hn0 : 0 < n := by
          obtain ⟨j, hj⟩ := hfil
          have h2 : j.val < n := (Finset.mem_filter.mp hj).2
          omega
        rw [runTrans_dupNextTrans]
        by_cases hpe : p.val = n
        · rw [if_pos (show p.val = n - 1 + 1 by omega)]
          rw [ih ⟨n - 1, by omega⟩]
          rw [if_pos (show n - 1 < n by omega),
            if_pos (show p.val < n + 1 by omega)]
          have hpJ : p ∉ J := by
            have hpfin : p = ⟨n, hnw⟩ := Fin.ext hpe
            rw [hpfin]; exact hpJn
          have hne : (J.filter (fun j => j ≤ p)).Nonempty := by
            obtain ⟨j, hj⟩ := hfil
            have hj1 := Finset.mem_filter.mp hj
            have h2 : j.val < n := hj1.2
            exact ⟨j, Finset.mem_filter.mpr
              ⟨hj1.1, Fin.le_def.mpr (by omega)⟩⟩
          have hh : J.filter (fun j => j ≤ (⟨n - 1, by omega⟩ : Fin w))
              = J.filter (fun j => j ≤ p) := by
            apply Finset.ext
            intro j
            rw [Finset.mem_filter, Finset.mem_filter]
            constructor
            · rintro ⟨hjJ, hjle⟩
              have h1 : j.val ≤ n - 1 := Fin.le_def.mp hjle
              exact ⟨hjJ, Fin.le_def.mpr (by omega)⟩
            · rintro ⟨hjJ, hjle⟩
              have h1 : j.val ≤ p.val := Fin.le_def.mp hjle
              refine ⟨hjJ, Fin.le_def.mpr ?_⟩
              change j.val ≤ n - 1
              rcases Nat.lt_or_ge j.val n with hlt | hge
              · omega
              · exfalso
                have hje : j = p := Fin.ext (by omega)
                rw [hje] at hjJ
                exact hpJ hjJ
          exact congrArg z (gsrc_congr hne hh)
        · by_cases hpn : p.val < n
          · rw [if_neg (show ¬ p.val = n - 1 + 1 by omega), ih p,
              if_pos hpn, if_pos (by omega)]
          · rw [if_neg (show ¬ p.val = n - 1 + 1 by omega), ih p,
              if_neg hpn, if_neg (by omega)]
    · next hnw =>
      rw [runTrans_one, ih p]
      have hpw : p.val < w := p.isLt
      rw [if_pos (by omega), if_pos (by omega)]

/-! ## The descending duplication sweep -/

/-- The descending layer at position `m`: copy onto `m` from `m + 1`. -/
noncomputable def descLayer (m : Nat) : TransMonoid w :=
  if h : m + 1 < w then
    optTrans (dupPrevRho (⟨m, by omega⟩ : Fin w) h) (beta0 w)
  else 1

noncomputable def descProd (t : Nat) : Nat → TransMonoid w
  | 0 => 1
  | m + 1 => descProd t m * descLayer (t - (m + 1))

theorem descLayer_mem (hw : 0 < w) (m : Nat) :
    descLayer (w := w) m ∈ NonCrossing w := by
  unfold descLayer
  split
  · next h => exact dupPrevTrans_mem hw ⟨m, by omega⟩ h
  · exact one_mem _

theorem descProd_mem (hw : 0 < w) (t n : Nat) :
    descProd (w := w) t n ∈ NonCrossing w := by
  induction n with
  | zero => exact one_mem _
  | succ n ih => exact mul_mem ih (descLayer_mem hw _)

theorem runTrans_descProd (t : Nat) (ht : t < w) (n : Nat) :
    ∀ (_ : n ≤ t) (z : Config w) (p : Fin w),
    runTrans (descProd (w := w) t n) z p
      = if t - n ≤ p.val ∧ p.val < t then z ⟨t, ht⟩ else z p := by
  induction n with
  | zero =>
    intro _ z p
    change runTrans (1 : TransMonoid w) z p = _
    rw [runTrans_one, if_neg (by omega)]
  | succ n ih =>
    intro hn z p
    have hnt : n ≤ t := by omega
    change runTrans (descProd t n * descLayer (t - (n + 1))) z p = _
    rw [runTrans_mul]
    unfold descLayer
    have hcond : t - (n + 1) + 1 < w := by omega
    rw [dif_pos hcond, runTrans_dupPrevTrans]
    by_cases hpe : p.val = t - (n + 1)
    · rw [if_pos (show p.val = t - (n + 1) from hpe)]
      rw [ih hnt z ⟨t - (n + 1) + 1, by omega⟩]
      by_cases hn0 : 0 < n
      · rw [if_pos (show t - n ≤ t - (n + 1) + 1 ∧ t - (n + 1) + 1 < t
            by omega),
          if_pos (show t - (n + 1) ≤ p.val ∧ p.val < t by omega)]
      · rw [if_neg (show ¬ (t - n ≤ t - (n + 1) + 1 ∧ t - (n + 1) + 1 < t)
            by omega),
          if_pos (show t - (n + 1) ≤ p.val ∧ p.val < t by omega)]
        exact congrArg z (Fin.ext (show t - (n + 1) + 1 = t by omega))
    · rw [if_neg (show ¬ p.val = t - (n + 1) from hpe), ih hnt z p]
      by_cases hpw : t - n ≤ p.val ∧ p.val < t
      · rw [if_pos hpw,
          if_pos (show t - (n + 1) ≤ p.val ∧ p.val < t by omega)]
      · rw [if_neg hpw,
          if_neg (show ¬ (t - (n + 1) ≤ p.val ∧ p.val < t) by omega)]

/-! ## The fill transition -/

/-- The fan-fill transition: ascending sweep over the whole width, then a
descending sweep over the initial segment below the minimum of `J`. -/
noncomputable def fillTrans (J : Finset (Fin w)) (hJ : J.Nonempty) :
    TransMonoid w :=
  ascProd J w * descProd (J.min' hJ).val (J.min' hJ).val

theorem fillTrans_mem (hw : 0 < w) (J : Finset (Fin w)) (hJ : J.Nonempty) :
    fillTrans J hJ ∈ NonCrossing w :=
  mul_mem (ascProd_mem hw J w) (descProd_mem hw _ _)

theorem runTrans_fillTrans (J : Finset (Fin w)) (hJ : J.Nonempty)
    (z : Config w) (p : Fin w) :
    runTrans (fillTrans J hJ) z p
      = if p.val < (J.min' hJ).val then z (J.min' hJ) else z (gsrc J p) := by
  change runTrans (ascProd J w * descProd (J.min' hJ).val (J.min' hJ).val) z p
    = _
  rw [runTrans_mul,
    runTrans_descProd (J.min' hJ).val (J.min' hJ).isLt _ (le_refl _)]
  by_cases hp : p.val < (J.min' hJ).val
  · rw [if_pos (show (J.min' hJ).val - (J.min' hJ).val ≤ p.val
        ∧ p.val < (J.min' hJ).val by omega), if_pos hp]
    rw [runTrans_ascProd, if_pos (show (J.min' hJ).val < w from
      (J.min' hJ).isLt)]
    have heta : (⟨(J.min' hJ).val, (J.min' hJ).isLt⟩ : Fin w) = J.min' hJ :=
      Fin.ext rfl
    rw [heta, gsrc_of_mem (Finset.min'_mem J hJ)]
  · rw [if_neg (show ¬ ((J.min' hJ).val - (J.min' hJ).val ≤ p.val
        ∧ p.val < (J.min' hJ).val) by omega), if_neg hp]
    rw [runTrans_ascProd, if_pos p.isLt]

/-! ## The leaf statement -/

/-- **T5a**: the clamp and fan-fill layers exist and are certified. -/
theorem clamp_fill_layers (x₀ : Config w) (J : Finset (Fin w))
    (hJ : J.Nonempty) :
    ∃ Al Bl : TransMonoid w, Al ∈ NonCrossing w ∧ Bl ∈ NonCrossing w ∧
      (∀ (z : Config w) (i : Fin w),
        runTrans Al z i = if i ∈ J then z i else x₀ i) ∧
      (∀ (z : Config w), ∀ j ∈ J, runTrans Bl z j = z j) ∧
      (∀ i : Fin w, i ∉ J → ∃ j ∈ J, ∀ z : Config w, runTrans Bl z i = z j) := by
  have hw : 0 < w := (J.min' hJ).pos
  refine ⟨clampTrans x₀ J, fillTrans J hJ, clampTrans_mem hw x₀ J,
    fillTrans_mem hw J hJ, runTrans_clampTrans x₀ J, ?_, ?_⟩
  · intro z j hj
    rw [runTrans_fillTrans]
    have h2 : (J.min' hJ).val ≤ j.val := Fin.le_def.mp (Finset.min'_le J j hj)
    rw [if_neg (show ¬ j.val < (J.min' hJ).val by omega),
      gsrc_of_mem hj]
  · intro i hi
    by_cases hip : i.val < (J.min' hJ).val
    · refine ⟨J.min' hJ, Finset.min'_mem J hJ, fun z => ?_⟩
      rw [runTrans_fillTrans, if_pos hip]
    · have hne : (J.filter (fun j => j ≤ i)).Nonempty :=
        ⟨J.min' hJ, Finset.mem_filter.mpr
          ⟨Finset.min'_mem J hJ, Fin.le_def.mpr (by omega)⟩⟩
      refine ⟨gsrc J i, gsrc_mem hne, fun z => ?_⟩
      rw [runTrans_fillTrans, if_neg hip]

end Internal
end AllenderOQ3
