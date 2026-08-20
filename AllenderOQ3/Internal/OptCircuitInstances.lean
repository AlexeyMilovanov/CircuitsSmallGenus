import AllenderOQ3.Internal.OptCircuitCert

/-!
# The elementary certified layers: freeze and adjacent duplication

Instantiations of the `optCircuit` machinery (`docs/LOCAL_DIVISOR_PLAN.md`
§9): the three elementary single-fan-in layers whose source-major and
target-major arc words literally coincide, with their membership in
`NonCrossing w`:

* `freezeTrans_mem` — freeze one coordinate to a constant, keep the rest;
* `dupNextTrans_mem` — copy coordinate `i` onto `i+1`, keep the rest;
* `dupPrevTrans_mem` — copy coordinate `i+1` onto `i`, keep the rest.

The clamp and fan-fill layers of T5a are products of these
(`ConstantElimination.lean`).  Everything here is `sorry`-free.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace AllenderOQ3
namespace Internal

attribute [local instance] Classical.propDecidable

variable {w : Nat}

/-! ## List helpers -/

theorem flatMap_congr' {α β : Type} {F G : α → List β} :
    ∀ l : List α, (∀ x ∈ l, F x = G x) → l.flatMap F = l.flatMap G := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a l ih =>
    intro h
    rw [List.flatMap_cons, List.flatMap_cons, h a (List.mem_cons_self ..),
      ih (fun x hx => h x (List.mem_cons_of_mem a hx))]

theorem flatMap_map' {α β γ : Type} (f : α → β) (g : β → List γ) :
    ∀ l : List α, (l.map f).flatMap g = l.flatMap (fun x => g (f x)) := by
  intro l
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, List.flatMap_cons, List.flatMap_cons, ih]

theorem mem_take_finRange {k : Nat} {p : Fin w}
    (h : p ∈ (List.finRange w).take k) : p.val < k := by
  obtain ⟨n, hn, hget⟩ := List.getElem_of_mem h
  rw [List.getElem_take, List.getElem_finRange] at hget
  have hval := congrArg Fin.val hget
  simp at hval
  have hlen : n < min k (List.finRange w).length := by
    simpa [List.length_take] using hn
  omega

theorem mem_drop_finRange {k : Nat} {p : Fin w}
    (h : p ∈ (List.finRange w).drop k) : k ≤ p.val := by
  obtain ⟨n, hn, hget⟩ := List.getElem_of_mem h
  rw [List.getElem_drop, List.getElem_finRange] at hget
  have hval := congrArg Fin.val hget
  simp at hval
  omega

/-- Splitting `finRange` around a pair of adjacent positions. -/
theorem finRange_split_pair (i : Fin w) (hi : i.val + 1 < w) :
    List.finRange w
      = (List.finRange w).take i.val
        ++ i :: (⟨i.val + 1, hi⟩ : Fin w) :: (List.finRange w).drop (i.val + 2) := by
  have hlen : (List.finRange w).length = w := List.length_finRange
  have h1 : List.finRange w
      = (List.finRange w).take i.val ++ (List.finRange w).drop i.val :=
    (List.take_append_drop _ _).symm
  have h2 : (List.finRange w).drop i.val
      = (List.finRange w)[i.val] :: (List.finRange w).drop (i.val + 1) :=
    List.drop_eq_getElem_cons (by omega)
  have h3 : (List.finRange w).drop (i.val + 1)
      = (List.finRange w)[i.val + 1] :: (List.finRange w).drop (i.val + 2) :=
    List.drop_eq_getElem_cons (by omega)
  have h4 : (List.finRange w)[i.val] = i := by
    rw [List.getElem_finRange]
    apply Fin.ext
    simp
  have h5 : ((List.finRange w)[i.val + 1] : Fin w) = ⟨i.val + 1, hi⟩ := by
    rw [List.getElem_finRange]
    apply Fin.ext
    simp
  conv_lhs => rw [h1]
  rw [h2, h3, h4, h5]

/-- Two block families with equal concatenations around an adjacent pair and
equal blocks elsewhere have equal words. -/
theorem flatMap_eq_of_agree_outside_pair {α : Type} (i : Fin w) (hi : i.val + 1 < w)
    (F G : Fin w → List α)
    (hlow : ∀ q : Fin w, q.val < i.val → F q = G q)
    (hhigh : ∀ q : Fin w, i.val + 1 < q.val → F q = G q)
    (hmid : F i ++ F ⟨i.val + 1, hi⟩ = G i ++ G ⟨i.val + 1, hi⟩) :
    (List.finRange w).flatMap F = (List.finRange w).flatMap G := by
  rw [finRange_split_pair i hi]
  rw [List.flatMap_append, List.flatMap_append, List.flatMap_cons, List.flatMap_cons,
    List.flatMap_cons, List.flatMap_cons]
  have hT1 : ((List.finRange w).take i.val).flatMap F
      = ((List.finRange w).take i.val).flatMap G :=
    flatMap_congr' _ (fun x hx => hlow x (mem_take_finRange hx))
  have hT2 : ((List.finRange w).drop (i.val + 2)).flatMap F
      = ((List.finRange w).drop (i.val + 2)).flatMap G :=
    flatMap_congr' _ (fun x hx => hhigh x (by
      have := mem_drop_finRange hx
      omega))
  rw [hT1, hT2]
  have hmid2 : F i ++ (F ⟨i.val + 1, hi⟩
        ++ ((List.finRange w).drop (i.val + 2)).flatMap G)
      = G i ++ (G ⟨i.val + 1, hi⟩
        ++ ((List.finRange w).drop (i.val + 2)).flatMap G) := by
    rw [← List.append_assoc, ← List.append_assoc, hmid]
  rw [hmid2]

/-! ## Positions of layer vertices -/

section Pos

variable (hw : 0 < w) (ρ : Fin w → Option (Fin w)) (β : Fin w → Bool)

/-- The position of a source-layer vertex. -/
def srcPos (u : LayerVertex (optCircuit w hw ρ β) 0) : Fin w :=
  ⟨u.val.val, by
    have h1 : u.val.val / w = 0 := u.2
    have h2 : u.val.val < 2 * w := u.val.isLt
    by_contra hcon
    push_neg at hcon
    have h3 : 1 ≤ u.val.val / w := (Nat.one_le_div_iff hw).mpr hcon
    omega⟩

/-- The position of a target-layer vertex. -/
def tgtPos (v : LayerVertex (optCircuit w hw ρ β) 1) : Fin w :=
  ⟨v.val.val - w, by
    have h1 : v.val.val / w = 1 := v.2
    have h2 : v.val.val < 2 * w := v.val.isLt
    have h3 : w ≤ v.val.val := by
      by_contra hcon
      push_neg at hcon
      have h4 : v.val.val / w = 0 := Nat.div_eq_of_lt hcon
      omega
    omega⟩

theorem srcVertex_srcPos (u : LayerVertex (optCircuit w hw ρ β) 0) :
    srcVertex hw ρ β (srcPos hw ρ β u) = u := by
  apply Subtype.ext
  apply Fin.ext
  rfl

theorem srcPos_srcVertex (q : Fin w) :
    srcPos hw ρ β (srcVertex hw ρ β q) = q := by
  apply Fin.ext
  rfl

theorem tgtVertex_tgtPos (v : LayerVertex (optCircuit w hw ρ β) 1) :
    tgtVertex hw ρ β (tgtPos hw ρ β v) = v := by
  apply Subtype.ext
  apply Fin.ext
  change w + (v.val.val - w) = v.val.val
  have h1 : v.val.val / w = 1 := v.2
  have h3 : w ≤ v.val.val := by
    by_contra hcon
    push_neg at hcon
    have h4 : v.val.val / w = 0 := Nat.div_eq_of_lt hcon
    omega
  omega

theorem tgtPos_tgtVertex (p : Fin w) :
    tgtPos hw ρ β (tgtVertex hw ρ β p) = p := by
  apply Fin.ext
  change (w + p.val) - w = p.val
  omega

/-! ## The incoming blocks -/

/-- The incoming arcs at target position `p`: the single prescribed arc, or
nothing. -/
noncomputable def incAt (p : Fin w) : List (TransitionArc (optCircuit w hw ρ β) 0) :=
  match h : ρ p with
  | some q => [optArc hw ρ β p q h]
  | none => []

theorem mem_incAt {p : Fin w} {e : TransitionArc (optCircuit w hw ρ β) 0} :
    e ∈ incAt hw ρ β p ↔ ∃ (q : Fin w) (h : ρ p = some q), e = optArc hw ρ β p q h := by
  unfold incAt
  constructor
  · intro hmem
    split at hmem
    · next q hq =>
      rw [List.mem_singleton] at hmem
      exact ⟨q, hq, hmem⟩
    · next => exact absurd hmem (List.not_mem_nil)
  · rintro ⟨q, h, rfl⟩
    split
    · next q' hq' =>
      rw [List.mem_singleton]
      have hqq : q = q' := Option.some.inj (h.symm.trans hq')
      subst hqq
      rfl
    · next hn => exact absurd (h.symm.trans hn) (by simp)

theorem incAt_nodup (p : Fin w) : (incAt hw ρ β p).Nodup := by
  unfold incAt
  split
  · exact List.nodup_singleton _
  · exact List.nodup_nil

/-- Exactness of the incoming blocks, for any `ρ`. -/
theorem incAt_exact (v : LayerVertex (optCircuit w hw ρ β) 1)
    (e : TransitionArc (optCircuit w hw ρ β) 0) :
    e ∈ incAt hw ρ β (tgtPos hw ρ β v) ↔ e.1.2 = v.1 := by
  constructor
  · intro hmem
    obtain ⟨q, h, rfl⟩ := (mem_incAt hw ρ β).mp hmem
    change (tgtVertex hw ρ β (tgtPos hw ρ β v)).val = v.val
    rw [tgtVertex_tgtPos]
  · intro he
    obtain ⟨p', q', h', rfl⟩ := arc_cases hw ρ β e
    have hv : tgtVertex hw ρ β p' = v := by
      apply Subtype.ext
      exact he
    have hp : p' = tgtPos hw ρ β v := by
      rw [← hv, tgtPos_tgtVertex]
    subst hp
    exact (mem_incAt hw ρ β).mpr ⟨q', h', rfl⟩

end Pos

/-! ## The freeze layer -/

section Freeze

variable (hw : 0 < w) (k : Fin w) (b : Bool)

/-- Freeze coordinate `k`, keep the rest. -/
noncomputable def freezeRho : Fin w → Option (Fin w) :=
  fun p => if p = k then none else some p

noncomputable def freezeBeta : Fin w → Bool := fun _ => b

theorem freezeRho_some {k p q : Fin w} (h : freezeRho k p = some q) :
    q = p ∧ p ≠ k := by
  have h' : (if p = k then (none : Option (Fin w)) else some p) = some q := h
  by_cases hpk : p = k
  · rw [if_pos hpk] at h'
    exact absurd h' (by simp)
  · rw [if_neg hpk] at h'
    exact ⟨(Option.some.inj h').symm, hpk⟩

/-- For the freeze layer the outgoing block of source `q` is the incoming
block of target `q`. -/
theorem freeze_out_exact (u : LayerVertex (optCircuit w hw (freezeRho k) (freezeBeta b)) 0)
    (e : TransitionArc (optCircuit w hw (freezeRho k) (freezeBeta b)) 0) :
    e ∈ incAt hw (freezeRho k) (freezeBeta b)
        (srcPos hw (freezeRho k) (freezeBeta b) u)
      ↔ e.1.1 = u.1 := by
  constructor
  · intro hmem
    obtain ⟨q, h, rfl⟩ := (mem_incAt hw (freezeRho k) (freezeBeta b)).mp hmem
    have hq : q = srcPos hw (freezeRho k) (freezeBeta b) u :=
      (freezeRho_some h).1
    subst hq
    change (srcVertex hw (freezeRho k) (freezeBeta b)
      (srcPos hw (freezeRho k) (freezeBeta b) u)).val = u.val
    rw [srcVertex_srcPos]
  · intro he
    obtain ⟨p', q', h', rfl⟩ := arc_cases hw (freezeRho k) (freezeBeta b) e
    have hqp : q' = p' ∧ p' ≠ k := freezeRho_some h'
    have hu : srcVertex hw (freezeRho k) (freezeBeta b) q' = u := by
      apply Subtype.ext
      exact he
    have hp : p' = srcPos hw (freezeRho k) (freezeBeta b) u := by
      rw [← hqp.1, ← hu, srcPos_srcVertex]
    subst hp
    exact (mem_incAt hw (freezeRho k) (freezeBeta b)).mpr ⟨q', h', rfl⟩

/-- The freeze word equality: outgoing and incoming blocks coincide
positionwise. -/
theorem freeze_word_eq :
    (srcListing hw (freezeRho k) (freezeBeta b)).entries.flatMap
        (fun u => incAt hw (freezeRho k) (freezeBeta b)
          (srcPos hw (freezeRho k) (freezeBeta b) u))
      = (tgtListing hw (freezeRho k) (freezeBeta b)).entries.flatMap
        (fun v => incAt hw (freezeRho k) (freezeBeta b)
          (tgtPos hw (freezeRho k) (freezeBeta b) v)) := by
  change ((List.finRange w).map (srcVertex hw (freezeRho k) (freezeBeta b))).flatMap _
    = ((List.finRange w).map (tgtVertex hw (freezeRho k) (freezeBeta b))).flatMap _
  rw [flatMap_map', flatMap_map']
  refine flatMap_congr' _ (fun p _ => ?_)
  rw [srcPos_srcVertex, tgtPos_tgtVertex]

include hw in
/-- **The freeze layer is certified.** -/
theorem freezeTrans_mem :
    optTrans (freezeRho k) (freezeBeta b) ∈ NonCrossing w := by
  refine optTrans_mem_nonCrossing hw (freezeRho k) (freezeBeta b)
    (optCylinder hw (freezeRho k) (freezeBeta b)
      (fun u => incAt hw (freezeRho k) (freezeBeta b)
        (srcPos hw (freezeRho k) (freezeBeta b) u))
      (fun v => incAt hw (freezeRho k) (freezeBeta b)
        (tgtPos hw (freezeRho k) (freezeBeta b) v))
      (fun u => incAt_nodup hw (freezeRho k) (freezeBeta b) _)
      (fun v => incAt_nodup hw (freezeRho k) (freezeBeta b) _)
      (freeze_out_exact hw k b)
      (incAt_exact hw (freezeRho k) (freezeBeta b))
      (freeze_word_eq hw k b))
    (optCylinder_canonical hw (freezeRho k) (freezeBeta b) _ _ _ _ _ _ _)

end Freeze

/-! ## The adjacent duplication layers -/

section Dup

variable (hw : 0 < w)

/-- The all-false constant table (unused by total `ρ`s). -/
noncomputable def beta0 (w' : Nat) : Fin w' → Bool := fun _ => false

/-- Arcs with equal endpoint data are equal. -/
theorem optArc_eq_of_val {ρ : Fin w → Option (Fin w)} {β : Fin w → Bool}
    {p₁ q₁ p₂ q₂ : Fin w} (h₁ : ρ p₁ = some q₁) (h₂ : ρ p₂ = some q₂)
    (hp : p₁ = p₂) (hq : q₁ = q₂) :
    optArc hw ρ β p₁ q₁ h₁ = optArc hw ρ β p₂ q₂ h₂ := by
  subst hp
  subst hq
  exact Subtype.ext rfl

/-- The incoming block at a position with a prescribed source. -/
theorem incAt_of_some {ρ : Fin w → Option (Fin w)} {β : Fin w → Bool}
    {p q : Fin w} (h : ρ p = some q) :
    incAt hw ρ β p = [optArc hw ρ β p q h] := by
  unfold incAt
  split
  · next q' hq' =>
    have hqq : q' = q := Option.some.inj (hq'.symm.trans h)
    subst hqq
    rfl
  · next hn => exact absurd (hn.symm.trans h) (by simp)

section DupNext

variable (i : Fin w) (hi : i.val + 1 < w)

/-- Copy coordinate `i` onto `i + 1`, keep the rest. -/
noncomputable def dupNextRho : Fin w → Option (Fin w) :=
  fun p => if p.val = i.val + 1 then some i else some p

theorem dupNextRho_some {p q : Fin w} (h : dupNextRho i p = some q) :
    (p.val = i.val + 1 ∧ q = i) ∨ (p.val ≠ i.val + 1 ∧ q = p) := by
  have h' : (if p.val = i.val + 1 then some i else some p) = some q := h
  by_cases hp : p.val = i.val + 1
  · rw [if_pos hp] at h'
    exact Or.inl ⟨hp, (Option.some.inj h').symm⟩
  · rw [if_neg hp] at h'
    exact Or.inr ⟨hp, (Option.some.inj h').symm⟩

theorem dupNextRho_self (p : Fin w) (hp : p.val ≠ i.val + 1) :
    dupNextRho i p = some p := by
  change (if p.val = i.val + 1 then some i else some p) = some p
  rw [if_neg hp]

theorem dupNextRho_succ : dupNextRho i ⟨i.val + 1, hi⟩ = some i := by
  change (if i.val + 1 = i.val + 1 then some i else _) = some i
  rw [if_pos rfl]

/-- The outgoing blocks of the forward duplication layer. -/
noncomputable def dupNextOut (q : Fin w) :
    List (TransitionArc (optCircuit w hw (dupNextRho i) (beta0 w)) 0) :=
  if q.val = i.val then
    [optArc hw (dupNextRho i) (beta0 w) i i (dupNextRho_self i i (by omega)),
     optArc hw (dupNextRho i) (beta0 w) ⟨i.val + 1, hi⟩ i (dupNextRho_succ i hi)]
  else if hq2 : q.val = i.val + 1 then []
  else [optArc hw (dupNextRho i) (beta0 w) q q (dupNextRho_self i q hq2)]

theorem dupNextOut_nodup (q : Fin w) : (dupNextOut hw i hi q).Nodup := by
  unfold dupNextOut
  split
  · refine List.nodup_cons.mpr ⟨?_, List.nodup_singleton _⟩
    intro hmem
    rw [List.mem_singleton] at hmem
    have h1 : (optArc hw (dupNextRho i) (beta0 w) i i
          (dupNextRho_self i i (by omega))).1.2.val
        = (optArc hw (dupNextRho i) (beta0 w) ⟨i.val + 1, hi⟩ i
          (dupNextRho_succ i hi)).1.2.val := by
      rw [hmem]
    have h2 : w + i.val = w + (i.val + 1) := h1
    omega
  · split
    · exact List.nodup_nil
    · exact List.nodup_singleton _

theorem dupNextOut_exact
    (u : LayerVertex (optCircuit w hw (dupNextRho i) (beta0 w)) 0)
    (e : TransitionArc (optCircuit w hw (dupNextRho i) (beta0 w)) 0) :
    e ∈ dupNextOut hw i hi (srcPos hw (dupNextRho i) (beta0 w) u)
      ↔ e.1.1 = u.1 := by
  constructor
  · intro hmem
    unfold dupNextOut at hmem
    split at hmem
    · next hq =>
      have hsrc : e.1.1 = (srcVertex hw (dupNextRho i) (beta0 w) i).val := by
        rcases List.mem_cons.mp hmem with h | h
        · rw [h]
          rfl
        · rw [List.mem_singleton] at h
          rw [h]
          rfl
      rw [hsrc]
      apply Fin.ext
      exact hq.symm
    · split at hmem
      · exact absurd hmem (List.not_mem_nil)
      · rw [List.mem_singleton] at hmem
        rw [hmem]
        exact Subtype.ext_iff.mp (srcVertex_srcPos hw (dupNextRho i) (beta0 w) u)
  · intro he
    obtain ⟨p', q', h', rfl⟩ := arc_cases hw (dupNextRho i) (beta0 w) e
    have hq' : q' = srcPos hw (dupNextRho i) (beta0 w) u := by
      have h2 : srcVertex hw (dupNextRho i) (beta0 w) q' = u := Subtype.ext he
      rw [← h2, srcPos_srcVertex]
    subst hq'
    rcases dupNextRho_some i h' with ⟨hp1, hq1⟩ | ⟨hp1, hq1⟩
    · unfold dupNextOut
      rw [if_pos (Fin.ext_iff.mp hq1)]
      refine List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr ?_))
      exact optArc_eq_of_val hw h' (dupNextRho_succ i hi) (Fin.ext hp1) hq1
    · have hv : (srcPos hw (dupNextRho i) (beta0 w) u).val = p'.val :=
        Fin.ext_iff.mp hq1
      unfold dupNextOut
      by_cases hpi : p'.val = i.val
      · rw [if_pos (hv.trans hpi)]
        refine List.mem_cons.mpr (Or.inl ?_)
        exact optArc_eq_of_val hw h' (dupNextRho_self i i (by omega))
          (Fin.ext hpi) (hq1.trans (Fin.ext hpi))
      · rw [if_neg (fun hc => hpi (hv.symm.trans hc)),
          dif_neg (fun hc => hp1 (hv.symm.trans hc))]
        rw [List.mem_singleton]
        exact optArc_eq_of_val hw h'
          (dupNextRho_self i _ (fun hc => hp1 (hv.symm.trans hc)))
          hq1.symm rfl

theorem dupNext_word_eq :
    (srcListing hw (dupNextRho i) (beta0 w)).entries.flatMap
        (fun u => dupNextOut hw i hi (srcPos hw (dupNextRho i) (beta0 w) u))
      = (tgtListing hw (dupNextRho i) (beta0 w)).entries.flatMap
        (fun v => incAt hw (dupNextRho i) (beta0 w)
          (tgtPos hw (dupNextRho i) (beta0 w) v)) := by
  change ((List.finRange w).map (srcVertex hw (dupNextRho i) (beta0 w))).flatMap _
    = ((List.finRange w).map (tgtVertex hw (dupNextRho i) (beta0 w))).flatMap _
  rw [flatMap_map', flatMap_map']
  rw [show (List.finRange w).flatMap
        (fun q => dupNextOut hw i hi
          (srcPos hw (dupNextRho i) (beta0 w)
            (srcVertex hw (dupNextRho i) (beta0 w) q)))
      = (List.finRange w).flatMap (dupNextOut hw i hi) from
    flatMap_congr' _ (fun q _ => by rw [srcPos_srcVertex])]
  rw [show (List.finRange w).flatMap
        (fun p => incAt hw (dupNextRho i) (beta0 w)
          (tgtPos hw (dupNextRho i) (beta0 w)
            (tgtVertex hw (dupNextRho i) (beta0 w) p)))
      = (List.finRange w).flatMap (incAt hw (dupNextRho i) (beta0 w)) from
    flatMap_congr' _ (fun p _ => by rw [tgtPos_tgtVertex])]
  refine flatMap_eq_of_agree_outside_pair i hi _ _ ?_ ?_ ?_
  · intro q hq
    unfold dupNextOut
    rw [if_neg (by omega), dif_neg (by omega),
      incAt_of_some hw (dupNextRho_self i q (by omega))]
  · intro q hq
    unfold dupNextOut
    rw [if_neg (by omega), dif_neg (by omega),
      incAt_of_some hw (dupNextRho_self i q (by omega))]
  · unfold dupNextOut
    rw [if_pos rfl, if_neg (by change ¬ i.val + 1 = i.val; omega), dif_pos rfl,
      incAt_of_some hw (dupNextRho_self i i (by omega)),
      incAt_of_some hw (dupNextRho_succ i hi)]
    rfl

include hw hi in
/-- **The forward duplication layer is certified.** -/
theorem dupNextTrans_mem :
    optTrans (dupNextRho i) (beta0 w) ∈ NonCrossing w := by
  refine optTrans_mem_nonCrossing hw (dupNextRho i) (beta0 w)
    (optCylinder hw (dupNextRho i) (beta0 w)
      (fun u => dupNextOut hw i hi (srcPos hw (dupNextRho i) (beta0 w) u))
      (fun v => incAt hw (dupNextRho i) (beta0 w)
        (tgtPos hw (dupNextRho i) (beta0 w) v))
      (fun u => dupNextOut_nodup hw i hi _)
      (fun v => incAt_nodup hw (dupNextRho i) (beta0 w) _)
      (dupNextOut_exact hw i hi)
      (incAt_exact hw (dupNextRho i) (beta0 w))
      (dupNext_word_eq hw i hi))
    (optCylinder_canonical hw (dupNextRho i) (beta0 w) _ _ _ _ _ _ _)

end DupNext

section DupPrev

variable (i : Fin w) (hi : i.val + 1 < w)

/-- Copy coordinate `i + 1` onto `i`, keep the rest. -/
noncomputable def dupPrevRho : Fin w → Option (Fin w) :=
  fun p => if p.val = i.val then some ⟨i.val + 1, hi⟩ else some p

theorem dupPrevRho_some {p q : Fin w} (h : dupPrevRho i hi p = some q) :
    (p.val = i.val ∧ q = ⟨i.val + 1, hi⟩) ∨ (p.val ≠ i.val ∧ q = p) := by
  have h' : (if p.val = i.val then some (⟨i.val + 1, hi⟩ : Fin w) else some p)
      = some q := h
  by_cases hp : p.val = i.val
  · rw [if_pos hp] at h'
    exact Or.inl ⟨hp, (Option.some.inj h').symm⟩
  · rw [if_neg hp] at h'
    exact Or.inr ⟨hp, (Option.some.inj h').symm⟩

theorem dupPrevRho_self (p : Fin w) (hp : p.val ≠ i.val) :
    dupPrevRho i hi p = some p := by
  change (if p.val = i.val then some (⟨i.val + 1, hi⟩ : Fin w) else some p) = some p
  rw [if_neg hp]

theorem dupPrevRho_base : dupPrevRho i hi i = some ⟨i.val + 1, hi⟩ := by
  change (if i.val = i.val then some (⟨i.val + 1, hi⟩ : Fin w) else _) = _
  rw [if_pos rfl]

/-- The outgoing blocks of the backward duplication layer. -/
noncomputable def dupPrevOut (q : Fin w) :
    List (TransitionArc (optCircuit w hw (dupPrevRho i hi) (beta0 w)) 0) :=
  if q.val = i.val + 1 then
    [optArc hw (dupPrevRho i hi) (beta0 w) i ⟨i.val + 1, hi⟩ (dupPrevRho_base i hi),
     optArc hw (dupPrevRho i hi) (beta0 w) ⟨i.val + 1, hi⟩ ⟨i.val + 1, hi⟩
       (dupPrevRho_self i hi ⟨i.val + 1, hi⟩ (by change i.val + 1 ≠ i.val; omega))]
  else if hq2 : q.val = i.val then []
  else [optArc hw (dupPrevRho i hi) (beta0 w) q q (dupPrevRho_self i hi q hq2)]

theorem dupPrevOut_nodup (q : Fin w) : (dupPrevOut hw i hi q).Nodup := by
  unfold dupPrevOut
  split
  · refine List.nodup_cons.mpr ⟨?_, List.nodup_singleton _⟩
    intro hmem
    rw [List.mem_singleton] at hmem
    have h1 : (optArc hw (dupPrevRho i hi) (beta0 w) i ⟨i.val + 1, hi⟩
          (dupPrevRho_base i hi)).1.2.val
        = (optArc hw (dupPrevRho i hi) (beta0 w) ⟨i.val + 1, hi⟩ ⟨i.val + 1, hi⟩
          (dupPrevRho_self i hi ⟨i.val + 1, hi⟩ (by change i.val + 1 ≠ i.val; omega))).1.2.val := by
      rw [hmem]
    have h2 : w + i.val = w + (i.val + 1) := h1
    omega
  · split
    · exact List.nodup_nil
    · exact List.nodup_singleton _

theorem dupPrevOut_exact
    (u : LayerVertex (optCircuit w hw (dupPrevRho i hi) (beta0 w)) 0)
    (e : TransitionArc (optCircuit w hw (dupPrevRho i hi) (beta0 w)) 0) :
    e ∈ dupPrevOut hw i hi (srcPos hw (dupPrevRho i hi) (beta0 w) u)
      ↔ e.1.1 = u.1 := by
  constructor
  · intro hmem
    unfold dupPrevOut at hmem
    split at hmem
    · next hq =>
      have hsrc : e.1.1
          = (srcVertex hw (dupPrevRho i hi) (beta0 w) ⟨i.val + 1, hi⟩).val := by
        rcases List.mem_cons.mp hmem with h | h
        · rw [h]
          rfl
        · rw [List.mem_singleton] at h
          rw [h]
          rfl
      rw [hsrc]
      apply Fin.ext
      exact hq.symm
    · split at hmem
      · exact absurd hmem (List.not_mem_nil)
      · rw [List.mem_singleton] at hmem
        rw [hmem]
        exact Subtype.ext_iff.mp (srcVertex_srcPos hw (dupPrevRho i hi) (beta0 w) u)
  · intro he
    obtain ⟨p', q', h', rfl⟩ := arc_cases hw (dupPrevRho i hi) (beta0 w) e
    have hq' : q' = srcPos hw (dupPrevRho i hi) (beta0 w) u := by
      have h2 : srcVertex hw (dupPrevRho i hi) (beta0 w) q' = u := Subtype.ext he
      rw [← h2, srcPos_srcVertex]
    subst hq'
    rcases dupPrevRho_some i hi h' with ⟨hp1, hq1⟩ | ⟨hp1, hq1⟩
    · unfold dupPrevOut
      rw [if_pos (Fin.ext_iff.mp hq1)]
      refine List.mem_cons.mpr (Or.inl ?_)
      exact optArc_eq_of_val hw h' (dupPrevRho_base i hi) (Fin.ext hp1) hq1
    · have hv : (srcPos hw (dupPrevRho i hi) (beta0 w) u).val = p'.val :=
        Fin.ext_iff.mp hq1
      unfold dupPrevOut
      by_cases hpi : p'.val = i.val + 1
      · rw [if_pos (hv.trans hpi)]
        refine List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr ?_))
        exact optArc_eq_of_val hw h'
          (dupPrevRho_self i hi ⟨i.val + 1, hi⟩ (by change i.val + 1 ≠ i.val; omega))
          (Fin.ext hpi) (hq1.trans (Fin.ext hpi))
      · rw [if_neg (fun hc => hpi (hv.symm.trans hc)),
          dif_neg (fun hc => hp1 (hv.symm.trans hc))]
        rw [List.mem_singleton]
        exact optArc_eq_of_val hw h'
          (dupPrevRho_self i hi _ (fun hc => hp1 (hv.symm.trans hc)))
          hq1.symm rfl

theorem dupPrev_word_eq :
    (srcListing hw (dupPrevRho i hi) (beta0 w)).entries.flatMap
        (fun u => dupPrevOut hw i hi (srcPos hw (dupPrevRho i hi) (beta0 w) u))
      = (tgtListing hw (dupPrevRho i hi) (beta0 w)).entries.flatMap
        (fun v => incAt hw (dupPrevRho i hi) (beta0 w)
          (tgtPos hw (dupPrevRho i hi) (beta0 w) v)) := by
  change ((List.finRange w).map (srcVertex hw (dupPrevRho i hi) (beta0 w))).flatMap _
    = ((List.finRange w).map (tgtVertex hw (dupPrevRho i hi) (beta0 w))).flatMap _
  rw [flatMap_map', flatMap_map']
  rw [show (List.finRange w).flatMap
        (fun q => dupPrevOut hw i hi
          (srcPos hw (dupPrevRho i hi) (beta0 w)
            (srcVertex hw (dupPrevRho i hi) (beta0 w) q)))
      = (List.finRange w).flatMap (dupPrevOut hw i hi) from
    flatMap_congr' _ (fun q _ => by rw [srcPos_srcVertex])]
  rw [show (List.finRange w).flatMap
        (fun p => incAt hw (dupPrevRho i hi) (beta0 w)
          (tgtPos hw (dupPrevRho i hi) (beta0 w)
            (tgtVertex hw (dupPrevRho i hi) (beta0 w) p)))
      = (List.finRange w).flatMap (incAt hw (dupPrevRho i hi) (beta0 w)) from
    flatMap_congr' _ (fun p _ => by rw [tgtPos_tgtVertex])]
  refine flatMap_eq_of_agree_outside_pair i hi _ _ ?_ ?_ ?_
  · intro q hq
    unfold dupPrevOut
    rw [if_neg (by omega), dif_neg (by omega),
      incAt_of_some hw (dupPrevRho_self i hi q (by omega))]
  · intro q hq
    unfold dupPrevOut
    rw [if_neg (by omega), dif_neg (by omega),
      incAt_of_some hw (dupPrevRho_self i hi q (by omega))]
  · unfold dupPrevOut
    rw [if_neg (by show ¬ i.val = i.val + 1; omega), dif_pos rfl, if_pos rfl,
      incAt_of_some hw (dupPrevRho_base i hi),
      incAt_of_some hw (dupPrevRho_self i hi ⟨i.val + 1, hi⟩ (by change i.val + 1 ≠ i.val; omega))]
    rfl

include hw hi in
/-- **The backward duplication layer is certified.** -/
theorem dupPrevTrans_mem :
    optTrans (dupPrevRho i hi) (beta0 w) ∈ NonCrossing w := by
  refine optTrans_mem_nonCrossing hw (dupPrevRho i hi) (beta0 w)
    (optCylinder hw (dupPrevRho i hi) (beta0 w)
      (fun u => dupPrevOut hw i hi (srcPos hw (dupPrevRho i hi) (beta0 w) u))
      (fun v => incAt hw (dupPrevRho i hi) (beta0 w)
        (tgtPos hw (dupPrevRho i hi) (beta0 w) v))
      (fun u => dupPrevOut_nodup hw i hi _)
      (fun v => incAt_nodup hw (dupPrevRho i hi) (beta0 w) _)
      (dupPrevOut_exact hw i hi)
      (incAt_exact hw (dupPrevRho i hi) (beta0 w))
      (dupPrev_word_eq hw i hi))
    (optCylinder_canonical hw (dupPrevRho i hi) (beta0 w) _ _ _ _ _ _ _)

end DupPrev

end Dup


end Internal
end AllenderOQ3
