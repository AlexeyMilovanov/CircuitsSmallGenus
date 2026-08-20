import AllenderOQ3.Base
import AllenderOQ3.Internal.OptCircuit
import AllenderOQ3.Internal.OptCircuitCert
import AllenderOQ3.Internal.OptCircuitInstances
import AllenderOQ3.Internal.ConstantFreeLayers
import AllenderOQ3.Internal.CFPairGate

namespace AllenderOQ3.Internal

variable {w : Nat} (hw : 0 < w)
variable (preds : Fin w → List (Fin w)) (tgtKind : Fin w → ADRGate 1)

def pair_srcVertex (p : Fin w) : LayerVertex (pairCircuit hw preds tgtKind) 0 :=
  ⟨⟨p.val, by change p.val < 2 * w; omega⟩, Nat.div_eq_of_lt p.isLt⟩

def pair_tgtVertex (p : Fin w) : LayerVertex (pairCircuit hw preds tgtKind) 1 :=
  ⟨⟨w + p.val, by change w + p.val < 2 * w; omega⟩, by
    change (w + p.val) / w = 1
    rw [Nat.add_comm, Nat.add_div_right _ hw, Nat.div_eq_of_lt p.isLt]⟩

theorem pair_srcVertex_injective : Function.Injective (pair_srcVertex hw preds tgtKind) := by
  intro a b hab
  have h1 := Fin.ext_iff.mp (Subtype.ext_iff.mp hab)
  exact Fin.ext h1

theorem pair_tgtVertex_injective : Function.Injective (pair_tgtVertex hw preds tgtKind) := by
  intro a b hab
  have h1 := Fin.ext_iff.mp (Subtype.ext_iff.mp hab)
  have h2 : w + a.val = w + b.val := h1
  exact Fin.ext (by omega)

noncomputable def pair_srcListing : CyclicListing (LayerVertex (pairCircuit hw preds tgtKind) 0)
  where
  entries := (List.finRange w).map (pair_srcVertex hw preds tgtKind)
  nodup := List.Nodup.map (pair_srcVertex_injective hw preds tgtKind) (List.nodup_finRange w)
  complete := by
    intro a
    have ha : a.val.val < w := by
      have h1 : a.val.val / w = 0 := a.2
      have h2 : a.val.val < 2 * w := a.val.isLt
      by_contra hcon
      push_neg at hcon
      have h3 : 1 ≤ a.val.val / w := (Nat.one_le_div_iff hw).mpr hcon
      rw [h1] at h3
      omega
    have heq : a = pair_srcVertex hw preds tgtKind ⟨a.val.val, ha⟩ := by
      apply Subtype.ext
      apply Fin.ext
      rfl
    rw [heq]
    exact List.mem_map_of_mem (List.mem_finRange _)

noncomputable def pair_tgtListing : CyclicListing (LayerVertex (pairCircuit hw preds tgtKind) 1)
  where
  entries := (List.finRange w).map (pair_tgtVertex hw preds tgtKind)
  nodup := List.Nodup.map (pair_tgtVertex_injective hw preds tgtKind) (List.nodup_finRange w)
  complete := by
    intro a
    have h1 : a.val.val / w = 1 := a.2
    have h2 : a.val.val < 2 * w := a.val.isLt
    have ha : w ≤ a.val.val := by
      by_contra hcon
      push_neg at hcon
      have h3 : a.val.val / w = 0 := Nat.div_eq_of_lt hcon
      rw [h1] at h3
      omega
    have hb : a.val.val - w < w := by omega
    have heq : a = pair_tgtVertex hw preds tgtKind ⟨a.val.val - w, hb⟩ := by
      apply Subtype.ext
      apply Fin.ext
      change a.val.val = w + (a.val.val - w)
      omega
    rw [heq]
    exact List.mem_map_of_mem (List.mem_finRange _)

theorem pairCircuit_edge_of (p q : Fin w) (h : q ∈ preds p) :
    (pairCircuit hw preds tgtKind).edge (pair_srcVertex hw preds tgtKind q).val
      (pair_tgtVertex hw preds tgtKind p).val = true := by
  dsimp [pairCircuit, pair_srcVertex, pair_tgtVertex]
  simp only [decide_eq_true_eq]
  refine ⟨q.isLt, by omega, ?_⟩
  have hp : (w + p.val) % w = p.val := by
    rw [Nat.add_comm, Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod, Nat.mod_eq_of_lt p.isLt]
  have hq : q.val % w = q.val := Nat.mod_eq_of_lt q.isLt
  have hq1 : (⟨q.val % w, Nat.mod_lt _ hw⟩ : Fin w) = q := Fin.eq_of_val_eq hq
  have hp1 : (⟨(w + p.val) % w, Nat.mod_lt _ hw⟩ : Fin w) = p := Fin.eq_of_val_eq hp
  rw [hq1, hp1]
  exact h

noncomputable def pairArc (p q : Fin w) (h : q ∈ preds p) :
    TransitionArc (pairCircuit hw preds tgtKind) 0 :=
  ⟨((pair_srcVertex hw preds tgtKind q).val, (pair_tgtVertex hw preds tgtKind p).val),
    pairCircuit_edge_of hw preds tgtKind p q h, (pair_srcVertex hw preds tgtKind q).2,
      (pair_tgtVertex hw preds tgtKind p).2⟩

theorem pairArc_source (p q : Fin w) (h : q ∈ preds p) :
    arcSource (pairArc hw preds tgtKind p q h) = pair_srcVertex hw preds tgtKind q :=
  Subtype.ext rfl

theorem pairArc_target (p q : Fin w) (h : q ∈ preds p) :
    arcTarget (pairArc hw preds tgtKind p q h) = pair_tgtVertex hw preds tgtKind p :=
  Subtype.ext rfl

noncomputable def pair_emptyListing (m : Nat) : CyclicListing
  (LayerVertex (pairCircuit hw preds tgtKind) (m + 2)) where
  entries := []
  nodup := List.nodup_nil
  complete := by
    intro a
    exfalso
    have h1 : (pairCircuit hw preds tgtKind).layer a.val = m + 2 := a.2
    have h2 := pairCircuit_layer_lt hw preds tgtKind a.val
    rw [h1] at h2
    omega

noncomputable def pairOrders :
    (ell : Nat) → CyclicListing (LayerVertex (pairCircuit hw preds tgtKind) ell)
  | 0 => pair_srcListing hw preds tgtKind
  | 1 => pair_tgtListing hw preds tgtKind
  -- Any empty listing of the correct type would do for the layers above the first two.
  | (m + 2) => pair_emptyListing hw preds tgtKind m

theorem pairArc_cases (e : TransitionArc (pairCircuit hw preds tgtKind) 0) :
    ∃ (p q : Fin w) (h : q ∈ preds p), e = pairArc hw preds tgtKind p q h := by
  obtain ⟨⟨u, v⟩, hedge, hlu, hlv⟩ := e
  obtain ⟨hu, hv, hρ⟩ := (pairCircuit_edge_iff hw preds tgtKind).mp hedge
  have hlv_val : v.val / w = 1 := hlv
  have hw_le : w ≤ v.val := by
    by_contra hcon
    push_neg at hcon
    have h0 : v.val / w = 0 := Nat.div_eq_of_lt hcon
    rw [hlv_val] at h0
    omega
  have hpw : v.val - w < w := by
    have h_bound : v.val < 2 * w := v.isLt
    omega
  use ⟨v.val - w, hpw⟩
  use ⟨u.val, hu⟩
  have heq_u : u.val % w = u.val := Nat.mod_eq_of_lt hu
  have heq_v : v.val % w = v.val - w := by
    have h1 : v.val / w = 1 := hlv
    have h2 : v.val = w * (v.val / w) + v.val % w := (Nat.div_add_mod _ _).symm
    rw [h1] at h2
    omega
  have hρ_cast : (⟨u.val, hu⟩ : Fin w) ∈ preds ⟨v.val - w, hpw⟩ := by
    have hu1 : (⟨u.val % w, Nat.mod_lt _ hw⟩ : Fin w) = ⟨u.val, hu⟩ := Fin.eq_of_val_eq heq_u
    have hv1 : (⟨v.val % w, Nat.mod_lt _ hw⟩ : Fin w) = ⟨v.val - w, hpw⟩ := Fin.eq_of_val_eq heq_v
    rw [← hu1, ← hv1]
    exact hρ
  use hρ_cast
  apply Subtype.ext
  apply Prod.ext
  · apply Fin.ext; rfl
  · apply Fin.ext; exact (Nat.add_sub_of_le hw_le).symm

theorem pairArc_eq_of_val
    {p1 q1 p2 q2 : Fin w}
    (h1 : q1 ∈ preds p1) (h2 : q2 ∈ preds p2)
    (hp : p1 = p2) (hq : q1 = q2) :
    pairArc hw preds tgtKind p1 q1 h1 = pairArc hw preds tgtKind p2 q2 h2 := by
  subst hp hq
  rfl

/-! ## Assembling the full incidence cylinder -/

/-- No arcs exist above the base transition of `pairCircuit`. -/
theorem pair_no_arc_above (ell : Nat)
    (e : TransitionArc (pairCircuit hw preds tgtKind) (ell + 1)) : False := by
  obtain ⟨⟨u, v⟩, hedge, hlu, hlv⟩ := e
  obtain ⟨hu, -, -⟩ := (pairCircuit_edge_iff hw preds tgtKind).mp hedge
  have h0 : (pairCircuit hw preds tgtKind).layer u = 0 := Nat.div_eq_of_lt hu
  rw [h0] at hlu
  omega

/-- The empty certificate for any transition above the base. -/
noncomputable def pair_emptyTransition (ell : Nat)
    (O₁ : CyclicListing (LayerVertex (pairCircuit hw preds tgtKind) (ell + 1)))
    (O₂ : CyclicListing (LayerVertex (pairCircuit hw preds tgtKind) (ell + 2))) :
    ArcOrderCertificate (pairCircuit hw preds tgtKind) (ell + 1) O₁ O₂ :=
  arcOrderCertificate_of_eq (fun _ => []) (fun _ => [])
    (fun _ => List.nodup_nil) (fun _ => List.nodup_nil)
    (fun _ e => (pair_no_arc_above hw preds tgtKind ell e).elim)
    (fun _ e => (pair_no_arc_above hw preds tgtKind ell e).elim)
    (by rw [flatMap_const_nil, flatMap_const_nil])

/-- The incidence cylinder of `pairCircuit`, from a base transition certificate. -/
noncomputable def pairCylinder
    (base : ArcOrderCertificate (pairCircuit hw preds tgtKind) 0
      (pair_srcListing hw preds tgtKind) (pair_tgtListing hw preds tgtKind)) :
    IncidenceCylinder (pairCircuit hw preds tgtKind) where
  layerOrder := pairOrders hw preds tgtKind
  transitionOrder := fun ell => match ell with
    | 0 => base
    | (m + 1) => pair_emptyTransition hw preds tgtKind m
        (pairOrders hw preds tgtKind (m + 1)) (pairOrders hw preds tgtKind (m + 2))

section AdjPair

variable (i : Fin w) (hi : i.val + 1 < w)

def staircasePreds : Fin w → List (Fin w) :=
  fun p =>
    if p.val = i.val + 1 then
      [i, ⟨i.val + 1, hi⟩]
    else
      [p]

theorem staircasePreds_len (p : Fin w) : (staircasePreds i hi p).length ≤ 2 := by
  unfold staircasePreds
  split
  · exact Nat.le_refl _
  · exact Nat.le_succ_of_le (Nat.le_refl _)

theorem staircasePreds_nonempty (p : Fin w) : (staircasePreds i hi p).length ≠ 0 := by
  unfold staircasePreds
  split
  · intro h; injection h
  · intro h; injection h

theorem staircasePreds_self (q : Fin w) (hq : q.val ≠ i.val + 1) :
    staircasePreds i hi q = [q] := by
  unfold staircasePreds
  rw [if_neg hq]

theorem staircasePreds_succ :
    staircasePreds i hi ⟨i.val + 1, hi⟩ = [i, ⟨i.val + 1, hi⟩] := by
  unfold staircasePreds
  rw [if_pos rfl]

noncomputable def adjOut (q : Fin w) :
    List (TransitionArc (pairCircuit hw (staircasePreds i hi) tgtKind) 0) :=
  if hq : q.val = i.val then
    [pairArc hw (staircasePreds i hi) tgtKind i i
      (by rw [staircasePreds_self i hi i (by omega)]; simp),
     pairArc hw (staircasePreds i hi) tgtKind ⟨i.val + 1, hi⟩ i
       (by rw [staircasePreds_succ i hi]; simp)]
  else if hq2 : q.val = i.val + 1 then
    [pairArc hw (staircasePreds i hi) tgtKind ⟨i.val + 1, hi⟩ ⟨i.val + 1, hi⟩
      (by rw [staircasePreds_succ i hi]; simp)]
  else
    [pairArc hw (staircasePreds i hi) tgtKind q q (by rw [staircasePreds_self i hi q hq2]; simp)]

theorem adjOut_nodup (q : Fin w) : (adjOut hw tgtKind i hi q).Nodup := by
  unfold adjOut
  split
  · refine List.nodup_cons.mpr ⟨?_, List.nodup_singleton _⟩
    intro hmem
    rw [List.mem_singleton] at hmem
    have h1 :
      ((pairArc hw (staircasePreds i hi) tgtKind i i
      (by rw [staircasePreds_self i hi i (by omega)]; simp)).1.2.val : Nat)
        = ((pairArc hw (staircasePreds i hi) tgtKind ⟨i.val + 1, hi⟩ i
          (by rw [staircasePreds_succ]; simp)).1.2.val : Nat) := by
      rw [hmem]
    have h2 : w + i.val = w + (i.val + 1) := h1
    omega
  · split
    · exact List.nodup_singleton _
    · exact List.nodup_singleton _



def pair_srcPos (u : LayerVertex (pairCircuit hw (staircasePreds i hi) tgtKind) 0) : Fin w :=
  ⟨u.val.val, by
    have h1 : u.val.val / w = 0 := u.2
    have h2 : u.val.val < 2 * w := u.val.isLt
    by_contra hcon
    push_neg at hcon
    have h3 : 1 ≤ u.val.val / w := (Nat.one_le_div_iff hw).mpr hcon
    omega⟩

theorem pair_srcPos_srcVertex (u : LayerVertex (pairCircuit hw (staircasePreds i hi) tgtKind) 0) :
    pair_srcVertex hw (staircasePreds i hi) tgtKind (pair_srcPos hw tgtKind i hi u) = u := by
  apply Subtype.ext
  apply Fin.ext
  rfl

theorem pair_srcPos_of_srcVertex (q : Fin w) :
    pair_srcPos hw tgtKind i hi (pair_srcVertex hw (staircasePreds i hi) tgtKind q) = q := by
  apply Fin.ext
  rfl

noncomputable def adjInc (q : Fin w) :
    List (TransitionArc (pairCircuit hw (staircasePreds i hi) tgtKind) 0) :=
  if hq : q.val = i.val + 1 then
    [pairArc hw (staircasePreds i hi) tgtKind ⟨i.val + 1, hi⟩ i
      (by rw [staircasePreds_succ i hi]; simp),
     pairArc hw (staircasePreds i hi) tgtKind ⟨i.val + 1, hi⟩ ⟨i.val + 1, hi⟩
       (by rw [staircasePreds_succ i hi]; simp)]
  else if hq2 : q.val = i.val then
    [pairArc hw (staircasePreds i hi) tgtKind i i
      (by rw [staircasePreds_self i hi i (by omega)]; simp)]
  else
    [pairArc hw (staircasePreds i hi) tgtKind q q (by rw [staircasePreds_self i hi q hq]; simp)]

theorem adjInc_nodup (q : Fin w) : (adjInc hw tgtKind i hi q).Nodup := by
  unfold adjInc
  split
  · refine List.nodup_cons.mpr ⟨?_, List.nodup_singleton _⟩
    intro hmem
    rw [List.mem_singleton] at hmem
    have h1 : ((pairArc hw (staircasePreds i hi) tgtKind ⟨i.val + 1, hi⟩ i
          (by rw [staircasePreds_succ i hi]; simp)).1.1.val : Nat)
        = ((pairArc hw (staircasePreds i hi) tgtKind ⟨i.val + 1, hi⟩ ⟨i.val + 1, hi⟩
          (by rw [staircasePreds_succ i hi]; simp)).1.1.val : Nat) := by
      rw [hmem]
    have h2 : i.val = i.val + 1 := h1
    omega
  · split
    · exact List.nodup_singleton _
    · exact List.nodup_singleton _

def pair_tgtPos (v : LayerVertex (pairCircuit hw (staircasePreds i hi) tgtKind) 1) : Fin w :=
  ⟨v.val.val - w, by
    have h1 : v.val.val / w = 1 := v.2
    have h2 : v.val.val < 2 * w := v.val.isLt
    have h3 : w ≤ v.val.val := by
      by_contra hcon
      push_neg at hcon
      have h4 : v.val.val / w = 0 := Nat.div_eq_of_lt hcon
      omega
    omega⟩

theorem pair_tgtPos_tgtVertex (v : LayerVertex (pairCircuit hw (staircasePreds i hi) tgtKind) 1) :
    pair_tgtVertex hw (staircasePreds i hi) tgtKind (pair_tgtPos hw tgtKind i hi v) = v := by
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

theorem pair_tgtPos_of_tgtVertex (p : Fin w) :
    pair_tgtPos hw tgtKind i hi (pair_tgtVertex hw (staircasePreds i hi) tgtKind p) = p := by
  apply Fin.ext
  change (w + p.val) - w = p.val
  omega

theorem adjInc_exact (v : LayerVertex (pairCircuit hw (staircasePreds i hi) tgtKind) 1)
    (e : TransitionArc (pairCircuit hw (staircasePreds i hi) tgtKind) 0) :
    e ∈ adjInc hw tgtKind i hi (pair_tgtPos hw tgtKind i hi v) ↔ e.1.2 = v.1 := by
  constructor
  · intro hmem
    have hwv : w ≤ v.val.val := by
      have h1 : v.val.val / w = 1 := v.2
      by_contra hcon
      push_neg at hcon
      have h4 : v.val.val / w = 0 := Nat.div_eq_of_lt hcon
      omega
    unfold adjInc at hmem
    split at hmem
    · next hq =>
      have htgt : e.1.2 = (pair_tgtVertex hw (staircasePreds i hi) tgtKind ⟨i.val + 1, hi⟩).val :=
        by
        rcases List.mem_cons.mp hmem with h | h
        · rw [h]; rfl
        · rw [List.mem_singleton] at h
          rw [h]; rfl
      rw [htgt]
      apply Fin.ext
      have hq' : v.val.val - w = i.val + 1 := hq
      change w + (i.val + 1) = v.val.val
      omega
    · split at hmem
      · next hq2 =>
        rw [List.mem_singleton] at hmem
        have htgt : e.1.2 = (pair_tgtVertex hw (staircasePreds i hi) tgtKind i).val := by
          rw [hmem]; rfl
        rw [htgt]
        apply Fin.ext
        have hq' : v.val.val - w = i.val := hq2
        change w + i.val = v.val.val
        omega
      · next hq2 =>
        rw [List.mem_singleton] at hmem
        rw [hmem]
        exact Subtype.ext_iff.mp (pair_tgtPos_tgtVertex hw tgtKind i hi v)
  · intro he
    obtain ⟨p', q', h', rfl⟩ := pairArc_cases hw (staircasePreds i hi) tgtKind e
    have hp' : p' = pair_tgtPos hw tgtKind i hi v := by
      have h2 : pair_tgtVertex hw (staircasePreds i hi) tgtKind p' = v := Subtype.ext he
      rw [← h2, pair_tgtPos_of_tgtVertex]
    subst hp'
    by_cases hp1 : (pair_tgtPos hw tgtKind i hi v).val = i.val + 1
    · have hsp : staircasePreds i hi (pair_tgtPos hw tgtKind i hi v) =
        [i, (⟨i.val + 1, hi⟩ : Fin w)] := by
        unfold staircasePreds
        rw [if_pos hp1]
      have hmem2 : q' ∈ [i, (⟨i.val + 1, hi⟩ : Fin w)] := hsp ▸ h'
      unfold adjInc
      rw [dif_pos hp1]
      rcases List.mem_cons.mp hmem2 with hqi | hqs
      · refine List.mem_cons.mpr (Or.inl ?_)
        exact pairArc_eq_of_val hw (staircasePreds i hi) tgtKind h' _ (Fin.ext hp1) hqi
      · rw [List.mem_singleton] at hqs
        refine List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr ?_))
        exact pairArc_eq_of_val hw (staircasePreds i hi) tgtKind h' _ (Fin.ext hp1) hqs
    · have hsp : staircasePreds i hi (pair_tgtPos hw tgtKind i hi v)
          = [pair_tgtPos hw tgtKind i hi v] := staircasePreds_self i hi _ hp1
      have hmem2 : q' ∈ [pair_tgtPos hw tgtKind i hi v] := hsp ▸ h'
      rw [List.mem_singleton] at hmem2
      by_cases hp2 : (pair_tgtPos hw tgtKind i hi v).val = i.val
      · unfold adjInc
        rw [dif_neg hp1, dif_pos hp2]
        refine List.mem_singleton.mpr ?_
        exact pairArc_eq_of_val hw (staircasePreds i hi) tgtKind h' _ (Fin.ext hp2)
          (hmem2.trans (Fin.ext hp2))
      · unfold adjInc
        rw [dif_neg hp1, dif_neg hp2]
        refine List.mem_singleton.mpr ?_
        exact pairArc_eq_of_val hw (staircasePreds i hi) tgtKind h' _ rfl hmem2


/-- Off the special pair, both the outgoing and incoming block of `q` is the
single diagonal arc `q → q`. -/
theorem adjOut_eq_adjInc_of_ne (q : Fin w) (h1 : q.val ≠ i.val) (h2 : q.val ≠ i.val + 1) :
    adjOut hw tgtKind i hi q = adjInc hw tgtKind i hi q := by
  unfold adjOut adjInc
  rw [dif_neg h1, dif_neg h2, dif_neg h2, dif_neg h1]

/-- The outgoing block of source `i`: fans to targets `i` and `i + 1`. -/
theorem adjOut_i_eq :
    adjOut hw tgtKind i hi i =
      [pairArc hw (staircasePreds i hi) tgtKind i i
          (by rw [staircasePreds_self i hi i (by omega)]; simp),
       pairArc hw (staircasePreds i hi) tgtKind ⟨i.val + 1, hi⟩ i
          (by rw [staircasePreds_succ i hi]; simp)] := by
  unfold adjOut
  rw [dif_pos rfl]

/-- The outgoing block of source `i + 1`: the diagonal arc `i+1 → i+1`. -/
theorem adjOut_succ_eq :
    adjOut hw tgtKind i hi ⟨i.val + 1, hi⟩ =
      [pairArc hw (staircasePreds i hi) tgtKind ⟨i.val + 1, hi⟩ ⟨i.val + 1, hi⟩
          (by rw [staircasePreds_succ i hi]; simp)] := by
  unfold adjOut
  rw [dif_neg (show ¬ ((⟨i.val + 1, hi⟩ : Fin w).val = i.val) by
        change ¬ (i.val + 1 = i.val); omega),
    dif_pos (show (⟨i.val + 1, hi⟩ : Fin w).val = i.val + 1 from rfl)]

/-- The incoming block of target `i`: the diagonal arc `i → i`. -/
theorem adjInc_i_eq :
    adjInc hw tgtKind i hi i =
      [pairArc hw (staircasePreds i hi) tgtKind i i
          (by rw [staircasePreds_self i hi i (by omega)]; simp)] := by
  unfold adjInc
  rw [dif_neg (show ¬ (i.val = i.val + 1) by omega), dif_pos rfl]

/-- The incoming block of target `i + 1`: gathered from sources `i` and `i + 1`. -/
theorem adjInc_succ_eq :
    adjInc hw tgtKind i hi ⟨i.val + 1, hi⟩ =
      [pairArc hw (staircasePreds i hi) tgtKind ⟨i.val + 1, hi⟩ i
          (by rw [staircasePreds_succ i hi]; simp),
       pairArc hw (staircasePreds i hi) tgtKind ⟨i.val + 1, hi⟩ ⟨i.val + 1, hi⟩
          (by rw [staircasePreds_succ i hi]; simp)] := by
  unfold adjInc
  rw [dif_pos (show (⟨i.val + 1, hi⟩ : Fin w).val = i.val + 1 from rfl)]

theorem pair_staircase_eq :
    (pair_srcListing hw (staircasePreds i hi) tgtKind).entries.flatMap
      (fun u => adjOut hw tgtKind i hi (pair_srcPos hw tgtKind i hi u)) =
    (pair_tgtListing hw (staircasePreds i hi) tgtKind).entries.flatMap
      (fun v => adjInc hw tgtKind i hi (pair_tgtPos hw tgtKind i hi v)) := by
  change ((List.finRange w).map (pair_srcVertex hw (staircasePreds i hi) tgtKind)).flatMap _
    = ((List.finRange w).map (pair_tgtVertex hw (staircasePreds i hi) tgtKind)).flatMap _
  rw [flatMap_map', flatMap_map']
  rw [show (List.finRange w).flatMap
        (fun q => adjOut hw tgtKind i hi
          (pair_srcPos hw tgtKind i hi (pair_srcVertex hw (staircasePreds i hi) tgtKind q)))
      = (List.finRange w).flatMap (adjOut hw tgtKind i hi) from
    flatMap_congr' _ (fun q _ => by rw [pair_srcPos_of_srcVertex])]
  rw [show (List.finRange w).flatMap
        (fun p => adjInc hw tgtKind i hi
          (pair_tgtPos hw tgtKind i hi (pair_tgtVertex hw (staircasePreds i hi) tgtKind p)))
      = (List.finRange w).flatMap (adjInc hw tgtKind i hi) from
    flatMap_congr' _ (fun p _ => by rw [pair_tgtPos_of_tgtVertex])]
  refine flatMap_eq_of_agree_outside_pair i hi _ _ ?_ ?_ ?_
  · intro q hq
    exact adjOut_eq_adjInc_of_ne hw tgtKind i hi q (by omega) (by omega)
  · intro q hq
    exact adjOut_eq_adjInc_of_ne hw tgtKind i hi q (by omega) (by omega)
  · rw [adjOut_i_eq, adjOut_succ_eq, adjInc_i_eq, adjInc_succ_eq]
    rfl

/-- The outgoing block of a source vertex lists exactly the arcs leaving it. -/
theorem adjOut_exact (u : LayerVertex (pairCircuit hw (staircasePreds i hi) tgtKind) 0)
    (e : TransitionArc (pairCircuit hw (staircasePreds i hi) tgtKind) 0) :
    e ∈ adjOut hw tgtKind i hi (pair_srcPos hw tgtKind i hi u) ↔ e.1.1 = u.1 := by
  constructor
  · intro hmem
    unfold adjOut at hmem
    split at hmem
    · next hq =>
      have hsrc : e.1.1 = (pair_srcVertex hw (staircasePreds i hi) tgtKind i).val := by
        rcases List.mem_cons.mp hmem with h | h
        · rw [h]; rfl
        · rw [List.mem_singleton] at h
          rw [h]; rfl
      rw [hsrc]
      apply Fin.ext
      exact hq.symm
    · split at hmem
      · next hq2 =>
        rw [List.mem_singleton] at hmem
        have hsrc : e.1.1 = (pair_srcVertex hw (staircasePreds i hi) tgtKind ⟨i.val + 1, hi⟩).val
          := by
          rw [hmem]; rfl
        rw [hsrc]
        apply Fin.ext
        exact hq2.symm
      · next hq2 =>
        rw [List.mem_singleton] at hmem
        rw [hmem]
        exact Subtype.ext_iff.mp (pair_srcPos_srcVertex hw tgtKind i hi u)
  · intro he
    obtain ⟨p', q', h', rfl⟩ := pairArc_cases hw (staircasePreds i hi) tgtKind e
    have hq' : q' = pair_srcPos hw tgtKind i hi u := by
      have h2 : pair_srcVertex hw (staircasePreds i hi) tgtKind q' = u := Subtype.ext he
      rw [← h2, pair_srcPos_of_srcVertex]
    subst hq'
    by_cases hp1 : p'.val = i.val + 1
    · have hsp : staircasePreds i hi p' = [i, (⟨i.val + 1, hi⟩ : Fin w)] := by
        unfold staircasePreds
        rw [if_pos hp1]
      have hmem2 : pair_srcPos hw tgtKind i hi u ∈ [i, (⟨i.val + 1, hi⟩ : Fin w)] := hsp ▸ h'
      rcases List.mem_cons.mp hmem2 with hqi | hqs
      · have hval : (pair_srcPos hw tgtKind i hi u).val = i.val := by rw [hqi]
        unfold adjOut
        rw [dif_pos hval]
        refine List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr ?_))
        exact pairArc_eq_of_val hw (staircasePreds i hi) tgtKind h' _ (Fin.ext hp1) hqi
      · rw [List.mem_singleton] at hqs
        have hval : (pair_srcPos hw tgtKind i hi u).val = i.val + 1 := by rw [hqs]
        unfold adjOut
        rw [dif_neg (show ¬ ((pair_srcPos hw tgtKind i hi u).val = i.val) by omega),
          dif_pos hval]
        refine List.mem_singleton.mpr ?_
        exact pairArc_eq_of_val hw (staircasePreds i hi) tgtKind h' _ (Fin.ext hp1) hqs
    · have hsp : staircasePreds i hi p' = [p'] := staircasePreds_self i hi p' hp1
      have hmem2 : pair_srcPos hw tgtKind i hi u ∈ [p'] := hsp ▸ h'
      rw [List.mem_singleton] at hmem2
      by_cases hp2 : p'.val = i.val
      · have hval : (pair_srcPos hw tgtKind i hi u).val = i.val := by rw [hmem2]; exact hp2
        unfold adjOut
        rw [dif_pos hval]
        refine List.mem_cons.mpr (Or.inl ?_)
        exact pairArc_eq_of_val hw (staircasePreds i hi) tgtKind h' _ (Fin.ext hp2)
          (hmem2.trans (Fin.ext hp2))
      · have hval1 : (pair_srcPos hw tgtKind i hi u).val ≠ i.val := by rw [hmem2]; exact hp2
        have hval2 : (pair_srcPos hw tgtKind i hi u).val ≠ i.val + 1 := by rw [hmem2]; exact hp1
        unfold adjOut
        rw [dif_neg hval1, dif_neg hval2]
        refine List.mem_singleton.mpr ?_
        exact pairArc_eq_of_val hw (staircasePreds i hi) tgtKind h' _ hmem2.symm rfl

noncomputable def adjPairCylinder :
    ArcOrderCertificate (pairCircuit hw (staircasePreds i hi) tgtKind) 0
      (pair_srcListing hw (staircasePreds i hi) tgtKind)
      (pair_tgtListing hw (staircasePreds i hi) tgtKind) :=
  arcOrderCertificate_of_eq
    (adjOut hw tgtKind i hi ∘ pair_srcPos hw tgtKind i hi)
    (adjInc hw tgtKind i hi ∘ pair_tgtPos hw tgtKind i hi)
    (fun u => by exact adjOut_nodup hw tgtKind i hi (pair_srcPos hw tgtKind i hi u))
    (fun v => by exact adjInc_nodup hw tgtKind i hi (pair_tgtPos hw tgtKind i hi v))
    (adjOut_exact hw tgtKind i hi)
    (adjInc_exact hw tgtKind i hi)
    (pair_staircase_eq hw tgtKind i hi)

/-- **The elementary adjacent fan-in-2 constant-free gate is certified.**  For any
target-kind assignment of AND/OR gates, the width-`w` transition realised by the
staircase gate lies in the constant-free submonoid `NonCrossingCF w`.  This is the
first family of genuine fan-in-2 members of `NonCrossingCF` (the copy layers of
`CFCopyLayer.lean` are all fan-in-1). -/
theorem pairGateTrans_memCF (h_comp : ∀ p, (tgtKind p).isComputation) :
    layerTrans (pairCircuit hw (staircasePreds i hi) tgtKind)
        (pairCylinder hw (staircasePreds i hi) tgtKind (adjPairCylinder hw tgtKind i hi))
        (fun _ => true) 0 ∈ NonCrossingCF w := by
  apply Submonoid.subset_closure
  refine ⟨1, pairCircuit hw (staircasePreds i hi) tgtKind,
    pairCylinder hw (staircasePreds i hi) tgtKind (adjPairCylinder hw tgtKind i hi),
    0, (fun _ => true),
    pairCircuit_hmvNormal hw (staircasePreds i hi) tgtKind h_comp (staircasePreds_len i hi),
    pairCircuit_totalWidth hw (staircasePreds i hi) tgtKind, ?_,
    pairCircuit_constantFreeLayer hw (staircasePreds i hi) tgtKind h_comp
      (staircasePreds_nonempty i hi), rfl⟩
  change (pair_tgtListing hw (staircasePreds i hi) tgtKind).entries.length = w
  simp [pair_tgtListing]

end AdjPair

end Internal

end AllenderOQ3
