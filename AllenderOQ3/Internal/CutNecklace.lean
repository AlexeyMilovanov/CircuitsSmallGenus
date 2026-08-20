import AllenderOQ3.Internal.DedupRotation

set_option autoImplicit false

/-!
# The transition necklace of a rotation

For a properly layered circuit with a rotation, the face permutation induces a
successor structure on the darts crossing a fixed transition (the *cut darts*):
follow the face boundary from a cut dart until it crosses the cut again (a
first-return map), then reverse the crossing dart.  Under proper layering this
*necklace permutation* preserves upward crossings, so it acts on the transition
arcs themselves.  The necklace word of a transition is the orbit of a canonical
arc under this permutation.

Everything up to and including `necklaceWord_nodup` and the layer listings is
proved without any planarity hypothesis.  The three remaining obligations —
completeness of the word (the single-necklace theorem) and the two grouping
statements — are exactly the genus-zero content of Hansen's Theorem 2 and are
stated with their full hypotheses (proper layering, a genus-zero rotation and
unique graph source and sink).
-/

namespace AllenderOQ3.Internal

variable {n : Nat} {c : ADRCircuit n}

/-! ## Cut darts -/

/-- A cut dart at layer `ell` is a dart whose endpoints are at layers `ell` and
`ell + 1`. -/
def isCutDart (c : ADRCircuit n) (ell : Nat) (d : CircuitDart c) : Bool :=
  min (c.layer d.source) (c.layer d.target) == ell

abbrev CutDart (c : ADRCircuit n) (ell : Nat) :=
  { d : CircuitDart c // isCutDart c ell d = true }

def cutDartReverse (c : ADRCircuit n) (ell : Nat) :
    CutDart c ell ≃ CutDart c ell where
  toFun d :=
    ⟨dartReverse c d.1, by
      have hd := d.2
      dsimp [isCutDart, dartReverse] at hd ⊢
      rw [min_comm]
      exact hd⟩
  invFun d :=
    ⟨dartReverse c d.1, by
      have hd := d.2
      dsimp [isCutDart, dartReverse] at hd ⊢
      rw [min_comm]
      exact hd⟩
  left_inv d := by
    apply Subtype.ext
    exact (dartReverse c).left_inv d.1
  right_inv d := by
    apply Subtype.ext
    exact (dartReverse c).right_inv d.1

/-- In a properly layered circuit every dart moves between adjacent layers. -/
theorem dart_layer_cases (hpl : ProperLayered c) (d : CircuitDart c) :
    c.layer d.target = c.layer d.source + 1 ∨
      c.layer d.source = c.layer d.target + 1 := by
  rcases d.property.1 with he | he
  · exact Or.inl (hpl _ _ he).symm
  · exact Or.inr (hpl _ _ he).symm

/-! ## First-return machinery -/

theorem exists_firstReturn {α : Type} [Finite α] (p : Equiv.Perm α)
    (S : α → Prop) (x : { a // S a }) :
    ∃ k ≥ 1, S ((p ^ k) x.1) := by
  refine ⟨orderOf p, orderOf_pos p, ?_⟩
  have h : (p ^ orderOf p) x.1 = x.1 := by
    rw [pow_orderOf_eq_one p]
    rfl
  rw [h]
  exact x.2

noncomputable def firstReturnTime {α : Type} [Fintype α] (p : Equiv.Perm α)
    (S : α → Prop) [DecidablePred S] (x : { a // S a }) : Nat :=
  Nat.find (exists_firstReturn p S x)

theorem firstReturnTime_pos {α : Type} [Fintype α] (p : Equiv.Perm α)
    (S : α → Prop) [DecidablePred S] (x : { a // S a }) :
    1 ≤ firstReturnTime p S x :=
  (Nat.find_spec (exists_firstReturn p S x)).1

theorem firstReturnTime_mem {α : Type} [Fintype α] (p : Equiv.Perm α)
    (S : α → Prop) [DecidablePred S] (x : { a // S a }) :
    S ((p ^ firstReturnTime p S x) x.1) :=
  (Nat.find_spec (exists_firstReturn p S x)).2

theorem firstReturnTime_not_mem {α : Type} [Fintype α] (p : Equiv.Perm α)
    (S : α → Prop) [DecidablePred S] (x : { a // S a })
    {j : Nat} (h1 : 1 ≤ j) (hj : j < firstReturnTime p S x) :
    ¬ S ((p ^ j) x.1) := by
  have h := Nat.find_min (exists_firstReturn p S x) hj
  intro hS
  exact h ⟨h1, hS⟩

noncomputable def firstReturnMap {α : Type} [Fintype α] (p : Equiv.Perm α)
    (S : α → Prop) [DecidablePred S] : { a // S a } → { a // S a } :=
  fun x => ⟨(p ^ firstReturnTime p S x) x.1, firstReturnTime_mem p S x⟩

theorem firstReturnMap_injective {α : Type} [Fintype α] (p : Equiv.Perm α)
    (S : α → Prop) [DecidablePred S] : Function.Injective (firstReturnMap p S) := by
  intro ⟨x, hx⟩ ⟨y, hy⟩ hxy
  dsimp [firstReturnMap] at hxy
  have heq : (p ^ firstReturnTime p S ⟨x, hx⟩) x
      = (p ^ firstReturnTime p S ⟨y, hy⟩) y := Subtype.mk.inj hxy
  set tx := firstReturnTime p S ⟨x, hx⟩ with htxdef
  set ty := firstReturnTime p S ⟨y, hy⟩ with htydef
  have htx : 1 ≤ tx := firstReturnTime_pos p S ⟨x, hx⟩
  have hty : 1 ≤ ty := firstReturnTime_pos p S ⟨y, hy⟩
  rcases lt_trichotomy tx ty with h | h | h
  · exfalso
    have h2 : p ^ ty = p ^ tx * p ^ (ty - tx) := by
      rw [← pow_add]
      congr 1
      omega
    have h3 : (p ^ ty) y = (p ^ tx) ((p ^ (ty - tx)) y) := by
      rw [h2, Equiv.Perm.mul_apply]
    rw [h3] at heq
    have h4 : x = (p ^ (ty - tx)) y := (p ^ tx).injective heq
    have h5 : S ((p ^ (ty - tx)) y) := h4 ▸ hx
    exact firstReturnTime_not_mem p S ⟨y, hy⟩ (by omega)
      (by omega : ty - tx < ty) h5
  · apply Subtype.ext
    rw [h] at heq
    exact (p ^ ty).injective heq
  · exfalso
    have h2 : p ^ tx = p ^ ty * p ^ (tx - ty) := by
      rw [← pow_add]
      congr 1
      omega
    have h3 : (p ^ tx) x = (p ^ ty) ((p ^ (tx - ty)) x) := by
      rw [h2, Equiv.Perm.mul_apply]
    rw [h3] at heq
    have h4 : y = (p ^ (tx - ty)) x := (p ^ ty).injective heq.symm
    have h5 : S ((p ^ (tx - ty)) x) := h4 ▸ hy
    exact firstReturnTime_not_mem p S ⟨x, hx⟩ (by omega)
      (by omega : tx - ty < tx) h5

noncomputable def firstReturnPerm {α : Type} [Fintype α] (p : Equiv.Perm α)
    (S : α → Prop) [DecidablePred S] : Equiv.Perm { a // S a } :=
  Equiv.ofBijective (firstReturnMap p S)
    ((Finite.injective_iff_bijective).mp (firstReturnMap_injective p S))

/-- The first-return map of the face permutation on the set of cut darts. -/
noncomputable def firstReturn (r : OrientableRotation c) (ell : Nat) :
    Equiv.Perm (CutDart c ell) :=
  firstReturnPerm (facePermutation r) (fun d => isCutDart c ell d = true)

theorem firstReturn_val (r : OrientableRotation c) (ell : Nat)
    (d0 : CutDart c ell) :
    ((firstReturn r ell) d0).1
      = (facePermutation r
          ^ firstReturnTime (facePermutation r)
              (fun d => isCutDart c ell d = true) d0) d0.1 := rfl

/-! ## The alternation lemma: the walk between crossings stays above -/

theorem facePermutation_source (r : OrientableRotation c) (d : CircuitDart c) :
    (facePermutation r d).source = d.target := by
  have h := r.preservesSource ((dartReverse c) d)
  dsimp [facePermutation] at h ⊢
  rw [h]
  rfl

/-- After an upward crossing, the face walk keeps its source strictly above the
cut until it crosses again. -/
theorem walk_source_above (hpl : ProperLayered c) (r : OrientableRotation c)
    {ell : Nat} (d0 : CircuitDart c) (h0 : c.layer d0.target = ell + 1) :
    ∀ k, 1 ≤ k →
      (∀ j, 1 ≤ j → j < k →
        isCutDart c ell ((facePermutation r ^ j) d0) = false) →
      ell + 1 ≤ c.layer ((facePermutation r ^ k) d0).source := by
  intro k
  induction k with
  | zero => intro h; exact absurd h (by omega)
  | succ m ih =>
    intro _ hnc
    by_cases hm : m = 0
    · subst hm
      have h1 : (facePermutation r ^ 1) d0 = facePermutation r d0 := by
        rw [pow_one]
      rw [h1, facePermutation_source r d0, h0]
    · have hm1 : 1 ≤ m := by omega
      have ihm := ih hm1 (fun j hj hjm => hnc j hj (by omega))
      have hncm : isCutDart c ell ((facePermutation r ^ m) d0) = false :=
        hnc m hm1 (by omega)
      have hmin :
          ¬ min (c.layer ((facePermutation r ^ m) d0).source)
              (c.layer ((facePermutation r ^ m) d0).target) = ell := by
        intro heq
        rw [isCutDart, heq] at hncm
        simp at hncm
      have htgt : ell + 1 ≤ c.layer ((facePermutation r ^ m) d0).target := by
        rcases dart_layer_cases hpl ((facePermutation r ^ m) d0) with h | h
        · omega
        · omega
      have hstep : (facePermutation r ^ (m + 1)) d0
          = facePermutation r ((facePermutation r ^ m) d0) := by
        rw [pow_succ', Equiv.Perm.mul_apply]
      rw [hstep, facePermutation_source]
      exact htgt

/-- The first return of an upward cut dart is a downward cut dart. -/
theorem firstReturn_down (hpl : ProperLayered c) (r : OrientableRotation c)
    {ell : Nat} (d0 : CutDart c ell) (hup : c.layer d0.1.source = ell) :
    c.layer ((firstReturn r ell) d0).1.source = ell + 1 ∧
      c.layer ((firstReturn r ell) d0).1.target = ell := by
  have hcut0 : min (c.layer d0.1.source) (c.layer d0.1.target) = ell := by
    have h := d0.2
    rwa [isCutDart, beq_iff_eq] at h
  have h0 : c.layer d0.1.target = ell + 1 := by
    rcases dart_layer_cases hpl d0.1 with h | h
    · omega
    · omega
  set T := firstReturnTime (facePermutation r)
    (fun d => isCutDart c ell d = true) d0 with hTdef
  have hT1 : 1 ≤ T := firstReturnTime_pos _ _ d0
  have hmem : isCutDart c ell ((facePermutation r ^ T) d0.1) = true :=
    firstReturnTime_mem (facePermutation r) _ d0
  have hmemmin :
      min (c.layer ((facePermutation r ^ T) d0.1).source)
        (c.layer ((facePermutation r ^ T) d0.1).target) = ell := by
    rwa [isCutDart, beq_iff_eq] at hmem
  have habove : ell + 1 ≤ c.layer ((facePermutation r ^ T) d0.1).source := by
    refine walk_source_above hpl r d0.1 h0 T hT1 (fun j hj hjT => ?_)
    have h := firstReturnTime_not_mem (facePermutation r)
      (fun d => isCutDart c ell d = true) d0 hj hjT
    exact Bool.eq_false_iff.mpr h
  have hval : ((firstReturn r ell) d0).1 = (facePermutation r ^ T) d0.1 :=
    firstReturn_val r ell d0
  rw [hval]
  rcases dart_layer_cases hpl ((facePermutation r ^ T) d0.1) with h | h
  · omega
  · omega

/-- After a downward crossing, the face walk keeps its source at or below the
cut until it crosses again. -/
theorem walk_source_below (hpl : ProperLayered c) (r : OrientableRotation c)
    {ell : Nat} (d0 : CircuitDart c) (h0 : c.layer d0.target = ell) :
    ∀ k, 1 ≤ k →
      (∀ j, 1 ≤ j → j < k →
        isCutDart c ell ((facePermutation r ^ j) d0) = false) →
      c.layer ((facePermutation r ^ k) d0).source ≤ ell := by
  intro k
  induction k with
  | zero => intro h; exact absurd h (by omega)
  | succ m ih =>
    intro _ hnc
    by_cases hm : m = 0
    · subst hm
      have h1 : (facePermutation r ^ 1) d0 = facePermutation r d0 := by
        rw [pow_one]
      rw [h1, facePermutation_source r d0, h0]
    · have hm1 : 1 ≤ m := by omega
      have ihm := ih hm1 (fun j hj hjm => hnc j hj (by omega))
      have hncm : isCutDart c ell ((facePermutation r ^ m) d0) = false :=
        hnc m hm1 (by omega)
      have hmin :
          ¬ min (c.layer ((facePermutation r ^ m) d0).source)
              (c.layer ((facePermutation r ^ m) d0).target) = ell := by
        intro heq
        rw [isCutDart, heq] at hncm
        simp at hncm
      have htgt : c.layer ((facePermutation r ^ m) d0).target ≤ ell := by
        rcases dart_layer_cases hpl ((facePermutation r ^ m) d0) with h | h
        · omega
        · omega
      have hstep : (facePermutation r ^ (m + 1)) d0
          = facePermutation r ((facePermutation r ^ m) d0) := by
        rw [pow_succ', Equiv.Perm.mul_apply]
      rw [hstep, facePermutation_source]
      exact htgt

/-- The first return of a downward cut dart is an upward cut dart. -/
theorem firstReturn_up (hpl : ProperLayered c) (r : OrientableRotation c)
    {ell : Nat} (d0 : CutDart c ell) (hdown : c.layer d0.1.source = ell + 1) :
    c.layer ((firstReturn r ell) d0).1.source = ell ∧
      c.layer ((firstReturn r ell) d0).1.target = ell + 1 := by
  have hcut0 : min (c.layer d0.1.source) (c.layer d0.1.target) = ell := by
    have h := d0.2
    rwa [isCutDart, beq_iff_eq] at h
  have h0 : c.layer d0.1.target = ell := by
    rcases dart_layer_cases hpl d0.1 with h | h
    · omega
    · omega
  set T := firstReturnTime (facePermutation r)
    (fun d => isCutDart c ell d = true) d0 with hTdef
  have hT1 : 1 ≤ T := firstReturnTime_pos _ _ d0
  have hmem : isCutDart c ell ((facePermutation r ^ T) d0.1) = true :=
    firstReturnTime_mem (facePermutation r) _ d0
  have hmemmin :
      min (c.layer ((facePermutation r ^ T) d0.1).source)
        (c.layer ((facePermutation r ^ T) d0.1).target) = ell := by
    rwa [isCutDart, beq_iff_eq] at hmem
  have hbelow : c.layer ((facePermutation r ^ T) d0.1).source ≤ ell := by
    refine walk_source_below hpl r d0.1 h0 T hT1 (fun j hj hjT => ?_)
    have h := firstReturnTime_not_mem (facePermutation r)
      (fun d => isCutDart c ell d = true) d0 hj hjT
    exact Bool.eq_false_iff.mpr h
  have hval : ((firstReturn r ell) d0).1 = (facePermutation r ^ T) d0.1 :=
    firstReturn_val r ell d0
  rw [hval]
  rcases dart_layer_cases hpl ((facePermutation r ^ T) d0.1) with h | h
  · omega
  · omega

/-! ## The necklace permutation and the transition arcs -/

/-- Cross the cut along a face and reverse: the necklace permutation of the cut
darts.  Defined for every rotation; proper layering makes it preserve upward
crossings. -/
noncomputable def neckPerm (r : OrientableRotation c) (ell : Nat) :
    Equiv.Perm (CutDart c ell) :=
  (firstReturn r ell).trans (cutDartReverse c ell)

theorem neckPerm_up (hpl : ProperLayered c) (r : OrientableRotation c)
    {ell : Nat} (d0 : CutDart c ell) (hup : c.layer d0.1.source = ell) :
    c.layer ((neckPerm r ell) d0).1.source = ell ∧
      c.layer ((neckPerm r ell) d0).1.target = ell + 1 := by
  have hdown := firstReturn_down hpl r d0 hup
  have hsrc : ((neckPerm r ell) d0).1.source
      = ((firstReturn r ell) d0).1.target := rfl
  have htgt : ((neckPerm r ell) d0).1.target
      = ((firstReturn r ell) d0).1.source := rfl
  rw [hsrc, htgt]
  exact ⟨hdown.2, hdown.1⟩

/-- The necklace permutation also preserves downward crossings. -/
theorem neckPerm_down (hpl : ProperLayered c) (r : OrientableRotation c)
    {ell : Nat} (d0 : CutDart c ell) (hdown : c.layer d0.1.source = ell + 1) :
    c.layer ((neckPerm r ell) d0).1.source = ell + 1 ∧
      c.layer ((neckPerm r ell) d0).1.target = ell := by
  have hup := firstReturn_up hpl r d0 hdown
  have hsrc : ((neckPerm r ell) d0).1.source
      = ((firstReturn r ell) d0).1.target := rfl
  have htgt : ((neckPerm r ell) d0).1.target
      = ((firstReturn r ell) d0).1.source := rfl
  rw [hsrc, htgt]
  exact ⟨hup.2, hup.1⟩

/-- The upward cut dart of a transition arc. -/
def upOfArc {ell : Nat} (e : TransitionArc c ell) : CutDart c ell :=
  ⟨⟨e.1, Or.inl e.2.1, by
      intro h
      have h1 := e.2.2.1
      have h2 := e.2.2.2
      rw [h] at h1
      omega⟩, by
    have h1 := e.2.2.1
    have h2 := e.2.2.2
    rw [isCutDart, beq_iff_eq]
    dsimp [CircuitDart.source, CircuitDart.target]
    omega⟩

theorem upOfArc_source {ell : Nat} (e : TransitionArc c ell) :
    c.layer (upOfArc e).1.source = ell := e.2.2.1

/-- The transition arc of an upward cut dart. -/
def arcOfUpDart (hpl : ProperLayered c) {ell : Nat} (d : CutDart c ell)
    (hup : c.layer d.1.source = ell) : TransitionArc c ell :=
  ⟨d.1.1, by
    have hcut : min (c.layer d.1.source) (c.layer d.1.target) = ell := by
      have h := d.2
      rwa [isCutDart, beq_iff_eq] at h
    dsimp [CircuitDart.source, CircuitDart.target] at hcut hup
    rcases d.1.property.1 with he | he
    · refine ⟨he, hup, ?_⟩
      have := hpl _ _ he
      omega
    · exfalso
      have := hpl _ _ he
      omega⟩

theorem arcOfUpDart_val (hpl : ProperLayered c) {ell : Nat} (d : CutDart c ell)
    (hup : c.layer d.1.source = ell) :
    (arcOfUpDart hpl d hup).1 = d.1.1 := rfl

/-- One necklace step on transition arcs. -/
noncomputable def arcNext (hpl : ProperLayered c) (r : OrientableRotation c)
    {ell : Nat} (e : TransitionArc c ell) : TransitionArc c ell :=
  arcOfUpDart hpl ((neckPerm r ell) (upOfArc e))
    (neckPerm_up hpl r (upOfArc e) (upOfArc_source e)).1

theorem arcNext_injective (hpl : ProperLayered c) (r : OrientableRotation c)
    (ell : Nat) : Function.Injective (arcNext hpl r (ell := ell)) := by
  intro e1 e2 h
  have hval1 : (arcNext hpl r e1).1 = (arcNext hpl r e2).1 :=
    congrArg Subtype.val h
  have hpair : ((neckPerm r ell) (upOfArc e1)).1.1
      = ((neckPerm r ell) (upOfArc e2)).1.1 := hval1
  have hup : upOfArc e1 = upOfArc e2 :=
    (neckPerm r ell).injective (Subtype.ext (Subtype.ext hpair))
  have hval : e1.1 = e2.1 := congrArg (fun d : CutDart c ell => d.1.1) hup
  exact Subtype.ext hval

/-- The necklace permutation of the transition arcs. -/
noncomputable def arcPerm (hpl : ProperLayered c) (r : OrientableRotation c)
    (ell : Nat) : Equiv.Perm (TransitionArc c ell) :=
  Equiv.ofBijective (arcNext hpl r)
    ((Finite.injective_iff_bijective).mp (arcNext_injective hpl r ell))

/-! ## Orbit words -/

section OrbitList

variable {α : Type} [Fintype α] [DecidableEq α]

/-- The length of the orbit of `a0` under `q`, as a first-return time. -/
noncomputable def orbitPeriod (q : Equiv.Perm α) (a0 : α) : Nat :=
  firstReturnTime q (fun a => a = a0) ⟨a0, rfl⟩

theorem orbitPeriod_pos (q : Equiv.Perm α) (a0 : α) : 1 ≤ orbitPeriod q a0 :=
  firstReturnTime_pos q (fun a => a = a0) ⟨a0, rfl⟩

theorem orbitPeriod_return (q : Equiv.Perm α) (a0 : α) :
    (q ^ orbitPeriod q a0) a0 = a0 :=
  firstReturnTime_mem q (fun a => a = a0) ⟨a0, rfl⟩

/-- The orbit of `a0` under `q`, listed from `a0`. -/
noncomputable def orbitList (q : Equiv.Perm α) (a0 : α) : List α :=
  (List.range (orbitPeriod q a0)).map (fun k => (q ^ k) a0)

theorem orbitList_pow_injective (q : Equiv.Perm α) (a0 : α) {i j : Nat}
    (hi : i < orbitPeriod q a0) (hj : j < orbitPeriod q a0)
    (h : (q ^ i) a0 = (q ^ j) a0) : i = j := by
  rcases lt_trichotomy i j with hij | hij | hij
  · exfalso
    have h2 : q ^ j = q ^ i * q ^ (j - i) := by
      rw [← pow_add]
      congr 1
      omega
    have h3 : (q ^ j) a0 = (q ^ i) ((q ^ (j - i)) a0) := by
      rw [h2, Equiv.Perm.mul_apply]
    rw [h3] at h
    have h4 : (q ^ (j - i)) a0 = a0 := ((q ^ i).injective h).symm
    exact firstReturnTime_not_mem q (fun a => a = a0) ⟨a0, rfl⟩
      (by omega) (by omega : j - i < orbitPeriod q a0) h4
  · exact hij
  · exfalso
    have h2 : q ^ i = q ^ j * q ^ (i - j) := by
      rw [← pow_add]
      congr 1
      omega
    have h3 : (q ^ i) a0 = (q ^ j) ((q ^ (i - j)) a0) := by
      rw [h2, Equiv.Perm.mul_apply]
    rw [h3] at h
    have h4 : (q ^ (i - j)) a0 = a0 := (q ^ j).injective h
    exact firstReturnTime_not_mem q (fun a => a = a0) ⟨a0, rfl⟩
      (by omega) (by omega : i - j < orbitPeriod q a0) h4

theorem orbitList_nodup (q : Equiv.Perm α) (a0 : α) : (orbitList q a0).Nodup := by
  refine List.Nodup.map_on ?_ (List.nodup_range)
  intro i hi j hj hij
  rw [List.mem_range] at hi hj
  exact orbitList_pow_injective q a0 hi hj hij

theorem self_mem_orbitList (q : Equiv.Perm α) (a0 : α) : a0 ∈ orbitList q a0 := by
  rw [orbitList, List.mem_map]
  refine ⟨0, ?_, by simp⟩
  rw [List.mem_range]
  exact orbitPeriod_pos q a0

theorem orbitList_closed (q : Equiv.Perm α) (a0 : α) {b : α}
    (hb : b ∈ orbitList q a0) : q b ∈ orbitList q a0 := by
  rw [orbitList, List.mem_map] at hb
  obtain ⟨k, hk, hkb⟩ := hb
  rw [List.mem_range] at hk
  by_cases hlast : k + 1 = orbitPeriod q a0
  · have : q b = a0 := by
      rw [← hkb, ← Equiv.Perm.mul_apply, ← pow_succ', hlast]
      exact orbitPeriod_return q a0
    rw [this]
    exact self_mem_orbitList q a0
  · rw [orbitList, List.mem_map]
    refine ⟨k + 1, ?_, ?_⟩
    · rw [List.mem_range]
      omega
    · rw [← hkb, ← Equiv.Perm.mul_apply, ← pow_succ']

theorem pow_mem_orbitList (q : Equiv.Perm α) (a0 : α) (k : Nat) :
    (q ^ k) a0 ∈ orbitList q a0 := by
  induction k with
  | zero =>
    have h : (q ^ 0) a0 = a0 := by rw [pow_zero]; rfl
    rw [h]
    exact self_mem_orbitList q a0
  | succ m ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    exact orbitList_closed q a0 ih

theorem mem_orbitList_iff_pow (q : Equiv.Perm α) (a0 : α) (b : α) :
    b ∈ orbitList q a0 ↔ ∃ k : Nat, (q ^ k) a0 = b := by
  constructor
  · intro hb
    rw [orbitList, List.mem_map] at hb
    obtain ⟨k, _, hkb⟩ := hb
    exact ⟨k, hkb⟩
  · rintro ⟨k, rfl⟩
    exact pow_mem_orbitList q a0 k

end OrbitList

/-! ## The necklace word and layer listings -/

open Classical in
/-- The necklace word of transition `ell`: the orbit of a canonical arc under
the necklace permutation (empty when the transition has no arcs). -/
noncomputable def necklaceWord (hpl : ProperLayered c) (r : OrientableRotation c)
    (ell : Nat) : List (TransitionArc c ell) :=
  if h : Nonempty (TransitionArc c ell) then
    orbitList (arcPerm hpl r ell) h.some
  else []

theorem necklaceWord_nodup (hpl : ProperLayered c) (r : OrientableRotation c)
    (ell : Nat) : (necklaceWord hpl r ell).Nodup := by
  unfold necklaceWord
  split
  · exact orbitList_nodup _ _
  · exact List.nodup_nil

/-- Membership in the necklace word is exactly membership in the orbit of the
canonical arc.  This reduces `necklaceWord_complete` to the single-orbit
statement for `arcPerm`. -/
theorem mem_necklaceWord_iff (hpl : ProperLayered c) (r : OrientableRotation c)
    {ell : Nat} (h : Nonempty (TransitionArc c ell)) (e : TransitionArc c ell) :
    e ∈ necklaceWord hpl r ell ↔
      ∃ k : Nat, ((arcPerm hpl r ell) ^ k) h.some = e := by
  unfold necklaceWord
  rw [dif_pos h]
  exact mem_orbitList_iff_pow (arcPerm hpl r ell) h.some e

/-- The single-orbit form of the completeness obligation: to prove
`necklaceWord_complete` it suffices that every transition arc is a power of
the necklace permutation applied to the canonical arc. -/
theorem necklaceWord_complete_of_single_orbit (hpl : ProperLayered c)
    (r : OrientableRotation c) {ell : Nat}
    (horb : ∀ (h : Nonempty (TransitionArc c ell)) (e : TransitionArc c ell),
      ∃ k : Nat, ((arcPerm hpl r ell) ^ k) h.some = e) :
    ∀ e : TransitionArc c ell, e ∈ necklaceWord hpl r ell := by
  intro e
  have h : Nonempty (TransitionArc c ell) := ⟨e⟩
  exact (mem_necklaceWord_iff hpl r h e).mpr (horb h e)

section Listing

variable {β : Type} [Fintype β] [DecidableEq β]

/-- Extend a prefix to a full cyclic listing of a finite type. -/
noncomputable def listingOfPrefix (pref : List β) : CyclicListing β where
  entries :=
    pref.dedup ++ (cyclicListingOfFintype β).entries.filter
      (fun b => decide (b ∉ pref.dedup))
  nodup := by
    refine List.Nodup.append (List.nodup_dedup pref)
      (((cyclicListingOfFintype β).nodup).filter _) ?_
    intro a ha hafil
    have h := (List.mem_filter.mp hafil).2
    rw [decide_eq_true_eq] at h
    exact h ha
  complete := by
    intro b
    by_cases hb : b ∈ pref.dedup
    · exact List.mem_append.mpr (Or.inl hb)
    · refine List.mem_append.mpr (Or.inr (List.mem_filter.mpr
        ⟨(cyclicListingOfFintype β).complete b, ?_⟩))
      rw [decide_eq_true_eq]
      exact hb

/-- A word whose key-fibres are contiguous is grouped along the cyclic listing
generated from its own key word: the fibres appear as the blocks of the
deduplicated key word, and the vertices carrying no letter get empty blocks at
the end. -/
theorem groupedAlong_listingOfPrefix_of_contiguous {alpha : Type}
    (key : alpha → β) (w : List alpha) (hc : KeyContiguous key w) :
    GroupedAlong key (listingOfPrefix (w.map key)).entries w := by
  refine groupedAlong_append_unused key _ _ w
    (groupedAlong_dedup_of_contiguous key w.length w le_rfl hc) ?_
  intro e he a ha hkey
  have h := (List.mem_filter.mp he).2
  rw [decide_eq_true_eq] at h
  exact h (by rw [← hkey]; exact List.mem_dedup.mpr (List.mem_map_of_mem ha))

/-- **Rotation-tolerant form of the previous lemma.**  If the key-fibres of `w`
are contiguous only after a cyclic rotation, then a matching cyclic rotation of
the listing generated from `w` groups that rotated word.  The rotation of the
listing is forced: the block order of a rotated word is the rotated block
order (`cyclicRotation_dedup_of_contiguous`), and the vertices carrying no
letter are inserted between the two halves. -/
theorem groupedAlong_listingOfPrefix_of_cyclicContiguous {alpha : Type}
    (key : alpha → β) (w : List alpha) (hc : CyclicContiguous key w) :
    ∃ (ls : List β) (v : List alpha),
      CyclicRotation (listingOfPrefix (w.map key)).entries ls ∧
      CyclicRotation w v ∧ GroupedAlong key ls v := by
  obtain ⟨w', ⟨p, q, hw, hw'⟩, hcont⟩ := hc
  classical
  set P : List β := p.map key with hP
  set Q : List β := q.map key with hQ
  have hmapw : w.map key = P ++ Q := by rw [hw, List.map_append]
  have hmapw' : w'.map key = Q ++ P := by rw [hw', List.map_append]
  have hcontig : SelfContiguous (Q ++ P) := by
    rw [← hmapw']
    exact selfContiguous_map key w' hcont
  set A : List β := (P.filter (fun x => decide (x ∉ Q))).dedup with hA
  set B : List β := Q.dedup with hB
  have hD1 : (w.map key).dedup = A ++ B := by
    rw [hmapw]; exact dedup_append_filter P Q
  have hD2 : (w'.map key).dedup = B ++ A := by
    rw [hmapw']; exact dedup_append_of_contiguous Q P hcontig
  set T : List β := (cyclicListingOfFintype β).entries.filter
    (fun b => decide (b ∉ (w.map key).dedup)) with hT
  refine ⟨B ++ T ++ A, w', ⟨A, B ++ T, ?_, ?_⟩, ⟨p, q, hw, hw'⟩, ?_⟩
  · change (w.map key).dedup ++ T = A ++ (B ++ T)
    rw [hD1, List.append_assoc]
  · rw [List.append_assoc]
  · have hbase : GroupedAlong key (B ++ A) w' := by
      rw [← hD2]
      exact groupedAlong_dedup_of_contiguous key w'.length w' le_rfl hcont
    have hunused : ∀ e ∈ T, ∀ a ∈ w', key a ≠ e := by
      intro e he a ha hkey
      have hnot := (List.mem_filter.mp he).2
      rw [decide_eq_true_eq] at hnot
      refine hnot ?_
      rw [← hkey]
      refine List.mem_dedup.mpr (List.mem_map_of_mem ?_)
      have : a ∈ q ++ p := by rw [← hw']; exact ha
      rw [hw]
      rcases List.mem_append.mp this with h | h
      · exact List.mem_append_right _ h
      · exact List.mem_append_left _ h
    exact groupedAlong_insert_unused_list key w' T B A hbase hunused

end Listing

/-- Cyclic layer listings induced by the necklace words: layer `ell + 1` is
ordered by the first occurrence of the incoming arcs on the necklace of
transition `ell`; the bottom listing is ordered by outgoing arcs. -/
noncomputable def necklaceLayerOrder (hpl : ProperLayered c)
    (r : OrientableRotation c) : ∀ ell : Nat, CyclicListing (LayerVertex c ell)
  | 0 => listingOfPrefix ((necklaceWord hpl r 0).map arcSource)
  | (m + 1) => listingOfPrefix ((necklaceWord hpl r m).map arcTarget)

/-- Definitional unfolding of the target-side layer listing: layer `m + 1` is
listed by the first occurrence of the incoming arcs of transition `m`.  This is
the coherence that makes the target grouping obligation follow directly from
contiguity of the incoming fibres of the necklace word. -/
theorem necklaceLayerOrder_succ (hpl : ProperLayered c)
    (r : OrientableRotation c) (m : Nat) :
    necklaceLayerOrder hpl r (m + 1)
      = listingOfPrefix ((necklaceWord hpl r m).map arcTarget) := rfl

/-- Definitional unfolding of the bottom layer listing: layer `0` is listed by
the first occurrence of the outgoing arcs of transition `0`.  This makes the
source grouping obligation at `ell = 0` follow directly from contiguity of the
outgoing fibres, with no cross-layer coherence involved. -/
theorem necklaceLayerOrder_zero (hpl : ProperLayered c)
    (r : OrientableRotation c) :
    necklaceLayerOrder hpl r 0
      = listingOfPrefix ((necklaceWord hpl r 0).map arcSource) := rfl

/-! ## The genus-zero obligations

The three statements below are the geometric content of Hansen's Theorem 2:
for a genus-zero rotation of a properly layered graph with unique source and
sink, the necklace of every transition is a single cycle whose source and
target fibers are contiguous, coherently with the induced layer listings. -/

/-
**The completeness obligation** has moved to
`AllenderOQ3/Internal/NecklaceGrouping.lean`, downstream of the single-orbit
base case `necklaceWord_complete_base` of `FirstReturnChain`.  Its statement is
unchanged:

theorem necklaceWord_complete ... (ell : Nat) (e : TransitionArc c ell) :
    e ∈ necklaceWord hpl r ell

The case where layer `ell` carries the graph source is now proved there; only
the remaining layers are open, isolated as `necklaceWord_complete_off_source`.
-/

/-
**Corrected form of the two grouping obligations.**  The two statements below
were originally asked for on the nose, i.e. as

theorem necklace_groupedAlong_source ... :
    GroupedAlong arcSource (necklaceLayerOrder hpl r ell).entries
      (necklaceWord hpl r ell)

theorem necklace_groupedAlong_target ... :
    GroupedAlong arcTarget (necklaceLayerOrder hpl r (ell + 1)).entries
      (necklaceWord hpl r ell)

Together with `necklaceWord_complete` this asks for *one* word per transition
that is grouped along the source listing and along the target listing
simultaneously.  That is impossible in general: by
`not_doubleGrouped_crossing_four`
(`AllenderOQ3/Internal/DoubleGroupingObstruction.lean`) a transition whose
source fibres and target fibres interleave admits no such word, and a planar
`K_{2,2}` transition -- two sources, two targets, all four arcs, embedded with
arc cycle `u₁v₂, u₁v₁, u₂v₁, u₂v₂` -- interleaves: its source fibres are
`{a,b}, {c,d}` while its target fibres are `{b,c}, {a,d}`.  So the pair of
non-rotated obligations is jointly unsatisfiable.

The frozen certificate field `ArcOrderCertificate.commonArcWord` only requires
the source-major and target-major words to agree up to a `CyclicRotation`, and
that slack is exactly what the interleaved case needs (rotating `a b c d` to
`b c d a` groups the targets).  The obligations are therefore stated below in
the rotation-tolerant form consumed by `incidenceCylinder_of_rotatedWords`;
they still yield the frozen `HansenArcOrderPrinciple` unchanged, and each is
implied by the corresponding original statement.
-/

/-
**The source grouping obligation** has moved to
`AllenderOQ3/Internal/NecklaceGrouping.lean`, where the outgoing-fibre
contiguity leaf `necklace_arcSource_cyclicContiguous` is available.  Its
statement is unchanged:

theorem necklace_groupedAlong_source ... (ell : Nat) :
    ∃ (sourceList : List (LayerVertex c ell))
      (wordS : List (TransitionArc c ell)),
      CyclicRotation (necklaceLayerOrder hpl r ell).entries sourceList ∧
      CyclicRotation (necklaceWord hpl r ell) wordS ∧
      GroupedAlong arcSource sourceList wordS

The case `ell = 0` is now proved there; only the cross-layer case `ell = m + 1`
remains open, isolated as `necklace_groupedAlong_source_succ`.
-/

/-
**Superseded leaf, kept for the audit trail.**  The target obligation was
previously reduced to the *on the nose* contiguity statement

theorem necklace_arcTarget_contiguous ... :
    KeyContiguous arcTarget (necklaceWord hpl r ell)

That statement cannot be proved: `necklaceWord` is the orbit list of the
arbitrary `Classical`-chosen arc `h.some`, and nothing pins that arc to the
first position of its target block, so the block through `h.some` generally
wraps around the end of the list.  The correct leaf is the cyclic form
`necklace_arcTarget_cyclicContiguous`, and it is all that the target grouping
consumes.

Both that leaf -- now **proved** -- and the target grouping obligation it
discharges live in `AllenderOQ3/Internal/NecklaceGrouping.lean`, downstream of
the max-corner necklace step of `FirstReturnChain` and the per-vertex corner
count of `VertexCorner`.
-/

end AllenderOQ3.Internal
