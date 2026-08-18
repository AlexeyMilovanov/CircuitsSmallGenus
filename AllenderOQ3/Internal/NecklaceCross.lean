import AllenderOQ3.Internal.NecklaceGrouping

set_option autoImplicit false

/-!
# Cross-layer coherence of the transition necklaces

The two remaining genus-zero obligations of `CutNecklace` — completeness of the
necklace word (the single-necklace theorem) and the source grouping obligation
above the bottom layer — both follow from one purely local statement about the
rotation at a vertex, proved here as `exit_agree`.

Fix a transition arc `e` of transition `ell` whose necklace successor has a
different target, i.e. `e` is the *exit* of its target fibre.  Then the
rotation successor of the descending dart of `e` is an ascending dart at the
same vertex `v = arcTarget e`, hence the ascending dart of a transition arc `f`
of transition `ell + 1` with `arcSource f = v`; and `f` is the exit of its own
source fibre.  The face walk that computes the necklace step of `e` runs
through the face walk that computes the necklace step of `f`, so the two steps
land on one and the same vertex of layer `ell + 1`:

`arcTarget (arcPerm ell e) = arcSource (arcPerm (ell+1) f)`.

In other words the cut at level `ell + 1/2` and the cut at level `ell + 3/2`
induce the *same* successor map on the vertices of layer `ell + 1`.  This is
the cross-layer coherence of Hansen's theorem; it also propagates the
single-necklace property from one transition to the next, which closes the
completeness obligation by induction on the layer, starting at the layer of the
graph source.
-/

namespace AllenderOQ3.Internal

variable {n : Nat} {c : ADRCircuit n}

/-! ## The exit dart of a target fibre continues into the next transition -/

/-- The rotation successor of the descending dart of an exit arc is a cut dart
of the next transition. -/
theorem exitDart_cut (hpl : ProperLayered c) (r : OrientableRotation c)
    {ell : Nat} (e : TransitionArc c ell)
    (hup : dartIsUp (r.rotation (downDart e)) = true) :
    isCutDart c (ell + 1) (r.rotation (downDart e)) = true := by
  have hsrc : c.layer (r.rotation (downDart e)).source = ell + 1 := by
    rw [r.preservesSource]
    exact e.2.2.2
  have htgt := layer_of_dartIsUp hpl _ hup
  rw [isCutDart, beq_iff_eq]
  omega

theorem exitDart_source (r : OrientableRotation c) {ell : Nat}
    (e : TransitionArc c ell) :
    c.layer (r.rotation (downDart e)).source = ell + 1 := by
  rw [r.preservesSource]
  exact e.2.2.2

/-- The transition arc of the next transition determined by an exit arc. -/
noncomputable def exitArc (hpl : ProperLayered c) (r : OrientableRotation c)
    {ell : Nat} (e : TransitionArc c ell)
    (hup : dartIsUp (r.rotation (downDart e)) = true) :
    TransitionArc c (ell + 1) :=
  arcOfUpDart hpl ⟨r.rotation (downDart e), exitDart_cut hpl r e hup⟩
    (exitDart_source r e)

theorem exitArc_source (hpl : ProperLayered c) (r : OrientableRotation c)
    {ell : Nat} (e : TransitionArc c ell)
    (hup : dartIsUp (r.rotation (downDart e)) = true) :
    arcSource (exitArc hpl r e hup) = arcTarget e := by
  refine Subtype.ext ?_
  change (r.rotation (downDart e)).source = e.1.2
  rw [r.preservesSource]
  rfl

/-! ### Two auxiliary facts about first returns -/

/-- A first-return time is determined by its two defining properties. -/
theorem firstReturnTime_eq {alpha : Type} [Fintype alpha] (p : Equiv.Perm alpha)
    (S : alpha → Prop) [DecidablePred S] (x : { a // S a }) (N : Nat)
    (hN : 1 ≤ N) (hS : S ((p ^ N) x.1))
    (hnone : ∀ j, 1 ≤ j → j < N → ¬ S ((p ^ j) x.1)) :
    firstReturnTime p S x = N := by
  have h1 : 1 ≤ firstReturnTime p S x := firstReturnTime_pos p S x
  have h2 : S ((p ^ firstReturnTime p S x) x.1) := firstReturnTime_mem p S x
  have h3 : ¬ (N < firstReturnTime p S x) := fun h =>
    firstReturnTime_not_mem p S x hN h hS
  have h4 : ¬ (firstReturnTime p S x < N) := fun h =>
    hnone _ h1 h h2
  omega

/-- Between an upward crossing of the cut at level `ell + 1` and its first
return, the face walk never crosses the cut at level `ell`. -/
theorem walk_not_cut_below (hpl : ProperLayered c) (r : OrientableRotation c)
    {ell : Nat} (B : CutDart c (ell + 1)) (hBsrc : c.layer B.1.source = ell + 1)
    (k : Nat) (hk1 : 1 ≤ k)
    (hkT : k ≤ firstReturnTime (facePermutation r)
      (fun d => isCutDart c (ell + 1) d = true) B) :
    isCutDart c ell ((facePermutation r ^ k) B.1) = false := by
  have h0 : c.layer B.1.target = ell + 1 + 1 := by
    have hcut : min (c.layer B.1.source) (c.layer B.1.target) = ell + 1 := by
      have h := B.2
      rwa [isCutDart, beq_iff_eq] at h
    rcases dart_layer_cases hpl B.1 with h | h
    · omega
    · omega
  have habove : ell + 1 + 1 ≤ c.layer ((facePermutation r ^ k) B.1).source := by
    refine walk_source_above hpl r B.1 h0 k hk1 (fun j hj hjk => ?_)
    have h := firstReturnTime_not_mem (facePermutation r)
      (fun d => isCutDart c (ell + 1) d = true) B hj (by omega)
    exact Bool.eq_false_iff.mpr h
  have htgt : ell + 1 ≤ c.layer ((facePermutation r ^ k) B.1).target := by
    rcases dart_layer_cases hpl ((facePermutation r ^ k) B.1) with h | h
    · omega
    · omega
  rw [isCutDart, beq_eq_false_iff_ne]
  omega

/-! ### The two necklace steps in terms of the first return -/

theorem arcTarget_arcPerm_val (hpl : ProperLayered c) (r : OrientableRotation c)
    {ell : Nat} (e : TransitionArc c ell) :
    (arcTarget ((arcPerm hpl r ell) e)).1
      = ((firstReturn r ell) (upOfArc e)).1.source := rfl

theorem arcSource_arcPerm_val (hpl : ProperLayered c) (r : OrientableRotation c)
    {ell : Nat} (e : TransitionArc c ell) :
    (arcSource ((arcPerm hpl r ell) e)).1
      = ((firstReturn r ell) (upOfArc e)).1.target := rfl

/-- **Cross-layer exit agreement.**  If `e` exits its target fibre, the
necklace step of `e` and the necklace step of the induced arc `exitArc` of the
next transition land on the same vertex of layer `ell + 1`. -/
theorem exit_agree (hpl : ProperLayered c)
    (hS : ∃! s, IsGraphSource c s) (hT : ∃! t, IsGraphSink c t)
    (r : OrientableRotation c) (hZero : rotationGenus r = 0)
    {ell : Nat} (e : TransitionArc c ell)
    (hup : dartIsUp (r.rotation (downDart e)) = true) :
    arcSource ((arcPerm hpl r (ell + 1)) (exitArc hpl r e hup))
      = arcTarget ((arcPerm hpl r ell) e) := by
  classical
  -- the ascending cut dart of the next transition determined by `e`
  have hcb : isCutDart c (ell + 1) (r.rotation (downDart e)) = true :=
    exitDart_cut hpl r e hup
  have hbsrc : c.layer (r.rotation (downDart e)).source = ell + 1 :=
    exitDart_source r e
  set B : CutDart c (ell + 1) := ⟨r.rotation (downDart e), hcb⟩ with hBdef
  have hBval : B.1 = r.rotation (downDart e) := rfl
  have hBsrc : c.layer B.1.source = ell + 1 := hbsrc
  have hupB : upOfArc (exitArc hpl r e hup) = B :=
    upOfArc_arcOfUpDart hpl B (exitDart_source r e)
  -- the first return of that dart to the cut at level `ell + 1`
  set T := firstReturnTime (facePermutation r)
    (fun d => isCutDart c (ell + 1) d = true) B with hTdef
  set g : CircuitDart c := (facePermutation r ^ T) B.1 with hgdef
  have hfr : ((firstReturn r (ell + 1)) B).1 = g := firstReturn_val r (ell + 1) B
  have hgl : c.layer g.source = ell + 1 + 1 ∧ c.layer g.target = ell + 1 := by
    have h := firstReturn_down hpl r B hBsrc
    rw [hfr] at h
    exact h
  have hgdown : dartIsUp g = false :=
    dartIsUp_eq_false_of_layer hpl g (by omega)
  have hdgup : dartIsUp (dartReverse c g) = true := by
    rw [dartIsUp_dartReverse hpl g, hgdown]
    rfl
  have hdgsrc : c.layer (dartReverse c g).source = ell + 1 := hgl.2
  have hcdg : isCutDart c (ell + 1) (dartReverse c g) = true := by
    have := layer_of_dartIsUp hpl _ hdgup
    rw [isCutDart, beq_iff_eq]
    omega
  -- the next necklace arc of transition `ell + 1`
  have harcf : (arcPerm hpl r (ell + 1)) (exitArc hpl r e hup)
      = arcOfUpDart hpl ⟨dartReverse c g, hcdg⟩ hdgsrc := by
    refine Subtype.ext ?_
    change ((neckPerm r (ell + 1)) (upOfArc (exitArc hpl r e hup))).1.1
      = (dartReverse c g).1
    rw [hupB]
    change (dartReverse c ((firstReturn r (ell + 1)) B).1).1 = (dartReverse c g).1
    rw [hfr]
  -- the rotation successor of the reversed return dart descends
  have hdown : dartIsUp (r.rotation (dartReverse c g)) = false := by
    by_contra hcon
    have h2 : dartIsUp (r.rotation (dartReverse c g)) = true := by
      simpa using hcon
    have hsrot : c.layer (r.rotation (dartReverse c g)).source = ell + 1 := by
      rw [r.preservesSource]
      exact hdgsrc
    have hcrot : isCutDart c (ell + 1) (r.rotation (dartReverse c g)) = true := by
      have := layer_of_dartIsUp hpl _ h2
      rw [isCutDart, beq_iff_eq]
      omega
    have hmin := arcPerm_of_minCorner' hpl hS hT r hZero (ell := ell + 1)
      (dartReverse c g) hdgup h2 hdgsrc hcrot hsrot hcdg
    have hXf : arcOfUpDart hpl ⟨r.rotation (dartReverse c g), hcrot⟩ hsrot
        = exitArc hpl r e hup := by
      refine (arcPerm hpl r (ell + 1)).injective ?_
      rw [hmin, harcf]
    have hupX := upOfArc_arcOfUpDart hpl
      ⟨r.rotation (dartReverse c g), hcrot⟩ hsrot
    rw [hXf, hupB] at hupX
    have hval : r.rotation (dartReverse c g) = r.rotation (downDart e) := by
      have := congrArg (fun z : CutDart c (ell + 1) => z.1) hupX
      simpa [hBval] using this.symm
    have hdg : dartReverse c g = downDart e := r.rotation.injective hval
    have hga : g = (upOfArc e).1 := (dartReverse c).injective hdg
    have hla : c.layer (upOfArc e).1.source = ell := e.2.2.1
    rw [hga] at hgl
    omega
  -- the walk out of `e` first meets the cut at level `ell` after `T + 2` steps
  have hstep : facePermutation r (upOfArc e).1 = B.1 := rfl
  have hshift : ∀ k : Nat, (facePermutation r ^ (k + 1)) (upOfArc e).1
      = (facePermutation r ^ k) B.1 := by
    intro k
    have h := perm_pow_apply_pow (facePermutation r) k 1 (upOfArc e).1
    rw [pow_one] at h
    rw [← h, hstep]
  have hlast : (facePermutation r ^ (T + 2)) (upOfArc e).1
      = r.rotation (dartReverse c g) := by
    have h1 : (facePermutation r ^ (T + 1 + 1)) (upOfArc e).1
        = (facePermutation r ^ (T + 1)) B.1 := hshift (T + 1)
    have h2 : (facePermutation r ^ (T + 1)) B.1
        = facePermutation r ((facePermutation r ^ T) B.1) := by
      have h := perm_pow_apply_pow (facePermutation r) 1 T B.1
      rw [pow_one] at h
      rw [h]
      exact congrArg (fun m => (facePermutation r ^ m) B.1) (Nat.add_comm T 1)
    have h3 : facePermutation r g = r.rotation (dartReverse c g) := rfl
    rw [show T + 2 = T + 1 + 1 from rfl, h1, h2, ← hgdef, h3]
  have hcutlast : isCutDart c ell ((facePermutation r ^ (T + 2)) (upOfArc e).1)
      = true := by
    rw [hlast]
    have hs : c.layer (r.rotation (dartReverse c g)).source = ell + 1 := by
      rw [r.preservesSource]
      exact hdgsrc
    have ht := layer_of_not_dartIsUp hpl _ hdown
    rw [isCutDart, beq_iff_eq]
    omega
  have hnone : ∀ j, 1 ≤ j → j < T + 2 →
      ¬ (isCutDart c ell ((facePermutation r ^ j) (upOfArc e).1) = true) := by
    intro j hj1 hj2
    rcases Nat.exists_eq_add_of_le hj1 with ⟨k, rfl⟩
    have hk : (facePermutation r ^ (1 + k)) (upOfArc e).1
        = (facePermutation r ^ k) B.1 := by
      rw [show 1 + k = k + 1 from Nat.add_comm 1 k]
      exact hshift k
    rw [hk]
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · have : isCutDart c ell B.1 = false := by
        have h1 : c.layer B.1.target = ell + 1 + 1 := by
          have := layer_of_dartIsUp hpl _ hup
          rw [hBval]
          omega
        rw [isCutDart, beq_eq_false_iff_ne]
        rw [hBsrc, h1]
        omega
      rw [pow_zero]
      simp [this]
    · have := walk_not_cut_below hpl r B hBsrc k hk1 (by omega)
      simp [this]
  have hFR : firstReturnTime (facePermutation r)
      (fun d => isCutDart c ell d = true) (upOfArc e) = T + 2 :=
    firstReturnTime_eq (facePermutation r) _ (upOfArc e) (T + 2) (by omega)
      hcutlast hnone
  have hfre : ((firstReturn r ell) (upOfArc e)).1
      = r.rotation (dartReverse c g) := by
    rw [firstReturn_val r ell (upOfArc e), hFR, hlast]
  -- conclude
  refine Subtype.ext ?_
  rw [arcSource_arcPerm_val, arcTarget_arcPerm_val, hupB, hfr, hfre]
  show g.target = (r.rotation (dartReverse c g)).source
  rw [r.preservesSource]
  rfl

/-! ## A generic clean-path lemma for cycles with at most one switch -/

section CleanPath

variable {alpha : Type}

/-- The first position at which a predicate fails along an orbit is preceded by
a `true → false` switch. -/
theorem exists_switch_before (p : Equiv.Perm alpha) (pred : alpha → Bool)
    (a : alpha) (ha : pred a = true) (K : Nat)
    (hK : ¬ (∀ i, i ≤ K → pred ((p ^ i) a) = true)) :
    ∃ i, i < K ∧ pred ((p ^ i) a) = true ∧ pred (p ((p ^ i) a)) = false := by
  classical
  push_neg at hK
  obtain ⟨j, hjK, hj⟩ := hK
  have hjf : pred ((p ^ j) a) = false := by
    cases h : pred ((p ^ j) a)
    · rfl
    · exact absurd h hj
  have hex : ∃ m, pred ((p ^ m) a) = false := ⟨j, hjf⟩
  have hspec : pred ((p ^ Nat.find hex) a) = false := Nat.find_spec hex
  have hjle : Nat.find hex ≤ j := Nat.find_le hjf
  have hpos : 0 < Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
    · rw [h] at hspec
      simp only [pow_zero, Equiv.Perm.coe_one, id_eq] at hspec
      rw [ha] at hspec
      exact absurd hspec (by simp)
    · exact h
  refine ⟨Nat.find hex - 1, by omega, ?_, ?_⟩
  · have hmin := Nat.find_min hex (m := Nat.find hex - 1) (by omega)
    cases h : pred ((p ^ (Nat.find hex - 1)) a)
    · exact absurd h hmin
    · rfl
  · have hstep : p ((p ^ (Nat.find hex - 1)) a) = (p ^ Nat.find hex) a := by
      rw [← Equiv.Perm.mul_apply, ← pow_succ']
      congr 2
      omega
    rw [hstep]
    exact hspec

/-- **Clean paths on a one-switch cycle.**  If the darts of a cycle carry a
predicate with at most one `true → false` switch, then any two `true` positions
are joined, in one of the two directions, by a path that never leaves the
predicate. -/
theorem exists_clean_path [Finite alpha] (p : Equiv.Perm alpha)
    (hcyc : ∀ x y : alpha, ∃ k : Nat, (p ^ k) x = y)
    (pred : alpha → Bool)
    (huniq : ∀ x y : alpha, pred x = true → pred (p x) = false →
      pred y = true → pred (p y) = false → x = y)
    (a b : alpha) (ha : pred a = true) (hb : pred b = true) :
    (∃ k : Nat, (p ^ k) a = b ∧ ∀ i, i ≤ k → pred ((p ^ i) a) = true) ∨
    (∃ k : Nat, (p ^ k) b = a ∧ ∀ i, i ≤ k → pred ((p ^ i) b) = true) := by
  classical
  have : DecidableEq alpha := Classical.decEq alpha
  have : Fintype alpha := Fintype.ofFinite alpha
  by_cases hab : a = b
  · refine Or.inl ⟨0, by simp [hab], ?_⟩
    intro i hi
    interval_cases i
    simpa using ha
  have hAB : (p ^ Nat.find (hcyc a b)) a = b := Nat.find_spec (hcyc a b)
  have hBA : (p ^ Nat.find (hcyc b a)) b = a := Nat.find_spec (hcyc b a)
  set Kab := Nat.find (hcyc a b) with hKabdef
  set Kba := Nat.find (hcyc b a) with hKbadef
  by_cases hcl1 : ∀ i, i ≤ Kab → pred ((p ^ i) a) = true
  · exact Or.inl ⟨Kab, hAB, hcl1⟩
  by_cases hcl2 : ∀ i, i ≤ Kba → pred ((p ^ i) b) = true
  · exact Or.inr ⟨Kba, hBA, hcl2⟩
  exfalso
  obtain ⟨i, hiK, hi1, hi2⟩ := exists_switch_before p pred a ha Kab hcl1
  obtain ⟨i', hi'K, hi'1, hi'2⟩ := exists_switch_before p pred b hb Kba hcl2
  have hswitch : (p ^ i) a = (p ^ i') b := huniq _ _ hi1 hi2 hi'1 hi'2
  have hKab1 : 1 ≤ Kab := by
    rcases Nat.eq_zero_or_pos Kab with h | h
    · rw [h] at hAB
      simp only [pow_zero, Equiv.Perm.coe_one, id_eq] at hAB
      exact absurd hAB hab
    · exact h
  have hPpos : 1 ≤ orbitPeriod p a := orbitPeriod_pos p a
  have hPret : (p ^ orbitPeriod p a) a = a := orbitPeriod_return p a
  have hKabP : Kab < orbitPeriod p a := by
    by_contra hcon
    push_neg at hcon
    have hb' : (p ^ (Kab - orbitPeriod p a)) a = b := by
      have h1 : (p ^ (Kab - orbitPeriod p a)) ((p ^ orbitPeriod p a) a)
          = (p ^ Kab) a := by
        rw [perm_pow_apply_pow]
        exact congrArg (fun m => (p ^ m) a) (by omega)
      rw [hPret] at h1
      rw [h1]
      exact hAB
    have := Nat.find_min' (hcyc a b) hb'
    omega
  have hret : (p ^ (Kab + Kba)) a = a := by
    have h1 : (p ^ Kba) ((p ^ Kab) a) = (p ^ (Kba + Kab)) a :=
      perm_pow_apply_pow p Kba Kab a
    rw [hAB, hBA] at h1
    rw [show Kab + Kba = Kba + Kab from Nat.add_comm _ _, ← h1]
  have hle1 : orbitPeriod p a ≤ Kab + Kba := by
    by_contra hcon
    push_neg at hcon
    exact firstReturnTime_not_mem p (fun x => x = a) ⟨a, rfl⟩
      (by omega) hcon hret
  have hle2 : Kba ≤ orbitPeriod p a - Kab := by
    have h1 : (p ^ (orbitPeriod p a - Kab)) ((p ^ Kab) a)
        = (p ^ (orbitPeriod p a)) a := by
      rw [perm_pow_apply_pow]
      exact congrArg (fun m => (p ^ m) a) (by omega)
    rw [hAB, hPret] at h1
    exact Nat.find_le h1
  have hsum : Kab + Kba = orbitPeriod p a := by omega
  have hkey : (p ^ i) a = (p ^ (i' + Kab)) a := by
    have h1 : (p ^ i') ((p ^ Kab) a) = (p ^ (i' + Kab)) a :=
      perm_pow_apply_pow p i' Kab a
    rw [hAB] at h1
    rw [hswitch, h1]
  have := orbitList_pow_injective p a (by omega : i < orbitPeriod p a)
    (by omega : i' + Kab < orbitPeriod p a) hkey
  omega

end CleanPath

/-! ## Linking arcs along the necklace -/

/-- Being reachable by iterating a permutation of a finite type is symmetric. -/
theorem exists_pow_symm {alpha : Type} [Finite alpha] (q : Equiv.Perm alpha)
    {x y : alpha} (h : ∃ k : Nat, (q ^ k) x = y) : ∃ k : Nat, (q ^ k) y = x := by
  obtain ⟨k, rfl⟩ := h
  have hN : 0 < orderOf q := orderOf_pos q
  have hkle : k + 1 ≤ orderOf q * (k + 1) := Nat.le_mul_of_pos_left _ hN
  refine ⟨orderOf q * (k + 1) - k, ?_⟩
  have hsum : (orderOf q * (k + 1) - k) + k = orderOf q * (k + 1) := by omega
  rw [perm_pow_apply_pow, hsum, pow_mul, pow_orderOf_eq_one, one_pow]
  rfl

/-- Reachability by iterating a permutation is transitive. -/
theorem exists_pow_trans {alpha : Type} (q : Equiv.Perm alpha) {x y z : alpha}
    (h1 : ∃ k : Nat, (q ^ k) x = y) (h2 : ∃ k : Nat, (q ^ k) y = z) :
    ∃ k : Nat, (q ^ k) x = z := by
  obtain ⟨k1, rfl⟩ := h1
  obtain ⟨k2, rfl⟩ := h2
  exact ⟨k2 + k1, (perm_pow_apply_pow q k2 k1 x).symm⟩

/-! ### Chains inside one fibre -/

theorem downDart_val {ell : Nat} (e : TransitionArc c ell) :
    (downDart e).1 = (e.1.2, e.1.1) := rfl

/-- Backwards rotation preserves the source vertex of a dart. -/
theorem rotation_inv_source (r : OrientableRotation c) (d : CircuitDart c) :
    (r.rotation⁻¹ d).source = d.source := by
  have hback : r.rotation (r.rotation⁻¹ d) = d := by simp
  have h := r.preservesSource (r.rotation⁻¹ d)
  rw [hback] at h
  exact h.symm

/-- Backwards rotation also preserves the source vertex of a dart. -/
theorem rotation_inv_pow_source (r : OrientableRotation c) :
    ∀ (k : Nat) (d : CircuitDart c), ((r.rotation⁻¹ ^ k) d).source = d.source := by
  have hone : ∀ d : CircuitDart c, (r.rotation⁻¹ d).source = d.source :=
    rotation_inv_source r
  intro k
  induction k with
  | zero =>
    intro d
    rw [pow_zero]
    rfl
  | succ m ih =>
    intro d
    rw [pow_succ, Equiv.Perm.mul_apply, ih (r.rotation⁻¹ d), hone]

/-- **Chaining max corners.**  As long as the rotation successors of the
descending dart of `e` keep descending, the necklace stays in the target fibre
and follows the rotation. -/
theorem arcPerm_pow_down_chain (hpl : ProperLayered c) (r : OrientableRotation c)
    {ell : Nat} :
    ∀ (k : Nat) (e : TransitionArc c ell),
      (∀ i, i ≤ k → dartIsUp ((r.rotation ^ i) (downDart e)) = false) →
      (((arcPerm hpl r ell) ^ k) e).1
        = (dartReverse c ((r.rotation ^ k) (downDart e))).1 := by
  intro k
  induction k with
  | zero =>
    intro e _
    rw [pow_zero, pow_zero]
    rfl
  | succ m ih =>
    intro e hall
    have hm := ih e (fun i hi => hall i (by omega))
    have hdsrc : c.layer (downDart e).source = ell + 1 := e.2.2.2
    have hd'down : dartIsUp ((r.rotation ^ m) (downDart e)) = false :=
      hall m (by omega)
    have hd'src : c.layer ((r.rotation ^ m) (downDart e)).source = ell + 1 := by
      rw [rotation_pow_source]
      exact hdsrc
    have hd'tgt : c.layer ((r.rotation ^ m) (downDart e)).target = ell := by
      have := layer_of_not_dartIsUp hpl _ hd'down
      omega
    have hrotstep : (r.rotation ^ (m + 1)) (downDart e)
        = r.rotation ((r.rotation ^ m) (downDart e)) := by
      have h := perm_pow_apply_pow r.rotation 1 m (downDart e)
      rw [pow_one] at h
      rw [h]
      exact congrArg (fun j => (r.rotation ^ j) (downDart e)) (Nat.add_comm m 1)
    have hrotdown : dartIsUp (r.rotation ((r.rotation ^ m) (downDart e))) = false := by
      rw [← hrotstep]
      exact hall (m + 1) le_rfl
    have hc1 : isCutDart c ell (dartReverse c ((r.rotation ^ m) (downDart e))) = true := by
      rw [isCutDart, beq_iff_eq]
      change min (c.layer ((r.rotation ^ m) (downDart e)).target)
        (c.layer ((r.rotation ^ m) (downDart e)).source) = ell
      omega
    have hu1 : c.layer (dartReverse c ((r.rotation ^ m) (downDart e))).source = ell := by
      change c.layer ((r.rotation ^ m) (downDart e)).target = ell
      omega
    have hc2 : isCutDart c ell (r.rotation ((r.rotation ^ m) (downDart e))) = true := by
      have h1 : c.layer (r.rotation ((r.rotation ^ m) (downDart e))).source = ell + 1 := by
        rw [r.preservesSource]
        exact hd'src
      have h2 := layer_of_not_dartIsUp hpl _ hrotdown
      rw [isCutDart, beq_iff_eq]
      omega
    have hu2 : c.layer ((cutDartReverse c ell)
        ⟨r.rotation ((r.rotation ^ m) (downDart e)), hc2⟩).1.source = ell := by
      change c.layer (r.rotation ((r.rotation ^ m) (downDart e))).target = ell
      have h1 : c.layer (r.rotation ((r.rotation ^ m) (downDart e))).source = ell + 1 := by
        rw [r.preservesSource]
        exact hd'src
      have h2 := layer_of_not_dartIsUp hpl _ hrotdown
      omega
    have hstep := arcPerm_of_maxCorner' hpl r ((r.rotation ^ m) (downDart e))
      hd'down hrotdown hd'tgt hc1 hu1 hc2 hu2
    have harg : arcOfUpDart hpl
        ⟨dartReverse c ((r.rotation ^ m) (downDart e)), hc1⟩ hu1
        = ((arcPerm hpl r ell) ^ m) e := by
      refine Subtype.ext ?_
      rw [arcOfUpDart_val]
      exact hm.symm
    rw [harg] at hstep
    have hpow : ((arcPerm hpl r ell) ^ (m + 1)) e
        = (arcPerm hpl r ell) (((arcPerm hpl r ell) ^ m) e) := by
      have h := perm_pow_apply_pow (arcPerm hpl r ell) 1 m e
      rw [pow_one] at h
      rw [h]
      exact congrArg (fun j => ((arcPerm hpl r ell) ^ j) e) (Nat.add_comm m 1)
    rw [hpow, hstep, hrotstep]
    rfl

/-- **Chaining min corners.**  As long as the rotation predecessors of the
ascending dart of `e` keep ascending, the necklace stays in the source fibre
and follows the rotation backwards. -/
theorem arcPerm_pow_up_chain (hpl : ProperLayered c)
    (hS : ∃! s, IsGraphSource c s) (hT : ∃! t, IsGraphSink c t)
    (r : OrientableRotation c) (hZero : rotationGenus r = 0) {ell : Nat} :
    ∀ (k : Nat) (e : TransitionArc c ell),
      (∀ i, i ≤ k → dartIsUp ((r.rotation⁻¹ ^ i) (upOfArc e).1) = true) →
      (((arcPerm hpl r ell) ^ k) e).1
        = ((r.rotation⁻¹ ^ k) (upOfArc e).1).1 := by
  intro k
  induction k with
  | zero =>
    intro e _
    rw [pow_zero, pow_zero]
    rfl
  | succ m ih =>
    intro e hall
    have hm := ih e (fun i hi => hall i (by omega))
    have husrc : c.layer (upOfArc e).1.source = ell := e.2.2.1
    have hu'up : dartIsUp ((r.rotation⁻¹ ^ m) (upOfArc e).1) = true :=
      hall m (by omega)
    have hu'src : c.layer ((r.rotation⁻¹ ^ m) (upOfArc e).1).source = ell := by
      rw [rotation_inv_pow_source]
      exact husrc
    have hstepinv : (r.rotation⁻¹ ^ (m + 1)) (upOfArc e).1
        = r.rotation⁻¹ ((r.rotation⁻¹ ^ m) (upOfArc e).1) := by
      have h := perm_pow_apply_pow r.rotation⁻¹ 1 m (upOfArc e).1
      rw [pow_one] at h
      rw [h]
      exact congrArg (fun j => (r.rotation⁻¹ ^ j) (upOfArc e).1) (Nat.add_comm m 1)
    have hdup : dartIsUp (r.rotation⁻¹ ((r.rotation⁻¹ ^ m) (upOfArc e).1)) = true := by
      rw [← hstepinv]
      exact hall (m + 1) le_rfl
    have hback : r.rotation (r.rotation⁻¹ ((r.rotation⁻¹ ^ m) (upOfArc e).1))
        = (r.rotation⁻¹ ^ m) (upOfArc e).1 := by
      simp
    have hlv : c.layer (r.rotation⁻¹ ((r.rotation⁻¹ ^ m) (upOfArc e).1)).source = ell := by
      have h := congrArg (fun d : CircuitDart c => c.layer d.source) hback
      simp only [r.preservesSource] at h
      rw [h]
      exact hu'src
    have hcd : isCutDart c ell (r.rotation⁻¹ ((r.rotation⁻¹ ^ m) (upOfArc e).1)) = true := by
      have h := layer_of_dartIsUp hpl _ hdup
      rw [isCutDart, beq_iff_eq]
      omega
    have hcrot : isCutDart c ell
        (r.rotation (r.rotation⁻¹ ((r.rotation⁻¹ ^ m) (upOfArc e).1))) = true := by
      rw [hback]
      have h := layer_of_dartIsUp hpl _ hu'up
      rw [isCutDart, beq_iff_eq]
      omega
    have hsrot : c.layer
        (r.rotation (r.rotation⁻¹ ((r.rotation⁻¹ ^ m) (upOfArc e).1))).source = ell := by
      rw [hback]
      exact hu'src
    have hrotup : dartIsUp
        (r.rotation (r.rotation⁻¹ ((r.rotation⁻¹ ^ m) (upOfArc e).1))) = true := by
      rw [hback]
      exact hu'up
    have hstep := arcPerm_of_minCorner' hpl hS hT r hZero
      (r.rotation⁻¹ ((r.rotation⁻¹ ^ m) (upOfArc e).1)) hdup hrotup hlv hcrot hsrot hcd
    have harg : arcOfUpDart hpl
        ⟨r.rotation (r.rotation⁻¹ ((r.rotation⁻¹ ^ m) (upOfArc e).1)), hcrot⟩ hsrot
        = ((arcPerm hpl r ell) ^ m) e := by
      refine Subtype.ext ?_
      rw [hm]
      change (r.rotation (r.rotation⁻¹ ((r.rotation⁻¹ ^ m) (upOfArc e).1))).1 = _
      rw [hback]
    rw [harg] at hstep
    have hpow : ((arcPerm hpl r ell) ^ (m + 1)) e
        = (arcPerm hpl r ell) (((arcPerm hpl r ell) ^ m) e) := by
      have h := perm_pow_apply_pow (arcPerm hpl r ell) 1 m e
      rw [pow_one] at h
      rw [h]
      exact congrArg (fun j => ((arcPerm hpl r ell) ^ j) e) (Nat.add_comm m 1)
    rw [hpow, hstep, hstepinv]
    rfl

/-! ### Reading the vertex rotation through the ambient rotation -/

theorem vertexRotation_pow_val (r : OrientableRotation c) (v : Fin c.gateCount)
    (k : Nat) (x : {d : CircuitDart c // d.source = v}) :
    (((vertexRotation r v) ^ k) x).1 = (r.rotation ^ k) x.1 := by
  rw [vertexRotation, Equiv.Perm.subtypePerm_pow, Equiv.Perm.subtypePerm_apply]

theorem vertexRotation_inv_apply_val (r : OrientableRotation c)
    (v : Fin c.gateCount) (x : {d : CircuitDart c // d.source = v}) :
    (((vertexRotation r v)⁻¹) x).1 = r.rotation⁻¹ x.1 := by
  have h : (vertexRotation r v) ((vertexRotation r v)⁻¹ x) = x := by simp
  have h2 : r.rotation (((vertexRotation r v)⁻¹ x).1) = x.1 :=
    congrArg Subtype.val h
  rw [← h2]
  simp

theorem vertexRotation_inv_pow_val (r : OrientableRotation c)
    (v : Fin c.gateCount) :
    ∀ (k : Nat) (x : {d : CircuitDart c // d.source = v}),
      ((((vertexRotation r v)⁻¹) ^ k) x).1 = (r.rotation⁻¹ ^ k) x.1 := by
  intro k
  induction k with
  | zero =>
    intro x
    rw [pow_zero, pow_zero]
    rfl
  | succ m ih =>
    intro x
    rw [pow_succ, Equiv.Perm.mul_apply, ih, vertexRotation_inv_apply_val,
      pow_succ, Equiv.Perm.mul_apply]

/-! ### Arcs with a common source are linked -/

/-- **Common source implies linked.**  Two arcs of one transition leaving the
same vertex lie on a common necklace orbit: the clean-path lemma applied to the
rotation at that vertex, whose ascending darts form one arc of the cycle by
`downUp_corner_unique`. -/
theorem same_source_linked (hpl : ProperLayered c)
    (hS : ∃! s, IsGraphSource c s) (hT : ∃! t, IsGraphSink c t)
    (r : OrientableRotation c) (hZero : rotationGenus r = 0)
    {ell : Nat} (e e' : TransitionArc c ell)
    (hs : arcSource e = arcSource e') :
    ∃ k : Nat, ((arcPerm hpl r ell) ^ k) e' = e := by
  classical
  set v : Fin c.gateCount := e.1.1 with hvdef
  have hval : e'.1.1 = v := (congrArg Subtype.val hs).symm
  set q : Equiv.Perm {d : CircuitDart c // d.source = v} :=
    (vertexRotation r v)⁻¹ with hqdef
  set pred : {d : CircuitDart c // d.source = v} → Bool :=
    fun x => dartIsUp x.1 with hpreddef
  have ha0 : (upOfArc e).1.source = v := rfl
  have hb0 : (upOfArc e').1.source = v := hval
  set a : {d : CircuitDart c // d.source = v} := ⟨(upOfArc e).1, ha0⟩ with hadef
  set b : {d : CircuitDart c // d.source = v} := ⟨(upOfArc e').1, hb0⟩ with hbdef
  have ha : pred a = true := e.2.1
  have hb : pred b = true := e'.2.1
  -- the inverse vertex rotation is still a single cycle
  have hcyc : ∀ x y : {d : CircuitDart c // d.source = v}, ∃ k : Nat, (q ^ k) x = y := by
    intro x y
    obtain ⟨k, hk⟩ := vertexRotation_cyclic r v y x
    refine ⟨k, ?_⟩
    rw [hqdef, inv_pow, ← hk]
    simp
  -- there is at most one down→up corner at `v`
  have huniq : ∀ x y : {d : CircuitDart c // d.source = v}, pred x = true →
      pred (q x) = false → pred y = true → pred (q y) = false → x = y := by
    intro x y hx1 hx2 hy1 hy2
    have hxv : (q x).1 = r.rotation⁻¹ x.1 := vertexRotation_inv_apply_val r v x
    have hyv : (q y).1 = r.rotation⁻¹ y.1 := vertexRotation_inv_apply_val r v y
    have hxb : r.rotation (r.rotation⁻¹ x.1) = x.1 := by simp
    have hyb : r.rotation (r.rotation⁻¹ y.1) = y.1 := by simp
    have hxs : (r.rotation⁻¹ x.1).source = v := by
      rw [rotation_inv_source]
      exact x.2
    have hys : (r.rotation⁻¹ y.1).source = v := by
      rw [rotation_inv_source]
      exact y.2
    have hxd : dartIsUp (r.rotation⁻¹ x.1) = false := by rw [← hxv]; exact hx2
    have hyd : dartIsUp (r.rotation⁻¹ y.1) = false := by rw [← hyv]; exact hy2
    have hxu : dartIsUp (r.rotation (r.rotation⁻¹ x.1)) = true := by
      rw [hxb]; exact hx1
    have hyu : dartIsUp (r.rotation (r.rotation⁻¹ y.1)) = true := by
      rw [hyb]; exact hy1
    have hcorner := downUp_corner_unique hpl hS hT r hZero hxs hxd hxu hys hyd hyu
    refine Subtype.ext ?_
    rw [← hxb, ← hyb, hcorner]
  -- turn a clean path into a chain of necklace steps
  have hchain : ∀ (x y : TransitionArc c ell) (hx : (upOfArc x).1.source = v)
      (hy : (upOfArc y).1.source = v) (k : Nat),
      (q ^ k) ⟨(upOfArc x).1, hx⟩ = ⟨(upOfArc y).1, hy⟩ →
      (∀ i, i ≤ k → pred ((q ^ i) ⟨(upOfArc x).1, hx⟩) = true) →
      ((arcPerm hpl r ell) ^ k) x = y := by
    intro x y hx hy k hk hall
    have hups : ∀ i, i ≤ k → dartIsUp ((r.rotation⁻¹ ^ i) (upOfArc x).1) = true := by
      intro i hi
      have h := hall i hi
      simpa only [hpreddef, hqdef, vertexRotation_inv_pow_val] using h
    have hpow := arcPerm_pow_up_chain hpl hS hT r hZero k x hups
    have hkv : (r.rotation⁻¹ ^ k) (upOfArc x).1 = (upOfArc y).1 := by
      have hv := congrArg Subtype.val hk
      simpa only [hqdef, vertexRotation_inv_pow_val] using hv
    refine Subtype.ext ?_
    rw [hpow, hkv]
    rfl
  rcases exists_clean_path q hcyc pred huniq a b ha hb with ⟨k, hk, hall⟩ | ⟨k, hk, hall⟩
  · have := hchain e e' ha0 hb0 k hk hall
    exact exists_pow_symm (arcPerm hpl r ell) ⟨k, this⟩
  · exact ⟨k, hchain e' e hb0 ha0 k hk hall⟩

/-! ## Completeness: a single necklace at every transition -/

/-- **The exit chain.**  Walking `k` necklace steps at transition `m` moves the
target vertex along a chain of layer-`(m+1)` vertices whose outgoing arcs are
all linked at transition `m + 1`. -/
theorem exit_chain (hpl : ProperLayered c)
    (hS : ∃! s, IsGraphSource c s) (hT : ∃! t, IsGraphSink c t)
    (r : OrientableRotation c) (hZero : rotationGenus r = 0) {m : Nat} :
    ∀ (k : Nat) (e : TransitionArc c m) (f f' : TransitionArc c (m + 1)),
      arcSource f = arcTarget e →
      arcSource f' = arcTarget (((arcPerm hpl r m) ^ k) e) →
      ∃ j : Nat, ((arcPerm hpl r (m + 1)) ^ j) f' = f := by
  intro k
  induction k with
  | zero =>
    intro e f f' hf hf'
    rw [pow_zero] at hf'
    exact same_source_linked hpl hS hT r hZero f f' (hf.trans hf'.symm)
  | succ k ih =>
    intro e f f' hf hf'
    set g : TransitionArc c m := ((arcPerm hpl r m) ^ k) e with hgdef
    have hsucc : ((arcPerm hpl r m) ^ (k + 1)) e = (arcPerm hpl r m) g := by
      rw [hgdef, pow_succ', Equiv.Perm.mul_apply]
    rw [hsucc] at hf'
    by_cases hEq : arcTarget ((arcPerm hpl r m) g) = arcTarget g
    · exact ih e f f' hf (by rw [hf', hEq])
    · have hup := downUp_of_arcTarget_exit hpl r g hEq
      set h : TransitionArc c (m + 1) := exitArc hpl r g hup with hhdef
      have hsrch : arcSource h = arcTarget g := exitArc_source hpl r g hup
      obtain ⟨j1, hj1⟩ := ih e f h hf hsrch
      have hag : arcSource ((arcPerm hpl r (m + 1)) h)
          = arcTarget ((arcPerm hpl r m) g) := exit_agree hpl hS hT r hZero g hup
      obtain ⟨j2, hj2⟩ := same_source_linked hpl hS hT r hZero
        ((arcPerm hpl r (m + 1)) h) f' (hag.trans hf'.symm)
      have step1 : ∃ j : Nat, ((arcPerm hpl r (m + 1)) ^ j) f'
          = (arcPerm hpl r (m + 1)) h := ⟨j2, hj2⟩
      have step2 : ∃ j : Nat, ((arcPerm hpl r (m + 1)) ^ j)
          ((arcPerm hpl r (m + 1)) h) = h := by
        refine exists_pow_symm (arcPerm hpl r (m + 1)) ⟨1, ?_⟩
        rw [pow_one]
      exact exists_pow_trans _ (exists_pow_trans _ step1 step2) ⟨j1, hj1⟩

/-- **The single-necklace theorem.**  For a genus-zero rotation of a properly
layered graph with unique source and sink, any two arcs of one transition lie
on a common necklace orbit. -/
theorem single_orbit_all (hpl : ProperLayered c)
    (hS : ∃! s, IsGraphSource c s) (hT : ∃! t, IsGraphSink c t)
    (r : OrientableRotation c) (hZero : rotationGenus r = 0) :
    ∀ (ell : Nat) (e e' : TransitionArc c ell),
      ∃ k : Nat, ((arcPerm hpl r ell) ^ k) e' = e := by
  intro ell
  induction ell with
  | zero =>
    intro e e'
    have hs0 : IsGraphSource c e.1.1 := by
      intro u
      by_contra hcon
      have hedge : c.edge u e.1.1 = true := by
        simpa using hcon
      have h1 := hpl _ _ hedge
      have h2 := e.2.2.1
      omega
    refine single_orbit_of_common_source hpl hS hT r hZero hs0 ?_ e e'
    intro x
    exact source_alone_in_layer hpl hS hs0 x.1.1 (by rw [x.2.2.1, e.2.2.1])
  | succ m ih =>
    intro f f'
    by_cases hsrc : IsGraphSource c f.1.1
    · refine single_orbit_of_common_source hpl hS hT r hZero hsrc ?_ f f'
      intro x
      exact source_alone_in_layer hpl hS hsrc x.1.1 (by rw [x.2.2.1, f.2.2.1])
    · have hin : ∀ (y : TransitionArc c (m + 1)), ¬ IsGraphSource c y.1.1 →
          ∃ z : TransitionArc c m, arcTarget z = arcSource y := by
        intro y hy
        obtain ⟨u, hu⟩ : ∃ u, c.edge u y.1.1 = true := by
          by_contra hcon
          push_neg at hcon
          exact hy (fun u => by simpa using hcon u)
        have h1 := hpl _ _ hu
        have h2 := y.2.2.1
        have hlu : c.layer u = m := by omega
        exact ⟨⟨(u, y.1.1), ⟨hu, hlu, y.2.2.1⟩⟩, Subtype.ext rfl⟩
      have hsrc' : ¬ IsGraphSource c f'.1.1 := by
        intro hcon
        have heq := source_alone_in_layer hpl hS hcon f.1.1 (by rw [f.2.2.1, f'.2.2.1])
        rw [← heq] at hcon
        exact hsrc hcon
      obtain ⟨e, he⟩ := hin f hsrc
      obtain ⟨e', he'⟩ := hin f' hsrc'
      obtain ⟨k, hk⟩ := ih e' e
      exact exit_chain hpl hS hT r hZero k e f f' he.symm (by rw [hk, he'])

/-- **Completeness off the source layer.**  This is the curated obligation; the
hypothesis `hne` (that the graph source does not sit on layer `ell`) turned out
to be unnecessary, since `single_orbit_all` covers the source layer as well. -/
theorem necklaceWord_complete_off_source (hpl : ProperLayered c)
    (r : OrientableRotation c) (hg : rotationGenus r = 0)
    (hsrc : ∃! s, IsGraphSource c s) (hsnk : ∃! t, IsGraphSink c t)
    (ell : Nat) (e : TransitionArc c ell)
    (hne : ∀ s, IsGraphSource c s → c.layer s ≠ ell) :
    e ∈ necklaceWord hpl r ell := by
  refine necklaceWord_complete_of_single_orbit hpl r ?_ e
  intro h x
  exact single_orbit_all hpl hsrc hsnk r hg ell x h.some

/-- **The completeness obligation.**  Every transition arc lies on the necklace
of its transition. -/
theorem necklaceWord_complete (hpl : ProperLayered c)
    (r : OrientableRotation c) (hg : rotationGenus r = 0)
    (hsrc : ∃! s, IsGraphSource c s) (hsnk : ∃! t, IsGraphSink c t)
    (ell : Nat) (e : TransitionArc c ell) : e ∈ necklaceWord hpl r ell := by
  refine necklaceWord_complete_of_single_orbit hpl r ?_ e
  intro h x
  exact single_orbit_all hpl hsrc hsnk r hg ell x h.some

/-!
## The source grouping obligation

The source grouping obligation of `CutNecklace` is proved in
`AllenderOQ3.Internal.NecklaceSource`, which compares the two cyclic orders
that the necklaces of transitions `m` and `m + 1` induce on layer `m + 1`.
-/

end AllenderOQ3.Internal
