import AllenderOQ3.Internal.DedupRotation
import AllenderOQ3.Internal.CutNecklace

set_option autoImplicit false

/-!
# Cyclic block orders

A word with contiguous key-fibres induces a cyclic order on its keys: the list
of block keys `(w.map key).dedup`.  This file isolates the combinatorics needed
to compare two such block orders.

The comparison device is `CycleOrder sigma l`: consecutive entries of `l` are
`sigma`-successors and the last entry wraps around to the first.  Two nodup
lists with the same members that both carry a `CycleOrder` for the *same*
`sigma` are cyclic rotations of one another (`cyclicRotation_of_cycleOrder`).

* `cycleOrder_rotate` — a cyclic rotation of a cycle order is a cycle order;
* `cycleOrder_orbitList` — the orbit word of a permutation is a cycle order for
  that permutation;
* `cycleOrder_dedup_of_contiguous` — the block order of a contiguous word is a
  cycle order for `sigma` as soon as every letter either keeps its key or moves
  it by `sigma`.
-/

namespace AllenderOQ3.Internal

variable {alpha beta : Type}

/-- `l` lists one cycle of `sigma`: consecutive entries are `sigma`-successors,
and the last entry wraps around to the first. -/
def CycleOrder (sigma : beta → beta) (l : List beta) : Prop :=
  List.IsChain (fun a b => sigma a = b) l ∧
    ∀ x ∈ l.getLast?, ∀ y ∈ l.head?, sigma x = y

theorem cycleOrder_nil (sigma : beta → beta) : CycleOrder sigma ([] : List beta) :=
  ⟨List.isChain_nil, by simp⟩

/-- A cyclic rotation of a cycle order is a cycle order. -/
theorem cycleOrder_rotate {sigma : beta → beta} (p q : List beta)
    (h : CycleOrder sigma (p ++ q)) : CycleOrder sigma (q ++ p) := by
  obtain ⟨hchain, hwrap⟩ := h
  rw [List.isChain_append] at hchain
  obtain ⟨hp, hq, hjoin⟩ := hchain
  by_cases hp0 : p = []
  · subst hp0
    simpa using ⟨hq, by simpa using hwrap⟩
  by_cases hq0 : q = []
  · subst hq0
    simpa using ⟨hp, by simpa using hwrap⟩
  have hhead : (p ++ q).head? = p.head? := by
    cases p with
    | nil => exact absurd rfl hp0
    | cons a l => simp
  have hlast : (p ++ q).getLast? = q.getLast? :=
    List.getLast?_append_of_ne_nil p hq0
  rw [hhead, hlast] at hwrap
  refine ⟨List.isChain_append.2 ⟨hq, hp, ?_⟩, ?_⟩
  · exact hwrap
  · have hhead' : (q ++ p).head? = q.head? := by
      cases q with
      | nil => exact absurd rfl hq0
      | cons a l => simp
    have hlast' : (q ++ p).getLast? = p.getLast? :=
      List.getLast?_append_of_ne_nil q hp0
    rw [hhead', hlast']
    exact hjoin

section Orbit

variable {gamma : Type} [Fintype gamma] [DecidableEq gamma]

/-- The orbit word of a permutation is a cycle order for that permutation. -/
theorem cycleOrder_orbitList (q : Equiv.Perm gamma) (a0 : gamma) :
    CycleOrder (fun x => q x) (orbitList q a0) := by
  classical
  have hPpos : 1 ≤ orbitPeriod q a0 := orbitPeriod_pos q a0
  have hlen : (orbitList q a0).length = orbitPeriod q a0 := by
    simp [orbitList]
  have hget : ∀ (i : Nat) (hi : i < (orbitList q a0).length),
      (orbitList q a0)[i] = (q ^ i) a0 := by
    intro i hi
    simp only [orbitList] at hi ⊢
    rw [List.getElem_map, List.getElem_range]
  refine ⟨?_, ?_⟩
  · rw [List.isChain_iff_getElem]
    intro i hi
    rw [hget i (by omega), hget (i + 1) hi]
    simp [pow_succ', Equiv.Perm.mul_apply]
  · intro x hx y hy
    have hlast : (orbitList q a0).getLast?
        = some ((q ^ (orbitPeriod q a0 - 1)) a0) := by
      rw [List.getLast?_eq_getElem?, hlen,
        List.getElem?_eq_getElem (by omega : orbitPeriod q a0 - 1 < _), hget]
    have hhead : (orbitList q a0).head? = some a0 := by
      rw [List.head?_eq_getElem?,
        List.getElem?_eq_getElem (by omega : 0 < (orbitList q a0).length),
        hget 0 (by omega), pow_zero]
      rfl
    rw [hlast] at hx
    rw [hhead] at hy
    have hx' : x = (q ^ (orbitPeriod q a0 - 1)) a0 := by simpa using hx.symm
    have hy' : y = a0 := by simpa using hy.symm
    have hstep : q ((q ^ (orbitPeriod q a0 - 1)) a0) = (q ^ orbitPeriod q a0) a0 := by
      rw [← Equiv.Perm.mul_apply, ← pow_succ']
      congr 2
      omega
    change q x = y
    rw [hx', hy', hstep]
    exact orbitPeriod_return q a0

end Orbit

/-- In a contiguous word with two different keys the first and the last letters
have different keys. -/
theorem keys_ne_of_contiguous (key : alpha → beta) (w : List alpha)
    (hc : KeyContiguous key w) {a b : alpha} (ha : a ∈ w) (hb : b ∈ w)
    (hab : key a ≠ key b) :
    ∀ x ∈ w.getLast?, ∀ y ∈ w.head?, key x ≠ key y := by
  intro x hx y hy hxy
  have hall : ∀ z ∈ w, key z = key y := by
    intro z hz
    cases w with
    | nil => simp at hz
    | cons y0 rest =>
      have hy0 : y = y0 := by simpa using hy.symm
      subst hy0
      rcases List.eq_nil_or_concat rest with rfl | ⟨mid, x0, rfl⟩
      · rcases List.mem_cons.mp hz with rfl | hz'
        · rfl
        · simp at hz'
      · simp only [List.concat_eq_append] at hc hz
        have hlx : (y :: mid.concat x0).getLast? = some x0 := by
          rw [show y :: mid.concat x0 = (y :: mid) ++ [x0] by simp]
          exact List.getLast?_append_of_ne_nil _ (by simp)
        rw [hlx] at hx
        have hx0 : x = x0 := by simpa using hx.symm
        subst hx0
        rcases List.mem_cons.mp hz with rfl | hz'
        · rfl
        · rcases List.mem_append.mp hz' with hzm | hzl
          · have hsub : [y, z, x].Sublist (y :: (mid ++ [x])) := by
              refine List.cons_sublist_cons.mpr ?_
              exact (List.singleton_sublist.mpr hzm).append (List.Sublist.refl [x])
            exact hc y z x hsub hxy.symm
          · have : z = x := by simpa using hzl
            subst this
            exact hxy
  exact hab ((hall a ha).trans (hall b hb).symm)

/-- The block order of a contiguous word chains by `sigma`, and its ends are the
keys of the ends of the word. -/
theorem dedup_block_chain [DecidableEq beta] (key : alpha → beta)
    (sigma : beta → beta) :
    ∀ (bound : Nat) (w : List alpha), w.length ≤ bound → KeyContiguous key w →
      List.IsChain (fun a b => key a = key b ∨ sigma (key a) = key b) w →
      List.IsChain (fun a b => sigma a = b) ((w.map key).dedup) ∧
        ((w.map key).dedup).head? = (w.map key).head? ∧
        ((w.map key).dedup).getLast? = (w.map key).getLast? := by
  intro bound
  induction bound with
  | zero =>
    intro w hlen _ _
    have hw : w = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)
    subst hw
    exact ⟨List.isChain_nil, rfl, rfl⟩
  | succ m ih =>
    intro w hlen hc hch
    cases w with
    | nil => exact ⟨List.isChain_nil, rfl, rfl⟩
    | cons a rest =>
      classical
      obtain ⟨w₁, w₂, hsplit, hne, h1, h2, hlen₂⟩ :
          ∃ w₁ w₂ : List alpha, w₁ ++ w₂ = a :: rest ∧ w₁ ≠ [] ∧
            (∀ z ∈ w₁, key z = key a) ∧ (∀ z ∈ w₂, key z ≠ key a) ∧
            w₂.length ≤ m := by
        refine ⟨a :: rest.takeWhile (fun z => decide (key z = key a)),
          rest.dropWhile (fun z => decide (key z = key a)), ?_, by simp, ?_, ?_, ?_⟩
        · rw [List.cons_append, List.takeWhile_append_dropWhile]
        · intro z hz
          rcases List.mem_cons.mp hz with rfl | hz'
          · rfl
          · simpa using List.mem_takeWhile_imp hz'
        · intro z hz
          cases hw : rest.dropWhile (fun z => decide (key z = key a)) with
          | nil =>
            rw [hw] at hz
            exact absurd hz (by simp)
          | cons t tl =>
            have htkey : key t ≠ key a := by
              have := not_of_dropWhile_eq_cons rest tl t hw
              simpa using this
            rw [hw] at hz
            rcases List.mem_cons.mp hz with rfl | hz''
            · exact htkey
            · intro hzs
              have hsuf : (t :: tl).Sublist rest := by
                rw [← hw]
                exact List.dropWhile_sublist _
              have hsub : [a, t, z].Sublist (a :: rest) :=
                List.cons_sublist_cons.mpr
                  ((List.cons_sublist_cons.mpr
                    (List.singleton_sublist.mpr hz'')).trans hsuf)
              exact htkey (hc a t z hsub hzs.symm)
        · have hle : (rest.dropWhile (fun z => decide (key z = key a))).length
              ≤ rest.length := (List.dropWhile_sublist _).length_le
          simp only [List.length_cons] at hlen
          omega
      have hsnot : key a ∉ w₂.map key := by
        intro hmem
        obtain ⟨z, hz, hzs⟩ := List.mem_map.mp hmem
        exact h2 z hz hzs
      have hdedup : ((a :: rest).map key).dedup = key a :: ((w₂.map key).dedup) := by
        rw [← hsplit, List.map_append]
        refine dedup_const_append (key a) (w₁.map key) (w₂.map key)
          (by simpa using hne) ?_ hsnot
        intro b hb
        obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hb
        exact h1 z hz
      have hsub₂ : w₂.Sublist (a :: rest) := by
        rw [← hsplit]
        exact List.sublist_append_right w₁ w₂
      have hch₂ : List.IsChain
          (fun x y => key x = key y ∨ sigma (key x) = key y) w₂ := by
        rw [← hsplit] at hch
        exact hch.right_of_append
      have ihres := ih w₂ hlen₂ (hc.sublist hsub₂) hch₂
      have hheadw : ((a :: rest).map key).head? = some (key a) := by simp
      by_cases hw2 : w₂ = []
      · subst hw2
        have hd : ((a :: rest).map key).dedup = [key a] := by
          rw [hdedup]
          simp
        refine ⟨by rw [hd]; exact List.isChain_singleton _, ?_, ?_⟩
        · rw [hd, hheadw]
          rfl
        · rw [hd]
          have hlast : ∃ z, (a :: rest).getLast? = some z ∧ z ∈ a :: rest := by
            refine ⟨(a :: rest).getLast (by simp), ?_, List.getLast_mem _⟩
            exact List.getLast?_eq_some_getLast _
          obtain ⟨z, hz1, hz2⟩ := hlast
          have hzkey : key z = key a := by
            refine h1 z ?_
            have hw1 : w₁ = a :: rest := by simpa using hsplit
            rw [hw1]
            exact hz2
          rw [List.getLast?_map, hz1]
          simp [hzkey]
      · have hd2ne : (w₂.map key).dedup ≠ [] := by
          intro hcon
          have : w₂.map key = [] := by
            have := List.dedup_eq_nil (l := w₂.map key)
            exact this.mp hcon
          exact hw2 (List.map_eq_nil_iff.mp this)
        obtain ⟨b0, hb0⟩ : ∃ b0, w₂.head? = some b0 := by
          cases w₂ with
          | nil => exact absurd rfl hw2
          | cons b0 tl => exact ⟨b0, rfl⟩
        have hb0mem : b0 ∈ w₂ := List.mem_of_mem_head? hb0
        have hjunction : sigma (key a) = key b0 := by
          rw [← hsplit, List.isChain_append] at hch
          obtain ⟨z, hz⟩ : ∃ z, w₁.getLast? = some z := by
            cases hw1 : w₁ with
            | nil => exact absurd hw1 hne
            | cons u tl =>
              refine ⟨(u :: tl).getLast (by simp), ?_⟩
              exact List.getLast?_eq_some_getLast _
          have hzmem : z ∈ w₁ := List.mem_of_mem_getLast? hz
          have hzkey : key z = key a := h1 z hzmem
          have hrel := hch.2.2 z hz b0 hb0
          rcases hrel with hrel | hrel
          · exact absurd (hzkey ▸ hrel.symm) (h2 b0 hb0mem)
          · rw [← hzkey]
            exact hrel
        have hd2head : ((w₂.map key).dedup).head? = some (key b0) := by
          rw [ihres.2.1, List.head?_map, hb0]
          rfl
        refine ⟨?_, ?_, ?_⟩
        · rw [hdedup]
          refine List.isChain_cons.mpr ⟨?_, ihres.1⟩
          intro y hy
          rw [hd2head] at hy
          have : y = key b0 := by simpa using hy.symm
          rw [this]
          exact hjunction
        · rw [hdedup, hheadw]
          rfl
        · rw [hdedup]
          have h1' : (key a :: (w₂.map key).dedup).getLast?
              = ((w₂.map key).dedup).getLast? :=
            List.getLast?_append_of_ne_nil [key a] hd2ne
          have hmapne : w₂.map key ≠ [] := by
            intro hcon
            exact hw2 (List.map_eq_nil_iff.mp hcon)
          have h2' : ((a :: rest).map key).getLast? = (w₂.map key).getLast? := by
            rw [← hsplit, List.map_append]
            exact List.getLast?_append_of_ne_nil _ hmapne
          rw [h1', ihres.2.2, h2']

/-- The block order of a contiguous word is a cycle order for `sigma`, provided
consecutive letters either share their key or move it by `sigma`, and the word
wraps around by `sigma` too. -/
theorem cycleOrder_dedup_of_contiguous [DecidableEq beta] (key : alpha → beta)
    (sigma : beta → beta) (w : List alpha) (hc : KeyContiguous key w)
    (hchain : List.IsChain (fun a b => key a = key b ∨ sigma (key a) = key b) w)
    (hwrap : ∀ x ∈ w.getLast?, ∀ y ∈ w.head?, sigma (key x) = key y) :
    CycleOrder sigma ((w.map key).dedup) := by
  obtain ⟨hch, hhd, hlst⟩ := dedup_block_chain key sigma w.length w le_rfl hc hchain
  refine ⟨hch, ?_⟩
  intro u hu v hv
  rw [hlst, List.getLast?_map] at hu
  rw [hhd, List.head?_map] at hv
  obtain ⟨x, hx, hxu⟩ : ∃ x, w.getLast? = some x ∧ key x = u := by
    cases hw : w.getLast? with
    | none => rw [hw] at hu; simp at hu
    | some x => exact ⟨x, rfl, by rw [hw] at hu; simpa using hu⟩
  obtain ⟨y, hy, hyv⟩ : ∃ y, w.head? = some y ∧ key y = v := by
    cases hw : w.head? with
    | none => rw [hw] at hv; simp at hv
    | some y => exact ⟨y, rfl, by rw [hw] at hv; simpa using hv⟩
  rw [← hxu, ← hyv]
  exact hwrap x (by rw [hx]; rfl) y (by rw [hy]; rfl)

/-- Along a cycle order every entry is the corresponding `sigma`-iterate of the
head. -/
theorem cycleOrder_getElem {sigma : beta → beta} {l : List beta}
    (c : CycleOrder sigma l) (h0 : 0 < l.length) :
    ∀ (i : Nat) (hi : i < l.length), l[i]'hi = sigma^[i] l[0] := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have hk' : k < l.length := by omega
    have hstep := List.isChain_iff_getElem.mp c.1 k (by omega)
    rw [← hstep, ih hk', Function.iterate_succ_apply']

/-- A cycle order returns to its head after `l.length` steps. -/
theorem cycleOrder_wrap {sigma : beta → beta} {l : List beta}
    (c : CycleOrder sigma l) (h0 : 0 < l.length) :
    sigma^[l.length] l[0] = l[0] := by
  have hlast : l.getLast? = some l[l.length - 1] := by
    rw [List.getLast?_eq_getElem?]
    exact List.getElem?_eq_getElem (by omega)
  have hhead : l.head? = some l[0] := by
    rw [List.head?_eq_getElem?]
    exact List.getElem?_eq_getElem h0
  have hw := c.2 _ (by rw [hlast]; rfl) _ (by rw [hhead]; rfl)
  rw [cycleOrder_getElem c h0 (l.length - 1) (by omega)] at hw
  have key : sigma^[(l.length - 1) + 1] l[0] = l[0] := by
    rw [Function.iterate_succ_apply']
    exact hw
  rwa [Nat.sub_add_cancel h0] at key

/-- Two nodup lists with the same members carrying the same cycle order are
cyclic rotations of one another. -/
theorem cyclicRotation_of_cycleOrder {sigma : beta → beta} (l1 l2 : List beta)
    (h1 : l1.Nodup) (h2 : l2.Nodup) (hmem : ∀ x, x ∈ l1 ↔ x ∈ l2)
    (c1 : CycleOrder sigma l1) (c2 : CycleOrder sigma l2) :
    CyclicRotation l1 l2 := by
  have hperm : l1.Perm l2 :=
    (h1.subperm (fun x hx => (hmem x).mp hx)).antisymm
      (h2.subperm (fun x hx => (hmem x).mpr hx))
  have hlen : l1.length = l2.length := hperm.length_eq
  rcases Nat.eq_zero_or_pos l1.length with hz | h0
  · have e1 : l1 = [] := List.eq_nil_of_length_eq_zero hz
    have e2 : l2 = [] := List.eq_nil_of_length_eq_zero (by omega)
    exact ⟨[], [], by simp [e1], by simp [e2]⟩
  have h0' : 0 < l2.length := by omega
  have hmem0 : l2[0] ∈ l1 := (hmem _).mpr (List.getElem_mem _)
  obtain ⟨j, hj, hjval⟩ := List.getElem_of_mem hmem0
  refine ⟨l1.take j, l1.drop j, (List.take_append_drop j l1).symm, ?_⟩
  have hrot : l1.rotate j = l1.drop j ++ l1.take j :=
    List.rotate_eq_drop_append_take (by omega)
  rw [← hrot]
  refine List.ext_getElem (by rw [List.length_rotate]; omega) ?_
  intro i hi1 _
  have hi : i < l2.length := hi1
  have hj2 : l2[0] = sigma^[j] l1[0] := by
    rw [← hjval]
    exact cycleOrder_getElem c1 h0 j hj
  rw [cycleOrder_getElem c2 h0' i hi, hj2, ← Function.iterate_add_apply,
    List.getElem_rotate,
    cycleOrder_getElem c1 h0 ((i + j) % l1.length) (Nat.mod_lt _ h0)]
  by_cases hc : i + j < l1.length
  · rw [Nat.mod_eq_of_lt hc]
  · have hlt : i + j - l1.length < l1.length := by omega
    have hmod : (i + j) % l1.length = i + j - l1.length := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hlt]
    rw [hmod]
    conv_lhs => rw [show i + j = (i + j - l1.length) + l1.length from by omega]
    rw [Function.iterate_add_apply, cycleOrder_wrap c1 h0]

end AllenderOQ3.Internal
