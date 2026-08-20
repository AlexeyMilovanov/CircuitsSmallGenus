import AllenderOQ3.Base

/-!
# Bounded change count gives a bounded block decomposition

A sequence `z : Nat → Z` that changes at most `K` times inside a window
`[start, start + len)` splits that window into at most `K + 1` blocks on each of
which `z` is constant, *except possibly at the very last step of the block*: the
change that ends a block is caused by the last letter of that block.

`exists_constant_blocks` produces the boundary sequence, `exists_constant_blocks_fin`
repackages it in the `Fin`-indexed form consumed by
`AllenderOQ3.Internal.exists_acc_blockAssembly`.

Everything here is `sorry`-free.
-/

set_option autoImplicit false

namespace AllenderOQ3
namespace Internal

/-- The set of positions inside a window at which a sequence changes. -/
def changeSet {Z : Type} [DecidableEq Z] (z : Nat → Z) (start len : Nat) : Finset Nat :=
  (Finset.range len).filter (fun i => z (start + i) ≠ z (start + i + 1))

theorem mem_changeSet {Z : Type} [DecidableEq Z] (z : Nat → Z) (start len i : Nat) :
    i ∈ changeSet z start len ↔ i < len ∧ z (start + i) ≠ z (start + i + 1) := by
  simp [changeSet]

/-- **Bounded change count gives a bounded block decomposition.**  If `z` changes
at most `K` times in the window `[start, start + len)`, there are boundaries
`0 = t 0 ≤ t 1 ≤ … ≤ t (K + 1) = len` such that inside each block `[t j, t (j+1))`
the sequence `z` is unchanged up to (and excluding) the last step. -/
theorem exists_constant_blocks {Z : Type} [DecidableEq Z] (z : Nat → Z) :
    ∀ (K start len : Nat), (changeSet z start len).card ≤ K →
      ∃ t : Nat → Nat, t 0 = 0 ∧ (∀ j, t j ≤ t (j + 1)) ∧ (∀ j, t j ≤ len) ∧
        t (K + 1) = len ∧
        (∀ j i, t j ≤ i → i + 1 < t (j + 1) → z (start + i) = z (start + i + 1)) := by
  intro K
  induction K with
  | zero =>
      intro start len hcard
      have hempty : changeSet z start len = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
      refine ⟨fun j => if j = 0 then 0 else len, rfl, ?_, ?_, ?_, ?_⟩
      · intro j
        by_cases hj : j = 0 <;> simp [hj]
      · intro j
        by_cases hj : j = 0 <;> simp [hj]
      · simp
      · intro j i hi hi'
        by_cases hj : j = 0
        · subst hj
          simp only [if_neg (Nat.one_ne_zero)] at hi hi'
          by_contra hne
          have : i ∈ changeSet z start len :=
            (mem_changeSet z start len i).mpr ⟨by omega, hne⟩
          rw [hempty] at this
          exact absurd this (Finset.notMem_empty i)
        · simp only [if_neg hj, if_neg (by omega : j + 1 ≠ 0)] at hi hi'
          omega
  | succ K ih =>
      intro start len hcard
      by_cases hne : (changeSet z start len).Nonempty
      · -- the first change position
        set i0 := (changeSet z start len).min' hne with hi0def
        have hi0mem : i0 ∈ changeSet z start len := (changeSet z start len).min'_mem hne
        have hi0lt : i0 < len := ((mem_changeSet z start len i0).mp hi0mem).1
        have hi0min : ∀ i ∈ changeSet z start len, i0 ≤ i := fun i hi =>
          (changeSet z start len).min'_le i hi
        -- the sub-window after the first change has at most `K` changes
        have hsub : (changeSet z (start + i0 + 1) (len - (i0 + 1))).card ≤ K := by
          have hinj : ∀ i ∈ changeSet z (start + i0 + 1) (len - (i0 + 1)),
              (i0 + 1 + i) ∈ (changeSet z start len).erase i0 := by
            intro i hi
            rw [mem_changeSet] at hi
            refine Finset.mem_erase.mpr ⟨by omega, ?_⟩
            refine (mem_changeSet z start len (i0 + 1 + i)).mpr ⟨by omega, ?_⟩
            have h1 : start + (i0 + 1 + i) = start + i0 + 1 + i := by omega
            rw [h1]
            exact hi.2
          have hcardle : (changeSet z (start + i0 + 1) (len - (i0 + 1))).card
              ≤ ((changeSet z start len).erase i0).card := by
            refine Finset.card_le_card_of_injOn (fun i => i0 + 1 + i) hinj ?_
            intro a _ b _ hab
            have hab' : i0 + 1 + a = i0 + 1 + b := hab
            omega
          have herase : ((changeSet z start len).erase i0).card
              = (changeSet z start len).card - 1 := Finset.card_erase_of_mem hi0mem
          omega
        obtain ⟨t', ht'0, ht'mono, ht'le, ht'last, ht'blocks⟩ :=
          ih (start + i0 + 1) (len - (i0 + 1)) hsub
        refine ⟨fun j => if j = 0 then 0 else (i0 + 1) + t' (j - 1), rfl, ?_, ?_, ?_, ?_⟩
        · intro j
          by_cases hj : j = 0
          · subst hj
            simp [ht'0]
          · have h1 : (j + 1) - 1 = (j - 1) + 1 := by omega
            simp only [if_neg hj, if_neg (by omega : j + 1 ≠ 0), h1]
            have := ht'mono (j - 1)
            omega
        · intro j
          by_cases hj : j = 0
          · subst hj; simp
          · simp only [if_neg hj]
            have := ht'le (j - 1)
            omega
        · have h1 : (K + 1 + 1) - 1 = K + 1 := by omega
          simp only [if_neg (by omega : K + 1 + 1 ≠ 0), h1, ht'last]
          omega
        · intro j i hi hi'
          by_cases hj : j = 0
          · subst hj
            simp only [if_neg (Nat.one_ne_zero)] at hi hi'
            simp only [ht'0, Nat.add_zero] at hi'
            by_contra hchange
            have hmem : i ∈ changeSet z start len :=
              (mem_changeSet z start len i).mpr ⟨by omega, hchange⟩
            have := hi0min i hmem
            omega
          · have h1 : (j + 1) - 1 = (j - 1) + 1 := by omega
            simp only [if_neg hj, if_neg (by omega : j + 1 ≠ 0), h1] at hi hi'
            have hkey := ht'blocks (j - 1) (i - (i0 + 1)) (by omega) (by omega)
            have h2 : start + i0 + 1 + (i - (i0 + 1)) = start + i := by omega
            rw [h2] at hkey
            have h3 : start + i + 1 = start + i + 1 := rfl
            simpa [h3] using hkey
      · have hempty : changeSet z start len = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
        refine ⟨fun j => if j = 0 then 0 else len, rfl, ?_, ?_, ?_, ?_⟩
        · intro j
          by_cases hj : j = 0 <;> simp [hj]
        · intro j
          by_cases hj : j = 0 <;> simp [hj]
        · simp
        · intro j i hi hi'
          by_cases hj : j = 0
          · subst hj
            simp only [if_neg (Nat.one_ne_zero)] at hi hi'
            by_contra hchange
            have : i ∈ changeSet z start len :=
              (mem_changeSet z start len i).mpr ⟨by omega, hchange⟩
            rw [hempty] at this
            exact absurd this (Finset.notMem_empty i)
          · simp only [if_neg hj, if_neg (by omega : j + 1 ≠ 0)] at hi hi'
            omega

/-- The `Fin`-indexed form of `exists_constant_blocks`, matching the shape of the
boundary data consumed by `exists_acc_blockAssembly`. -/
theorem exists_constant_blocks_fin {Z : Type} [DecidableEq Z] (z : Nat → Z)
    (K start len : Nat) (hcard : (changeSet z start len).card ≤ K) :
    ∃ t : Fin (K + 2) → Fin (len + 1),
      (t 0).val = 0 ∧ (t (Fin.last (K + 1))).val = len ∧
      (∀ j : Fin (K + 1), (t j.castSucc).val ≤ (t j.succ).val) ∧
      (∀ (j : Fin (K + 1)) (i : Nat), (t j.castSucc).val ≤ i → i + 1 < (t j.succ).val →
        z (start + i) = z (start + i + 1)) := by
  obtain ⟨t, ht0, htmono, htle, htlast, htblocks⟩ := exists_constant_blocks z K start len hcard
  refine ⟨fun j => ⟨t j.val, by have := htle j.val; omega⟩, by simpa using ht0, ?_, ?_, ?_⟩
  · simpa [Fin.val_last] using htlast
  · intro j
    simpa [Fin.val_castSucc, Fin.val_succ] using htmono j.val
  · intro j i hi hi'
    simp only [Fin.val_castSucc, Fin.val_succ] at hi hi'
    exact htblocks j.val i hi hi'

end Internal
end AllenderOQ3
