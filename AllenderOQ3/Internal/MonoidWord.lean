import AllenderOQ3.Base

namespace AllenderOQ3
namespace Internal

variable (M : Type) [Monoid M]

/-- Green's right preorder: `a ≤_R b` iff `a ∈ b • M`, i.e., `a = b * c` for some `c`. -/
def RPreorder (a b : M) : Prop := ∃ c : M, a = b * c

/-- `RPreorder` is reflexive. -/
theorem RPreorder_refl (a : M) : RPreorder M a a :=
  ⟨1, (mul_one a).symm⟩

/-- `RPreorder` is transitive. -/
theorem RPreorder_trans (a b c : M) (h1 : RPreorder M a b) (h2 : RPreorder M b c) :
    RPreorder M a c := by
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  use y * x
  rw [hx, hy, mul_assoc]

/-- Two elements are in the same R-class if they divide each other on the right. -/
def REquiv (a b : M) : Prop := RPreorder M a b ∧ RPreorder M b a

/-- `REquiv` is an equivalence relation. -/
theorem REquiv_refl (a : M) : REquiv M a a :=
  ⟨RPreorder_refl M a, RPreorder_refl M a⟩

theorem REquiv_symm (a b : M) (h : REquiv M a b) : REquiv M b a :=
  ⟨h.2, h.1⟩

theorem REquiv_trans (a b c : M) (h1 : REquiv M a b) (h2 : REquiv M b c) : REquiv M a c :=
  ⟨RPreorder_trans M a b c h1.1 h2.1, RPreorder_trans M c b a h2.2 h1.2⟩

/-- Prefix products of a word are `≤_R`-non-increasing. -/
theorem prefix_RPreorder (word : Nat → M) (start : M) (n : Nat) :
    RPreorder M (start * (List.ofFn (fun i : Fin n => word i)).prod) start := by
  use (List.ofFn (fun i : Fin n => word i)).prod

/-- The single right-multiplication step of Green's preorder: a right multiple
`a * b` is `≤_R a`.  Along the prefix products of a word this is the one-letter
step making the prefixes `R`-non-increasing. -/
theorem RPreorder_mul_right (a b : M) : RPreorder M (a * b) a :=
  ⟨b, rfl⟩

/-- Convexity of `R`-classes along an `R`-non-increasing chain.  If `b` lies
`R`-between `a` (on top) and `c` (below), and the two ends `a`, `c` are already
`R`-equivalent, then `a` and `b` are `R`-equivalent too.  Concretely, for prefix
products `a = pᵢ`, `b = pⱼ`, `c = pₖ` with `i ≤ j ≤ k`, an equality of
`R`-classes at the two ends forces equality throughout: the `R`-classes visited
by a word occur in contiguous blocks.  This is the combinatorial heart of the
"at most `|M|` `R`-descents" decomposition (E2-D2). -/
theorem REquiv_of_between (a b c : M)
    (hba : RPreorder M b a) (hcb : RPreorder M c b) (hac : REquiv M a c) :
    REquiv M a b :=
  ⟨RPreorder_trans M a c b hac.1 hcb, hba⟩

/-- Monotonicity of an `R`-non-increasing chain: if every one-step transition of
`f : Fin (L+1) → M` goes down in Green's right preorder, then so does every
transition between comparable indices. -/
theorem RPreorder_of_le {L : Nat} (f : Fin (L + 1) → M)
    (hmono : ∀ i : Fin L, RPreorder M (f i.succ) (f i.castSucc))
    (a b : Fin (L + 1)) (hab : a ≤ b) : RPreorder M (f b) (f a) := by
  obtain ⟨k, hk⟩ : ∃ k : Nat, (b : Nat) = (a : Nat) + k :=
    ⟨(b : Nat) - (a : Nat), by omega⟩
  induction k generalizing b with
  | zero =>
      have hba : a = b := Fin.ext (by omega)
      subst hba
      exact RPreorder_refl M (f a)
  | succ k ih =>
      have hlt : (a : Nat) + k < L := by
        have := b.isLt; omega
      set i : Fin L := ⟨(a : Nat) + k, hlt⟩ with hi
      have hb : b = i.succ := Fin.ext (by simp [hi, hk]; omega)
      have hcs : (i.castSucc : Fin (L + 1)) = ⟨(a : Nat) + k, by omega⟩ :=
        Fin.ext (by simp [hi])
      have h1 : RPreorder M (f i.castSucc) (f a) := by
        refine ih (i.castSucc) ?_ ?_
        · rw [hcs]; exact Fin.mk_le_mk.mpr (by omega) |>.trans_eq rfl
        · simp [hi]
      have h2 : RPreorder M (f b) (f i.castSucc) := by
        rw [hb]; exact hmono i
      exact RPreorder_trans M _ _ _ h2 h1


/-- `Nat`-indexed version of `RPreorder_of_le`: along an `R`-non-increasing
chain indexed by `Nat`, later entries are below earlier ones. -/
theorem RPreorder_of_le_nat (f : Nat → M)
    (hmono : ∀ i : Nat, RPreorder M (f (i + 1)) (f i)) (a b : Nat) (hab : a ≤ b) :
    RPreorder M (f b) (f a) := by
  obtain ⟨k, rfl⟩ : ∃ k : Nat, b = a + k := ⟨b - a, by omega⟩
  induction k with
  | zero => exact RPreorder_refl M (f a)
  | succ k ih =>
      exact RPreorder_trans M _ _ _ (hmono (a + k)) (ih (by omega))

/-- **`R`-classes are constant on descent-free intervals.**  If no step between
`a` and `b` drops the `R`-class of an `R`-non-increasing chain, then the two ends
are `R`-equivalent.  This is the block half of the descent decomposition: the
`R`-descent bound splits a word into blocks, and inside a block the transition
stays in one `R`-class. -/
theorem REquiv_of_no_descent (f : Nat → M) (a b : Nat) (hab : a ≤ b)
    (h : ∀ i : Nat, a ≤ i → i < b → REquiv M (f i) (f (i + 1))) :
    REquiv M (f a) (f b) := by
  obtain ⟨k, rfl⟩ : ∃ k : Nat, b = a + k := ⟨b - a, by omega⟩
  induction k with
  | zero => exact REquiv_refl M (f a)
  | succ k ih =>
      refine REquiv_trans M _ (f (a + k)) _ (ih (by omega) ?_) ?_
      · intro i hi hlt
        exact h i hi (by omega)
      · exact h (a + k) (by omega) (by omega)

open Classical in
/-- **The `R`-descent bound (E2-D2).**  Along an `R`-non-increasing chain of
length `L` in a finite monoid `M`, the number of strict `R`-descents — steps
where the `R`-class actually drops — is at most `|M|`.  Consequently the chain
splits into at most `|M| + 1` maximal `R`-constant blocks.

The proof is the injectivity of `i ↦ f i.succ` on the descent set: if two
descents carried the same monoid element, the later one would be squeezed
between two `R`-equivalent ends, hence not a descent, by `REquiv_of_between`. -/
theorem card_RDescents_le [Fintype M] {L : Nat} (f : Fin (L + 1) → M)
    (hmono : ∀ i : Fin L, RPreorder M (f i.succ) (f i.castSucc)) :
    (Finset.univ.filter fun i : Fin L =>
        ¬ REquiv M (f i.castSucc) (f i.succ)).card ≤ Fintype.card M := by
  classical
  have key : ∀ i j : Fin L, i < j →
      ¬ REquiv M (f j.castSucc) (f j.succ) → f i.succ ≠ f j.succ := by
    intro i j hij hj heq
    apply hj
    have h1 : RPreorder M (f j.castSucc) (f i.succ) := by
      refine RPreorder_of_le M f hmono i.succ j.castSucc ?_
      simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
      omega
    have h2 : RPreorder M (f j.succ) (f j.castSucc) := hmono j
    have h3 : REquiv M (f i.succ) (f j.succ) := by
      rw [heq]; exact REquiv_refl M _
    have hbetween :=
      REquiv_of_between M (f i.succ) (f j.castSucc) (f j.succ) h1 h2 h3
    have h4 := REquiv_symm M _ _ hbetween
    rw [heq] at h4
    exact h4
  refine le_trans (Finset.card_le_card_of_injOn (fun i : Fin L => f i.succ)
    (fun i _ => Finset.mem_univ _) ?_) (le_of_eq Finset.card_univ)
  intro i hi j hj hfe
  simp only [Finset.coe_filter, Set.mem_setOf_eq] at hi hj
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact key i j h hj.2 hfe
  · exact key j i h hi.2 hfe.symm

end Internal
end AllenderOQ3
