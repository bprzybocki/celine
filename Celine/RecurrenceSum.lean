import Mathlib.Data.Finsupp.Basic

open Finset

-- A Recurrence is a structure encoding a recurrence of a bivariate function
-- F(n,-) is finitely supported for each n : ℤ
-- c(i,-) is the coefficient of the recurrence
-- E.g., in the recurrences output by Sister Celine's algorithm, each c(i,-) would be a rational function
structure Recurrence {R : Type*} [Semiring R] (F : ℤ → ℤ →₀ R) where
  {α : Type}
  [hα : Fintype α]
  c : α → ℤ → R
  l : α → ℤ
  r : α → ℤ
  F_sum : ∀ (n k : ℤ), ∑ i, (c i n) * (F (n + (l i)) (k + (r i))) = 0

attribute [instance] Recurrence.hα

lemma sum_over_k {R : Type*} [Semiring R] (F : ℤ → ℤ →₀ R) (F_rec : Recurrence F) (s : Finset ℤ) :
  ∀ (n : ℤ), ∑ i, (F_rec.c i n) * ∑ k ∈ s, (F (n + (F_rec.l i)) (k + (F_rec.r i))) = 0 := by
  intro n
  have h1 : ∑ k ∈ s, ∑ i, (F_rec.c i n) * (F (n + (F_rec.l i)) (k + (F_rec.r i))) = 0 := by
    rw [sum_congr rfl (fun k _ => F_rec.F_sum n k)]
    simp
  have h2 : ∑ i, ∑ k ∈ s, (F_rec.c i n) * (F (n + (F_rec.l i)) (k + (F_rec.r i))) = 0 := by
    rw [← h1]
    exact Eq.symm Finset.sum_comm
  rw [← h2]
  apply Finset.sum_congr rfl
  intros x _
  exact Finset.mul_sum s (fun i ↦ (F (n + F_rec.l x)) (i + F_rec.r x)) (F_rec.c x n)

lemma sum_shift {R : Type*} [Semiring R] (F : ℤ → ℤ →₀ R) (n r : ℤ) :
  ∑ k ∈ (F n).support.image (fun k ↦ k-r), F n (k + r) = ∑ k ∈ (F n).support, F n k := by
  refine sum_equiv ⟨fun i ↦ i+r, fun i ↦ i-r, by intro; simp, by intro; simp⟩ ?_ ?_
  · simp
    intro i
    constructor
    · intro h
      rcases h with ⟨a, ha⟩
      rcases ha with ⟨ha1,ha2⟩
      rw [← ha2]
      simp
      assumption
    · intro h
      use i+r
      simp
      assumption
  · simp

-- Given a recurrence for F, we can derive a recurrence for the summation of F
theorem sum_from_rec {R : Type*} [Semiring R] (F : ℤ → ℤ →₀ R) (F_rec : Recurrence F) :
  ∀ (n : ℤ), ∑ i, (F_rec.c i n) * ∑ k ∈ (F (n + (F_rec.l i))).support, F (n + (F_rec.l i)) k = 0 := by
  intro n
  have h : ∑ i, (F_rec.c i n) * ∑ k ∈ univ.biUnion (fun j ↦ (F (n + (F_rec.l j))).support.image (fun k ↦ k - (F_rec.r j))), F (n + (F_rec.l i)) (k + (F_rec.r i)) = 0 := by
    exact sum_over_k F F_rec (univ.biUnion (fun j ↦ (F (n + (F_rec.l j))).support.image (fun k ↦ k - (F_rec.r j)))) n
  rw [← h]
  apply Finset.sum_congr rfl
  intro x h'
  apply congrArg
  rw  [← sum_shift F (n + F_rec.l x) (F_rec.r x)]
  refine sum_subset ?_ ?_
  · refine image_subset_iff.mpr ?_
    intros x' h''
    simp
    use x, x'
    simp
    simp at h''
    assumption
  · intros x' h1 h2
    simp at h2
    specialize h2 (x' + F_rec.r x)
    simp at h2
    assumption
