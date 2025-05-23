import Mathlib.Data.Nat.Choose.Basic

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic

open Nat Finset Finsupp

def ext_to_z (f : ℕ → ℕ) : ℤ → ℕ := fun n => if n < 0 then 0 else f n.toNat

namespace Nat
    def ichoose (n : ℕ) : ℤ → ℕ := ext_to_z n.choose
end Nat

def irange (n : ℕ) : Finset ℤ := (range n).map ⟨Int.ofNat, cast_injective⟩

lemma irange_nonneg (n : ℕ) (k : ℤ) : k ∈ irange n → k ≥ 0 := by
    intros h
    unfold irange at h
    rw [mem_map] at h
    cases h with
    | intro w hw =>
      cases hw with
      | intro hw1 hw2 =>
        simp at hw2
        rw [← hw2]
        omega

lemma irange_shift (n : ℕ) : irange (n + 1) = insert 0 (map ⟨Int.succ, add_left_injective 1⟩ (irange n)) := by
    unfold irange
    have h : 0 = Int.ofNat 0 := by simp
    rw [h]
    rw [range_succ, map_insert]
    simp
    rw [map_map]
    simp
    induction n with
    | zero =>
      simp
    | succ n' hn' =>
      simp
      rw [range_succ, map_insert]
      rw [map_insert]
      rw [insert_comm 0]
      rw [← hn']
      simp
      unfold Int.succ
      rfl

lemma range_irange_equiv (f : ℕ → ℕ) (n : ℕ) : ∑ k ∈ range (n + 1), f k = ∑ k ∈ irange (n + 1), f k.toNat := by
    unfold irange
    rw [sum_map (range (n + 1)) ⟨Int.ofNat, cast_injective⟩]
    simp

lemma sum_range_irange_equiv (f : ℕ → ℕ) (n : ℕ) : ∑ k ∈ range (n + 1), f k = ∑ k ∈ irange (n + 1), (ext_to_z f) k := by
    unfold ext_to_z
    rw [range_irange_equiv]
    have h : (∀ k ∈ irange (n + 1), f k.toNat = if k < 0 then 0 else f k.toNat) := by
        intros k a
        apply irange_nonneg at a
        apply not_lt_of_ge at a
        rw [ite_cond_eq_false]
        apply eq_false at a
        assumption
    rw [sum_congr rfl h]

lemma choose_rec (n : ℕ) (k : ℤ) : (n+1).ichoose k = n.ichoose k + n.ichoose (k-1) := by
    sorry

lemma insert_irange (n : ℕ) : irange (n + 1) = insert (Int.ofNat n) (irange n) := by
    unfold irange
    cases n
    · simp
    · rw [range_succ, map_insert]
      rfl

lemma sum_choose_trunc (n : ℕ) : ∑ k ∈ irange (n + 2), n.ichoose k = ∑ k ∈ irange (n + 1), n.ichoose k := by
    rw [insert_irange (n+1), sum_insert]
    · simp
      unfold ichoose ext_to_z
      simp
    · unfold irange
      simp
      omega

lemma sum_choose_shift (n : ℕ) : ∑ k ∈ irange (n + 2), n.ichoose (k - 1) = ∑ k ∈ irange (n + 1), n.ichoose k := by
    rw [irange_shift, sum_insert]
    rw [sum_map (irange (n + 1)) ⟨Int.succ, add_left_injective 1⟩]
    simp
    unfold Int.succ
    simp
    unfold ichoose ext_to_z
    simp
    simp
    intros x
    intros h
    apply irange_nonneg at h
    unfold Int.succ
    omega

lemma sum_choose_ind (n : ℕ) : (∑ k ∈ irange (n+2), (n+1).ichoose k) = 2 * (∑ k ∈ irange (n + 1), n.ichoose k) := by
    rw [sum_congr rfl (fun k _ => choose_rec n k), sum_add_distrib, sum_choose_trunc, sum_choose_shift]
    rw [Nat.two_mul]

theorem sum_choose (n : ℕ) : (∑ k ∈ range (n + 1), n.choose k) = 2 ^ n := by
    rw [sum_range_irange_equiv]
    rw [← ichoose]
    induction n with
    | zero =>
      simp
      unfold irange
      rw [sum_map (range 1) ⟨Int.ofNat, cast_injective⟩]
      rw [sum_range_succ, range_zero, sum_empty, zero_add]
      simp
      unfold ichoose ext_to_z
      simp
    | succ n' hn' =>
      rw [sum_choose_ind n']
      omega

-- F(n,-) is finitely supported for each n : ℤ
-- c(i,-) is the coefficient of the recurrence
structure Recurrence {R : Type*} [Semiring R] (F : ℤ → ℤ →₀ R) where
  {α : Type*}
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
