import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Factorial.Basic

open Nat

theorem succ_add_fact (n m : ℕ) : ((n+1) + m)! = ((n + m)+1)! := by rw [succ_add]

macro "ring_fact" : tactic =>
  `(tactic| repeat first
  | fail_if_no_progress ring_nf
  | (try erw [succ_add_fact]);
    simp only [factorial_zero, factorial_succ])

example (n : ℕ) : (n+5)! = n*(n+4)!+(5*n+20)*(n+3)! := by ring_fact
