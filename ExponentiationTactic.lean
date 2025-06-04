import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Factors

open Nat
open Qq

def mkProd {u} {α : Q(Type u)} (inst : Q(One $α)) (inst : Q(Mul $α)) (xs : List Q($α)) : Q($α):=
  go xs.reverse
where go : List Q($α) → Q($α)
  | [] => q(1)
  | [x] => x
  | x :: xs =>
    let rest := go xs
    q($rest * $x)

-- Simplification procedure to factorize natural numbers in an expression, courtesy of Eric Wieser
simproc_decl Nat.factorize (_) := .ofQ fun u α e => do
  match u, α, e with
  | 1, ~q(ℕ), ~q(OfNat.ofNat $en) => do
    let .some n := en.rawNatLit? | return .continue
    have factors : List Q(Nat) := n.primeFactorsList.map Lean.toExpr
    if factors.length < 2 then
      return .continue
    have new_rhs : Q(Nat) := mkProd q(inferInstance) q(inferInstance) factors
    have : $new_rhs =Q $en := ⟨⟩
    return .continue <| some <| .mk q($new_rhs) none
  | _, _, _ => return .continue

macro "ring_exp" : tactic =>
  `(tactic| (
  ring_nf
  try simp only [pow_mul']; try ring_nf
  try simp_rw [factorize, mul_pow]; try ring_nf))

example (n m : ℕ) : 7^((2^n)*(3^(m^2))*(5^n)) = (7^(10^n))^((3^m)^m) := by ring_exp
