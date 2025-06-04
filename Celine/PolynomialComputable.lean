import Mathlib.Data.Rat.Init

-- A univariate polynomial is a list of coefficients
-- We use rational numbers, but any field should work
abbrev UniPolynomial := List ℚ

-- Returns true if the list of coefficients is all zeros
def all_zeros_uni (a : UniPolynomial) : Bool :=
  match a with
  | [] => true
  | x :: xs => x = 0 ∧ all_zeros_uni xs

-- Canonize a univariate polynomial by removing trailing zeros
def canon_uni (a : UniPolynomial) : UniPolynomial :=
  if all_zeros_uni a then [] else match a with
  | [] => []
  | x :: xs => x :: (canon_uni xs)

-- Add two univariate polynomials
def add_uni (a b : UniPolynomial) : UniPolynomial :=
  match a, b with
  | [], _ => b
  | _, [] => a
  | x :: xs, y :: ys => canon_uni ((x + y) :: (add_uni xs ys))

-- Scale a univariate polynomial by a scalar
def scale_uni (a : UniPolynomial) (c : ℚ) : UniPolynomial :=
  if c = 0 then [] else match a with
  | [] => []
  | x :: xs => c*x :: (scale_uni xs c)

-- Multiply two univariate polynomials
def mult_uni (a b : UniPolynomial) : UniPolynomial :=
  match a, b with
  | [], _ | _, [] => []
  | x1::xs, _ => add_uni (scale_uni b x1) (0::(mult_uni xs b))

-- Create n copies of x
def n_copies {α : Type} (x : α) (n : ℕ) : List α :=
  match n with
  | 0 => []
  | Nat.succ n' => (n_copies x n').concat x

def div_uni_aux (a b q r : UniPolynomial) (b_nonempty : b.length > 0) : UniPolynomial × UniPolynomial :=
  if h : r.length ≥ b.length then
  let t := (n_copies 0 (r.length - b.length)).concat (r[r.length-1] / b[b.length-1])
  let q' := add_uni q t
  let r' := (add_uni r (scale_uni (mult_uni t b) (-1))).take (r.length - 1)
  div_uni_aux a b q' r' b_nonempty
  else (q,r)

-- Division with remainder of two univariate polynomials
def div_uni (a b : UniPolynomial) : UniPolynomial × UniPolynomial :=
  if h : (canon_uni b).length > 0 then div_uni_aux (canon_uni a) (canon_uni b) [] (canon_uni a) h
  else ([],[])

-- GCD of two univariate polynomials
def gcd_uni (a b : UniPolynomial) : UniPolynomial :=
  if h : b.length > 0 ∧ (canon_uni b).length > 0 then gcd_uni b ((div_uni a b).snd.take (b.length - 1)) else a
  termination_by b.length

-- Substitutes b into a
def subst_uni (a b : UniPolynomial) : UniPolynomial :=
  match a with
  | [] => []
  | x :: xs => add_uni [x] (mult_uni b (subst_uni xs b))

-- Evaluates a at n
def eval_uni (a : UniPolynomial) (n : ℚ) : ℚ :=
  match a with
  | [] => 0
  | x :: xs => x + n * eval_uni xs n

-- A bivariate polynomial in variables x,y is a list of univariate polynomials in x
-- x is called the inner variable and y is called the outer variable
abbrev BiPolynomial := List UniPolynomial

-- Check whether a bivariate polynomial has only zero coefficients
def all_zeros_bi (a : BiPolynomial) : Bool :=
  match a with
  | [] => true
  | x :: xs => (canon_uni x = []) ∧ all_zeros_bi xs

-- Canonize a bivariate polynomial by removing excess zeros
def canon_bi (a : BiPolynomial) : BiPolynomial :=
  if all_zeros_bi a then [] else match a with
  | [] => []
  | x :: xs => x :: (canon_bi xs)

def add_bi (a b : BiPolynomial) : BiPolynomial :=
  match a, b with
  | [], _ => b
  | _, [] => a
  | x :: xs, y :: ys => canon_bi ((add_uni x y) :: (add_bi xs ys))

def scale_bi (a : BiPolynomial) (c : UniPolynomial) : BiPolynomial :=
  if canon_uni c = [] then [] else match a with
  | [] => []
  | x :: xs => (mult_uni c x) :: (scale_bi xs c)

def mult_bi (a b : BiPolynomial) : BiPolynomial :=
  match a, b with
  | [], _ | _, [] => []
  | x1::xs, _ => add_bi (scale_bi b x1) ([]::(mult_bi xs b))

def subst_inner_bi (a : BiPolynomial) (b : UniPolynomial) : BiPolynomial :=
  List.map (fun a' => subst_uni a' b) a

def subst_outer_bi (a : BiPolynomial) (b : UniPolynomial) : BiPolynomial :=
  match a with
  | [] => []
  | x :: xs => add_bi [x] (mult_bi (List.map (fun b' => [b']) b) (subst_outer_bi xs b))

-- Substitutes b for the inner variable and c for the outer variable
def subst_bi (a : BiPolynomial) (b c : UniPolynomial) : BiPolynomial :=
  subst_outer_bi (subst_inner_bi a b) c

-- Evaluates a with n as the inner variable and k as the outer variable
def eval_bi (a : BiPolynomial) (n k : ℚ) : ℚ :=
  match a with
  | [] => 0
  | x :: xs => (eval_uni x n) + k * eval_bi xs n k

-- A univariate rational function is a pair of univariate polynomials,
-- representing the numerator and denominator respectively
abbrev UniRatFunc := UniPolynomial × UniPolynomial

-- Check whether a univariate rational function is the zero function
def is_zero_uni_ratfunc (a : UniRatFunc) : Bool :=
  canon_uni a.fst = [] ∧ canon_uni a.snd ≠ []

-- Reduce a univariate rational function by cancelling out GCD
def reduce_uni_ratfunc (a : UniRatFunc) : UniRatFunc :=
  let g := gcd_uni a.fst a.snd
  ((div_uni a.fst g).fst, (div_uni a.snd g).fst)

def add_uni_ratfunc (a b : UniRatFunc) : UniRatFunc :=
  reduce_uni_ratfunc (add_uni (mult_uni a.fst b.snd) (mult_uni a.snd b.fst), mult_uni a.snd b.snd)

def mult_uni_ratfunc (a b : UniRatFunc) : UniRatFunc :=
  reduce_uni_ratfunc (mult_uni a.fst b.fst, mult_uni a.snd b.snd)

def neg_uni_ratfunc (a : UniRatFunc) : UniRatFunc :=
  mult_uni_ratfunc ([-1], [1]) a

def div_uni_ratfunc (a b : UniRatFunc) : UniRatFunc :=
  reduce_uni_ratfunc (mult_uni a.fst b.snd, mult_uni a.snd b.fst)

def inverse_uni_ratfunc (a : UniRatFunc) : UniRatFunc :=
  div_uni_ratfunc ([1],[1]) a

-- A bivariate rational function is a pair of bivariate polynomials
abbrev BiRatFunc := BiPolynomial × BiPolynomial

def add_bi_ratfunc (a b : BiRatFunc) : BiRatFunc :=
  (add_bi (mult_bi a.fst b.snd) (mult_bi a.snd b.fst), mult_bi a.snd b.snd)

def mult_bi_ratfunc (a b : BiRatFunc) : BiRatFunc :=
  (mult_bi a.fst b.fst, mult_bi a.snd b.snd)

def div_bi_ratfunc (a b : BiRatFunc) : BiRatFunc :=
  (mult_bi a.fst b.snd, mult_bi a.snd b.fst)

def subst_bi_ratfunc (a : BiRatFunc) (b c : UniPolynomial) : BiRatFunc :=
  (subst_bi a.fst b c, subst_bi a.snd b c)
