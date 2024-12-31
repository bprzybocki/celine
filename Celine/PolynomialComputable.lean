import Mathlib.Data.Rat.Init

abbrev UniPolynomial := List Rat

def all_zeros_uni (a : UniPolynomial) : Bool :=
  match a with
  | [] => true
  | x :: xs => x = 0 ∧ all_zeros_uni xs

def canon_uni (a : UniPolynomial) : UniPolynomial :=
  if all_zeros_uni a then [] else match a with
  | [] => []
  | x :: xs => x :: (canon_uni xs)

def add_uni (a b : UniPolynomial) : UniPolynomial :=
  match a, b with
  | [], _ => b
  | _, [] => a
  | x :: xs, y :: ys => canon_uni ((x + y) :: (add_uni xs ys))

def scale_uni (a : UniPolynomial) (c : Rat) : UniPolynomial :=
  if c = 0 then [] else match a with
  | [] => []
  | x :: xs => c*x :: (scale_uni xs c)

def mult_uni (a b : UniPolynomial) : UniPolynomial :=
  match a, b with
  | [], _ | _, [] => []
  | x1::xs, _ => add_uni (scale_uni b x1) (0::(mult_uni xs b))

def n_copies {α : Type} (x : α) (n : Nat) : List α :=
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

def div_uni (a b : UniPolynomial) : UniPolynomial × UniPolynomial :=
  if h : (canon_uni b).length > 0 then div_uni_aux (canon_uni a) (canon_uni b) [] (canon_uni a) h
  else ([],[])

def gcd_uni (a b : UniPolynomial) : UniPolynomial :=
  if h : b.length > 0 ∧ (canon_uni b).length > 0 then gcd_uni b ((div_uni a b).snd.take (b.length - 1)) else a
  termination_by b.length

-- Substitutes b into a
def subst_uni (a b : UniPolynomial) : UniPolynomial :=
  match a with
  | [] => []
  | x :: xs => add_uni [x] (mult_uni b (subst_uni xs b))

abbrev BiPolynomial := List UniPolynomial

def all_zeros_bi (a : BiPolynomial) : Bool :=
  match a with
  | [] => true
  | x :: xs => (canon_uni x = []) ∧ all_zeros_bi xs

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

abbrev UniRatFunc := UniPolynomial × UniPolynomial

def is_zero_uni_ratfunc (a : UniRatFunc) : Bool :=
  canon_uni a.fst = [] ∧ canon_uni a.snd ≠ []

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

abbrev BiRatFunc := BiPolynomial × BiPolynomial

def add_bi_ratfunc (a b : BiRatFunc) : BiRatFunc :=
  (add_bi (mult_bi a.fst b.snd) (mult_bi a.snd b.fst), mult_bi a.snd b.snd)

def mult_bi_ratfunc (a b : BiRatFunc) : BiRatFunc :=
  (mult_bi a.fst b.fst, mult_bi a.snd b.snd)

def div_bi_ratfunc (a b : BiRatFunc) : BiRatFunc :=
  (mult_bi a.fst b.snd, mult_bi a.snd b.fst)

def subst_bi_ratfunc (a : BiRatFunc) (b c : UniPolynomial) : BiRatFunc :=
  (subst_bi a.fst b c, subst_bi a.snd b c)
