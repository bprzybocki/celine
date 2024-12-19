abbrev UniPolynomial := List Int

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

def scale_uni (a : UniPolynomial) (c : Int) : UniPolynomial :=
  if c = 0 then [] else match a with
  | [] => []
  | x :: xs => c*x :: (scale_uni xs c)

def mult_uni (a b : UniPolynomial) : UniPolynomial :=
  match a, b with
  | [], _ | _, [] => []
  | x1::xs, _ => add_uni (scale_uni b x1) (0::(mult_uni xs b))

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

abbrev UniRatFunc := UniPolynomial × UniPolynomial

def is_zero_uni_ratfunc (a : UniRatFunc) : Bool :=
  canon_uni a.fst = []

def add_uni_ratfunc (a b : UniRatFunc) : UniRatFunc :=
  (add_uni (mult_uni a.fst b.snd) (mult_uni a.snd b.fst), mult_uni a.snd b.snd)

def mult_uni_ratfunc (a b : UniRatFunc) : UniRatFunc :=
  (mult_uni a.fst b.fst, mult_uni a.snd b.snd)

def neg_uni_ratfunc (a : UniRatFunc) : UniRatFunc :=
  mult_uni_ratfunc ([-1], [1]) a

def div_uni_ratfunc (a b : UniRatFunc) : UniRatFunc :=
  (mult_uni a.fst b.snd, mult_uni a.snd b.fst)

def inverse_uni_ratfunc (a : UniRatFunc) : UniRatFunc :=
  div_uni_ratfunc ([1],[1]) a
