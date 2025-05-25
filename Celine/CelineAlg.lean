import Celine.GaussianElim

-- Computes F(n-j,k-i)/F(n,k)
def f_nj_ki (f1 f2 : BiRatFunc) (i j : ℕ) : BiRatFunc :=
  match i, j with
  | 0, 0 => ([[1]],[[1]])
  | 0, j'+1 => div_bi_ratfunc (f_nj_ki f1 f2 0 j') (subst_bi_ratfunc f1 [-j'-1, 1] [0,1])
  | i'+1, _ => div_bi_ratfunc (f_nj_ki f1 f2 i' j) (subst_bi_ratfunc f2 [-j,1] [-i'-1, 1])

-- Product of the denominators in a list of bivariate rational functions
def prod_of_denoms (l : List BiRatFunc) : BiPolynomial :=
  match l with
  | [] => [[1]]
  | x :: xs => mult_bi x.snd (prod_of_denoms xs)

def put_over_comm_denom_aux (l : List BiRatFunc) (past_denom_prod : BiPolynomial) : List BiRatFunc :=
  match l with
  | [] => []
  | x :: xs => let future_denom_prod := prod_of_denoms xs
  let denom := mult_bi past_denom_prod future_denom_prod
  (mult_bi_ratfunc x (denom,denom)) :: (put_over_comm_denom_aux xs (mult_bi past_denom_prod x.snd))

-- Put a list of bivariate rational functions over a common denominator
def put_over_comm_denom (l : List BiRatFunc) : List BiRatFunc :=
  put_over_comm_denom_aux l [[1]]

def list_of_birats_aux (f1 f2 : BiRatFunc) (I J i j : ℕ) (l : List BiRatFunc) : List BiRatFunc :=
  if i > I then l else if j > J then list_of_birats_aux f1 f2 I J (i+1) 0 l else
  list_of_birats_aux f1 f2 I J i (j+1) (l.concat (f_nj_ki f1 f2 i j))
  termination_by (I+1-i,J+1-j)

-- Get the list of bivariate rational functions F(n-j,k-i)/F(n,k) for 0 <= i <= I and 0 <= j <= J
def list_of_birats (f1 f2 : BiRatFunc) (I J : ℕ) : List BiRatFunc :=
  put_over_comm_denom (list_of_birats_aux f1 f2 I J 0 0 [])

-- Get max degree (actually, the degree plus 1) of numerator in a list of bivariate rational functions
-- This becomes the number of rows in the m × n matrix we construct, hence the name
def get_m (l : List BiRatFunc) : ℕ :=
  match l with
  | [] => 0
  | x :: xs => Nat.max (x.fst.length) (get_m xs)

-- Given a bivariate polynomial, extract the list of coefficients into a list of univariate rational functions
def bipoly_to_list_uniratfunc (a : BiPolynomial) : List UniRatFunc :=
  List.map (fun x => (x,[1])) a

-- Construct the matrix as described in Sister Celine's algorithm
def get_matrix (l : List BiRatFunc) : RatFuncMatrix (get_m l) l.length :=
  transpose { toList := (List.map (fun x => pad_with_zeros (bipoly_to_list_uniratfunc x.fst) (get_m l)) l), size_toArray := by simp }

-- A CelineRecurrence is a list of univariate rational functions, giving the coefficients of the recurrence
abbrev CelineRecurrence := List UniRatFunc

-- Sister Celine's algorithm. I and J control the order of the recurrence we search for.
-- f1 and f2 are F(n+1,k)/F(n,k) and F(n,k+1)/F(n,k) respectively.
def celine (f1 f2 : BiRatFunc) (I J : ℕ) : Option (CelineRecurrence) :=
  (get_nontrivial_sol (get_matrix (list_of_birats f1 f2 I J))).map fun v => v.toList

#eval celine ([[1,1]],[[1,1],[-1]]) ([[0,1],[-1]],[[],[1]]) 1 1
