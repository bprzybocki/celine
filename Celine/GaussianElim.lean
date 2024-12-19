import Celine.PolynomialComputable

abbrev RatFuncMatrix m n := Vector (Vector UniRatFunc n) m

def swap_rows (A : RatFuncMatrix m n) (i j : Nat) (h : i < m ∧ j < m) : RatFuncMatrix m n :=
    (A.set i A[j]).set j A[i]

def mult_row (A : RatFuncMatrix m n) (i : Nat) (h : i < m) (a : UniRatFunc) : RatFuncMatrix m n :=
    A.set i (A[i].map (fun x => mult_uni_ratfunc x a))

def add_mult_row (A : RatFuncMatrix m n) (i j : Nat) (h : i < m ∧ j < m) (a : UniRatFunc) : RatFuncMatrix m n :=
    A.set j (A[j].zipWith (A[i].map (fun x => mult_uni_ratfunc x a)) add_uni_ratfunc)

def get_next_nonzero_row (A : RatFuncMatrix m n) (i j : Nat) (h : i < m ∧ j < n) : {i' : Nat // i ≤ i' ∧ i' < m} :=
    if h' : is_zero_uni_ratfunc A[i][j] ∧ i+1 < m then
    let res := get_next_nonzero_row A (i+1) j ⟨h'.right, h.right⟩
    ⟨res.val, ⟨Nat.le_of_succ_le res.property.left, res.property.right⟩⟩
    else ⟨i, ⟨Nat.le_refl i, h.left⟩⟩
    termination_by m-i

def row_echelon_aux (A : RatFuncMatrix m n) (i j : Nat) (h : i < m ∧ j < n) (just_swapped : Bool) (row_to_clear : Nat) : RatFuncMatrix m n :=
    if h_swap : just_swapped then
    if h'' : row_to_clear < m then let ⟨i'', h'''⟩ := get_next_nonzero_row A row_to_clear j ⟨h'', h.right⟩
    if is_zero_uni_ratfunc A[i''][j] then if h'''' : i+1 < m ∧ j+1 < n then row_echelon_aux A (i+1) (j+1) h'''' false (i+2) else A else
    row_echelon_aux (add_mult_row A i i'' ⟨h.left, h'''.right⟩ (div_uni_ratfunc (neg_uni_ratfunc A[i''][j]) A[i][j])) i j h true (i''+1) else
    if h'''' : i+1 < m ∧ j+1 < n then row_echelon_aux A (i+1) (j+1) h'''' false (i+2) else A else
    let ⟨i', h'⟩ := get_next_nonzero_row A i j h
    if is_zero_uni_ratfunc A[i'][j] then if h'' : j+1 < n then row_echelon_aux A i (j+1) ⟨h.left, h''⟩ false (i+1) else A else
    row_echelon_aux (swap_rows A i i' ⟨h.left, h'.right⟩) i j h true row_to_clear
    termination_by ((m-i)+(n-j), 1-just_swapped.toNat, m - row_to_clear)
    decreasing_by
        left
        refine Nat.add_lt_add ?_ ?_
        refine Nat.sub_succ_lt_self m i ?_
        exact h.left
        refine Nat.sub_succ_lt_self n j ?_
        exact h.right
        right
        rewrite [h_swap]
        right
        refine Nat.sub_lt_sub_left h'' ?_
        refine Nat.lt_add_one_of_le ?_
        exact h'''.left
        left
        refine Nat.add_lt_add ?_ ?_
        refine Nat.sub_succ_lt_self m i ?_
        exact h.left
        refine Nat.sub_succ_lt_self n j ?_
        exact h.right
        left
        simp
        refine Nat.sub_succ_lt_self n j ?_
        exact h.right
        right
        left
        simp at h_swap
        rewrite [h_swap]
        simp

def row_echelon (A : RatFuncMatrix m n) : RatFuncMatrix m n :=
    if h : 0 < m ∧ 0 < n then row_echelon_aux A 0 0 h false 1 else A

def normalize_pivots_aux (A : RatFuncMatrix m n) (i j : Nat) (h : i < m ∧ j < n) : RatFuncMatrix m n :=
    if is_zero_uni_ratfunc A[i][j] then if h' : j+1 < n then normalize_pivots_aux A i (j+1) ⟨h.left, h'⟩ else A else
    if h' : i+1 < m ∧ j+1 < n then normalize_pivots_aux (mult_row A i h.left (inverse_uni_ratfunc A[i][j])) (i+1) (j+1) h' else
    mult_row A i h.left (inverse_uni_ratfunc A[i][j])

def normalize_pivots (A : RatFuncMatrix m n) : RatFuncMatrix m n :=
    if h : 0 < m ∧ 0 < n then normalize_pivots_aux A 0 0 h else A

def get_prev_nonzero_row (A : RatFuncMatrix m n) (i j : Nat) (h : i < m ∧ j < n) : {i' : Nat // 0 ≤ i' ∧ i' ≤ i} :=
    if h' : i = 0 then ⟨0, ⟨Nat.le_refl 0, Nat.zero_le i⟩⟩ else
    if h'' : is_zero_uni_ratfunc A[i][j] then
    let res := get_prev_nonzero_row A (i-1) j ⟨Nat.lt_of_le_of_lt (Nat.sub_le i 1) h.left, h.right⟩
    ⟨res.val, ⟨res.property.left, Nat.le_trans res.property.right (Nat.sub_le i 1)⟩⟩
    else ⟨i, ⟨Nat.zero_le i, Nat.le_refl i⟩⟩

def back_substitute_aux (A : RatFuncMatrix m n) (i j : Nat) (h : i < m ∧ j < n) (row_to_clear : Nat) (h' : row_to_clear < m) : RatFuncMatrix m n :=
    if is_zero_uni_ratfunc A[i][j] then if h'' : j+1 < n then back_substitute_aux A i (j+1) ⟨h.left, h''⟩ (i-1) (Nat.lt_of_le_of_lt (Nat.sub_le i 1) h.left) else A else
    let ⟨i', h''⟩ := get_prev_nonzero_row A row_to_clear j ⟨h', h.right⟩
    if is_zero_uni_ratfunc A[i'][j] then if h''' : i+1 < m ∧ j+1 < n then back_substitute_aux A (i+1) (j+1) h''' i h.left else A else
    let A' := add_mult_row A i i' ⟨h.left, Nat.lt_of_le_of_lt h''.right h'⟩ (neg_uni_ratfunc A[i'][j])
    if i' = 0 then if h''' : i+1 < m ∧ j+1 < n then back_substitute_aux A' (i+1) (j+1) h''' i h.left else A' else
    back_substitute_aux A' i j h (i'-1) (Nat.lt_of_le_of_lt (Nat.sub_le i' 1) (Nat.lt_of_le_of_lt h''.right h'))

def back_substitute (A : RatFuncMatrix m n) : RatFuncMatrix m n :=
    if h : 1 < m ∧ 1 < n then back_substitute_aux A 1 1 h 0 (Nat.lt_trans Nat.zero_lt_one h.left) else A

def gaussian_elim (A : RatFuncMatrix m n) : RatFuncMatrix m n :=
    back_substitute (normalize_pivots (row_echelon A))

def M : RatFuncMatrix 3 4 := #v[#v[([],[1]), ([],[1]), ([0,1,1],[1]), ([1,2,1],[1])], #v[([1,1],[1]), ([1,1],[1]), ([-1,-2],[1]), ([-1,-1],[1])], #v[([-1],[1]), ([],[1]), ([1],[1]), ([],[1])]]

#eval gaussian_elim M
