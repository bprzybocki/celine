import Lean
import Lean.Elab
import Celine.PolynomialComputable
import Celine.Recurrence
import Celine.CelineAlg

deriving instance Lean.ToExpr for List

-- Lean.ToExpr instance for ℚ, courtesy of Aaron Liu
instance : Lean.ToExpr Rat where
  toTypeExpr := .const ``Rat []
  toExpr q :=
    let lit r := Lean.mkApp3 (.const ``OfNat.ofNat [Lean.levelZero]) (.const ``Rat [])
      (Lean.mkRawNatLit r) (.app (.const ``Rat.instOfNat []) (Lean.mkRawNatLit r))
    let numAbs := lit q.num.natAbs
    let num :=
      if q.num ≥ 0 then numAbs else
        Lean.mkApp3 (.const ``Neg.neg [Lean.levelZero]) (.const ``Rat []) (.const ``Rat.instNeg []) numAbs
    if q.den = 1 then num else
      let den := lit q.den
      Lean.mkApp6 (.const ``HDiv.hDiv [Lean.levelZero, Lean.levelZero, Lean.levelZero])
        (.const ``Rat []) (.const ``Rat []) (.const ``Rat [])
        (Lean.mkApp2 (.const ``instHDiv [Lean.levelZero]) (.const ``Rat []) (.const ``Rat.instDiv []))
        num den

structure CelineUserInput where
  f : ℤ → ℤ → ℚ
  rec_N : List (List ℚ) × List (List ℚ)
  rec_K : List (List ℚ) × List (List ℚ)
  f_eq_rec_N : ∀ n k, f (n + 1) k * (eval_bi rec_N.snd n k) = f n k * (eval_bi rec_N.fst n k)
  f_eq_rec_K : ∀ n k, f n (k + 1) * (eval_bi rec_K.snd n k) = f n k * (eval_bi rec_K.fst n k)
-- deriving Lean.ToExpr

#check CelineUserInput.mk

-- evaluate a UniRatFunc
def eval_uniratfunc (a : UniRatFunc) (n : ℚ) : ℚ :=
  (eval_uni a.fst n) / (eval_uni a.snd n)

-- get coefficients of the recurrence from celine output
def get_c_from_celine_rec (celine_rec : CelineRecurrence) (s : Fin celine_rec.length) (n : ℤ) : ℚ :=
  match s with
  | {val := i, isLt := _} => eval_uniratfunc celine_rec[i] n

-- get l function
def get_l_from_celine_rec (I J : ℕ) (s : Fin ((I+1)*(J+1))) : ℤ :=
  (max I J) - (s % (I+1))

-- get r function
def get_r_from_celine_rec (I J : ℕ) (s : Fin ((I+1)*(J+1))) : ℤ :=
  (max I J) - (s / (I+1))

namespace ReflectCelineInput
open Lean Meta Elab

/-- info: Prod.mk.{u, v} {α : Type u} {β : Type v} (fst : α) (snd : β) : α × β -/
#guard_msgs in #check Prod.mk
/-- Match a Lean expression for `Prod.mk` and return the two components --/
def prodMkOfExpr (e : Expr) : Option (Expr × Expr) :=
   match_expr e with
   | Prod.mk _α _β fst snd => .some (fst, snd)
   | _ => none

/-- Match a Lean expression for `CelineUserInput.mk` and return the two components --/
def celineMkOfExpr (e : Expr) : Option (Expr × Expr × Expr × Expr × Expr) :=
   match_expr e with
   | CelineUserInput.mk f rec_N rec_K f_eq_rec_N f_eq_rec_K =>
    some (f, rec_N, rec_K, f_eq_rec_N, f_eq_rec_K)
   | _ => none

def listOfExpr (e : Expr) : Option (List Expr) :=
    match e.listLit? with
    | none => none
    | some (_e, es) => some es

/-- info: Lean.Expr.nat? (e : Expr) : Option ℕ -/
#guard_msgs in #check Expr.nat?

/-- parse an 'Expr' into a list of list of natural numbers -/
def listNatNat (essExpr : Expr) : Option (List (List Nat)) := do
    let ess ← listOfExpr essExpr
    let ess ← ess.mapM listOfExpr
    ess.mapM (fun es => es.mapM Expr.nat?)

/-- parse an 'Expr' into a list of list of natural numbers -/
def listListInt (essExpr : Expr) : Option (List (List ℤ)) := do
    let ess ← listOfExpr essExpr
    let ess ← ess.mapM listOfExpr
    ess.mapM (fun es => es.mapM Expr.int?)

def listListRat (essExpr : Expr) : Option (List (List ℚ)) := do
    let ess ← listOfExpr essExpr
    let ess ← ess.mapM listOfExpr
    ess.mapM (fun es => es.mapM Expr.rat?)

end ReflectCelineInput

open Lean Meta in
-- CoreM: the Lean environment, the state of the Lean system
-- MetaM: everything you need to implement DTT / 'Lean.Expr'
--   (type inference, unification, reduction, ...)
-- TermElabM: stuff that controls conversion / rules from syntax
--              to lean expressions. 'Lean.Syntax'
-- CommandElabM:
--  toplevel stuff: 'Lean.Environment', 'Lean.NameGenerator', ..
--  file we are parsing, error messages we have produced, and so on.
-- def liftTermElabM
  --  (x : TermElabM α) :
  -- CommandElabM α := do
open Lean Meta Elab Term Command in
elab "add_celine_recurrence" defnName:ident : command => do
  -- arg1 : TSyntax `term
  -- 1) elaborate it into Expr (internal well-typed Lean expressions)
  -- 2) "interpret" the expr at the meta-level into the data structure we want it to be.
  -- We expect the type to be a `Prod (List (List Nat)) (List (List Nat))`
  let natTy : Lean.Expr := Lean.mkConst ``Nat
  let listNatTy : Lean.Expr := Lean.mkApp (Lean.mkConst ``List [0]) natTy
  let listListNatTy : Lean.Expr := Lean.mkApp (Lean.mkConst ``List [0]) listNatTy
  let prod : Lean.Expr := Lean.mkApp2 (Lean.mkConst ``Prod [0, 0]) listListNatTy listListNatTy
  let env ← getEnv
  let .some info := env.find? defnName.getId
    | throwError "unable to find any constant name '{defnName}'"
  let dinfo ← match info with
    | .defnInfo d => pure d
    | _ => throwError "unable to find definition named '{defnName}', instead found constant {info.type}"
  liftTermElabM do
    -- let expr ← elabTerm dinfo.value expectedType?
    let expr := dinfo.value
    logInfo m!"elaborated expr: {expr}"
    -- let (f, args) :=  expr.getAppFnArgs
    -- if f != ``CelineUserInput.mk then
    --   throwError "expected invocation of {``CelineUserInput.mk}, found {f} / {repr f}"
    -- let f_expr := args[0]!
    -- let rec_N_expr := args[1]!
    -- let rec_K_expr := args[2]!
    -- let f_eq_rec_N_expr := args[3]!
    -- let f_eq_rec_K_expr := args[4]!

    -- logInfo m!"f: {f} | args: {args}"
    -- -- OK, we now have an `Expr`. We need to 'parse' an `Expr` into data that we can consume.
    let some (f_expr, rec_N_expr, rec_K_expr, f_eq_rec_N_expr, f_eq_rec_K_expr) := ReflectCelineInput.celineMkOfExpr expr
      | throwError m!"Internal error: Expected CelineUserInput, found {expr} | raw: {repr expr}"
    let some (rec_N_expr_fst, rec_N_expr_snd) := ReflectCelineInput.prodMkOfExpr rec_N_expr
      | throwError m!"Internal error: Expected product, found {rec_N_expr}"
    let some rec_N_fst := ReflectCelineInput.listListRat rec_N_expr_fst
      | throwError m!"Expected [[Rat]] for 1st argument, found {rec_N_expr_fst}"
    let some rec_N_snd := ReflectCelineInput.listListRat rec_N_expr_snd
      | throwError m!"Expected [[Rat]] for 2nd argument, found {rec_N_expr_snd}"
    let some (rec_K_expr_fst, rec_K_expr_snd) := ReflectCelineInput.prodMkOfExpr rec_K_expr
      | throwError m!"Internal error: Expected product, found {rec_K_expr}"
    let some rec_K_fst := ReflectCelineInput.listListRat rec_K_expr_fst
      | throwError m!"Expected [[Rat]] for 1st argument, found {rec_K_expr_fst}"
    let some rec_K_snd := ReflectCelineInput.listListRat rec_K_expr_snd
      | throwError m!"Expected [[Rat]] for 2nd argument, found {rec_K_expr_snd}"

    let rec_N : List (List ℚ) × List (List ℚ) := (rec_N_fst, rec_N_snd)
    let rec_K : List (List ℚ) × List (List ℚ) := (rec_K_fst, rec_K_snd)
    -- (Recurrence.mk α hα c l r f_sum) : Recurrence {R} [Semiring R] F
    -- mkConst : Name → List Level → Expr
    -- let _ := mkAppN
    -- let _ := mkAppOptM

    let I := 1
    let J := 1

    let some celine_rec := celine rec_N rec_K I J
      | throwError m!"Could not find recurrence with order I,J"

    logInfo m!"celine_rec: {celine_rec}"

    logInfo m!"f_expr: {f_expr}"
    let thmTy ← instantiateMVars <| ← mkAppM ``Recurrence #[f_expr]
    logInfo m!"thmTy: {thmTy}"
    --let thmVal ← instantiateMVars <|  ← mkSorry thmTy (synthetic := true)
    let α_expr ← instantiateMVars <| ← mkAppM ``Fin #[mkNatLit celine_rec.length]
    let c_expr ← instantiateMVars <| ← mkAppM ``get_c_from_celine_rec #[Lean.toExpr celine_rec]
    let l_expr ← instantiateMVars <| ← mkAppM ``get_l_from_celine_rec #[mkNatLit I, mkNatLit J]
    let r_expr ← instantiateMVars <| ← mkAppM ``get_r_from_celine_rec #[mkNatLit I, mkNatLit J]

    let F_sum_ty ← instantiateMVars <| ← mkAppM ``Recurrence #[f_expr]
    let F_sum_expr ← instantiateMVars <|  ← mkSorry F_sum_ty (synthetic := true)
    let thmVal ← instantiateMVars <| ← mkAppM ``Recurrence.mk #[α_expr, c_expr, l_expr, r_expr, sorry]
    logInfo m!"thmVal: {thmVal}"
    addDecl <| Declaration.defnDecl {
      name := defnName.getId.append (Name.mkSimple "celine")
      levelParams := []
      type := thmTy
      value := thmVal,
      hints := ReducibilityHints.abbrev,
      safety := DefinitionSafety.safe
    }

def binom_n : List (List ℚ) × List (List ℚ) :=
  ([[1,1]] , [[1,1],[-1]])

def binom_k : List (List ℚ) × List (List ℚ) :=
  ([[0,1],[-1]], [[1],[1]])

-- user gives us: binom_n, binom_k, boundary conditions.
-- tactic spits out a 'Recurrence' object.

def ext_to_z (f : ℕ → ℕ) : ℤ → ℚ := fun n => if n < 0 then 0 else f n.toNat

namespace Int
    def ichoose (n : ℤ) : ℤ → ℚ := ext_to_z n.toNat.choose
end Int

def ichoose_rec_N : List (List ℚ) × List (List ℚ) := ([[1,1]] , [[1,1],[-1]])
def ichoose_rec_K : List (List ℚ) × List (List ℚ) := ([[0,1],[-1]], [[1],[1]])

lemma ichoose_f_eq_rec_N (n k : ℤ) : Int.ichoose (n + 1) k * (eval_bi ichoose_rec_N.snd n k) = Int.ichoose n k * (eval_bi ichoose_rec_N.fst n k) := by
  sorry

lemma ichoose_f_eq_rec_K (n k : ℤ) : Int.ichoose n (k+1) * (eval_bi ichoose_rec_K.snd n k) = Int.ichoose n k * (eval_bi ichoose_rec_K.fst n k) := by
  sorry

def binomCelineInput : CelineUserInput where
  f := Int.ichoose
  rec_N := ([[1,1]] , [[1,1],[-1]])
  rec_K := ([[0,1],[-1]], [[1],[1]])
  f_eq_rec_N := ichoose_f_eq_rec_N
  f_eq_rec_K := ichoose_f_eq_rec_K

set_option pp.explicit true in
#print binomCelineInput

add_celine_recurrence binomCelineInput

-- user writes 'add_celine_recurrence binomCelineInput'
-- the tactic will create the following definition automatically, and add it to the enrivonment:

def binomCelineInput.recurrence : Recurrence binomCelineInput.f where
  α := Fin 3
  -- c : α → ℤ → R
  -- l : α → ℤ
  -- r : α → ℤ
  -- F_sum : ∀ (n k : ℤ), ∑ i, (c i n) * (F (n + (l i)) (k + (r i))) = 0


-- add_celine_recurrence binomCelineInput
-- as output, I should get a 'binomCelineInput.recurrence : Recurrence binomCelineInput.f'

open Lean Meta Elab Term Command in
elab "add_celine_recurrence_expr" t:term : command => do
  -- arg1 : TSyntax `term
  -- 1) elaborate it into Expr (internal well-typed Lean expressions)
  -- 2) "interpret" the expr at the meta-level into the data structure we want it to be.
  -- We expect the type to be a `Prod (List (List Nat)) (List (List Nat))`
  let natTy : Lean.Expr := Lean.mkConst ``Nat
  let listNatTy : Lean.Expr := Lean.mkApp (Lean.mkConst ``List [0]) natTy
  let listListNatTy : Lean.Expr := Lean.mkApp (Lean.mkConst ``List [0]) listNatTy
  let prod : Lean.Expr := Lean.mkApp2 (Lean.mkConst ``Prod [0, 0]) listListNatTy listListNatTy
  let env ← getEnv
  try liftTermElabM do
    let expectedType? := prod
    let expr ← elabTerm t expectedType?
    -- let expr := dinfo.value
    logInfo m!"elaborated expr: {expr}"
    -- OK, we now have an `Expr`. We need to 'parse' an `Expr` into data that we can consume.
    let some (fstExpr, sndExpr) := ReflectCelineInput.prodMkOfExpr expr
      | throwError m!"Internal error: Expected product, found {expr}"
    let some fst := ReflectCelineInput.listNatNat fstExpr
      | throwError m!"Expected [[Nat]] for 1st argument, found {fstExpr}"
    let some snd := ReflectCelineInput.listNatNat sndExpr
      | throwError m!"Expected [[Nat]] for 1st argument, found {sndExpr}"
    let celineVal : List (List Nat) × List (List Nat) := (fst, snd)
    logInfo m!"found tuple: {celineVal} with lengths: {(celineVal.fst.length, celineVal.snd.length)}"
    let thmTy ← instantiateMVars <| ← mkEq fstExpr sndExpr
    let thmVal ← instantiateMVars <|  ← mkSorry thmTy (synthetic := true)
    logInfo m!"thmTy: {thmTy}"
    logInfo m!"thmVal: {thmVal}"
    addDecl <| Declaration.thmDecl {
      name := (Name.mkSimple "celine")
      levelParams := []
      type := thmTy
      value := thmVal
    }
  catch e =>
    throwError m!"ERROR: unable to parse definition {t} into a valid Celin input. {e.toMessageData}"


add_celine_recurrence_expr ([[1, 2], [2, 3]], [[3, 4, 5], [6, 7, 8]])

#print binom.celine


/--
info: elaborated expr: ([[1, 2], [2, 3]], [[3, 4, 5], [6, 7, 8]])
---
info: found tuple: ([[1, 2], [2, 3]], [[3, 4, 5], [6, 7, 8]]) with lengths: (2, 2)
---
info: thmTy: [[1, 2], [2, 3]] = [[3, 4, 5], [6, 7, 8]]
---
info: thmVal: sorry
---
warning: declaration uses 'sorry'
-/
#guard_msgs in add_celine_recurrence binom


/--
info: theorem binom.celine : [[1, 2], [2, 3]] = [[3, 4, 5], [6, 7, 8]] :=
sorry
-/
#guard_msgs in #print binom.celine

def wrong : String := "foo"

/--
info: elaborated expr: "foo"
---
error: ERROR: unable to parse definition "foo" into a valid Celin input. Internal error: Expected product, found "foo"
-/
#guard_msgs in add_celine_recurrence wrong
