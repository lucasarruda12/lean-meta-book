import Lean
open Lean

def zero : Expr := Expr.const ``Nat.zero []

def exprNat : Nat → Expr
  | Nat.zero => zero
  | Nat.succ n => Expr.app (Expr.const ``Nat.succ []) (exprNat n)

def one := exprNat (Nat.succ Nat.zero)
def two := exprNat (Nat.succ $ Nat.succ $ Nat.zero)

-- 2 + 1 :)
#eval Expr.app (Expr.app (Expr.const ``Nat.add []) one) two

-- 2 + 1 (2) :)
#check Lean.mkAppN
#eval Lean.mkAppN (Expr.const ``Nat.add []) #[one, two]

-- λ x => 1 + x
#check Expr.lam
#check Expr.lam `x (Expr.const ``Nat []) (
    Lean.mkAppN (Expr.const ``Nat.add []) #[(Expr.bvar 0), one]
  ) Lean.BinderInfo.default

-- λ a => λ b => λ c => (a + b) * c
def exNat : Expr := Expr.const ``Nat []
def exAdd : Expr := Expr.const ``Nat.add []
def myLam : Expr := Expr.lam `a (exNat) (
  (Expr.lam `b exNat (
    (Expr.lam `c exNat (
      Lean.mkAppN exAdd #[(Lean.mkAppN exAdd #[Expr.bvar 2, Expr.bvar 1]), Expr.bvar 0]
    )) Lean.BinderInfo.default
  )) Lean.BinderInfo.default
) Lean.BinderInfo.default

#eval Lean.mkAppN myLam #[zero, one, two]

-- λ x y => x + y
#check Expr.lam `x exNat (
  Expr.lam `y exNat (
    Lean.mkAppN exAdd #[Expr.bvar 1, Expr.bvar 0]
  ) Lean.BinderInfo.default
) Lean.BinderInfo.default

-- λ x => String.append "Hello " x
#check Expr.lam `x (Expr.const ``String []) (
  Lean.mkAppN (Expr.const ``String.append []) #[
    (Expr.lit $ Literal.strVal "Hello "), Expr.bvar 0
  ]
) Lean.BinderInfo.default
