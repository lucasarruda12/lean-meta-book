import Lean
open Lean

def zero : Expr := Expr.const ``Nat.zero []

def exprNat : Nat → Expr
  | Nat.zero => zero
  | Nat.succ n => Expr.app (Expr.const ``Nat.succ []) (exprNat n)

def one := exprNat (Nat.succ Nat.zero)
def two := exprNat (Nat.succ $ Nat.succ $ Nat.zero)

-- 1. 2 + 1 :)
def first : Expr := Expr.app (Expr.app (Expr.const ``Nat.add []) one) two

elab "first" : term => return first
#check first
#reduce first

-- 2. 2 + 1 (2) :)
def second : Expr := Lean.mkAppN (Expr.const ``Nat.add []) #[one, two]

elab "second" : term => return second
#check second
#reduce second

-- 3. λ x => 1 + x
def third : Expr := Expr.lam `x (Expr.const ``Nat []) (
    Lean.mkAppN (Expr.const ``Nat.add []) #[(Expr.bvar 0), one]
  ) Lean.BinderInfo.default

elab "third" : term => return third
#check third
#reduce third

-- 4. λ a => λ b => λ c => (a + b) * c
def exNat : Expr := Expr.const ``Nat []
def exAdd : Expr := Expr.const ``Nat.add []
def exMul : Expr := Expr.const ``Nat.mul []
def fourth : Expr := Expr.lam `a (exNat) (
  (Expr.lam `b exNat (
    (Expr.lam `c exNat (
      Lean.mkAppN exMul #[(Lean.mkAppN exAdd #[Expr.bvar 2, Expr.bvar 1]), Expr.bvar 0]
    )) Lean.BinderInfo.default
  )) Lean.BinderInfo.default
) Lean.BinderInfo.default

elab "fourth" : term => return fourth
#check fourth

-- 5. λ x y => x + y
def fifth : Expr := Expr.lam `x exNat (
  Expr.lam `y exNat (
    Lean.mkAppN exAdd #[Expr.bvar 1, Expr.bvar 0]
  ) Lean.BinderInfo.default
) Lean.BinderInfo.default

elab "fifth" : term => return fifth
#check fifth

-- 6. λ x => String.append "Hello " x
def sixth : Expr := Expr.lam `x (Expr.const ``String []) (
  Lean.mkAppN (Expr.const ``String.append []) #[
    (Expr.lit $ Literal.strVal "Hello "), Expr.bvar 0
  ]
) Lean.BinderInfo.default

elab "sixth" : term => return sixth
#check sixth

-- 7. ∀x : Prop, x ∧ x
def seventh : Expr := Expr.forallE `x (Expr.sort Level.zero) (
  Lean.mkAppN (Expr.const ``And []) #[Expr.bvar 0, Expr.bvar 0]
) Lean.BinderInfo.default

elab "seventh" : term => return seventh
#check seventh

-- 8. Nat → String
def eigth : Expr := Expr.forallE `x
  (exNat) (Expr.const ``String []) Lean.BinderInfo.default

elab "eigth" : term => return eigth
#check eigth

-- 9. λ (p : Prop) => (λ hP : p => hP)
def nineth : Expr := Expr.lam `p (Expr.sort Level.zero) (
  Expr.lam `hp (Expr.bvar 0) (Expr.bvar 0) Lean.BinderInfo.default
) Lean.BinderInfo.default

elab "nineth" : term => return nineth
#check nineth

-- 10. Type 6

def natToLevel : Nat → Level
  | Nat.zero => Level.zero
  | Nat.succ n => Level.succ (natToLevel n)

-- Prop = Sort 0
-- Type 0 = Sort 1
-- Type 1 = Sort 2
-- ...
-- Type 6 = Sort 7
def tenth : Expr := Expr.sort (natToLevel 7)

elab "tenth" : term => return tenth
#check tenth
