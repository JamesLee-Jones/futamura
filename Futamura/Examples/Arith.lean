import Futamura.Projections

/-- An inductive data type for basic arithmetic programs.-/
inductive ArithProg : Type → Type → Type where
  | add : ArithProg Nat Nat → ArithProg Nat Nat → ArithProg Nat Nat
  | sub : ArithProg Nat Nat → ArithProg Nat Nat → ArithProg Nat Nat
  | lit : Nat → ArithProg Nat Nat
  | inp : ArithProg Nat Nat

/-- A function for evaluating arithmetic expressions. -/
def evalArith {I O : Type} (prog : ArithProg I O) (x : I) : O :=
  match prog, x with
  | .add a b, i => evalArith a i + evalArith b i
  | .sub a b, i => evalArith a i - evalArith b i
  | .lit l, _ => l
  | .inp, i => i

/-- A language for arithmetic expressions. -/
def Arith : Lang where
  Prog := ArithProg
  eval := evalArith

/-- A language where programs are Lean functions and evaluation is Lean function evaluation. -/
def LeanFunctions : Lang where
  Prog := fun I O => I → O
  eval := fun f x => f x

/-- An interpreter for `Arith` programs implemented using `LeanFunctions`. -/
def interp {I O : Type} : @Interp I O Arith LeanFunctions where
  prog := fun (arith, x) => evalArith arith x
  correct := by
    intro p x
    rfl

/-- A partial evaluator for `LeanFunctions`. -/
def mix : Mix LeanFunctions where
  prog := fun (f, s) => fun d => f (s, d)
  correct := by
    intro St Dy O p s x
    rfl


/-- The program `(x + 5) - 3` where `x` is an input. -/
def example1 : Arith.Prog Nat Nat := ArithProg.sub (ArithProg.add ArithProg.inp (ArithProg.lit 5)) (ArithProg.lit 3)

-- When `x` is `1`, `example1` reduces to `6`.
#reduce Arith.eval example1 1

/-
Applying the first Futramura projection yields the function `fun x => x + 3`.
This is the compiled version of `(x + 5) - 3`.
-/
#reduce projection1 Arith LeanFunctions mix interp example1

/-
Applying the second Futramura projection yields a compiler that when given `example1`, produces the function `fun x => x + 3`.
-/
#reduce (projection2 Arith LeanFunctions mix interp).prog example1

/-
Applying the third Futramura projection yields a compiler generator for `LeanFunctions`.
Applying the compiler generator to the `Arith` interpreter yields a compiler for `Arith` programs.
Applying the generated comiler to `example1` yields `fun x => x + 3`.
-/
#reduce ((projection3 Arith LeanFunctions mix) interp.prog) example1
