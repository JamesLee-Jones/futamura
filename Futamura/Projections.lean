/--
A representation of a programming language.

Progams in language `L` that take inputs of type `I` and return outputs of type `O` have type `L.Prog I O`.
Each language has an associated evaluator, so that program `p` can be run on input `x` with `L.eval p x`.
-/
structure Lang where
  /-- The type of programs. -/
  Prog: Type → Type → Type
  /-- Evaluates a program on an input. -/
  eval: {I O : Type} → Prog I O → I → O

/-- An interpreter for `S` written in `T`: a `T`-program that takes a source program and its input, and produces the output. -/
structure Interp {I O : Type} (S T : Lang) where
  /-- The interpreter program. -/
  prog: T.Prog (S.Prog I O × I) O
  /-- Running the interpreter yields the same result as evaluating the source program directly. -/
  correct: ∀ (p : S.Prog I O) (x: I), S.eval p x = T.eval prog (p, x)

/-- A compiler from `S` to `T` written in `T`: a `T`-program that takes a source program from `I` to `O` and returns a `T` program from `I` to `O`. -/
structure Compiler {I O : Type} (S T : Lang) where
  /-- The compiler program.-/
  prog: T.Prog (S.Prog I O) (T.Prog I O)
  /-- Compiling and running a program yileds the same result as evaluating the source program directly. -/
  correct: ∀ (p : S.Prog I O) (x : I), S.eval p x = T.eval (T.eval prog p) x

/-- A specializer (partial evaluator) for `T`: a `T`-program that takes a program expecting a static-dynamic pair and a static input, and produces a residual program over just the dynamic input. -/
structure Mix {St Dy O : Type} (T : Lang) where
  /-- The partial evaluator program. -/
  prog: T.Prog ((T.Prog (St × Dy) O) × St) (T.Prog Dy O)
  /-- The residual program is equivalent to the original with the static input fixed. -/
  correct: ∀ (p : T.Prog (St × Dy) O) (s : St) (x : Dy),
    T.eval p (s, x) = T.eval (T.eval prog (p, s)) x

/-- First Futamura projection: specializing an interpreter to a program yields a compiled program. -/
def projection1 {I O : Type}
    (S T : Lang) (mix : @Mix (S.Prog I O) I O T) (interp : @Interp I O S T) (p : S.Prog I O) : T.Prog I O :=
  T.eval mix.prog (interp.prog, p)

/-- The compiled program behaves the same as the source program. -/
theorem projection1_correct {I O : Type}
    (S T : Lang) (mix : @Mix (S.Prog I O) I O T)
    (interp : @Interp I O S T) (p : S.Prog I O)
    (x : I) :
    S.eval p x = T.eval (projection1 S T mix interp p) x := by
  unfold projection1
  rw [← Mix.correct]
  rw [← Interp.correct]
