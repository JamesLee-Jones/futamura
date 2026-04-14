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
structure Mix {S D O : Type} (T : Lang) where
  /-- The partial evaluator program. -/
  prog: T.Prog ((T.Prog (S × D) O) × S) (T.Prog D O)
  /-- The residual program is equivalent to the original with the static input fixed. -/
  correct: ∀ (p : T.Prog (S × D) O) (s : S) (x : D),
    T.eval p (s, x) = T.eval (T.eval prog (p, s)) x
