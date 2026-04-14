/--
A representation of a programming language.

Progams in language `L` that take inputs of type `i` and return outputs of type `o` have type `L.Prog i o`.
Each language has an associated evaluator, so that program `p` can be run on input `x` with `L.eval p x`.
-/
structure Lang where
  /-- The type of programs. -/
  Prog: Type → Type → Type
  /-- Evaluates a program on an input. -/
  eval: {i o : Type} → Prog i o → i → o

/-- An interpreter for `S` written in `T`: a `T`-program that takes a source program and its input, and produces the output. -/
def interp {i o : Type} (S T : Lang) :=
  T.Prog (S.Prog i o × i) o

/-- A compiler from `S` to `T` written in `T`: a `T`-program that takes a source program from `i` to `o` and returns a `T` program from `i` to `o`. -/
def compiler {i o : Type} (S T : Lang) :=
  T.Prog (S.Prog i o) (T.Prog i o)

/-- A specializer (partial evaluator) for `T`: a `T`-program that takes a program expecting a static-dynamic pair and a static input, and produces a residual program over just the dynamic input. -/
def mix {s d o : Type} (T : Lang) :=
  T.Prog (T.Prog (s × d) o × s) (T.Prog d o)
