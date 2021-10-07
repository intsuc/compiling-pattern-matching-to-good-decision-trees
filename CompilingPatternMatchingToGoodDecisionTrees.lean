inductive Value where
  | constructor : String → List Value → Value
  deriving Inhabited

partial instance : ToString Value where
  toString :=
    open Std in let rec f
      | Value.constructor c [] => c
      | Value.constructor c vs => s!"{c}({Format.joinSep (vs.map f) ", "})"
    f

def «at» : Value → List Nat → Value
  | v,              []     => v
  | Value.constructor c vs, k :: o => «at» (vs.get! k) o

infix:70 " / " => «at»

inductive Pattern where
  | wildcard    : Pattern
  | constructor : String → List Pattern → Pattern
  | or          : Pattern → Pattern → Pattern

partial instance : ToString Pattern where
  toString :=
    open Std in let rec f
      | Pattern.wildcard         => "_"
      | Pattern.constructor c [] => c
      | Pattern.constructor c ps => s!"{c}({Format.joinSep (ps.map f) ", "})"
      | Pattern.or p₁ p₂         => s!"{f p₁} | {f p₂}"
    f

abbrev PatternRow := List Pattern
abbrev PatternMatrix := List PatternRow

abbrev ClauseRow (α : Type) := List Pattern × α
abbrev ClauseMatrix (α : Type) := List (ClauseRow α)

mutual
  partial def «instance» : Pattern → Value → Bool
    | Pattern.wildcard,          _                       => true
    | Pattern.or p₁ p₂,          v                       => «instance» p₁ v || «instance» p₂ v
    | Pattern.constructor pc ps, Value.constructor vc vs => pc == vc && instance' ps vs

  partial def instance' (ps : List Pattern) (vs : List Value) : Bool :=
    ps |>.zip vs |>.all fun (p, v) => «instance» p v
end

infix:50 " ⪯ " => «instance»
infix:50 " ⪯ " => instance'

partial def specialization (constructor : String) (arity : Nat) : ClauseMatrix α → ClauseMatrix α :=
  List.join ∘ List.map fun
    | (Pattern.constructor c qs :: ps, a) => if constructor == c then [(qs ++ ps, a)] else []
    | (Pattern.wildcard :: ps,         a) => [(List.replicate arity Pattern.wildcard ++ ps, a)]
    | (Pattern.or q₁ q₂ :: ps,         a) => specialization constructor arity [(q₁ :: ps, a)] ++
                                             specialization constructor arity [(q₂ :: ps, a)]
    | ([],                             a) => [([], a)]

#eval
  let nil := Pattern.constructor "nil" []
  let cons p₁ p₂ := Pattern.constructor "cons" [p₁, p₂]
  let __ := Pattern.wildcard
  let pa : ClauseMatrix Nat :=
    [
      ([nil,        __        ], 1),
      ([__,         nil       ], 2),
      ([cons __ __, cons __ __], 3)
    ]
  (specialization "cons" 2 pa, specialization "nil" 0 pa)

partial def default : ClauseMatrix α → ClauseMatrix α :=
  List.join ∘ List.map fun
    | (Pattern.constructor c qs :: ps, _) => []
    | (Pattern.wildcard :: ps,         a) => [(ps, a)]
    | (Pattern.or q₁ q₂ :: ps,         a) => default [(q₁ :: ps, a)] ++
                                             default [(q₂ :: ps, a)]
    | ([],                             a) => [([], a)]

#eval
  let nil := Pattern.constructor "nil" []
  let __ := Pattern.wildcard
  let qb : ClauseMatrix Nat :=
    [
      ([nil, __ ], 1),
      ([__,  nil], 2),
      ([__,  __ ], 3)
    ]
  default qb
