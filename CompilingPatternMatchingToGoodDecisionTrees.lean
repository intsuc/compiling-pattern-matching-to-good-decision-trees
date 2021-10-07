import Std.Data.HashSet

inductive Value where
  | constructor : String → List Value → Value
  deriving Inhabited

partial instance : ToString Value where
  toString :=
    open Std in let rec go
      | Value.constructor c [] => c
      | Value.constructor c vs => s!"{c}({Format.joinSep (vs.map go) ", "})"
    go

inductive Pattern where
  | wildcard    : Pattern
  | constructor : String → List Pattern → Pattern
  | or          : Pattern → Pattern → Pattern
  deriving Inhabited

partial instance : ToString Pattern where
  toString :=
    open Std in let rec go
      | Pattern.wildcard         => "_"
      | Pattern.constructor c [] => c
      | Pattern.constructor c ps => s!"{c}({Format.joinSep (ps.map go) ", "})"
      | Pattern.or p₁ p₂         => s!"{go p₁} | {go p₂}"
    go

abbrev ClauseRow (α : Type) [Inhabited α] := List Pattern × α
abbrev ClauseMatrix (α : Type) [Inhabited α] := List (ClauseRow α)

partial def specialize [Inhabited α] (constructor : String) (arity : Nat) : ClauseMatrix α → ClauseMatrix α :=
  List.join ∘ List.map fun
    | (Pattern.constructor c qs :: ps, a) => if constructor == c then [(qs ++ ps, a)] else []
    | (Pattern.wildcard :: ps,         a) => [(List.replicate arity Pattern.wildcard ++ ps, a)]
    | (Pattern.or q₁ q₂ :: ps,         a) => specialize constructor arity [(q₁ :: ps, a)] ++
                                             specialize constructor arity [(q₂ :: ps, a)]
    | ([],                             a) => [([], a)]

partial def default [Inhabited α] : ClauseMatrix α → ClauseMatrix α :=
  List.join ∘ List.map fun
    | (Pattern.constructor c qs :: ps, _) => []
    | (Pattern.wildcard :: ps,         a) => [(ps, a)]
    | (Pattern.or q₁ q₂ :: ps,         a) => default [(q₁ :: ps, a)] ++
                                             default [(q₂ :: ps, a)]
    | ([],                             a) => [([], a)]

abbrev Occurrence := List Nat

inductive DecisionTree (α : Type) where
  | leaf   : α → DecisionTree α
  | switch : Occurrence → List (String × DecisionTree α) → DecisionTree α
  deriving Inhabited

partial instance [ToString α] : ToString (DecisionTree α) where
  toString :=
    open Std in let rec go
      | DecisionTree.leaf a     => s!"{a}"
      | DecisionTree.switch o l => s!"switch {Format.joinSep o "."} {Format.indentD $ Format.joinSep (l.reverse.map (fun (c, t) => s!"{c} => {go t}")) "\n"}"
    go

abbrev CaseList (α : Type) := List (String × DecisionTree α)

def Pattern.isWildcard : Pattern → Bool
  | Pattern.wildcard => true
  | _                => false

def List.swap [Inhabited α] (as : List α) (i₁ i₂ : Nat) : List α :=
  as |>.set i₁ (as.get! i₂) |>.set i₂ (as.get! i₁)

open Std

def HashSet.union [BEq α] [Hashable α] (m₁ m₂ : HashSet α) : HashSet α :=
  HashSet.empty |>.fold (·.insert) m₁ |>.fold (·.insert) m₂

partial def compile [Inhabited α] (signatures : List Nat) : List Occurrence → ClauseMatrix α → Except String (DecisionTree α)
  | _,           []                    => throw "fail"
  | occurrences, matrix@((ps, a) :: _) =>
    if ps.all (·.isWildcard) then
      DecisionTree.leaf a
    else
      let (o, os) := (occurrences.head!, occurrences.tail!)
      let index := (List.range ps.length) |>.find? (fun n => matrix.any fun (ps, _) => !(ps.get! n).isWildcard) |>.get!
      if index == 0 then do
        let column := matrix.map (·.fst.get! index)
        let headConstructors := column |>.map headConstructors |>.foldl HashSet.union HashSet.empty |>.toList
        let caseList := ← headConstructors.mapM fun
          (c, a) => do (c, ← compile signatures ((List.range a).map (o ++ [·]) ++ os) (specialize c a matrix))
        if headConstructors.length == signatures.head! then
          DecisionTree.switch o caseList
        else
          DecisionTree.switch o (("_", ← compile signatures os (default matrix)) :: caseList)
      else
        let matrix := matrix.map fun (ps, a) => (ps.swap 0 index, a)
        compile signatures (occurrences.swap 0 index) matrix
where
  headConstructors : Pattern → HashSet (String × Nat)
    | Pattern.wildcard         => HashSet.empty
    | Pattern.constructor c ps => HashSet.empty.insert (c, ps.length)
    | Pattern.or q₁ q₂         => HashSet.union (headConstructors q₁) (headConstructors q₂)

---

def nil := Pattern.constructor "nil" []
def cons p₁ p₂ := Pattern.constructor "cons" [p₁, p₂]
def __ := Pattern.wildcard

#eval specialize "cons" 2
  [
    ([nil,        __        ], 1),
    ([__,         nil       ], 2),
    ([cons __ __, cons __ __], 3)
  ]

#eval specialize "nil" 0
  [
    ([nil,        __        ], 1),
    ([__,         nil       ], 2),
    ([cons __ __, cons __ __], 3)
  ]

#eval default
  [
    ([nil, __ ], 1),
    ([__,  nil], 2),
    ([__,  __ ], 3)
  ]

#eval compile [2, 2] [[0], [1]]
  [
    ([nil,        __        ], 1),
    ([__,         nil       ], 2),
    ([cons __ __, cons __ __], 3)
  ]

#eval compile [2, 2] [[1], [0]]
  [
    ([__,         nil       ], 1),
    ([nil,        __        ], 2),
    ([cons __ __, cons __ __], 3)
  ]

#eval compile [2, 2] [[0], [1]]
  [
    ([cons __ __, __        ], 1),
    ([__,         cons __ __], 2),
    ([nil,        nil       ], 3)
  ]

#eval compile [2, 2] [[0], [1]]
  [
    ([cons __ (cons __ (cons __ __)), __ ], 1),
    ([__,                             nil], 2),
    ([__,                             __ ], 3)
  ]

#eval compile [2] [[0]]
  [
    ([nil], 1)
  ]
