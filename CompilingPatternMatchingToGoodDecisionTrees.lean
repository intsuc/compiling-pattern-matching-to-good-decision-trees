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
    open Std in let rec f
      | Pattern.wildcard         => "_"
      | Pattern.constructor c [] => c
      | Pattern.constructor c ps => s!"{c}({Format.joinSep (ps.map f) ", "})"
      | Pattern.or p₁ p₂         => s!"{f p₁} | {f p₂}"
    f

abbrev PatternRow := List Pattern
abbrev PatternMatrix := List PatternRow

abbrev ClauseRow (α : Type) [Inhabited α] := List Pattern × α
abbrev ClauseMatrix (α : Type) [Inhabited α] := List (ClauseRow α)

partial def specialization [Inhabited α] (constructor : String) (arity : Nat) : ClauseMatrix α → ClauseMatrix α :=
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

partial def default [Inhabited α] : ClauseMatrix α → ClauseMatrix α :=
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

inductive DecisionTree (α : Type) where
  | leaf   : α → DecisionTree α
  | fail   : DecisionTree α
  | switch : List (String × DecisionTree α) → DecisionTree α
  | swap   : Nat → DecisionTree α → DecisionTree α
  deriving Inhabited

partial instance [ToString α] : ToString (DecisionTree α) where
  toString :=
    open Std in let rec go
      | DecisionTree.leaf a   => s!"leaf({a})"
      | DecisionTree.fail     => "fail"
      | DecisionTree.switch l => s!"switch({Format.joinSep (l.map (fun (c, t) => s!"{c}:{go t}")) ", "})"
      | DecisionTree.swap i t => s!"swap_{i}({go t})"
    go

abbrev CaseList (α : Type) := List (String × DecisionTree α)

def List.swap [Inhabited α] (as : List α) (i₁ i₂ : Nat) : List α :=
  as |>.set i₁ (as.get! i₂) |>.set i₂ (as.get! i₁)

mutual
  partial def evaluation [Inhabited α] : List Value → DecisionTree α → α
    | _,                            DecisionTree.leaf a   => a
    | vs,                           DecisionTree.swap i t => evaluation (vs.swap 0 i) t
    | Value.constructor c ws :: vs, DecisionTree.switch l => let (c, t) := caseSelection c l
                                                             if c == "*" then evaluation vs t else evaluation (ws ++ vs) t
    | _,                            _                     => arbitrary

  partial def caseSelection (constructor : String) : CaseList α → (String × DecisionTree α)
    | [("*", t)]  => ("*", t)
    | (c, t) :: l => if constructor == c then (c, t) else caseSelection constructor l
    | _           => arbitrary
end

open Std

def HashSet.union [BEq α] [Hashable α] (m₁ m₂ : HashSet α) : HashSet α :=
  HashSet.empty |>.fold (·.insert) m₁ |>.fold (·.insert) m₂

partial def headConstructors : Pattern → HashSet (String × Nat)
  | Pattern.wildcard         => HashSet.empty
  | Pattern.constructor c ps => HashSet.empty.insert (c, ps.length)
  | Pattern.or q₁ q₂         => HashSet.union (headConstructors q₁) (headConstructors q₂)

def Pattern.isWildcard : Pattern → Bool
  | Pattern.wildcard => true
  | _                => false

partial def compilation [Inhabited α] (signatures : List Nat) : ClauseMatrix α → DecisionTree α
  | matrix@((ps, a) :: _) =>
    if ps.all (·.isWildcard) then DecisionTree.leaf a
    else
      let index := (List.range matrix.length) |>.find? (fun n => matrix.any fun (ps, _) => !(ps.get! n).isWildcard) |>.get!
      let column := matrix.map (·.1.get! index)
      if index == 0 then
        let headConstructors := column |>.map headConstructors |>.foldl HashSet.union HashSet.empty |>.toList
        let caseList : CaseList α := headConstructors.map fun (c, a) => (c, compilation signatures (specialization c a matrix))
        let signature := signatures.head!
        DecisionTree.switch ((if caseList.length == signature then [] else [("*", compilation signatures (default matrix))]) ++ caseList)
      else
        let matrix := matrix.map fun (ps, a) => (ps.swap 0 index, a)
        DecisionTree.swap index (compilation signatures matrix)
  | _ => DecisionTree.fail

#eval
  let nil := Pattern.constructor "nil" []
  let cons p₁ p₂ := Pattern.constructor "cons" [p₁, p₂]
  let __ := Pattern.wildcard
  (
    compilation [2, 2]
      [
        ([nil,        __        ], 1),
        ([__,         nil       ], 2),
        ([cons __ __, cons __ __], 3)
      ],
    compilation [2, 2]
      [
        ([__,         nil       ], 1),
        ([nil,        __        ], 2),
        ([cons __ __, cons __ __], 3)
      ],
    compilation [2, 2]
      [
        ([cons __ __, __        ], 1),
        ([__,         cons __ __], 2),
        ([nil,        nil       ], 3)
      ]
  )
