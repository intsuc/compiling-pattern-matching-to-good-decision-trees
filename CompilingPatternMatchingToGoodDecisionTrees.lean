import Std.Data.HashSet

open Std

inductive Value where
  | constructor : String → List Value → Value
  deriving Inhabited

inductive Pattern where
  | wildcard    : Pattern
  | constructor : String → List Pattern → Pattern
  | or          : Pattern → Pattern → Pattern
  deriving Inhabited

abbrev ClauseRow (α : Type) := List Pattern × α

abbrev ClauseMatrix (α : Type) := List (ClauseRow α)

abbrev Occurrence := List Nat

mutual
  inductive DecisionTree (α : Type) where
    | leaf   : α → DecisionTree α
    | switch : Occurrence → CaseList α → DecisionTree α
    deriving Inhabited

  inductive CaseList (α : Type) where
    | mk : List (String × DecisionTree α) → CaseList α
end

def Pattern.isWildcard : Pattern → Bool
  | Pattern.wildcard => true
  | _                => false

def List.swap [Inhabited α] (as : List α) (i₁ i₂ : Nat) : List α :=
  as |>.set i₁ (as.get! i₂) |>.set i₂ (as.get! i₁)

def HashSet.union [BEq α] [Hashable α] (m₁ m₂ : HashSet α) : HashSet α :=
  HashSet.empty |>.fold (·.insert) m₁ |>.fold (·.insert) m₂

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
          DecisionTree.switch o (CaseList.mk caseList)
        else
          DecisionTree.switch o (CaseList.mk (("_", ← compile signatures os (default matrix)) :: caseList))
      else
        let matrix := matrix.map fun (ps, a) => (ps.swap 0 index, a)
        compile signatures (occurrences.swap 0 index) matrix
where
  headConstructors : Pattern → HashSet (String × Nat)
    | Pattern.wildcard         => HashSet.empty
    | Pattern.constructor c ps => HashSet.empty.insert (c, ps.length)
    | Pattern.or q₁ q₂         => HashSet.union (headConstructors q₁) (headConstructors q₂)
