import CompilingPatternMatchingToGoodDecisionTrees

open Std.Format

partial instance : ToString Value where
  toString :=
    let rec go
      | Value.constructor c [] => c
      | Value.constructor c vs => s!"{c}({joinSep (vs.map go) ", "})"
    go

partial instance : ToString Pattern where
  toString :=
    let rec go
      | Pattern.wildcard         => "_"
      | Pattern.constructor c [] => c
      | Pattern.constructor c ps => s!"{c}({joinSep (ps.map go) ", "})"
      | Pattern.or p₁ p₂         => s!"{go p₁} | {go p₂}"
    go

partial instance [ToString α] : ToString (DecisionTree α) where
  toString :=
    let rec go
      | DecisionTree.leaf a                   => s!"{a}"
      | DecisionTree.switch o (CaseList.mk l) => s!"switch {joinSep o "."} {indentD $ joinSep (l.reverse.map (fun (c, t) => s!"{c} => {go t}")) "\n"}"
    go
