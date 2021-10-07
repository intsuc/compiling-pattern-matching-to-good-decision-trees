import Std.Data.HashSet

def List.swap [Inhabited α] (as : List α) (i₁ i₂ : Nat) : List α :=
  as |>.set i₁ (as.get! i₂) |>.set i₂ (as.get! i₁)

open Std in def HashSet.union [BEq α] [Hashable α] (m₁ m₂ : HashSet α) : HashSet α :=
  HashSet.empty |>.fold (·.insert) m₁ |>.fold (·.insert) m₂
