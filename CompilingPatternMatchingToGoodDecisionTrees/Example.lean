import CompilingPatternMatchingToGoodDecisionTrees
import CompilingPatternMatchingToGoodDecisionTrees.ToString

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
