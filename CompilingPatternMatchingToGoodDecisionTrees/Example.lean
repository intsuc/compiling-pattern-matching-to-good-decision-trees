import CompilingPatternMatchingToGoodDecisionTrees
import CompilingPatternMatchingToGoodDecisionTrees.ToString

def unit := Pattern.constructor "unit" []

def nil := Pattern.constructor "nil" []

def cons p₁ p₂ := Pattern.constructor "cons" [p₁, p₂]

def signatures := [
  ("unit", 1),
  ("nil", 2),
  ("cons", 2)
]

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

#eval compile signatures [[0], [1]]
  [
    ([nil,        __        ], 1),
    ([__,         nil       ], 2),
    ([cons __ __, cons __ __], 3)
  ]

#eval compile signatures [[1], [0]]
  [
    ([__,         nil       ], 1),
    ([nil,        __        ], 2),
    ([cons __ __, cons __ __], 3)
  ]

#eval compile signatures [[0], [1]]
  [
    ([cons __ __, __        ], 1),
    ([__,         cons __ __], 2),
    ([nil,        nil       ], 3)
  ]

#eval compile signatures [[0], [1]]
  [
    ([cons __ (cons __ (cons __ __)), __ ], 1),
    ([__,                             nil], 2),
    ([__,                             __ ], 3)
  ]

#eval compile signatures [[0]]
  [
    ([nil], 1)
  ]

#eval compile signatures [[0]]
  [
    ([unit], 1)
  ]

#eval compile signatures [[0], [1]]
  [
    ([unit, unit], 1)
  ]

#eval compile signatures [[0], [1]]
  [
    ([unit, nil       ], 1),
    ([unit, cons __ __], 2)
  ]

#eval compile signatures [[0], [1]]
  [
    ([nil       , unit], 1),
    ([cons __ __, unit], 2)
  ]
