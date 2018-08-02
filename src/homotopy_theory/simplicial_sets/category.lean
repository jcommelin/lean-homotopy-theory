import categories.category
import categories.functor_categories
import categories.types
import categories.opposites

import categories.simplex

open categories

local notation `Δ` := simplex_category
local notation `Set` := Type.{0}

def sSet := Δᵒᵖ ↝ Set
