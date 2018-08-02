import algebra.module

import categories.category
import categories.colimits
import categories.Ring

open categories

universes u v

structure LeftMod_ (R : Ring.{v}) : Type (max (u+1) v) :=
(carrier : Type u)
(is_a_module : module R carrier)

namespace LeftMod_

variables {R : Ring}

local notation R`-Mod` : max := LeftMod_.{u} R

instance (M : R-Mod) : module R M.carrier := M.is_a_module

instance : has_coe_to_sort (R-Mod) :=
{ S := Type u, coe := λ M, M.carrier }

def module_hom (M N : R-Mod) := {f : M → N // is_linear_map f}

instance {M N : R-Mod} : has_coe_to_fun (module_hom M N) :=
{ F := λ _, M → N, coe := λ f, f.val }

-- instance {M N : R-Mod} (f : module_hom M N) : is_linear_map f.val := f.property
-- fails: is_linear_map is not a class

instance foo : category (R-Mod) :=
{ Hom := module_hom,
  identity := λ R, ⟨id, is_linear_map.id⟩,
  compose := λ _ _ _ f g, ⟨g.val ∘ f.val, is_linear_map.comp g.property f.property⟩ }

section zm

open punit

def zero_module : R-Mod :=
{ carrier := punit,
  is_a_module :=
  by refine
  { smul := λ _ _, star,
    zero := star,
    add  := λ _ _, star,
    neg  := λ _, star,
    .. }; finish }

end zm

instance zero_module_is_initial : @has_initial_object (R-Mod) LeftMod_.foo :=
{ initial_object :=
{ ob := zero_module,
  is_initial_object :=
  begin
    constructor,
    intro M,
    constructor,
    refl,
    constructor,
    swap 3,
    intro f, exact trivial,
    intro triv,
    constructor,
    swap 2,
    intro z, exact 0,
    exact is_linear_map.map_zero,
    tidy,
    dsimp [function.left_inverse],
    intro f,
    apply subtype.eq,
    funext x,
    simp,
    tidy,
    sorry
  end
} }

end LeftMod_
