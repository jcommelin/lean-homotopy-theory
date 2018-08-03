import algebra.module
import group_theory.subgroup

import categories.category
import categories.universal.instances
import categories.universal.kernels
import categories.Ring

open categories

universes u v

structure LeftMod_ (R : Ring.{v}) : Type (max (u+1) v) :=
(carrier : Type u)
(is_a_module : module R carrier)

namespace LeftMod_

variables {R : Ring}

local notation R`-Mod` : max := LeftMod_.{u} R

instance : has_coe_to_sort (R-Mod) :=
{ S := Type u, coe := λ M, M.carrier }

instance (M : R-Mod) : module R M := M.is_a_module

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

variable (R)

def zero_module : R-Mod :=
{ carrier := punit,
  is_a_module :=
  by refine
  { smul := λ _ _, star,
    zero := star,
    add  := λ _ _, star,
    neg  := λ _, star,
    .. }; finish }

variable {R}

lemma zero_is_star : (0 : (zero_module R)) = star := rfl

end zm

instance LeftMod__has_ZeroObject : @universal.has_ZeroObject (R-Mod) LeftMod_.foo :=
{ zero_object :=
{ zero_object := zero_module R,
  is_initial  := ⟨λ M : R-Mod, ⟨λ _, 0, is_linear_map.map_zero⟩,
  begin
    intros M f g,
    tidy,
    rw [← zero_is_star, is_linear_map.zero f_property, is_linear_map.zero g_property]
  end ⟩,
  is_terminal :=
  begin
    obviously'
  end
} }

instance LeftMod__has_BinaryProducts : @universal.has_BinaryProducts (R-Mod) LeftMod_.foo :=
{ binary_product := λ M N : R-Mod,
⟨ ⟨ ↥M × ↥N,
begin
  refine
  {
    smul := λ r p, (r • p.1, r • p.2),
    zero := (0, 0),
    add := λ p q, (p.1 + q.1, p.2 + q.2),
    neg := λ p, (-p.1, -p.2),
    ..
  }; try { simp }; intros; sorry
end
 ⟩,
  ⟨ prod.fst, by obviously ⟩,
  ⟨ prod.snd, by obviously ⟩,
  λ T f g, ⟨λ t, (f t, g t), sorry ⟩,
  sorry, sorry, sorry
  -- by obviously',  -- these work, but timeout
  -- by obviously,
  -- by obviously
⟩

}

-- instance LeftMod__has_Kernels : @universal.has_Kernels (R-Mod) LeftMod_.foo (by apply_instance) :=
-- { kernel := λ M N f,
-- ⟨ ⟨ f ⁻¹' {0}, sorry ⟩,
--   ⟨ subtype.val, sorry ⟩,
--   λ T k h, sorry,
--   sorry,
--   sorry,
--   by obviously
-- ⟩
-- }

end LeftMod_
