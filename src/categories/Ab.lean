import categories.category

open categories

universe u

structure Ab : Type (u+1) :=
(carrier : Type u)
(group : add_comm_group carrier)

namespace Ab

local notation `Ab` := Ab.{u}

instance : has_coe_to_sort Ab :=
{ S := Type u, coe := λ A, A.carrier }

instance (A : Ab) : add_comm_group A.carrier := A.group

section -- for_mathlib

variables {A : Type*} {B : Type*} [add_group A] [add_group B]

@[class]
def is_add_group_hom (f : A → B) : Prop := @is_group_hom (multiplicative A) (multiplicative B) _ _ f

end -- for_mathlib

def add_group_hom (A : Ab) (B: Ab) := {f : A → B // is_add_group_hom f }

instance {A B : Ab} : has_coe_to_fun (add_group_hom A B) :=
{ F := λ _, A → B, coe := λ f, f.val }

instance {A B : Ab} (f : add_group_hom A B) : is_add_group_hom f := f.property

instance : category Ab :=
{ Hom      := add_group_hom,
  identity := λ A, ⟨id, is_group_hom.id⟩,
  compose  := λ A B C f g, ⟨g.val ∘ f.val, @is_group_hom.comp _ _ _ _ _ f.property _ _ _ g.property⟩ }

end «Ab»
