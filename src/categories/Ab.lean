import categories.category

open categories

universe u

structure Ab : Type (u+1) :=
(carrier : Type u)
(group : add_comm_group carrier)

section -- for_mathlib

section

variables {A : Type*} {B : Type*} [add_group A] [add_group B]

@[class]
def is_add_group_hom (f : A → B) : Prop := @is_group_hom (multiplicative A) (multiplicative B) _ _ f

instance add_group_map {T : Type*} {G : Type*} [add_group G] : add_group (T → G) :=
{ add := λ f g t, f t + g t,
  add_assoc := λ f g h, funext $ λ t, add_assoc _ _ _,
  zero := λ t, 0,
  add_zero := λ f, funext $ λ t, add_zero _,
  zero_add := λ f, funext $ λ t, zero_add _,
  neg := λ f t, -f t,
  add_left_neg := λ f, funext $ λ t, add_left_neg _ }

instance add_comm_group_map {T : Type*} {G : Type*} [add_comm_group G] : add_comm_group (T → G) :=
{ add_comm := λ f g, funext $ λ t, add_comm _ _,
  ..add_group_map }

end -- nameless section

section

def add_group_hom (A : Type*) (B : Type*) [add_group A] [add_group B] := {f : A → B // is_add_group_hom f }

instance add_comm_group_hom (A : Type*) (B : Type*) [add_group A] [add_comm_group B] : add_comm_group (add_group_hom A B) := sorry
-- we need additive subgroups once again, and I don't feel like copy-pasting them from the perfectoid project.

end -- nameless section

end -- for_mathlib

namespace Ab

local notation `Ab` := Ab.{u}

instance : has_coe_to_sort Ab :=
{ S := Type u, coe := λ A, A.carrier }

instance (A : Ab) : add_comm_group A.carrier := A.group

instance {A B : Ab} : has_coe_to_fun (add_group_hom A B) :=
{ F := λ _, A → B, coe := λ f, f.val }

instance {A B : Ab} (f : add_group_hom A B) : is_add_group_hom f := f.property

instance : category Ab :=
{ Hom      := λ A B, add_group_hom A B,
  identity := λ A, ⟨id, is_group_hom.id⟩,
  compose  := λ A B C f g, ⟨g.val ∘ f.val, @is_group_hom.comp _ _ _ _ _ f.property _ _ _ g.property⟩ }

end «Ab»
