import categories.category

open categories

universe u

structure Ring : Type (u+1) :=
(carrier : Type u)
(is_a_ring : ring carrier)

namespace Ring

local notation `Ring` := Ring.{u}

instance (R : Ring) : ring R.carrier := R.is_a_ring

instance : has_coe_to_sort Ring :=
{ S := Type u, coe := λ R, R.carrier }

def ring_hom (R S : Ring) := {f : R → S // is_ring_hom f}

instance {R S : Ring} : has_coe_to_fun (ring_hom R S) :=
{ F := λ _, R → S, coe := λ f, f.val }

instance {R S : Ring} (f : ring_hom R S) : is_ring_hom f.val := f.property

instance : category Ring :=
{ Hom := ring_hom,
  identity := λ R, ⟨id, is_ring_hom.id⟩,
  compose := λ _ _ _ f g, ⟨g.val ∘ f.val, is_ring_hom.comp _ _⟩ }

end «Ring»
