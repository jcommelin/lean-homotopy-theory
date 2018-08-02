import categories.category
import categories.opposites
import categories.functor

universe u

open categories categories.opposites categories.functor

section

parameters (C : Type u) [cat : category C]

include cat

definition op_op : C ↝ ((Cᵒᵖ)ᵒᵖ) :=
⟨λ X, X,
 λ X Y f, f,
 by obviously,
 by obviously⟩

definition op_op.inv : ((Cᵒᵖ)ᵒᵖ) ↝ C :=
⟨λ X, X,
 λ X Y f, f,
 by obviously,
 by obviously⟩

lemma comp₁ : op_op ⋙ op_op.inv = IdentityFunctor C := rfl
lemma comp₂ : op_op.inv ⋙ op_op = IdentityFunctor C := rfl

lemma op_op' : @opposites.Opposite C (@opposites.Opposite C cat) = cat :=
begin
  tactic.unfreeze_local_instances,
  cases cat,
  dsimp [opposites.Opposite],
  congr
end

end

