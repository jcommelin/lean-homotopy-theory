import categories.category
import categories.functor_categories

import categories.poset
import categories.Ab

open categories

universe u

namespace chain_complex

def differential (K : ℤ ↝ Ab) (i : ℤ) := K &> (begin dsimp only [category.Hom], refine plift.up _, simp end : i ⟶ (i+1))

def is_complex (K : ℤ ↝ Ab) : Prop := ∀ i, (differential K i ≫ differential K (i+1)) = 0

end chain_complex

def Ch := {K : ℤ ↝ Ab // chain_complex.is_complex K}

instance : category Ch :=
{ Hom := λ K K', K.val ⟶ K'.val,
  identity := λ K, 𝟙 K.val,
  compose := λ _ _ _ f g, f ⊟ g }
