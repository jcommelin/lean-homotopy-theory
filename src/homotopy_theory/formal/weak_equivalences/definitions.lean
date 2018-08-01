import categories.category
import categories.replete

open categories
local notation f ` ∘ `:80 g:80 := g ≫ f

universes u v

namespace homotopy_theory.weak_equivalences

class has_weak_equivalences (C : Type u) [category C] :=
(is_weq : Π ⦃a b : C⦄, (a ⟶ b) → Prop)

def is_weq {C : Type u} [category C] [has_weak_equivalences C] ⦃a b : C⦄ (f : a ⟶ b) :=
has_weak_equivalences.is_weq f

-- TODO: should this be a Prop mix-in?
class category_with_weak_equivalences (C : Type u) [category.{u v} C]
  extends has_weak_equivalences C :=
[weq_replete_wide : replete_wide_subcategory.{u v} C is_weq]
(weq_of_comp_weq_left : ∀ ⦃a b c : C⦄ {f : a ⟶ b} {g : b ⟶ c},
  is_weq f → is_weq (g ∘ f) → is_weq g)
(weq_of_comp_weq_right : ∀ ⦃a b c : C⦄ {f : a ⟶ b} {g : b ⟶ c},
  is_weq g → is_weq (g ∘ f) → is_weq f)

instance (C : Type u) [category.{u v} C] [category_with_weak_equivalences C] :
  replete_wide_subcategory.{u v} C is_weq :=
category_with_weak_equivalences.weq_replete_wide C

section
variables {C : Type u} [cat : category.{u v} C] [category_with_weak_equivalences C]
include cat
lemma weq_id (a : C) : is_weq (𝟙 a) := mem_id a
lemma weq_comp {a b c : C} {f : a ⟶ b} {g : b ⟶ c} :
  is_weq f → is_weq g → is_weq (g ∘ f) := mem_comp
lemma weq_iso {a b : C} (i : a ≅ b) : is_weq (i : a ⟶ b) := mem_iso i
end

section isomorphisms
variables {C : Type u} [cat : category.{u v} C]
include cat

def is_iso ⦃a b : C⦄ (f : a ⟶ b) : Prop := ∃ i : a ≅ b, i.morphism = f

lemma iso_iso ⦃a b : C⦄ (i : a ≅ b) : is_iso i.morphism := ⟨i, rfl⟩
lemma iso_comp ⦃a b c : C⦄ {f : a ⟶ b} {g : b ⟶ c} :
  is_iso f → is_iso g → is_iso (g ∘ f) :=
assume ⟨i, hi⟩ ⟨j, hj⟩, ⟨i.trans j, by rw [←hi, ←hj]; refl⟩

lemma iso_of_comp_iso_left ⦃a b c : C⦄ {f : a ⟶ b} {g : b ⟶ c} :
  is_iso f → is_iso (g ∘ f) → is_iso g :=
assume ⟨i, hi⟩ ⟨j, hj⟩,
  ⟨i.symm.trans j, show j.morphism ∘ i.inverse = g, by rw [hj, ←hi]; simp⟩
lemma iso_of_comp_iso_right ⦃a b c : C⦄ {f : a ⟶ b} {g : b ⟶ c} :
  is_iso g → is_iso (g ∘ f) → is_iso f :=
assume ⟨i, hi⟩ ⟨j, hj⟩,
  ⟨j.trans i.symm, show i.inverse ∘ j.morphism = f, by rw [hj, ←hi]; simp⟩

instance is_iso.replete_wide_subcategory : replete_wide_subcategory.{u v} C is_iso :=
replete_wide_subcategory.mk' iso_iso iso_comp

def isomorphisms_as_weak_equivalences : category_with_weak_equivalences C :=
{ is_weq := is_iso,
  weq_of_comp_weq_left := iso_of_comp_iso_left,
  weq_of_comp_weq_right := iso_of_comp_iso_right }

end isomorphisms

section preimage
-- TODO: generalize to different universes?
variables {C D : Type u} [catC : category.{u v} C] [catD : category.{u v} D]
include catC catD
variables (F : C ↝ D)

def preimage_weq (weqD : has_weak_equivalences D) : has_weak_equivalences C :=
{ is_weq := λ a b f, is_weq (F &> f) }

instance preimage_weq.replete_wide_subcategory [weqD : category_with_weak_equivalences D] :
  replete_wide_subcategory.{u v} C (preimage_weq F weqD.to_has_weak_equivalences).is_weq :=
replete_wide_subcategory.mk'
    (λ a b i, weq_iso (F.onIsomorphisms i))
    (λ a b c f g hf hg, show is_weq (F &> (g ∘ f)),
      by rw F.functoriality; exact weq_comp hf hg)

def preimage_with_weak_equivalences [weqD : category_with_weak_equivalences D] :
  category_with_weak_equivalences C :=
{ to_has_weak_equivalences := preimage_weq F weqD.to_has_weak_equivalences,
  weq_of_comp_weq_left := λ a b c f g hf hgf, begin
    change is_weq (F &> (g ∘ f)) at hgf, rw F.functoriality at hgf,
    exact category_with_weak_equivalences.weq_of_comp_weq_left hf hgf
  end,
  weq_of_comp_weq_right := λ a b c f g hg hgf, begin
    change is_weq (F &> (g ∘ f)) at hgf, rw F.functoriality at hgf,
    exact category_with_weak_equivalences.weq_of_comp_weq_right hg hgf
  end }

end preimage

end homotopy_theory.weak_equivalences
