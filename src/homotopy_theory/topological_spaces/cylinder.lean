import analysis.real
import categories.adjunctions
import tactic.norm_num

import homotopy_theory.formal.cylinder.definitions
import .category
import .exponentiable

noncomputable theory

open categories
open homotopy_theory.cylinder

namespace homotopy_theory.topological_spaces

-- TODO: Universes. We may eventually want to do homotopy theory in
-- Top.{u} for arbitrary u. The type ℝ and its associated structures
-- live only in Type 0, and transferring all that structure across
-- `ulift` sounds tedious. Maybe it'd be better to think of Top.{u} as
-- tensored over Top.{0} and use this structure to define IX = X × I
-- rather than trying to transfer the object I to Top.{u} (and using
-- the product in Top.{u} to define IX).
--
-- For now, we stick to Top.{0}.
local notation `Top` := Top.{0}

-- The standard unit interval [0,1].
def I01 : Top := Top.mk_ob { t : ℝ // 0 ≤ t ∧ t ≤ 1 }

instance : has_zero I01 := ⟨⟨0, by norm_num, by norm_num⟩⟩
instance : has_one I01 := ⟨⟨1, by norm_num, by norm_num⟩⟩

instance : t2_space I01 :=
by dsimp [I01, Top.mk_ob]; apply_instance

instance : locally_compact_space I01 :=
locally_compact_of_compact (compactness_intrinsic compact_ivl)

-- The endpoint of [0,1] corresponding to an abstract endpoint.
def I01_of_endpoint : endpoint → I01
| 0 := 0
| 1 := 1

-- The "time-reversal" function on [0,1].
def I01.v : I01 ⟶ I01 :=
Top.mk_hom
  (λ t, ⟨1 - t.val, sub_nonneg_of_le t.property.right, sub_le_self 1 t.property.left⟩)
  (by continuity)

local attribute [extensionality] natural_transformation.NaturalTransformations_componentwise_equal

instance : has_cylinder_with_involution Top :=
{ I := -×I01,
  i := λ ε, Top.prod_pt_trans (I01_of_endpoint ε),
  p := Top.pr₁_trans,
  pi := assume ε, rfl,

  v := Top.product_by_trans I01.v,
  vi := assume ε, by cases ε; refl,
  vv := begin
    ext X p, rcases p with ⟨x, t, h⟩,
    change (x, subtype.mk (1 - (1 - t)) _) = (x, subtype.mk t _),
    simp
  end,
  pv := rfl }

instance : cylinder_has_interchange.{1 0} Top :=
{ T := { components := λ X, Top.mk_hom (λ q, ((q.1.1, q.2), q.1.2)) (by continuity) },
  Ti := by intros ε X; ext p; refl,
  TIi := by intros ε X; ext p; cases p; refl }

instance I.has_right_adjoint : has_right_adjoint (I : Top ↝ Top) :=
by unfold I; apply_instance

end homotopy_theory.topological_spaces
