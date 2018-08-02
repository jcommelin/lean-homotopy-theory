import data.finsupp

import homotopy_theory.simplicial_sets.category

namespace sSet

universes u v w

variables {R : Type u} [ring R]
variables {M : Type v} [hrm: module R M]

include hrm
def C (X : sSet) : ℕ → Type _ := λ n, ((X +> n) →₀ M)

#print C

end sSet