import analysis.topology.topological_structures
import tidy.tidy

attribute [applicable]
  continuous_id
  continuous_subtype_val
  continuous_fst continuous_snd
  continuous_inl continuous_inr continuous_sum_rec
  continuous_top continuous_bot

-- Applying continuous.comp is not always a good idea, so we have some
-- extra logic here to try to avoid bad cases.
--
-- * If the function we're trying to prove is actually constant, and
-- that constant is a function application `f z`, then continuous.comp
-- would produce new goals `continuous f`, `continuous (λ _, z)`,
-- which is silly. We avoid this by failing if we could apply
-- continuous_const.
--
-- * continuous.comp will always succeed on `continuous (λ x, f x)`
-- and produce new goals `continuous (λ x, x)`, `continuous f`. We
-- detect this by failing if a new goal can be closed by applying
-- continuous_id.
@[tidy] meta def apply_continuous.comp :=
`[fail_if_success { exact continuous_const };
  refine continuous.comp _ _;
  fail_if_success { exact continuous_id }]

-- `apply` is often not smart enough to guess how many auxiliary goals
-- to add when that number is not 1. We add tidy tactics with the
-- correct number of goals specified explicitly.
@[tidy] meta def apply_continuous_subtype_mk := `[refine continuous_subtype_mk _ _]
@[tidy] meta def apply_continuous.prod_mk := `[refine continuous.prod_mk _ _]
@[tidy] meta def apply_continuous_min := `[refine continuous_min _ _]
@[tidy] meta def apply_continuous_max := `[refine continuous_max _ _]
@[tidy] meta def apply_continuous_neg' := `[exact continuous_neg']
@[tidy] meta def apply_continuous_add := `[refine continuous_add _ _]
@[tidy] meta def apply_continuous_sub := `[refine continuous_sub _ _]
@[tidy] meta def apply_continuous_mul := `[refine continuous_mul _ _]
@[tidy] meta def apply_continuous_const := `[exact continuous_const]


open tactic

meta def continuity_tactics : list (tactic string) :=
[
  applicable                             >>= λ n, pure ("apply " ++ n.to_string),
  automatic_induction,
  tactic.interactive.apply_assumption    >> pure "apply_assumption",
  run_tidy_tactics
]

meta def continuity (cfg : tidy_cfg := {}) : tactic unit :=
let tactics := continuity_tactics ++ cfg.extra_tactics in
do
  results ← chain tactics cfg.to_chain_cfg,
  try tactic.interactive.resetI,
  when cfg.trace_result $
    interaction_monad.trace ("---\n" ++ (",\n".intercalate results) ++ "\n---")

-- For use with auto_param
meta def continuity' : tactic unit := continuity
