import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UniformSpace.UniformConvergence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


open _root_.Filter _root_.Set

open _root_.TendstoUniformlyOn in
theorem TendstoUniformlyOn.comp_continuousAt_of_isCompact_image
    {A E F N : Type*} [UniformSpace E] [UniformSpace F]
    {K : Set A} {X : N → A → E} {v : A → E} {l : Filter N}
    (hX : TendstoUniformlyOn X v l K) (hK : IsCompact (v '' K))
    {g : E → F} (hg : ∀ y ∈ v '' K, ContinuousAt g y) :
    TendstoUniformlyOn (fun n x => g (X n x)) (fun x => g (v x)) l K := by
  intro V hV
  filter_upwards [hX _ (hK.uniformContinuousAt_of_continuousAt g hg hV)] with n hn x hx
  exact (hn x hx) (_root_.Set.mem_image_of_mem v hx)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.TendstoUniformlyOn
  let env ← Lean.getEnv
  if env.contains `TendstoUniformlyOn.comp_continuousAt_of_isCompact_image then
    throwError "Refusing to shadow existing declaration TendstoUniformlyOn.comp_continuousAt_of_isCompact_image"
  Lean.modifyEnv fun env => Lean.addAlias env `TendstoUniformlyOn.comp_continuousAt_of_isCompact_image ``Submission.TendstoUniformlyOn.comp_continuousAt_of_isCompact_image
