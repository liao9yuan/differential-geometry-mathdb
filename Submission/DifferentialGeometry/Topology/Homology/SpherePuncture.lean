import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SpherePuncture

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.ContinuousMap _root_.Set _root_.Metric
open scoped _root_.Topology

universe u

namespace DifferentialGeometry.Topology

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem integralSingularHomology_subsingleton_of_punctured_sphere (n : ℕ) (hn : n ≠ 0)
    (v : _root_.Metric.sphere (0 : E) 1) :
    Subsingleton (integralSingularHomology n ({v}ᶜ : Set (_root_.Metric.sphere (0 : E) 1))) := by
  let := spherePuncture_contractible v
  exact integralSingularHomology_subsingleton_of_contractible n hn _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularHomology_subsingleton_of_punctured_sphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularHomology_subsingleton_of_punctured_sphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularHomology_subsingleton_of_punctured_sphere ``Submission.DifferentialGeometry.Topology.integralSingularHomology_subsingleton_of_punctured_sphere

end DifferentialGeometry.Topology
