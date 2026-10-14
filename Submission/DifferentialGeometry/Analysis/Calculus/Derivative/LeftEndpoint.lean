import Mathlib.Analysis.Calculus.Deriv.Slope

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


set_option autoImplicit false
open _root_.Filter _root_.Set
open scoped _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood


theorem hasDerivWithinAt_left_of_mem_nhdsLE
    {f : ℝ → ℝ} {J : Set ℝ} {t : ℝ}
    (hf : DifferentiableWithinAt ℝ f J t) (hJ : J ∈ 𝓝[≤] t) :
    HasDerivWithinAt f (derivWithin f (_root_.Set.Iic t) t) J t := by
  have hleft : HasDerivWithinAt f (derivWithin f J t) (_root_.Set.Iic t) t :=
    hf.hasDerivWithinAt.mono_of_mem_nhdsWithin hJ
  rw [hleft.derivWithin (uniqueDiffWithinAt_Iic t)]
  exact hf.hasDerivWithinAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.hasDerivWithinAt_left_of_mem_nhdsLE then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.hasDerivWithinAt_left_of_mem_nhdsLE"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.hasDerivWithinAt_left_of_mem_nhdsLE ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.hasDerivWithinAt_left_of_mem_nhdsLE

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
