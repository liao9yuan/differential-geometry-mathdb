import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.GoodPointDerivatives

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

universe u uE uH

open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]

theorem localShiUniformConstant (I : ModelWithCorners ℝ E H) [I.Boundaryless] :
    LocalShiUniformConstant.{u, uE, uH} I :=
  fun m _ _ _ hT hK hR => shi_local_all_orders_uniform_constant I m hT hK hR

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.localShiUniformConstant then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.localShiUniformConstant"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.localShiUniformConstant ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.localShiUniformConstant

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
