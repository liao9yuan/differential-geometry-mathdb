import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Reparametrization

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open _root_.MeasureTheory
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

open _root_.Submission.DifferentialGeometry.Geometry.Curvature

universe u uE uH

section

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
variable {D : RealTimeInterval}

noncomputable def lRegularizedSpeedSq
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (alpha : Real → M) (s : Real) : Real :=
  (S.base.metric (T - s ^ 2)).inner (alpha s)
    (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedSpeedSq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedSpeedSq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedSpeedSq ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedSpeedSq

noncomputable def lRegularizedLagrangian
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (alpha : Real → M) (s : Real) : Real :=
  let g := S.base.metric (T - s ^ 2)
  let A := lVelocity (I := I) alpha s
  (1 / 2 : Real) * g.inner (alpha s) A A +
    2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha s)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedLagrangian then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedLagrangian"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedLagrangian ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedLagrangian

noncomputable def lRegularizedAction
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (alpha : Real → M) (a b : Real) : Real :=
  ∫ s in a..b, lRegularizedLagrangian S T alpha s

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction

end

end DifferentialGeometry.PDE.RicciFlow.Perelman
