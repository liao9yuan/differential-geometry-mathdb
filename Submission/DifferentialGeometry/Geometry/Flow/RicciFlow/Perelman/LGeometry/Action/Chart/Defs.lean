import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.H1.Basic
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Defs
import Submission.DifferentialGeometry.Geometry.Operator.Family.Gram.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.ContDiff _root_.Manifold

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
variable {D : RealTimeInterval}

noncomputable def lChartLagrangian
    (S : SolutionOn (I := I) (M := M) D) (T a : Real) (p : M)
    {L : Real} (u : timeH1 E L) (r : Real) : Real :=
  _root_.Inner.inner Real
    (((1 / 2 : Real) • chartGramOp (I := I) S.family p
      (T - (a + r) ^ 2, u.toFun r)) (u.deriv r))
    (u.deriv r) +
  2 * (a + r) ^ 2 * S.scalar (T - (a + r) ^ 2)
    ((extChartAt I p).symm (u.toFun r))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lChartLagrangian then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lChartLagrangian"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lChartLagrangian ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lChartLagrangian

noncomputable def lChartAction
    (S : SolutionOn (I := I) (M := M) D) (T a : Real) (p : M)
    {L : Real} (u : timeH1 E L) : Real :=
  ∫ r in (0 : Real)..L, lChartLagrangian S T a p u r

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lChartAction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lChartAction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lChartAction ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lChartAction

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
