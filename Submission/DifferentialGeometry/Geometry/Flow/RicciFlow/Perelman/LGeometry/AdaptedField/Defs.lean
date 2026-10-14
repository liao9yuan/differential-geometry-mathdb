import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Variation.MovingMetric
import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Identities.Ricci

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open scoped _root_.Manifold _root_.ContDiff

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
variable {D : RealTimeInterval}

def IsLAdaptedAt
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (alpha : Real → M) (P : ∀ s, TangentSpace I (alpha s))
    (s : Real) : Prop :=
  covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) alpha P s =
    (-2 * s) •
      ricciSharp (I := I) (S.base.metric (T - s ^ 2)) (alpha s) (P s)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.IsLAdaptedAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.IsLAdaptedAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.IsLAdaptedAt ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.IsLAdaptedAt

def IsLAdapted
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (alpha : Real → M) (P : ∀ s, TangentSpace I (alpha s))
    (J : Set Real) : Prop :=
  ∀ s ∈ J, IsLAdaptedAt S T alpha P s

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.IsLAdapted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.IsLAdapted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.IsLAdapted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.IsLAdapted

end DifferentialGeometry.PDE.RicciFlow.Perelman
