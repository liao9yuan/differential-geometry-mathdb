import Submission.DifferentialGeometry.Geometry.Coordinates.MetricCompatibility.Covariant

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



set_option autoImplicit false

namespace DifferentialGeometry.Tensor.Coordinates

noncomputable section

open _root_.Bundle _root_.Submission.Bundle

open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section Components

variable {Idx : Type*} [Fintype Idx]
variable {u : Set M}

def metricCovDerivForMetricCompInFrame
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M) (d a b : Idx) : Real :=
  mvfderiv (I := I)
      (fun y : M => metricCompForMetricInFrame (I := I) g frame y a b)
      x (frame d x) -
    (∑ p : Idx,
      christoffelSymbolInFrame cov frame hframe x d a p *
        metricCompForMetricInFrame (I := I) g frame x p b) -
    (∑ p : Idx,
      christoffelSymbolInFrame cov frame hframe x d b p *
        metricCompForMetricInFrame (I := I) g frame x a p)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.metricCovDerivForMetricCompInFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.metricCovDerivForMetricCompInFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.metricCovDerivForMetricCompInFrame ``Submission.DifferentialGeometry.Tensor.Coordinates.metricCovDerivForMetricCompInFrame

def metricCovDeriv2ForMetricCompInFrame
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M) (d a b c : Idx) : Real :=
  mvfderiv (I := I)
      (fun y : M =>
        metricCovDerivForMetricCompInFrame
          (I := I) g cov frame hframe y a b c)
      x (frame d x) -
    (∑ p : Idx,
      christoffelSymbolInFrame cov frame hframe x d a p *
        metricCovDerivForMetricCompInFrame
          (I := I) g cov frame hframe x p b c) -
    (∑ p : Idx,
      christoffelSymbolInFrame cov frame hframe x d b p *
        metricCovDerivForMetricCompInFrame
          (I := I) g cov frame hframe x a p c) -
    (∑ p : Idx,
      christoffelSymbolInFrame cov frame hframe x d c p *
        metricCovDerivForMetricCompInFrame
          (I := I) g cov frame hframe x a b p)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.metricCovDeriv2ForMetricCompInFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.metricCovDeriv2ForMetricCompInFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.metricCovDeriv2ForMetricCompInFrame ``Submission.DifferentialGeometry.Tensor.Coordinates.metricCovDeriv2ForMetricCompInFrame

def metricCovDeriv3ForMetricCompInFrame
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M) (m d a b c : Idx) : Real :=
  mvfderiv (I := I)
      (fun y : M =>
        metricCovDeriv2ForMetricCompInFrame
          (I := I) g cov frame hframe y d a b c)
      x (frame m x) -
    (∑ p : Idx,
      christoffelSymbolInFrame cov frame hframe x m d p *
        metricCovDeriv2ForMetricCompInFrame
          (I := I) g cov frame hframe x p a b c) -
    (∑ p : Idx,
      christoffelSymbolInFrame cov frame hframe x m a p *
        metricCovDeriv2ForMetricCompInFrame
          (I := I) g cov frame hframe x d p b c) -
    (∑ p : Idx,
      christoffelSymbolInFrame cov frame hframe x m b p *
        metricCovDeriv2ForMetricCompInFrame
          (I := I) g cov frame hframe x d a p c) -
    (∑ p : Idx,
      christoffelSymbolInFrame cov frame hframe x m c p *
        metricCovDeriv2ForMetricCompInFrame
          (I := I) g cov frame hframe x d a b p)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.metricCovDeriv3ForMetricCompInFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.metricCovDeriv3ForMetricCompInFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.metricCovDeriv3ForMetricCompInFrame ``Submission.DifferentialGeometry.Tensor.Coordinates.metricCovDeriv3ForMetricCompInFrame

end Components

end

end DifferentialGeometry.Tensor.Coordinates
