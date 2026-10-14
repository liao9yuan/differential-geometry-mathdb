import Submission.DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties
import Submission.DifferentialGeometry.Analysis.Integration.L2.Basic
import Submission.DifferentialGeometry.Geometry.Metric.PointwiseInner.Defs
import Submission.DifferentialGeometry.Geometry.Metric.PointwiseInner.DualMetric
import Submission.DifferentialGeometry.Geometry.Metric.PointwiseInner.Algebra
import Submission.DifferentialGeometry.Tensor.RSTensor.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Analysis.Real.Sqrt

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators _root_.Matrix

namespace DifferentialGeometry
namespace Integral
namespace L2

open _root_.Submission.DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance _root_.Submission.DifferentialGeometry.Integral.L2.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.L2.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.L2.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.L2.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.L2.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.L2.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.L2.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.L2.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.L2.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.L2.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.L2.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.L2.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

noncomputable def tensorL2Inner
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : M → TensorRSModel r s ℝ E) : ℝ :=
  ∫ x, tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x)
    ∂(riemannianVolumeMeasure (I := I) (M := M) g)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.tensorL2Inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.tensorL2Inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.tensorL2Inner ``Submission.DifferentialGeometry.Integral.L2.tensorL2Inner

def MemL2
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : M → TensorRSModel r s ℝ E) : Prop :=
  MeasureTheory.Integrable
    (fun x => tensorInnerPointwise (I := I) (M := M) g r s x (S x) (S x))
    (riemannianVolumeMeasure (I := I) (M := M) g)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.MemL2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.MemL2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.MemL2 ``Submission.DifferentialGeometry.Integral.L2.MemL2


lemma MemL2.integrable_inner_self
    [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {S : M → TensorRSModel r s ℝ E} (hS : MemL2 (I := I) (M := M) g r s S) :
    MeasureTheory.Integrable
      (fun x => tensorInnerPointwise (I := I) (M := M) g r s x (S x) (S x))
      (riemannianVolumeMeasure (I := I) (M := M) g) := hS

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Integral.L2.MemL2
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.MemL2.integrable_inner_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.MemL2.integrable_inner_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.MemL2.integrable_inner_self ``Submission.DifferentialGeometry.Integral.L2.MemL2.integrable_inner_self


theorem MemL2.zero
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    MemL2 (I := I) (M := M) g r s (fun _ : M => (0 : TensorRSModel r s ℝ E)) := by
  unfold MemL2
  have hzero :
      (fun x : M => tensorInnerPointwise (I := I) (M := M) g r s x
          ((fun _ : M => (0 : TensorRSModel r s ℝ E)) x)
          ((fun _ : M => (0 : TensorRSModel r s ℝ E)) x))
        = (fun _ : M => (0 : ℝ)) := by
    funext x
    exact tensorInnerPointwise_zero_left (I := I) (M := M) g r s x 0
  rw [hzero]
  exact MeasureTheory.integrable_zero M ℝ
    (riemannianVolumeMeasure (I := I) (M := M) g)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.MemL2.zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.MemL2.zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.MemL2.zero ``Submission.DifferentialGeometry.Integral.L2.MemL2.zero

noncomputable def tensorL2Norm
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : M → TensorRSModel r s ℝ E) : ℝ :=
  Real.sqrt (tensorL2Inner (I := I) (M := M) g r s S S)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.tensorL2Norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.tensorL2Norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.tensorL2Norm ``Submission.DifferentialGeometry.Integral.L2.tensorL2Norm


lemma tensorL2Norm_def
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : M → TensorRSModel r s ℝ E) :
    tensorL2Norm (I := I) (M := M) g r s S =
      Real.sqrt (tensorL2Inner (I := I) (M := M) g r s S S) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.tensorL2Norm_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.tensorL2Norm_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.tensorL2Norm_def ``Submission.DifferentialGeometry.Integral.L2.tensorL2Norm_def


theorem tensorL2Norm_nonneg
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : M → TensorRSModel r s ℝ E) :
    0 ≤ tensorL2Norm (I := I) (M := M) g r s S :=
  Real.sqrt_nonneg _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.tensorL2Norm_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.tensorL2Norm_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.tensorL2Norm_nonneg ``Submission.DifferentialGeometry.Integral.L2.tensorL2Norm_nonneg

end L2
end Integral
end DifferentialGeometry

end
