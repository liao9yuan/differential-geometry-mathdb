import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChartComponent.ComponentSobolevBound
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Components.Defs
import Submission.DifferentialGeometry.Analysis.Integration.L2.SmoothSections.PreHilbert
import Submission.DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Integrability
import Submission.DifferentialGeometry.Geometry.Metric.PointwiseInner.Algebra
import Submission.DifferentialGeometry.Analysis.Integration.L2.Pairing.Defs
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.NNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem tensorChartComponentScalar_eLpNorm_two_lt_top
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    eLpNorm (tensorChartComponentScalar (I := I) (M := M) g r s S α Idx Jdx) 2
        (riemannianVolumeMeasure (I := I) (M := M) g) < ⊤ := by
  classical
  have hsmooth :=
    tensorChartComponentScalar_contMDiff (I := I) (M := M) g r s S α Idx Jdx
  have hcc :=
    tensorChartComponentScalar_hasCompactSupport
      (I := I) (M := M) g r s S α Idx Jdx
  have hcont : Continuous
      (tensorChartComponentScalar (I := I) (M := M) g r s S α Idx Jdx) :=
    hsmooth.continuous
  have : _root_.MeasureTheory.IsFiniteMeasureOnCompacts (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g
  have : _root_.MeasureTheory.IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  exact (hcont.memLp_of_hasCompactSupport
      (μ := riemannianVolumeMeasure (I := I) (M := M) g) (p := 2) hcc).eLpNorm_lt_top

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_eLpNorm_two_lt_top then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_eLpNorm_two_lt_top"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_eLpNorm_two_lt_top ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_eLpNorm_two_lt_top

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem tensorChartComponentScalar_eLpNorm_le_per_section
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm (tensorChartComponentScalar (I := I) (M := M)
            g r s S α Idx Jdx) 2
        (riemannianVolumeMeasure (I := I) (M := M) g) ≤
        ENNReal.ofReal C *
          (ENNReal.ofReal (tensorL2Norm (I := I) (M := M) g r s S.toFun) + 1) := by
  classical
  have hlt :=
    tensorChartComponentScalar_eLpNorm_two_lt_top
      (I := I) (M := M) g r s S α Idx Jdx
  have hne : _root_.MeasureTheory.eLpNorm (tensorChartComponentScalar (I := I) (M := M)
        g r s S α Idx Jdx) 2
      (riemannianVolumeMeasure (I := I) (M := M) g) ≠ ⊤ := hlt.ne
  set a : ℝ := (_root_.MeasureTheory.eLpNorm
      (tensorChartComponentScalar (I := I) (M := M) g r s S α Idx Jdx) 2
      (riemannianVolumeMeasure (I := I) (M := M) g)).toReal with ha_def
  have ha_nn : 0 ≤ a := ENNReal.toReal_nonneg
  refine ⟨a + 1, by linarith, ?_⟩
  have h_lhs_eq : _root_.MeasureTheory.eLpNorm
        (tensorChartComponentScalar (I := I) (M := M) g r s S α Idx Jdx) 2
      (riemannianVolumeMeasure (I := I) (M := M) g) = ENNReal.ofReal a := by
    rw [ha_def, ENNReal.ofReal_toReal hne]
  rw [h_lhs_eq]
  have h1 : ENNReal.ofReal a ≤ ENNReal.ofReal (a + 1) := by
    apply ENNReal.ofReal_le_ofReal; linarith
  have h_one_le :
      (1 : ℝ≥0∞) ≤
        (ENNReal.ofReal
          (tensorL2Norm (I := I) (M := M) g r s S.toFun) + 1) := le_add_self
  have h2 : ENNReal.ofReal (a + 1) ≤
      ENNReal.ofReal (a + 1) *
        (ENNReal.ofReal
          (tensorL2Norm (I := I) (M := M) g r s S.toFun) + 1) :=
    calc ENNReal.ofReal (a + 1)
        = ENNReal.ofReal (a + 1) * 1 := by rw [mul_one]
      _ ≤ ENNReal.ofReal (a + 1) *
            (ENNReal.ofReal
              (tensorL2Norm (I := I) (M := M) g r s S.toFun) + 1) :=
            mul_le_mul_of_nonneg_left h_one_le (by exact zero_le)
  exact h1.trans h2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_eLpNorm_le_per_section then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_eLpNorm_le_per_section"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_eLpNorm_le_per_section ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_eLpNorm_le_per_section

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem tensorChartComponentScalar_eLpNorm_le_l2
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ∀ S : SmoothCcTensor g r s,
      ∃ C : ℝ, 0 ≤ C ∧
        eLpNorm (tensorChartComponentScalar (I := I) (M := M)
              g r s S α Idx Jdx) 2
          (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal C *
            (ENNReal.ofReal
              (tensorL2Norm (I := I) (M := M) g r s S.toFun) + 1) := fun S =>
  tensorChartComponentScalar_eLpNorm_le_per_section
    (I := I) (M := M) g r s S α Idx Jdx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_eLpNorm_le_l2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_eLpNorm_le_l2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_eLpNorm_le_l2 ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_eLpNorm_le_l2

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
