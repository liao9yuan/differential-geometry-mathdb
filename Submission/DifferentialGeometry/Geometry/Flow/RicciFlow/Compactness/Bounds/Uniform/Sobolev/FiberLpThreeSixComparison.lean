import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.OperatorField.LpProduct

import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Uniform.Sobolev.GagliardoNirenberg

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow

open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Integral.Connection
open _root_.Submission.DifferentialGeometry.Analysis.Spectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instMeasurableSpace_differentialGeometry : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instBorelSpace_differentialGeometry : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instBorelSpace_differentialGeometry target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
theorem fiber_lp_three_le_uniform_constant_mul_lp_six
    (gBase : SmoothRiemannianMetric I M) (Λ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        ∀ (r s : ℕ) (S : SmoothCcTensor g r s),
          _root_.MeasureTheory.lpNorm (fiberLpFun g r s S) 3
              (riemannianVolumeMeasure (I := I) (M := M) g) ≤
            C * _root_.MeasureTheory.lpNorm (fiberLpFun g r s S) 6
              (riemannianVolumeMeasure (I := I) (M := M) g) := by
  let VBase : ℝ :=
    ((riemannianVolumeMeasure (I := I) (M := M) gBase) Set.univ).toReal
  let C : ℝ :=
    (volCompareC (E := E) Λ * VBase) ^ (1 / 6 : ℝ)
  have hbase : 0 ≤ VBase := by
    dsimp [VBase]
    exact ENNReal.toReal_nonneg
  have hvolC : 0 ≤ volCompareC (E := E) Λ := by
    exact Real.sqrt_nonneg _
  have hC : 0 ≤ C := by
    dsimp [C]
    exact Real.rpow_nonneg (mul_nonneg hvolC hbase) _
  refine ⟨C, hC, ?_⟩
  intro g hEq r s S
  have hroot :
      (((riemannianVolumeMeasure (I := I) (M := M) g) Set.univ) ^
          (1 / 6 : ℝ)).toReal ≤ C := by
    rw [← ENNReal.toReal_rpow]
    dsimp only [C, VBase]
    exact Real.rpow_le_rpow ENNReal.toReal_nonneg
      (volumeReal_cross (I := I) (M := M) gBase g hEq).1 (by norm_num)
  calc
    _root_.MeasureTheory.lpNorm (fiberLpFun g r s S) 3
        (riemannianVolumeMeasure (I := I) (M := M) g) ≤
      (((riemannianVolumeMeasure (I := I) (M := M) g) Set.univ) ^
          (1 / 6 : ℝ)).toReal *
        _root_.MeasureTheory.lpNorm (fiberLpFun g r s S) 6
          (riemannianVolumeMeasure (I := I) (M := M) g) :=
      fiberLp3_le_6 (I := I) (M := M) g r s S
    _ ≤ C * _root_.MeasureTheory.lpNorm (fiberLpFun g r s S) 6
        (riemannianVolumeMeasure (I := I) (M := M) g) :=
      mul_le_mul_of_nonneg_right hroot _root_.MeasureTheory.lpNorm_nonneg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.fiber_lp_three_le_uniform_constant_mul_lp_six then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.fiber_lp_three_le_uniform_constant_mul_lp_six"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.fiber_lp_three_le_uniform_constant_mul_lp_six ``Submission.DifferentialGeometry.PDE.RicciFlow.fiber_lp_three_le_uniform_constant_mul_lp_six

end RicciFlow
end PDE
end DifferentialGeometry

end
