import Submission.DifferentialGeometry.Geometry.Curvature.RoughLaplacian.CurvatureOperator.DifferentiatedCurvature
import Submission.DifferentialGeometry.Analysis.Integration.L2.Pairing.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Geometry.Curvature


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators

namespace DifferentialGeometry
namespace Geometry
namespace Curvature

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M]

private local instance _root_.Submission.DifferentialGeometry.Geometry.Curvature.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

theorem tensorL2Inner_GcurvSection_covGrad_eq_pureRGenuineDiffOp
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (genuineCurvatureOnlySection (I := I) (M := M) g s S).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun =
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pureRGenuineDiffOp (I := I) (M := M) g 0 (s + 1)
          (covGrad (I := I) (M := M) g 0 s S)).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun := by
  rw [pureRGenuineDiffOp0_eq_GcurvSection (I := I) (M := M) g s S]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.tensorL2Inner_GcurvSection_covGrad_eq_pureRGenuineDiffOp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.tensorL2Inner_GcurvSection_covGrad_eq_pureRGenuineDiffOp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.tensorL2Inner_GcurvSection_covGrad_eq_pureRGenuineDiffOp ``Submission.DifferentialGeometry.Geometry.Curvature.tensorL2Inner_GcurvSection_covGrad_eq_pureRGenuineDiffOp

theorem exists_GcurvSection_eq_operatorFieldApplication_curvatureOpField
    (g : SmoothRiemannianMetric I M) :
    ∃ Φ₀ : ∀ r : ℕ, SmoothCcTensor g (r + 0) (r + 0),
      ∀ (s : ℕ) (S : SmoothCcTensor g 0 s),
        genuineCurvatureOnlySection (I := I) (M := M) g s S =
          operatorFieldApply (I := I) (M := M) g ((s + 1) + 0) ((s + 1) + 0) (Φ₀ (s + 1))
            (covGrad (I := I) (M := M) g 0 s S) := by
  obtain ⟨Φ₀, hΦ₀⟩ := exists_baseOperatorField_apply_eq_pureRGenuineDiffOp (I := I) (M := M) g
  refine ⟨Φ₀, fun s S => ?_⟩
  rw [← pureRGenuineDiffOp0_eq_GcurvSection (I := I) (M := M) g s S]
  exact hΦ₀ (s + 1) (covGrad (I := I) (M := M) g 0 s S)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.exists_GcurvSection_eq_operatorFieldApplication_curvatureOpField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.exists_GcurvSection_eq_operatorFieldApplication_curvatureOpField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.exists_GcurvSection_eq_operatorFieldApplication_curvatureOpField ``Submission.DifferentialGeometry.Geometry.Curvature.exists_GcurvSection_eq_operatorFieldApplication_curvatureOpField

end Curvature
end Geometry
end DifferentialGeometry

end
