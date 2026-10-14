import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.UniformChartBounds.Tensor.SlotBound
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.UniformChartBounds.ChartTransition.LocallyConstantAtlas
import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.Chart.Local
import Submission.DifferentialGeometry.Geometry.Connection.ChartTensorNabla.Tensor0S.ChartTensor0SCovariantDerivative

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Connection


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Finset _root_.Set.Finset
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open _root_.Submission.DifferentialGeometry.Integral.Measure

open _root_.Submission.DifferentialGeometry.Tensor
open _root_.Submission.DifferentialGeometry.Tensor.Tensor0SRiemannian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma chartLeviCivitaParallelCLM_opNorm_le_factors
    (g : SmoothRiemannianMetric I M) (α b : M)
    (X : Π b' : M, TangentSpace I b')
    (C_J C_Jinv C_χ : ℝ)
    (hCJ : ‖chartTrivializationLinearMap (I := I) (M := M) α b‖ ≤ C_J) (_hCJ_nn : 0 ≤ C_J)
    (hCJinv : ‖chartTrivializationLinearMapSymm (I := I) (M := M) α b‖ ≤ C_Jinv)
      (hCJinv_nn : 0 ≤ C_Jinv)
    (hCχ : ∀ Y : E, ‖christoffelCorrection (I := I) g α b Y‖ ≤ C_χ * ‖Y‖)
    (hCχ_nn : 0 ≤ C_χ) :
    ‖chartLeviCivitaParallelCLM (I := I) g α b X‖ ≤
      C_Jinv * C_χ * C_J * ‖X b‖ := by
  classical
  unfold chartLeviCivitaParallelCLM
  set Y : E := trivToE (I := I) α b (X b) with hY_def
  have h_comp_le :
      ‖(trivFromE (I := I) α b).comp
          (christoffelCorrection (I := I) g α b Y)‖ ≤
        ‖trivFromE (I := I) α b‖ *
          ‖christoffelCorrection (I := I) g α b Y‖ :=
    ContinuousLinearMap.opNorm_comp_le _ _
  have h_trivFromE_norm :
      ‖trivFromE (I := I) α b‖ = ‖chartTrivializationLinearMapSymm (I := I) (M := M) α b‖ := rfl
  have h_trivFromE_le : ‖trivFromE (I := I) α b‖ ≤ C_Jinv := by
    rw [h_trivFromE_norm]; exact hCJinv
  have h_trivFromE_nn : 0 ≤ ‖trivFromE (I := I) α b‖ := norm_nonneg _
  have h_Y_le_triv :
      ‖Y‖ ≤ ‖trivToE (I := I) α b‖ * ‖X b‖ := by
    rw [hY_def]
    exact (trivToE (I := I) α b).le_opNorm (X b)
  have h_triv_J : ‖trivToE (I := I) α b‖ = ‖chartTrivializationLinearMap (I := I) (M := M) α b‖ :=
    rfl
  have h_Xb_nn : 0 ≤ ‖X b‖ := norm_nonneg _
  have h_Y_le : ‖Y‖ ≤ C_J * ‖X b‖ := by
    refine h_Y_le_triv.trans ?_
    rw [h_triv_J]
    exact mul_le_mul_of_nonneg_right hCJ h_Xb_nn
  have h_χ_Y : ‖christoffelCorrection (I := I) g α b Y‖ ≤ C_χ * ‖Y‖ := hCχ Y
  have h_Y_nn : 0 ≤ ‖Y‖ := norm_nonneg _
  have h_χ_le : ‖christoffelCorrection (I := I) g α b Y‖ ≤ C_χ * (C_J * ‖X b‖) :=
    h_χ_Y.trans (mul_le_mul_of_nonneg_left h_Y_le hCχ_nn)
  have h_χ_nn : 0 ≤ ‖christoffelCorrection (I := I) g α b Y‖ := norm_nonneg _
  have h_step1 :
      ‖trivFromE (I := I) α b‖ *
          ‖christoffelCorrection (I := I) g α b Y‖ ≤
        C_Jinv * ‖christoffelCorrection (I := I) g α b Y‖ :=
    mul_le_mul_of_nonneg_right h_trivFromE_le h_χ_nn
  have h_step2 :
      C_Jinv * ‖christoffelCorrection (I := I) g α b Y‖ ≤
        C_Jinv * (C_χ * (C_J * ‖X b‖)) :=
    mul_le_mul_of_nonneg_left h_χ_le hCJinv_nn
  have h_rearrange :
      C_Jinv * (C_χ * (C_J * ‖X b‖)) = C_Jinv * C_χ * C_J * ‖X b‖ := by ring
  linarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLeviCivitaParallelCLM_opNorm_le_factors
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLeviCivitaParallelCLM_opNorm_le_factors target :: scope.openDecls } }

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
