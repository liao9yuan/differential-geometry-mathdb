import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricPerturbation.Difference.JetNorm
import Submission.DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.RHS.Section
import Submission.DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.RHS.Smoothness
import Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.FiberNorm.FiberNormRiemannianBridge
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieCorrection.SummandLipschitz
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.Ricci.AffineDifference

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.IsManifold _root_.ContinuousLinearMap _root_.Submission.ContinuousLinearMap _root_.Bundle.ContinuousLinearMap _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.ContDiff _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

open _root_.Submission.DifferentialGeometry.Integral.Measure

open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Tensor
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow _root_.Submission.DifferentialGeometry.Analysis.Parabolic
    DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients
open _root_.Submission.DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

attribute [local instance]
  pointwiseModelDualNormedAddCommGroup
  pointwiseModelDualNormedSpace
  pointwiseModelBilinearNormedAddCommGroup
  pointwiseModelBilinearNormedSpace
  pointwiseModelTrilinearNormedAddCommGroup
  pointwiseModelTrilinearNormedSpace
  pointwiseModelQuadrilinearNormedAddCommGroup
  pointwiseModelQuadrilinearNormedSpace
  pointwiseTangentDualNormedAddCommGroup
  pointwiseTangentDualNormedSpace
  pointwiseTangentBilinearNormedAddCommGroup
  pointwiseTangentBilinearNormedSpace
  pointwiseTangentTrilinearNormedAddCommGroup
  pointwiseTangentTrilinearNormedSpace
  pointwiseTangentTrilinearAddCommGroup
  pointwiseTangentTrilinearModule
  pointwiseTangentTrilinearSMul
  pointwiseTangentTrilinearTopology
  pointwiseSectionAddCommGroup
  pointwiseSectionModule
  pointwiseTangentQuadrilinearNormedAddCommGroup
  pointwiseTangentQuadrilinearNormedSpace
  pointwiseTangentQuadrilinearAddCommGroup
  pointwiseTangentQuadrilinearModule
  pointwiseTangentBilinearAddCommGroup
  pointwiseTangentBilinearModule
  pointwiseBilinearSectionAddCommGroup
  pointwiseBilinearSectionModule
  pointwiseTensor0SModelNormedAddCommGroup
  pointwiseTensor0SModelNormedSpace
  pointwiseTensorRSModelNormedAddCommGroup
  pointwiseTensorRSModelNormedSpace
  pointwiseTensor01TotalSpaceTopology
  pointwiseTensor01FiberBundle
  pointwiseTensor01VectorBundle
  pointwiseTensor01ContMDiffVectorBundle
  pointwiseTensor02TotalSpaceTopology
  pointwiseIteratedTensor02FiberBundle
  pointwiseIteratedTensor02VectorBundle
  pointwiseIteratedTensor02ContMDiffVectorBundle
  pointwiseTensor03TotalSpaceTopology
  pointwiseTensor03FiberBundle
  pointwiseTensor03VectorBundle
  pointwiseTensor03ContMDiffVectorBundle
  pointwiseTensor04TotalSpaceTopology
  pointwiseTensor04FiberBundle
  pointwiseTensor04VectorBundle
  pointwiseTensor04ContMDiffVectorBundle
  pointwiseTensorRSTotalSpaceTopology
  pointwiseTensorRSFiberBundle

private local instance pointwiseTensorRSNormedAddCommGroup
    (r s : ℕ) [Bundle.RiemannianBundle (fun y : M => TensorRSSpace r s I y)] (x : M) :
    NormedAddCommGroup (TensorRSSpace r s I x) :=
  Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
    (E := fun y : M => TensorRSSpace r s I y) x

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.pointwiseTensorRSNormedAddCommGroup
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.pointwiseTensorRSNormedAddCommGroup target :: scope.openDecls } }

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem deTurckRHS_diff_frame_component_apply
    (g_bg g₁ g₂ : SmoothRiemannianMetric I M) (α x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    (deTurckRicciRHS (I := I) g_bg g₁ x - deTurckRicciRHS (I := I) g_bg g₂ x)
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i x) (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j x) =
      deTurckRicciRHS (I := I) g_bg g₁ x
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i x) (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j x)
      - deTurckRicciRHS (I := I) g_bg g₂ x
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i x) (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j x) := by
  rw [sub_apply, sub_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.deTurckRHS_diff_frame_component_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.deTurckRHS_diff_frame_component_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.deTurckRHS_diff_frame_component_apply ``Submission.DifferentialGeometry.Analysis.Spectral.deTurckRHS_diff_frame_component_apply

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem deTurckRHS_diff_frame_component_contMDiffOn
    (g_bg g₁ g₂ : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x : M =>
        (deTurckRicciRHS (I := I) g_bg g₁ x - deTurckRicciRHS (I := I) g_bg g₂ x)
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i x) (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j x))
      (chartAt H α).source := by
  have h₁ : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x : M => deTurckRicciRHS (I := I) g_bg g₁ x
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i x) (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j x))
      (chartAt H α).source :=
    combine_smoothness_of_summands (I := I) g_bg g₁ α i j
  have h₂ : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x : M => deTurckRicciRHS (I := I) g_bg g₂ x
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i x) (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j x))
      (chartAt H α).source :=
    combine_smoothness_of_summands (I := I) g_bg g₂ α i j
  refine (h₁.sub h₂).congr (fun x _ => ?_)
  exact deTurckRHS_diff_frame_component_apply (I := I) g_bg g₁ g₂ α x i j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.deTurckRHS_diff_frame_component_contMDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.deTurckRHS_diff_frame_component_contMDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.deTurckRHS_diff_frame_component_contMDiffOn ``Submission.DifferentialGeometry.Analysis.Spectral.deTurckRHS_diff_frame_component_contMDiffOn

attribute [-instance] Bundle.continuousMultilinearMap.instNormedAddCommGroup
  Bundle.continuousMultilinearMap.instNormedSpace
  Bundle.continuousMultilinearMap.mixedInstNormedAddCommGroup
  Bundle.continuousMultilinearMap.mixedInstNormedSpace
  Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem deTurckRHS_diff_gNorm_le_modelNorm_pointwise
    (g₀ : SmoothRiemannianMetric I M) (x₀ : M) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 2 I b) :=
      Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g₀ 0 2
    ∃ D : ℝ, 0 < D ∧ ∀ T : TensorRSSpace 0 2 I x₀,
      ‖T‖ ≤ D * ‖TensorRSSpace.toModel (𝕜 := ℝ) (I := I) T‖ :=
  gNorm_le_modelNorm_pointwise (I := I) (M := M) g₀ 0 2 x₀

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.deTurckRHS_diff_gNorm_le_modelNorm_pointwise then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.deTurckRHS_diff_gNorm_le_modelNorm_pointwise"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.deTurckRHS_diff_gNorm_le_modelNorm_pointwise ``Submission.DifferentialGeometry.Analysis.Spectral.deTurckRHS_diff_gNorm_le_modelNorm_pointwise

def chartDeTurckRHSComp (g_bg g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  (-2 : ℝ) * chartRicciTensor (I := I) g α i j y
    + chartLieDeTurckComp (I := I) g g_bg α i j y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.chartDeTurckRHSComp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.chartDeTurckRHSComp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.chartDeTurckRHSComp ``Submission.DifferentialGeometry.Analysis.Spectral.chartDeTurckRHSComp

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
@[simp] theorem chartDeTurckRHSComp_def (g_bg g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckRHSComp (I := I) g_bg g α i j y =
      (-2 : ℝ) * chartRicciTensor (I := I) g α i j y
        + chartLieDeTurckComp (I := I) g g_bg α i j y := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.chartDeTurckRHSComp_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.chartDeTurckRHSComp_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.chartDeTurckRHSComp_def ``Submission.DifferentialGeometry.Analysis.Spectral.chartDeTurckRHSComp_def

omit [CompactSpace M] in
omit [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem exists_chartDeTurckRHSComp_lipschitz_on_compact
    (g_bg g₁ g₂ : SmoothRiemannianMetric I M) (α : M)
    {K : Set E} (hK : IsCompact K)
    (hKsub : K ⊆ interior (extChartAt I α).target) :
    ∃ C : ℝ, 0 < C ∧ ∀ y ∈ K, ∀ i j : Fin (Module.finrank ℝ E),
      |chartDeTurckRHSComp (I := I) g_bg g₁ α i j y -
          chartDeTurckRHSComp (I := I) g_bg g₂ α i j y| ≤
        C * chartMetricJet2DiffSup (I := I) (M := M) g₁ g₂ α y := by
  classical
  obtain ⟨Cric, hCric_pos, hCric⟩ :=
    DeTurckCoefficients.exists_chartRicciTensor_lipschitz_on_compact
      (I := I) (M := M) g₁ g₂ α hK hKsub
  obtain ⟨Clie, hClie_pos, hClie⟩ :=
    DeTurckCoefficients.exists_chartLieDeTurckComp_lipschitz_on_compact
      (I := I) (M := M) g₁ g₂ g_bg α hK hKsub
  refine ⟨2 * Cric + Clie, ?_, ?_⟩
  · have h1 : 0 < 2 * Cric := by positivity
    linarith
  intro y hy i j
  have hjet2_nn : 0 ≤ chartMetricJet2DiffSup (I := I) (M := M) g₁ g₂ α y :=
    DeTurckCoefficients.chartMetricJet2DiffSup_nonneg _ _ _ _
  set jet2 : ℝ := chartMetricJet2DiffSup (I := I) (M := M) g₁ g₂ α y with hjet2_def
  have hsplit :
      chartDeTurckRHSComp (I := I) g_bg g₁ α i j y -
          chartDeTurckRHSComp (I := I) g_bg g₂ α i j y =
        (-2 : ℝ) * (chartRicciTensor (I := I) g₁ α i j y -
              chartRicciTensor (I := I) g₂ α i j y)
          + (chartLieDeTurckComp (I := I) g₁ g_bg α i j y -
              chartLieDeTurckComp (I := I) g₂ g_bg α i j y) := by
    rw [chartDeTurckRHSComp_def, chartDeTurckRHSComp_def]; ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  have hric_bound : |(-2 : ℝ) * (chartRicciTensor (I := I) g₁ α i j y -
        chartRicciTensor (I := I) g₂ α i j y)| ≤ 2 * Cric * jet2 := by
    rw [abs_mul]
    have h2 : |(-2 : ℝ)| = 2 := by norm_num
    rw [h2]
    have hR := hCric y hy i j
    calc 2 * |chartRicciTensor (I := I) g₁ α i j y -
            chartRicciTensor (I := I) g₂ α i j y|
        ≤ 2 * (Cric * jet2) :=
          mul_le_mul_of_nonneg_left hR (by norm_num)
      _ = 2 * Cric * jet2 := by ring
  have hlie_bound : |chartLieDeTurckComp (I := I) g₁ g_bg α i j y -
        chartLieDeTurckComp (I := I) g₂ g_bg α i j y| ≤ Clie * jet2 :=
    hClie y hy i j
  calc |(-2 : ℝ) * (chartRicciTensor (I := I) g₁ α i j y -
            chartRicciTensor (I := I) g₂ α i j y)|
        + |chartLieDeTurckComp (I := I) g₁ g_bg α i j y -
            chartLieDeTurckComp (I := I) g₂ g_bg α i j y|
      ≤ 2 * Cric * jet2 + Clie * jet2 := add_le_add hric_bound hlie_bound
    _ = (2 * Cric + Clie) * jet2 := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.exists_chartDeTurckRHSComp_lipschitz_on_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.exists_chartDeTurckRHSComp_lipschitz_on_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.exists_chartDeTurckRHSComp_lipschitz_on_compact ``Submission.DifferentialGeometry.Analysis.Spectral.exists_chartDeTurckRHSComp_lipschitz_on_compact


end Spectral
end Analysis
end DifferentialGeometry

end
