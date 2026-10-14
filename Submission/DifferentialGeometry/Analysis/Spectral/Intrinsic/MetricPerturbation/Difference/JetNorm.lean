import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricPerturbation.Difference.TensorFields
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Inner.TensorRSContRiemannianBundle

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

private local instance metricDifferenceJetNormTensorRSNormedAddCommGroup
    (r s : ℕ) [Bundle.RiemannianBundle (fun y : M => TensorRSSpace r s I y)] (x : M) :
    NormedAddCommGroup (TensorRSSpace r s I x) :=
  Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
    (E := fun y : M => TensorRSSpace r s I y) x

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.metricDifferenceJetNormTensorRSNormedAddCommGroup
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.metricDifferenceJetNormTensorRSNormedAddCommGroup target :: scope.openDecls } }

omit [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private theorem continuous_riemannian_fiber_norm_of_continuous_section
    {F₀ : Type*} [NormedAddCommGroup F₀] [NormedSpace ℝ F₀]
    {V₀ : M → Type*} [∀ x, NormedAddCommGroup (V₀ x)] [∀ x, InnerProductSpace ℝ (V₀ x)]
    [TopologicalSpace (_root_.Bundle.TotalSpace F₀ V₀)] [FiberBundle F₀ V₀] [VectorBundle ℝ F₀ V₀]
    [IsContinuousRiemannianBundle F₀ V₀]
    {σ : Π x : M, V₀ x}
    (hσ : Continuous (fun x : M => TotalSpace.mk' F₀ (E := V₀) x (σ x))) :
    Continuous (fun x : M => ‖σ x‖) := by
  have h_inner : Continuous (fun x : M => (_root_.Inner.inner ℝ (σ x) (σ x) : ℝ)) :=
    Continuous.inner_bundle (F := F₀) (E := V₀) hσ hσ
  have h_eq : (fun x : M => ‖σ x‖) = fun x : M => Real.sqrt (_root_.Inner.inner ℝ (σ x) (σ x)) := by
    funext x
    rw [real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  rw [h_eq]
  exact Real.continuous_sqrt.comp h_inner

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.continuous_riemannian_fiber_norm_of_continuous_section
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.continuous_riemannian_fiber_norm_of_continuous_section target :: scope.openDecls } }

attribute [-instance] Bundle.continuousMultilinearMap.instNormedAddCommGroup
  Bundle.continuousMultilinearMap.instNormedSpace
  Bundle.continuousMultilinearMap.mixedInstNormedAddCommGroup
  Bundle.continuousMultilinearMap.mixedInstNormedSpace
  Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace in
def metricDifference2JetNorm (g₀ g₁ g₂ : SmoothRiemannianMetric I M) (x : M) : ℝ :=
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 2 I b) :=
    Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g₀ 0 2
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 3 I b) :=
    Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g₀ 0 3
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 4 I b) :=
    Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g₀ 0 4
  ‖metricDifference02MixedSection (I := I) g₁ g₂ x‖
    + ‖metricDifference02CovMixedSection (I := I) g₀ g₁ g₂ x‖
    + ‖metricDifference02CovIterateMixedSection (I := I) g₀ g₁ g₂ x‖

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.metricDifference2JetNorm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.metricDifference2JetNorm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.metricDifference2JetNorm ``Submission.DifferentialGeometry.Analysis.Spectral.metricDifference2JetNorm

attribute [-instance] Bundle.continuousMultilinearMap.instNormedAddCommGroup
  Bundle.continuousMultilinearMap.instNormedSpace
  Bundle.continuousMultilinearMap.mixedInstNormedAddCommGroup
  Bundle.continuousMultilinearMap.mixedInstNormedSpace
  Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem metricDifference2JetNorm_eq_riemannianNorm_sum
    (g₀ g₁ g₂ : SmoothRiemannianMetric I M) (x : M) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 2 I b) :=
      Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g₀ 0 2
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 3 I b) :=
      Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g₀ 0 3
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 4 I b) :=
      Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g₀ 0 4
    metricDifference2JetNorm (I := I) g₀ g₁ g₂ x =
      ‖metricDifference02MixedSection (I := I) g₁ g₂ x‖
        + ‖metricDifference02CovMixedSection (I := I) g₀ g₁ g₂ x‖
        + ‖metricDifference02CovIterateMixedSection (I := I) g₀ g₁ g₂ x‖ :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.metricDifference2JetNorm_eq_riemannianNorm_sum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.metricDifference2JetNorm_eq_riemannianNorm_sum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.metricDifference2JetNorm_eq_riemannianNorm_sum ``Submission.DifferentialGeometry.Analysis.Spectral.metricDifference2JetNorm_eq_riemannianNorm_sum

attribute [-instance] Bundle.continuousMultilinearMap.instNormedAddCommGroup
  Bundle.continuousMultilinearMap.instNormedSpace
  Bundle.continuousMultilinearMap.mixedInstNormedAddCommGroup
  Bundle.continuousMultilinearMap.mixedInstNormedSpace
  Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem metricDifference2JetNorm_nonneg
    (g₀ g₁ g₂ : SmoothRiemannianMetric I M) (x : M) :
    0 ≤ metricDifference2JetNorm (I := I) g₀ g₁ g₂ x := by
  let : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 2 I b) :=
    Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g₀ 0 2
  let : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 3 I b) :=
    Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g₀ 0 3
  let : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 4 I b) :=
    Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g₀ 0 4
  rw [metricDifference2JetNorm_eq_riemannianNorm_sum (I := I) g₀ g₁ g₂ x]
  exact add_nonneg
    (add_nonneg
      (norm_nonneg (metricDifference02MixedSection (I := I) g₁ g₂ x))
      (norm_nonneg (metricDifference02CovMixedSection (I := I) g₀ g₁ g₂ x)))
    (norm_nonneg (metricDifference02CovIterateMixedSection (I := I) g₀ g₁ g₂ x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.metricDifference2JetNorm_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.metricDifference2JetNorm_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.metricDifference2JetNorm_nonneg ``Submission.DifferentialGeometry.Analysis.Spectral.metricDifference2JetNorm_nonneg

attribute [-instance] Bundle.continuousMultilinearMap.instNormedAddCommGroup
  Bundle.continuousMultilinearMap.instNormedSpace
  Bundle.continuousMultilinearMap.mixedInstNormedAddCommGroup
  Bundle.continuousMultilinearMap.mixedInstNormedSpace
  Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem metricDifference2JetNorm_continuous
    (g₀ g₁ g₂ : SmoothRiemannianMetric I M) :
    Continuous (fun x : M => metricDifference2JetNorm (I := I) g₀ g₁ g₂ x) := by
  let : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 2 I b) :=
    Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g₀ 0 2
  let : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 3 I b) :=
    Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g₀ 0 3
  let : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 4 I b) :=
    Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g₀ 0 4
  let : TopologicalSpace
      (_root_.Bundle.TotalSpace (TensorRSModel 0 2 ℝ E) (fun b : M => TensorRSSpace 0 2 I b)) :=
    pointwiseTensorRSTotalSpaceTopology 0 2
  let : FiberBundle (TensorRSModel 0 2 ℝ E) (fun b : M => TensorRSSpace 0 2 I b) :=
    pointwiseTensorRSFiberBundle 0 2
  let : TopologicalSpace
      (_root_.Bundle.TotalSpace (TensorRSModel 0 3 ℝ E) (fun b : M => TensorRSSpace 0 3 I b)) :=
    pointwiseTensorRSTotalSpaceTopology 0 3
  let : FiberBundle (TensorRSModel 0 3 ℝ E) (fun b : M => TensorRSSpace 0 3 I b) :=
    pointwiseTensorRSFiberBundle 0 3
  let : TopologicalSpace
      (_root_.Bundle.TotalSpace (TensorRSModel 0 4 ℝ E) (fun b : M => TensorRSSpace 0 4 I b)) :=
    pointwiseTensorRSTotalSpaceTopology 0 4
  let : FiberBundle (TensorRSModel 0 4 ℝ E) (fun b : M => TensorRSSpace 0 4 I b) :=
    pointwiseTensorRSFiberBundle 0 4
  have hC2 : IsContinuousRiemannianBundle (TensorRSModel 0 2 ℝ E)
      (fun b : M => TensorRSSpace 0 2 I b) :=
    TensorRSRiemannianBundleContinuous.tensorRS_isContinuousRiemannianBundle
      (I := I) (M := M) g₀ 0 2
  have hC3 : IsContinuousRiemannianBundle (TensorRSModel 0 3 ℝ E)
      (fun b : M => TensorRSSpace 0 3 I b) :=
    TensorRSRiemannianBundleContinuous.tensorRS_isContinuousRiemannianBundle
      (I := I) (M := M) g₀ 0 3
  have hC4 : IsContinuousRiemannianBundle (TensorRSModel 0 4 ℝ E)
      (fun b : M => TensorRSSpace 0 4 I b) :=
    TensorRSRiemannianBundleContinuous.tensorRS_isContinuousRiemannianBundle
      (I := I) (M := M) g₀ 0 4
  have h0 : Continuous (fun x : M => ‖metricDifference02MixedSection (I := I) g₁ g₂ x‖) :=
    continuous_riemannian_fiber_norm_of_continuous_section
      (F₀ := TensorRSModel 0 2 ℝ E) (V₀ := fun b : M => TensorRSSpace 0 2 I b)
      (σ := fun x => metricDifference02MixedSection (I := I) g₁ g₂ x)
      (metricDifference02MixedSection (I := I) g₁ g₂).contMDiff.continuous
  have h1 : Continuous (fun x : M => ‖metricDifference02CovMixedSection (I := I) g₀ g₁ g₂ x‖) :=
    continuous_riemannian_fiber_norm_of_continuous_section
      (F₀ := TensorRSModel 0 3 ℝ E) (V₀ := fun b : M => TensorRSSpace 0 3 I b)
      (σ := fun x => metricDifference02CovMixedSection (I := I) g₀ g₁ g₂ x)
      (metricDifference02CovMixedSection (I := I) g₀ g₁ g₂).contMDiff.continuous
  have h2 : Continuous (fun x : M => ‖metricDifference02CovIterateMixedSection (I := I) g₀ g₁ g₂ x‖) :=
    continuous_riemannian_fiber_norm_of_continuous_section
      (F₀ := TensorRSModel 0 4 ℝ E) (V₀ := fun b : M => TensorRSSpace 0 4 I b)
      (σ := fun x => metricDifference02CovIterateMixedSection (I := I) g₀ g₁ g₂ x)
      (metricDifference02CovIterateMixedSection (I := I) g₀ g₁ g₂).contMDiff.continuous
  have hsum := (h0.add h1).add h2
  refine hsum.congr (fun x => ?_)
  rw [metricDifference2JetNorm_eq_riemannianNorm_sum (I := I) g₀ g₁ g₂ x]
  simp only [Pi.add_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.metricDifference2JetNorm_continuous then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.metricDifference2JetNorm_continuous"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.metricDifference2JetNorm_continuous ``Submission.DifferentialGeometry.Analysis.Spectral.metricDifference2JetNorm_continuous

end Spectral
end Analysis
end DifferentialGeometry

end
