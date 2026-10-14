import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieCorrection.Zero.FiberOperators
import Submission.DifferentialGeometry.Analysis.Parabolic.RicciLinearization.PalatiniDecomposition.TameEstimates

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section
set_option backward.isDefEq.respectTransparency false

open _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry.Tensor0SBundle
    ContinuousLinearMap
open scoped _root_.ENNReal _root_.NNReal _root_.BigOperators _root_.Manifold _root_.Topology _root_.ContDiff _root_.Matrix _root_.Submission.Matrix

namespace DifferentialGeometry.Analysis.Spectral

open _root_.Submission.DifferentialGeometry.Integral.L2

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization
open _root_.Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

def lieCorrectionZeroInsertion (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (lieCorrectionZeroInsertionFib (I := I) g₀ g₁ g_bg x))
      contMDiff_toFun := lieCorrectionZeroInsertionFib_contMDiff (I := I) g₀ g₁ g_bg }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.lieCorrectionZeroInsertion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.lieCorrectionZeroInsertion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.lieCorrectionZeroInsertion ``Submission.DifferentialGeometry.Analysis.Spectral.lieCorrectionZeroInsertion

def lieCorrectionZeroVectorBundle (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (lieCorrectionZeroVBFib (I := I) g₀ g₁ x))
      contMDiff_toFun := lieCorrectionZeroVBFib_contMDiff (I := I) g₀ g₁ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.lieCorrectionZeroVectorBundle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.lieCorrectionZeroVectorBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.lieCorrectionZeroVectorBundle ``Submission.DifferentialGeometry.Analysis.Spectral.lieCorrectionZeroVectorBundle

def lieCorrectionZeroMixedConnection (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (lieCorrectionZeroMixedConnectionFib (I := I) g₀ g₁ g_bg x))
      contMDiff_toFun := lieCorrectionZeroMixedConnectionFib_contMDiff (I := I) g₀ g₁ g_bg }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.lieCorrectionZeroMixedConnection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.lieCorrectionZeroMixedConnection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.lieCorrectionZeroMixedConnection ``Submission.DifferentialGeometry.Analysis.Spectral.lieCorrectionZeroMixedConnection

def lieCorrectionZeroRiemann (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (lieCorrectionZeroRiemFib (I := I) g₀ g₁ x))
      contMDiff_toFun := lieCorrectionZeroRiemFib_contMDiff (I := I) g₀ g₁ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.lieCorrectionZeroRiemann then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.lieCorrectionZeroRiemann"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.lieCorrectionZeroRiemann ``Submission.DifferentialGeometry.Analysis.Spectral.lieCorrectionZeroRiemann

omit [NeZero (Module.finrank ℝ E)]
  [CompactSpace M]
  [I.Boundaryless]
  [SigmaCompactSpace M] in
theorem nEndo_base (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    lieCorrectionZeroNEndo (I := I) g₀ g₁ g₀ x =
      -deTurckVectorFieldCovariantDerivativeEndomorphism (I := I) g₁ g₀ x := by
  rw [lieCorrectionZeroNEndo, sub_self, zero_sub]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.nEndo_base then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.nEndo_base"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.nEndo_base ``Submission.DifferentialGeometry.Analysis.Spectral.nEndo_base

omit [NeZero (Module.finrank ℝ E)]
  [CompactSpace M]
  [I.Boundaryless]
  [SigmaCompactSpace M] in
theorem nEndo_diff (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    lieCorrectionZeroNEndo (I := I) g₀ g₁ g_bg x -
        lieCorrectionZeroNEndo (I := I) g₀ g₁ g₀ x =
      PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
          ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ :
            ∀ b : M, TangentSpace I b) x) -
        PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
          ((PDE.DeTurck.deTurckVF (I := I) g₁ g_bg :
            ∀ b : M, TangentSpace I b) x) := by
  rw [nEndo_base (I := I) (M := M) g₀ g₁ x, lieCorrectionZeroNEndo]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.nEndo_diff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.nEndo_diff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.nEndo_diff ``Submission.DifferentialGeometry.Analysis.Spectral.nEndo_diff

omit [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem insert_base (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g_bg +
        deTurckLieEndoTermField (I := I) (M := M) g₀ g₁ g₀ =
      lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g_bg -
        lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g₀ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  change Tensor0SSpace.toModel
        (lieCorrectionZeroInsertionFib (I := I) g₀ g₁ g_bg x D) m +
      Tensor0SSpace.toModel
        (deTurckLieCovariantDerivativeInsertionFib (I := I) g₁ g₀ x D) m =
    Tensor0SSpace.toModel
        (lieCorrectionZeroInsertionFib (I := I) g₀ g₁ g_bg x D) m -
      Tensor0SSpace.toModel
        (lieCorrectionZeroInsertionFib (I := I) g₀ g₁ g₀ x D) m
  rw [lieCorrectionZeroInsertionFib_toModel (I := I) g₀ g₁ g_bg x D m,
    lieCorrectionZeroInsertionFib_toModel (I := I) g₀ g₁ g₀ x D m,
    deTurckLieCovariantDerivativeInsertionFib_toModel (I := I) g₁ g₀ x D m]
  have hN0 : ∀ v : TangentSpace I x,
      lieCorrectionZeroNEndo (I := I) g₀ g₁ g₀ x v =
        -(deTurckVectorFieldCovariantDerivativeEndomorphism (I := I) g₁ g₀ x v) := by
    intro v
    simpa using congrArg
      (fun A : TangentSpace I x →L[ℝ] TangentSpace I x => A v)
      (nEndo_base (I := I) (M := M) g₀ g₁ x)
  have hN0Model : ∀ v : E,
      tangentLinearMapToModel
          (lieCorrectionZeroNEndo (I := I) g₀ g₁ g₀ x) v =
        -(tangentLinearMapToModel
          (deTurckVectorFieldCovariantDerivativeEndomorphism
            (I := I) g₁ g₀ x) v) := by
    intro v
    simpa only [tangentLinearMapToModel_apply, map_neg] using congrArg
      (tangentSpaceModelContinuousLinearEquiv (I := I) x)
      (hN0 ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm v))
  have e0 : Tensor0SSpace.toModel D
      (Function.update m 0
        (tangentLinearMapToModel
          (lieCorrectionZeroNEndo (I := I) g₀ g₁ g₀ x) (m 0))) =
      -(Tensor0SSpace.toModel D
        (Function.update m 0
          (tangentLinearMapToModel
            (deTurckVectorFieldCovariantDerivativeEndomorphism
              (I := I) g₁ g₀ x) (m 0)))) := by
    rw [hN0Model (m 0), show
        (-(tangentLinearMapToModel
          (deTurckVectorFieldCovariantDerivativeEndomorphism
            (I := I) g₁ g₀ x) (m 0))) =
        ((-1 : ℝ) • (tangentLinearMapToModel
          (deTurckVectorFieldCovariantDerivativeEndomorphism
            (I := I) g₁ g₀ x) (m 0))) from
          (neg_one_smul ℝ _).symm]
    rw [ContinuousMultilinearMap.map_update_smul, neg_one_smul]
  have e1 : Tensor0SSpace.toModel D
      (Function.update m 1
        (tangentLinearMapToModel
          (lieCorrectionZeroNEndo (I := I) g₀ g₁ g₀ x) (m 1))) =
      -(Tensor0SSpace.toModel D
        (Function.update m 1
          (tangentLinearMapToModel
            (deTurckVectorFieldCovariantDerivativeEndomorphism
              (I := I) g₁ g₀ x) (m 1)))) := by
    rw [hN0Model (m 1), show
        (-(tangentLinearMapToModel
          (deTurckVectorFieldCovariantDerivativeEndomorphism
            (I := I) g₁ g₀ x) (m 1))) =
        ((-1 : ℝ) • (tangentLinearMapToModel
          (deTurckVectorFieldCovariantDerivativeEndomorphism
            (I := I) g₁ g₀ x) (m 1))) from
          (neg_one_smul ℝ _).symm]
    rw [ContinuousMultilinearMap.map_update_smul, neg_one_smul]
  rw [e0, e1]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.insert_base then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.insert_base"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.insert_base ``Submission.DifferentialGeometry.Analysis.Spectral.insert_base

omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem lieCorrectionZero_decomp (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    lieCorrectionZeroField (I := I) (M := M) g₀ g₁ g_bg =
      ((lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g_bg +
          lieCorrectionZeroVectorBundle (I := I) (M := M) g₀ g₁) +
        lieCorrectionZeroMixedConnection (I := I) (M := M) g₀ g₁ g_bg) +
      lieCorrectionZeroRiemann (I := I) (M := M) g₀ g₁ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  change TensorRSSpace.ofCLM
      (lieCorrectionZeroTotalFib (I := I) g₀ g₁ g_bg x) = _
  rw [lieCorrectionZeroTotalFib]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.lieCorrectionZero_decomp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.lieCorrectionZero_decomp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.lieCorrectionZero_decomp ``Submission.DifferentialGeometry.Analysis.Spectral.lieCorrectionZero_decomp

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] in
theorem tail_base_split (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    lieCorrectionZeroField (I := I) (M := M) g₀ g₁ g_bg +
        deTurckLieEndoTermField (I := I) (M := M) g₀ g₁ g₀ =
      (((lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g_bg -
            lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g₀) +
          lieCorrectionZeroVectorBundle (I := I) (M := M) g₀ g₁) +
        lieCorrectionZeroMixedConnection (I := I) (M := M) g₀ g₁ g_bg) +
      lieCorrectionZeroRiemann (I := I) (M := M) g₀ g₁ := by
  rw [lieCorrectionZero_decomp (I := I) (M := M) g₀ g₁ g_bg]
  rw [← insert_base (I := I) (M := M) g₀ g₁ g_bg]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.tail_base_split then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.tail_base_split"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.tail_base_split ``Submission.DifferentialGeometry.Analysis.Spectral.tail_base_split

end DifferentialGeometry.Analysis.Spectral

end
