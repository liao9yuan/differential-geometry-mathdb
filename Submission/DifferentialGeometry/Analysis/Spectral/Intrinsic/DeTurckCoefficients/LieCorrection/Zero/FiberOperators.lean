import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.MetricJets.CovariantJetBounds
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieCorrection.Zero.ChartComponents
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieCorrection.Zero.NormalForm.ZeroOrderRemainderNormalForm
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurck.LieHigherOrderCoefficientField
import Submission.DifferentialGeometry.Geometry.Curvature.Metric.LeviCivita

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Submission.DifferentialGeometry.Geometry.Connection.Realization _root_.Submission.DifferentialGeometry.Tensor.Multilinear
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection

noncomputable section

set_option backward.isDefEq.respectTransparency false
open _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry.Tensor0SBundle
    ContinuousLinearMap
open scoped _root_.ENNReal _root_.NNReal _root_.BigOperators _root_.Manifold _root_.ContDiff _root_.Matrix _root_.Submission.Matrix

namespace DifferentialGeometry.Analysis.Spectral

open _root_.Submission.DifferentialGeometry.Integral.L2

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization
open _root_.Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
  [SigmaCompactSpace M]

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (deTurckVectorFieldCovariantDerivativeEndomorphism deTurckVectorFieldCovariantDerivativeEndomorphism_apply deTurckVectorFieldCovariantDerivativeEndomorphism_homSection_contMDiff
    deTurckVFCovDeriv connectionDifferenceOp_homSection_contMDiff metricConnectionDifferenceLoweredFib
    metricConnectionDifferenceLoweredFib_toModel metricConnectionDifferenceLoweredFib_contMDiff domDomCongrFibRank
    domDomCongrFibRank_apply tensor0SProdKappaFib tensor0SProdKappaFib_apply)
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.DeTurck
  (cometricDoubleTraceFib cometricDoubleTraceFib_toModel cometricDoubleTraceFib_contMDiff)

namespace LieCorrectionZeroFiberOperators

noncomputable def lieCorrectionZeroNEndo
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
      ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π b : M, TangentSpace I b) x)
    - PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
      ((PDE.DeTurck.deTurckVF (I := I) g₁ g_bg : Π b : M, TangentSpace I b) x)
    - deTurckVectorFieldCovariantDerivativeEndomorphism (I := I) g₁ g₀ x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroNEndo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroNEndo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroNEndo ``Submission.DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroNEndo

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem lieCorrectionZeroNEndo_homSection_contMDiff
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) x
        (lieCorrectionZeroNEndo (I := I) g₀ g₁ g_bg x)) := by
  have hBV : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) x
        (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
          ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π b : M, TangentSpace I b) x))) :=
    ContMDiff.clm_bundle_apply (b := id)
      (connectionDifferenceOp_homSection_contMDiff (I := I) g₁ g₀)
      (PDE.DeTurck.deTurckVF (I := I) g₁ g₀).contMDiff
  have hBW : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) x
        (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
          ((PDE.DeTurck.deTurckVF (I := I) g₁ g_bg : Π b : M, TangentSpace I b) x))) :=
    ContMDiff.clm_bundle_apply (b := id)
      (connectionDifferenceOp_homSection_contMDiff (I := I) g₁ g₀)
      (PDE.DeTurck.deTurckVF (I := I) g₁ g_bg).contMDiff
  have hW := deTurckVectorFieldCovariantDerivativeEndomorphism_homSection_contMDiff (I := I) g₁ g₀
  exact (hBV.sub_section hBW).sub_section hW

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroNEndo_homSection_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroNEndo_homSection_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroNEndo_homSection_contMDiff ``Submission.DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroNEndo_homSection_contMDiff

noncomputable def lieCorrectionZeroInsertionFib
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  slotInsertEndoFib (I := I) (M := M) 2 0 x (lieCorrectionZeroNEndo (I := I) g₀ g₁ g_bg x) +
    slotInsertEndoFib (I := I) (M := M) 2 1 x (lieCorrectionZeroNEndo (I := I) g₀ g₁ g_bg x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroInsertionFib then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroInsertionFib"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroInsertionFib ``Submission.DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroInsertionFib

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem lieCorrectionZeroInsertionFib_toModel
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (lieCorrectionZeroInsertionFib (I := I) g₀ g₁ g_bg x D) v =
      Tensor0SSpace.toModel D
          (Function.update v 0
            (tangentLinearMapToModel (lieCorrectionZeroNEndo (I := I) g₀ g₁ g_bg x) (v 0))) +
        Tensor0SSpace.toModel D
          (Function.update v 1
            (tangentLinearMapToModel (lieCorrectionZeroNEndo (I := I) g₀ g₁ g_bg x) (v 1))) := by
  rw [lieCorrectionZeroInsertionFib, add_apply, Tensor0SSpace.toModel_add,
    add_apply, slotInsertEndoFib_apply_eval, slotInsertEndoFib_apply_eval]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroInsertionFib_toModel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroInsertionFib_toModel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroInsertionFib_toModel ``Submission.DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroInsertionFib_toModel

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem lieCorrectionZeroInsertionFib_contMDiff
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (lieCorrectionZeroInsertionFib (I := I) g₀ g₁ g_bg x))) := by
  classical
  have h0 := slotInsertEndoFib_contMDiff (I := I) (M := M) g₀ 2 0
    (fun x => lieCorrectionZeroNEndo (I := I) g₀ g₁ g_bg x)
    (lieCorrectionZeroNEndo_homSection_contMDiff (I := I) g₀ g₁ g_bg)
  have h1 := slotInsertEndoFib_contMDiff (I := I) (M := M) g₀ 2 1
    (fun x => lieCorrectionZeroNEndo (I := I) g₀ g₁ g_bg x)
    (lieCorrectionZeroNEndo_homSection_contMDiff (I := I) g₀ g₁ g_bg)
  have hadd := ContMDiff.add_section
    (s := fun x => (show TensorRSSpace 2 2 I x from
      TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) 2 0 x
        (lieCorrectionZeroNEndo (I := I) g₀ g₁ g_bg x))))
    (t := fun x => (show TensorRSSpace 2 2 I x from
      TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) 2 1 x
        (lieCorrectionZeroNEndo (I := I) g₀ g₁ g_bg x))))
    h0 h1
  refine hadd.congr ?_
  intro x
  refine congrArg (TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
    (E := fun z : M => TensorRSSpace 2 2 I z) x) ?_
  rw [lieCorrectionZeroInsertionFib]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroInsertionFib_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroInsertionFib_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroInsertionFib_contMDiff ``Submission.DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroInsertionFib_contMDiff

noncomputable def lieCorrectionZeroTraceStep
    (g : SmoothRiemannianMetric I M) (p : ℕ)
    (σ : Equiv.Perm (Fin (p + 2))) (x : M) :
    Tensor0SSpace (p + 2) I x →L[ℝ] Tensor0SSpace p I x :=
  (cometricDoubleTraceFib (I := I) g p x).comp
    (domDomCongrFibRank (I := I) (p + 2) σ x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroTraceStep then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroTraceStep"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroTraceStep ``Submission.DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroTraceStep

def lieCorrectionZeroVectorBundleTracePermutation : Equiv.Perm (Fin 4) :=
  ⟨![1, 2, 3, 0], ![3, 0, 1, 2], by decide, by decide⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroVectorBundleTracePermutation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroVectorBundleTracePermutation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroVectorBundleTracePermutation ``Submission.DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroVectorBundleTracePermutation

noncomputable def lieCorrectionZeroVBFib
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  (2 : ℝ) • ((lieCorrectionZeroTraceStep (I := I) g₁ 2 lieCorrectionZeroVectorBundleTracePermutation x).comp
    ((tensor0SProdKappaFib (I := I) (p := 1) (q := 3) x
        (metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ g₀ x)).comp
      (Tensor0SBundle.interiorProduct (𝕜 := ℝ) (I := I) 1 x
        ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π b : M, TangentSpace I b) x))))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroVBFib then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroVBFib"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroVBFib ``Submission.DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroVBFib

def lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour : Equiv.Perm (Fin 5) :=
  ⟨![1, 4, 2, 3, 0], ![4, 0, 2, 3, 1], by decide, by decide⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour ``Submission.DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour

def lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne : Equiv.Perm (Fin 6) :=
  ⟨![2, 0, 3, 1, 4, 5], ![1, 3, 0, 2, 4, 5], by decide, by decide⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne ``Submission.DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne

def lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne : Equiv.Perm (Fin 4) :=
  ⟨![2, 0, 1, 3], ![1, 2, 0, 3], by decide, by decide⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne ``Submission.DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne

noncomputable def lieCorrectionZeroMixedConnectionHalfFib
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  (lieCorrectionZeroTraceStep (I := I) g₁ 2 lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne x).comp
    ((lieCorrectionZeroTraceStep (I := I) g₁ 4 lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne x).comp
      ((tensor0SProdKappaFib (I := I) (p := 3) (q := 3) x
          (metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ g_bg x)).comp
        ((lieCorrectionZeroTraceStep (I := I) g₁ 3 lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour x).comp
          (tensor0SProdKappaFib (I := I) (p := 2) (q := 3) x
            (metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ g₀ x)))))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroMixedConnectionHalfFib then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroMixedConnectionHalfFib"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroMixedConnectionHalfFib ``Submission.DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroMixedConnectionHalfFib

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
    [SigmaCompactSpace M] [NeZero (Module.finrank ℝ E)] in
theorem lieCorrectionZeroMixedConnectionHalfFib_apply
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) (D : Tensor0SSpace 2 I x) :
    lieCorrectionZeroMixedConnectionHalfFib (I := I) g₀ g₁ g_bg x D =
      lieCorrectionZeroTraceStep (I := I) g₁ 2
        lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne x
        (lieCorrectionZeroTraceStep (I := I) g₁ 4
          lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne x
          (tensor0SProdKappaFib (I := I) (p := 3) (q := 3) x
            (metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ g_bg x)
            (lieCorrectionZeroTraceStep (I := I) g₁ 3
              lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour x
              (tensor0SProdKappaFib (I := I) (p := 2) (q := 3) x
                (metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ g₀ x) D)))) := by
  rw [lieCorrectionZeroMixedConnectionHalfFib]
  repeat' rw [ContinuousLinearMap.comp_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroMixedConnectionHalfFib_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroMixedConnectionHalfFib_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroMixedConnectionHalfFib_apply ``Submission.DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroMixedConnectionHalfFib_apply

noncomputable def lieCorrectionZeroMixedConnectionFib
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  (2 : ℝ) • (lieCorrectionZeroMixedConnectionHalfFib (I := I) g₀ g₁ g_bg x +
    (domDomCongrFibRank (I := I) 2 (Equiv.swap 0 1) x).comp
      (lieCorrectionZeroMixedConnectionHalfFib (I := I) g₀ g₁ g_bg x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroMixedConnectionFib then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroMixedConnectionFib"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroMixedConnectionFib ``Submission.DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroMixedConnectionFib

noncomputable def lieCorrectionZeroRiemLoweredFib
    (g₀ : SmoothRiemannianMetric I M) (x : M) : Tensor0SSpace 4 I x :=
  metricRm04At (I := I) g₀ x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroRiemLoweredFib then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroRiemLoweredFib"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroRiemLoweredFib ``Submission.DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroRiemLoweredFib

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem lieCorrectionZeroRiemLoweredFib_toModel
    (g₀ : SmoothRiemannianMetric I M) (x : M) (v : Fin 4 → TangentSpace I x) :
    Tensor0SSpace.toModel (lieCorrectionZeroRiemLoweredFib (I := I) g₀ x)
        (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x (v i)) =
      g₀.inner x (DifferentialGeometry.Geometry.Curvature.riemannOp (LeviCivita (I := I) g₀) x
        (v 0) (v 1) (v 2)) (v 3) := by
  rw [Tensor0SSpace.toModel_apply_tangent, lieCorrectionZeroRiemLoweredFib,
    Tensor0SSpace.eval_eq, metricRm04At_eq_riemannCurvature04At]
  have hv : v = vec4 (v 0) (v 1) (v 2) (v 3) := by
    funext i
    fin_cases i <;> rfl
  conv_lhs => rw [hv]
  have hcov := leviCivita_contMDiffCovariantDerivativeLocally (I := I) g₀
  rw [CovariantDerivative.riemannCurvature04At_apply_const
      (hcov := hcov),
    connectionRiemannCurvatureField_tangentConst_eq_riemannOp (LeviCivita (I := I) g₀) hcov]
  exact g₀.symm x _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroRiemLoweredFib_toModel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroRiemLoweredFib_toModel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroRiemLoweredFib_toModel ``Submission.DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroRiemLoweredFib_toModel

def lieCorrectionZeroRiemPerm1 : Equiv.Perm (Fin 6) :=
  ⟨![1, 5, 2, 3, 4, 0], ![5, 0, 2, 3, 4, 1], by decide, by decide⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroRiemPerm1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroRiemPerm1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroRiemPerm1 ``Submission.DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroRiemPerm1

def lieCorrectionZeroRiemPerm2 : Equiv.Perm (Fin 4) :=
  ⟨![2, 3, 0, 1], ![2, 3, 0, 1], by decide, by decide⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroRiemPerm2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroRiemPerm2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroRiemPerm2 ``Submission.DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroRiemPerm2

noncomputable def lieCorrectionZeroRiemFib
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  (-1 : ℝ) • ((lieCorrectionZeroTraceStep (I := I) g₁ 2 lieCorrectionZeroRiemPerm2 x).comp
    ((lieCorrectionZeroTraceStep (I := I) g₀ 4 lieCorrectionZeroRiemPerm1 x).comp
      (tensor0SProdKappaFib (I := I) (p := 2) (q := 4) x
        (lieCorrectionZeroRiemLoweredFib (I := I) g₀ x))))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroRiemFib then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroRiemFib"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroRiemFib ``Submission.DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroRiemFib

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
theorem lieCorrectionZero_ddc_section_contMDiff
    {d : ℕ} (ρ : Equiv.Perm (Fin d)) (Z : ∀ x : M, Tensor0SSpace d I x)
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel d ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SSpace d I z) x (Z x))) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel d ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SSpace d I z) x
        (Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
          (ContinuousMultilinearMap.domDomCongr ρ (Tensor0SSpace.toModel (Z x))))) := by
  refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
    (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞))
    (Module.finBasis ℝ E)
    (fun x => (Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
        (ContinuousMultilinearMap.domDomCongr ρ (Tensor0SSpace.toModel (Z x))) :
          Tensor0SSpace d I x))).mpr ?_
  have hZcoord := (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
    (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞))
    (Module.finBasis ℝ E) (fun x => Z x)).mp hZ
  intro τ x₀
  refine (hZcoord (τ ∘ ρ) x₀).congr_of_eventuallyEq ?_
  filter_upwards [Filter.univ_mem] with x _
  rw [continuousMultilinearMap_basis_repr, continuousMultilinearMap_basis_repr]
  change (ContinuousMultilinearMap.domDomCongr ρ (Tensor0SSpace.toModel (Z x)))
      (fun j => tangentSpaceModelContinuousLinearEquiv (I := I) x
        ((Bundle.Trivialization.symmL ℝ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀) x)
          ((Module.finBasis ℝ E) (τ j)))) = _
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  simp only [tangentSpaceModelContinuousLinearEquiv_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZero_ddc_section_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZero_ddc_section_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZero_ddc_section_contMDiff ``Submission.DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZero_ddc_section_contMDiff

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
theorem lieCorrectionZero_prod_section_contMDiff
    {p q : ℕ} (Y : ∀ x : M, Tensor0SSpace p I x) (K : ∀ x : M, Tensor0SSpace q I x)
    (hY : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel p ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel p ℝ E)
        (E := fun z : M => Tensor0SSpace p I z) x (Y x)))
    (hK : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel q ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel q ℝ E)
        (E := fun z : M => Tensor0SSpace q I z) x (K x))) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (p + q) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel (p + q) ℝ E)
        (E := fun z : M => Tensor0SSpace (p + q) I z) x
        (tensor0SProdKappaFib (I := I) x (K x) (Y x))) := by
  classical
  have hbase : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (p + q) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel (p + q) ℝ E)
        (E := fun z : M => Tensor0SSpace (p + q) I z) x
        (Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
          (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q
            (Tensor0SSpace.toModel (Y x)) (Tensor0SSpace.toModel (K x))))) := by
    refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞))
      (Module.finBasis ℝ E)
      (fun x => (Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
          (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q
            (Tensor0SSpace.toModel (Y x)) (Tensor0SSpace.toModel (K x))) :
            Tensor0SSpace (p + q) I x))).mpr ?_
    have hYc := (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞))
      (Module.finBasis ℝ E) (fun x => Y x)).mp hY
    have hKc := (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞))
      (Module.finBasis ℝ E) (fun x => K x)).mp hK
    intro τ x₀
    refine (((contMDiffAt_const (I := I) (x := x₀) (n := (∞ : WithTop ℕ∞))
      (c := ContinuousLinearMap.mul ℝ ℝ)).clm_apply
        (hYc (τ ∘ Fin.castAdd q) x₀)).clm_apply
          (hKc (τ ∘ Fin.natAdd p) x₀)).congr_of_eventuallyEq ?_
    filter_upwards [Filter.univ_mem] with x _
    rw [continuousMultilinearMap_basis_repr, continuousMultilinearMap_basis_repr,
      continuousMultilinearMap_basis_repr]
    change (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q
        (Tensor0SSpace.toModel (Y x)) (Tensor0SSpace.toModel (K x)))
        (fun j => tangentSpaceModelContinuousLinearEquiv (I := I) x
          ((Bundle.Trivialization.symmL ℝ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀) x)
            ((Module.finBasis ℝ E) (τ j)))) = _
    rw [Bundle.continuousMultilinearMap.modelProduct_apply]
    simp only [tangentSpaceModelContinuousLinearEquiv_apply]
    rfl
  refine hbase.congr (fun x => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel (p + q) ℝ E)
    (E := fun z : M => Tensor0SSpace (p + q) I z) x t) ?_
  rw [tensor0SProdKappaFib_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZero_prod_section_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZero_prod_section_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZero_prod_section_contMDiff ``Submission.DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZero_prod_section_contMDiff

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem lieCorrectionZeroTraceStep_section_contMDiff
    (g : SmoothRiemannianMetric I M) (p : ℕ) (σ : Equiv.Perm (Fin (p + 2)))
    (Z : ∀ x : M, Tensor0SSpace (p + 2) I x)
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (p + 2) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel (p + 2) ℝ E)
        (E := fun z : M => Tensor0SSpace (p + 2) I z) x (Z x))) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel p ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel p ℝ E)
        (E := fun z : M => Tensor0SSpace p I z) x
        (lieCorrectionZeroTraceStep (I := I) g p σ x (Z x))) := by
  have hZρ := lieCorrectionZero_ddc_section_contMDiff (I := I) σ (fun x => Z x) hZ
  have hfield := ContMDiff.clm_bundle_apply (b := id)
    (cometricDoubleTraceFib_contMDiff (I := I) g p) hZρ
  refine hfield.congr (fun x => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel p ℝ E)
    (E := fun z : M => Tensor0SSpace p I z) x t) ?_
  rw [lieCorrectionZeroTraceStep, ContinuousLinearMap.comp_apply, domDomCongrFibRank_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroTraceStep_section_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroTraceStep_section_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroTraceStep_section_contMDiff ``Submission.DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroTraceStep_section_contMDiff

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem lieCorrectionZeroVBFib_contMDiff
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (lieCorrectionZeroVBFib (I := I) g₀ g₁ x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel 2 ℝ E) (V₁ := fun x : M => Tensor0SSpace 2 I x)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SSpace 2 I x)
    (φ := fun x => lieCorrectionZeroVBFib (I := I) g₀ g₁ x)
  intro Y
  have hip : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 1 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 1 ℝ E)
        (E := fun z : M => Tensor0SSpace 1 I z) x
        (Tensor0SBundle.interiorProduct (𝕜 := ℝ) (I := I) 1 x
          ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π b : M, TangentSpace I b) x) (Y x))) :=
    (Tensor0SBundle.contractTensor0SField (𝕜 := ℝ) (I := I) (n := (∞ : WithTop ℕ∞)) 1 Y
      (PDE.DeTurck.deTurckVF (I := I) g₁ g₀)).contMDiff
  have hprod := lieCorrectionZero_prod_section_contMDiff (I := I) (p := 1) (q := 3)
    (fun x => Tensor0SBundle.interiorProduct (𝕜 := ℝ) (I := I) 1 x
      ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π b : M, TangentSpace I b) x) (Y x))
    (fun x => metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ g₀ x)
    hip (metricConnectionDifferenceLoweredFib_contMDiff (I := I) g₁ g₁ g₀)
  have htr := lieCorrectionZeroTraceStep_section_contMDiff (I := I) g₁ 2 lieCorrectionZeroVectorBundleTracePermutation
    (fun x => tensor0SProdKappaFib (I := I) x (metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ g₀ x)
      (Tensor0SBundle.interiorProduct (𝕜 := ℝ) (I := I) 1 x
        ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π b : M, TangentSpace I b) x) (Y x)))
    hprod
  have hsmul : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        ((2 : ℝ) • lieCorrectionZeroTraceStep (I := I) g₁ 2 lieCorrectionZeroVectorBundleTracePermutation x
          (tensor0SProdKappaFib (I := I) x (metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ g₀ x)
            (Tensor0SBundle.interiorProduct (𝕜 := ℝ) (I := I) 1 x
              ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π b : M, TangentSpace I b) x) (Y x))))) :=
    ContMDiff.smul_section contMDiff_const htr
  refine hsmul.congr (fun x => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SSpace 2 I z) x t) ?_
  rw [lieCorrectionZeroVBFib]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroVBFib_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroVBFib_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroVBFib_contMDiff ``Submission.DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroVBFib_contMDiff

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem lieCorrectionZeroMixedConnectionHalfFib_section_contMDiff
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (Y : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun x : M => Tensor0SSpace 2 I x⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        (lieCorrectionZeroMixedConnectionHalfFib (I := I) g₀ g₁ g_bg x (Y x))) := by
  classical
  have hprod1 := lieCorrectionZero_prod_section_contMDiff (I := I) (p := 2) (q := 3)
    (fun x => Y x) (fun x => metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ g₀ x)
    Y.contMDiff (metricConnectionDifferenceLoweredFib_contMDiff (I := I) g₁ g₁ g₀)
  have htr1 := lieCorrectionZeroTraceStep_section_contMDiff (I := I) g₁ 3 lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour
    (fun x => tensor0SProdKappaFib (I := I) x (metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ g₀ x)
      (Y x)) hprod1
  have hprod2 := lieCorrectionZero_prod_section_contMDiff (I := I) (p := 3) (q := 3)
    (fun x => lieCorrectionZeroTraceStep (I := I) g₁ 3 lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour x
      (tensor0SProdKappaFib (I := I) x (metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ g₀ x) (Y x)))
    (fun x => metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ g_bg x)
    htr1 (metricConnectionDifferenceLoweredFib_contMDiff (I := I) g₁ g₁ g_bg)
  have htr2 := lieCorrectionZeroTraceStep_section_contMDiff (I := I) g₁ 4 lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne
    (fun x => tensor0SProdKappaFib (I := I) x (metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ g_bg x)
      (lieCorrectionZeroTraceStep (I := I) g₁ 3 lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour x
        (tensor0SProdKappaFib (I := I) x
          (metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ g₀ x) (Y x)))) hprod2
  have htr3 := lieCorrectionZeroTraceStep_section_contMDiff (I := I) g₁ 2 lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne
    (fun x => lieCorrectionZeroTraceStep (I := I) g₁ 4 lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne x
      (tensor0SProdKappaFib (I := I) x (metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ g_bg x)
        (lieCorrectionZeroTraceStep (I := I) g₁ 3 lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour x
          (tensor0SProdKappaFib (I := I) x
            (metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ g₀ x) (Y x))))) htr2
  refine htr3.congr (fun x => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SSpace 2 I z) x t) ?_
  rw [lieCorrectionZeroMixedConnectionHalfFib]
  repeat rw [ContinuousLinearMap.comp_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroMixedConnectionHalfFib_section_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroMixedConnectionHalfFib_section_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroMixedConnectionHalfFib_section_contMDiff ``Submission.DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroMixedConnectionHalfFib_section_contMDiff

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem lieCorrectionZeroMixedConnectionFib_contMDiff
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (lieCorrectionZeroMixedConnectionFib (I := I) g₀ g₁ g_bg x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel 2 ℝ E) (V₁ := fun x : M => Tensor0SSpace 2 I x)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SSpace 2 I x)
    (φ := fun x => lieCorrectionZeroMixedConnectionFib (I := I) g₀ g₁ g_bg x)
  intro Y
  have hhalf := lieCorrectionZeroMixedConnectionHalfFib_section_contMDiff (I := I) g₀ g₁ g_bg Y
  have hswap := lieCorrectionZero_ddc_section_contMDiff (I := I) (Equiv.swap 0 1)
    (fun x => lieCorrectionZeroMixedConnectionHalfFib (I := I) g₀ g₁ g_bg x (Y x)) hhalf
  have hswap' : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        (domDomCongrFibRank (I := I) 2 (Equiv.swap 0 1) x
          (lieCorrectionZeroMixedConnectionHalfFib (I := I) g₀ g₁ g_bg x (Y x)))) := by
    refine hswap.congr (fun x => ?_)
    refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
      (E := fun z : M => Tensor0SSpace 2 I z) x t) ?_
    rw [domDomCongrFibRank_apply]
  have hadd := ContMDiff.add_section
    (s := fun x => lieCorrectionZeroMixedConnectionHalfFib (I := I) g₀ g₁ g_bg x (Y x))
    (t := fun x => domDomCongrFibRank (I := I) 2 (Equiv.swap 0 1) x
      (lieCorrectionZeroMixedConnectionHalfFib (I := I) g₀ g₁ g_bg x (Y x))) hhalf hswap'
  have hsmul : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        ((2 : ℝ) • (lieCorrectionZeroMixedConnectionHalfFib (I := I) g₀ g₁ g_bg x (Y x) +
          domDomCongrFibRank (I := I) 2 (Equiv.swap 0 1) x
            (lieCorrectionZeroMixedConnectionHalfFib (I := I) g₀ g₁ g_bg x (Y x))))) :=
    ContMDiff.smul_section contMDiff_const hadd
  refine hsmul.congr (fun x => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SSpace 2 I z) x t) ?_
  rw [lieCorrectionZeroMixedConnectionFib]
  rw [smul_apply, add_apply, ContinuousLinearMap.comp_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroMixedConnectionFib_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroMixedConnectionFib_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroMixedConnectionFib_contMDiff ``Submission.DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroMixedConnectionFib_contMDiff

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
theorem lieCorrectionZeroRiemLoweredFib_section_contMDiff
    (g₀ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 4 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 4 ℝ E)
        (E := fun z : M => Tensor0SSpace 4 I z) x
        (lieCorrectionZeroRiemLoweredFib (I := I) g₀ x)) := by
  classical
  refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
    (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞))
    (Module.finBasis ℝ E)
    (fun x : M => (lieCorrectionZeroRiemLoweredFib (I := I) g₀ x : Tensor0SSpace 4 I x))).mpr ?_
  intro σ x₀
  set b := Module.finBasis ℝ E with hb
  set e₁ := _root_.FiberBundle.trivializationAt E (TangentSpace I : M → Type _) x₀ with he₁def
  have he₁ : x₀ ∈ e₁.baseSet := _root_.FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x₀
  have hframe := e₁.isLocalFrameOn_localFrame_baseSet I (⊤ : ℕ∞) b
  obtain ⟨Y, hY⟩ := hframe.exists_contMDiffSection_eqOn_nhd e₁.open_baseSet he₁
  have hscalar : ContMDiff I 𝓘(ℝ) ∞
      (fun x : M => g₀.inner x
        (DifferentialGeometry.Geometry.Curvature.riemannOp (LeviCivita (I := I) g₀) x
          ((Y (σ 0)) x) ((Y (σ 1)) x) ((Y (σ 2)) x)) ((Y (σ 3)) x)) :=
    DifferentialGeometry.Analysis.Spectral.mixedKernelScalar_global (I := I) g₀ g₀
      (Y (σ 0)).contMDiff (Y (σ 3)).contMDiff (Y (σ 1)).contMDiff (Y (σ 2)).contMDiff
  refine hscalar.contMDiffAt.congr_of_eventuallyEq ?_
  have h_base₁ : ∀ᶠ x in nhds x₀, x ∈ e₁.baseSet := e₁.open_baseSet.mem_nhds he₁
  filter_upwards [h_base₁, hY] with x hx₁ hYx
  rw [continuousMultilinearMap_basis_repr]
  have hframe' : ∀ j : Fin 4, e₁.symmL ℝ x (b (σ j)) = (Y (σ j)) x := by
    intro j
    rw [hYx (σ j), Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
    exact Trivialization.symmL_apply e₁ hx₁ (b (σ j))
  change Tensor0SSpace.toModel (lieCorrectionZeroRiemLoweredFib (I := I) g₀ x)
      (fun j : Fin 4 => tangentSpaceModelContinuousLinearEquiv (I := I) x
        (e₁.symmL ℝ x (b (σ j)))) = _
  rw [lieCorrectionZeroRiemLoweredFib_toModel]
  rw [hframe' 0, hframe' 1, hframe' 2, hframe' 3]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroRiemLoweredFib_section_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroRiemLoweredFib_section_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroRiemLoweredFib_section_contMDiff ``Submission.DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroRiemLoweredFib_section_contMDiff

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem lieCorrectionZeroRiemFib_contMDiff
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (lieCorrectionZeroRiemFib (I := I) g₀ g₁ x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel 2 ℝ E) (V₁ := fun x : M => Tensor0SSpace 2 I x)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SSpace 2 I x)
    (φ := fun x => lieCorrectionZeroRiemFib (I := I) g₀ g₁ x)
  intro Y
  have hprod := lieCorrectionZero_prod_section_contMDiff (I := I) (p := 2) (q := 4)
    (fun x => Y x) (fun x => lieCorrectionZeroRiemLoweredFib (I := I) g₀ x)
    Y.contMDiff (lieCorrectionZeroRiemLoweredFib_section_contMDiff (I := I) g₀)
  have htr1 := lieCorrectionZeroTraceStep_section_contMDiff (I := I) g₀ 4 lieCorrectionZeroRiemPerm1
    (fun x => tensor0SProdKappaFib (I := I) x (lieCorrectionZeroRiemLoweredFib (I := I) g₀ x) (Y x))
    hprod
  have htr2 := lieCorrectionZeroTraceStep_section_contMDiff (I := I) g₁ 2 lieCorrectionZeroRiemPerm2
    (fun x => lieCorrectionZeroTraceStep (I := I) g₀ 4 lieCorrectionZeroRiemPerm1 x
      (tensor0SProdKappaFib (I := I) x (lieCorrectionZeroRiemLoweredFib (I := I) g₀ x) (Y x))) htr1
  have hsmul : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        ((-1 : ℝ) • lieCorrectionZeroTraceStep (I := I) g₁ 2 lieCorrectionZeroRiemPerm2 x
          (lieCorrectionZeroTraceStep (I := I) g₀ 4 lieCorrectionZeroRiemPerm1 x
            (tensor0SProdKappaFib (I := I) x
              (lieCorrectionZeroRiemLoweredFib (I := I) g₀ x) (Y x))))) :=
    ContMDiff.smul_section contMDiff_const htr2
  refine hsmul.congr (fun x => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SSpace 2 I z) x t) ?_
  rw [lieCorrectionZeroRiemFib]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroRiemFib_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroRiemFib_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroRiemFib_contMDiff ``Submission.DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroRiemFib_contMDiff

noncomputable def lieCorrectionZeroTotalFib
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  lieCorrectionZeroInsertionFib (I := I) g₀ g₁ g_bg x + lieCorrectionZeroVBFib (I := I) g₀ g₁ x +
    lieCorrectionZeroMixedConnectionFib (I := I) g₀ g₁ g_bg x + lieCorrectionZeroRiemFib (I := I) g₀ g₁ x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroTotalFib then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroTotalFib"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroTotalFib ``Submission.DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroTotalFib

omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem lieCorrectionZeroTotalFib_contMDiff
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (lieCorrectionZeroTotalFib (I := I) g₀ g₁ g_bg x))) := by
  classical
  have h12 := ContMDiff.add_section
    (s := fun x => (show TensorRSSpace 2 2 I x from
      TensorRSSpace.ofCLM (lieCorrectionZeroInsertionFib (I := I) g₀ g₁ g_bg x)))
    (t := fun x => (show TensorRSSpace 2 2 I x from
      TensorRSSpace.ofCLM (lieCorrectionZeroVBFib (I := I) g₀ g₁ x)))
    (lieCorrectionZeroInsertionFib_contMDiff (I := I) g₀ g₁ g_bg)
    (lieCorrectionZeroVBFib_contMDiff (I := I) g₀ g₁)
  have h123 := ContMDiff.add_section
    (s := fun x => (show TensorRSSpace 2 2 I x from
      TensorRSSpace.ofCLM (lieCorrectionZeroInsertionFib (I := I) g₀ g₁ g_bg x)) +
      (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (lieCorrectionZeroVBFib (I := I) g₀ g₁ x)))
    (t := fun x => (show TensorRSSpace 2 2 I x from
      TensorRSSpace.ofCLM (lieCorrectionZeroMixedConnectionFib (I := I) g₀ g₁ g_bg x)))
    h12 (lieCorrectionZeroMixedConnectionFib_contMDiff (I := I) g₀ g₁ g_bg)
  have h1234 := ContMDiff.add_section
    (s := fun x => ((show TensorRSSpace 2 2 I x from
      TensorRSSpace.ofCLM (lieCorrectionZeroInsertionFib (I := I) g₀ g₁ g_bg x)) +
      (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (lieCorrectionZeroVBFib (I := I) g₀ g₁ x))) +
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (lieCorrectionZeroMixedConnectionFib (I := I) g₀ g₁ g_bg x)))
    (t := fun x => (show TensorRSSpace 2 2 I x from
      TensorRSSpace.ofCLM (lieCorrectionZeroRiemFib (I := I) g₀ g₁ x)))
    h123 (lieCorrectionZeroRiemFib_contMDiff (I := I) g₀ g₁)
  refine h1234.congr (fun x => ?_)
  refine congrArg (TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
    (E := fun z : M => TensorRSSpace 2 2 I z) x) ?_
  rw [lieCorrectionZeroTotalFib]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroTotalFib_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroTotalFib_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroTotalFib_contMDiff ``Submission.DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators.lieCorrectionZeroTotalFib_contMDiff

end LieCorrectionZeroFiberOperators

open _root_.Submission.DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators

def lieCorrectionZeroField (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (lieCorrectionZeroTotalFib (I := I) g₀ g₁ g_bg x))
      contMDiff_toFun := lieCorrectionZeroTotalFib_contMDiff (I := I) g₀ g₁ g_bg }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.lieCorrectionZeroField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.lieCorrectionZeroField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.lieCorrectionZeroField ``Submission.DifferentialGeometry.Analysis.Spectral.lieCorrectionZeroField

omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem lieCorrectionZeroField_apply
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    (lieCorrectionZeroField (I := I) (M := M) g₀ g₁ g_bg).toSection x =
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (lieCorrectionZeroTotalFib (I := I) g₀ g₁ g_bg x)) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.lieCorrectionZeroField_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.lieCorrectionZeroField_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.lieCorrectionZeroField_apply ``Submission.DifferentialGeometry.Analysis.Spectral.lieCorrectionZeroField_apply

end DifferentialGeometry.Analysis.Spectral

end
