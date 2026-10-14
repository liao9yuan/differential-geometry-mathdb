import Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert.OperatorField.ApplicationJetWindow
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.Pairing.TopOrder.DifferenceEnergy
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.MetricPrincipalDefect.Symmetry
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.RHS.CovariantJetCancellation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.ContDiff _root_.RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Spectral


open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization
open _root_.Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

def firstOrderCoefficientAction (g : SmoothRiemannianMetric I M)
    (C₀ : SmoothCcTensor g 2 2) (C₁ : SmoothCcTensor g 3 2)
    (W : SmoothCcTensor g 0 2) : SmoothCcTensor g 0 2 :=
  operatorFieldApply (I := I) (M := M) g 2 2 C₀ W +
    operatorFieldApply (I := I) (M := M) g 3 2 C₁
      (iteratedCovGrad (I := I) g 0 2 1 W)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.firstOrderCoefficientAction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.firstOrderCoefficientAction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.firstOrderCoefficientAction ``Submission.DifferentialGeometry.Analysis.Spectral.firstOrderCoefficientAction

omit [NeZero (Module.finrank Real E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem zero_metricPerturbation_bound (g : SmoothRiemannianMetric I M) :
    metricCauchySchwarzBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) 0 := by
  intro x v w
  have h0 : (0 : SmoothCcTensor g 0 2) =
      (0 : Real) • (0 : SmoothCcTensor g 0 2) := (zero_smul Real _).symm
  rw [h0, ccTensorBilinSymm_smul]
  simp only [_root_.MulZeroClass.zero_mul, abs_zero, le_refl]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.zero_metricPerturbation_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.zero_metricPerturbation_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.zero_metricPerturbation_bound ``Submission.DifferentialGeometry.Analysis.Spectral.zero_metricPerturbation_bound

omit [NeZero (Module.finrank Real E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem zero_metricPerturbation_symmetric (g : SmoothRiemannianMetric I M) :
    ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g (0 : SmoothCcTensor g 0 2) x v w =
        smoothCcTensorBilinForm (I := I) g (0 : SmoothCcTensor g 0 2) x w v := by
  intro x v w
  have h0 : (0 : SmoothCcTensor g 0 2) =
      (0 : Real) • (0 : SmoothCcTensor g 0 2) := (zero_smul Real _).symm
  rw [h0]
  simp only [ccTensorBilin_apply, ccTensorModel_smul,
    smul_apply, smul_eq_mul, _root_.MulZeroClass.zero_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.zero_metricPerturbation_symmetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.zero_metricPerturbation_symmetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.zero_metricPerturbation_symmetric ``Submission.DifferentialGeometry.Analysis.Spectral.zero_metricPerturbation_symmetric

def metricPerturbationPathFromZero (g : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2)
    {δ : Real}
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g W) δ) (s : Real) :
    SmoothRiemannianMetric I M :=
  metricPerturbationPath (I := I) g W 0 hδ (zero_metricPerturbation_bound (I := I) (M := M) g) s

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.metricPerturbationPathFromZero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.metricPerturbationPathFromZero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.metricPerturbationPathFromZero ``Submission.DifferentialGeometry.Analysis.Spectral.metricPerturbationPathFromZero

def backgroundZeroOrderCoefficient (g g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 2 2 :=
  (deTurckLieCoeffField (I := I) (M := M) g g g_bg +
      lieCorrectionZeroField (I := I) (M := M) g g g_bg) +
    metricPrincipalDefectCurvCoeff (I := I) g g

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.backgroundZeroOrderCoefficient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.backgroundZeroOrderCoefficient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.backgroundZeroOrderCoefficient ``Submission.DifferentialGeometry.Analysis.Spectral.backgroundZeroOrderCoefficient

def backgroundFirstOrderCoefficient (g g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 3 2 :=
  deTurckLieFirstOrderCoeff (I := I) (M := M) g g g_bg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.backgroundFirstOrderCoefficient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.backgroundFirstOrderCoefficient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.backgroundFirstOrderCoefficient ``Submission.DifferentialGeometry.Analysis.Spectral.backgroundFirstOrderCoefficient

def metricDependentZeroOrderCoefficient (g g1 g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 2 2 :=
  (-2 : Real) •
      linearizedRicciConnectionDifferenceOrder0CoeffField (I := I) (M := M) g g1 +
    ((deTurckLieCoeffField (I := I) (M := M) g g1 g_bg +
        lieCorrectionZeroField (I := I) (M := M) g g1 g_bg) +
      metricPrincipalDefectCurvCoeff (I := I) g g1) -
    backgroundZeroOrderCoefficient (I := I) (M := M) g g_bg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.metricDependentZeroOrderCoefficient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.metricDependentZeroOrderCoefficient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.metricDependentZeroOrderCoefficient ``Submission.DifferentialGeometry.Analysis.Spectral.metricDependentZeroOrderCoefficient

def metricDependentFirstOrderCoefficient (g g1 g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 3 2 :=
  (-2 : Real) •
      linearizedRicciConnectionDifferenceOrder1CoeffField (I := I) (M := M) g g1 +
    deTurckLieFirstOrderCoeff (I := I) (M := M) g g1 g_bg -
    backgroundFirstOrderCoefficient (I := I) (M := M) g g_bg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.metricDependentFirstOrderCoefficient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.metricDependentFirstOrderCoefficient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.metricDependentFirstOrderCoefficient ``Submission.DifferentialGeometry.Analysis.Spectral.metricDependentFirstOrderCoefficient

def backgroundLowOrderAction (g g_bg : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g 0 2) : SmoothCcTensor g 0 2 :=
  firstOrderCoefficientAction (I := I) (M := M) g
    (backgroundZeroOrderCoefficient (I := I) (M := M) g g_bg)
    (backgroundFirstOrderCoefficient (I := I) (M := M) g g_bg) W

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.backgroundLowOrderAction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.backgroundLowOrderAction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.backgroundLowOrderAction ``Submission.DifferentialGeometry.Analysis.Spectral.backgroundLowOrderAction

def metricDependentLowOrderAction (g g1 g_bg : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g 0 2) : SmoothCcTensor g 0 2 :=
  firstOrderCoefficientAction (I := I) (M := M) g
    (metricDependentZeroOrderCoefficient (I := I) (M := M) g g1 g_bg)
    (metricDependentFirstOrderCoefficient (I := I) (M := M) g g1 g_bg) W

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.metricDependentLowOrderAction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.metricDependentLowOrderAction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.metricDependentLowOrderAction ``Submission.DifferentialGeometry.Analysis.Spectral.metricDependentLowOrderAction

omit [SigmaCompactSpace M] in
theorem lowOrderZeroCoefficient_eq_background_add_metricDependent
    (g g1 g_bg : SmoothRiemannianMetric I M) :
    let A0 :=
      (-2 : Real) •
          linearizedRicciConnectionDifferenceOrder0CoeffField (I := I) (M := M) g g1 +
        (deTurckLieCoeffField (I := I) (M := M) g g1 g_bg +
          lieCorrectionZeroField (I := I) (M := M) g g1 g_bg)
    A0 + metricPrincipalDefectCurvCoeff (I := I) g g1 =
      backgroundZeroOrderCoefficient (I := I) (M := M) g g_bg +
        metricDependentZeroOrderCoefficient (I := I) (M := M) g g1 g_bg := by
  dsimp only
  simp only [backgroundZeroOrderCoefficient, metricDependentZeroOrderCoefficient]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.lowOrderZeroCoefficient_eq_background_add_metricDependent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.lowOrderZeroCoefficient_eq_background_add_metricDependent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.lowOrderZeroCoefficient_eq_background_add_metricDependent ``Submission.DifferentialGeometry.Analysis.Spectral.lowOrderZeroCoefficient_eq_background_add_metricDependent

omit [SigmaCompactSpace M] in
theorem principalCoefficientAction_decomposition
    (g g1 : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g 0 2) :
    operatorFieldApply (I := I) (M := M) g 4 2
        (deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g1)
        (iteratedCovGrad (I := I) g 0 2 2 W) =
      (rawTensorConnLapSmooth (I := I) g 0 2 W +
          deTurckPrincipalCometricTerm (I := I) (M := M) g g1 W) +
        operatorFieldApply (I := I) (M := M) g 2 2
          (metricPrincipalDefectCurvCoeff (I := I) g g1) W := by
  have hlap : rawTensorConnLapSmooth (I := I) g 0 2 W =
      operatorFieldApply (I := I) (M := M) g 4 2
        (cometricDoubleTraceCoefficient (I := I) (M := M) g g)
        (iteratedCovGrad (I := I) g 0 2 2 W) := by
    apply smoothCcTensor_ext_of_unitModel
    intro x
    apply ContinuousMultilinearMap.ext
    intro v
    exact rawTensorConnLapSmooth_eq_operatorFieldApplication_cometricDoubleTrace
      (I := I) (M := M) g W x v
  rw [show deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g1 =
      cometricDoubleTraceCoefficient (I := I) (M := M) g g1 +
        (deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g1 -
          cometricDoubleTraceCoefficient (I := I) (M := M) g g1) by abel]
  rw [operatorFieldApplication_add_left,
    metricPrincipalDefect_curvature_contraction (I := I) (M := M) g g1 W,
    iteratedCovGrad_zero, deTurckPrincipalCometricTerm,
    deTurckPrincipalCometricCoeff, operatorFieldApplication_sub_left, hlap]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.principalCoefficientAction_decomposition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.principalCoefficientAction_decomposition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.principalCoefficientAction_decomposition ``Submission.DifferentialGeometry.Analysis.Spectral.principalCoefficientAction_decomposition

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank Real E)] [BoundarylessManifold I M] in
private theorem edgeLower_add
    (g : SmoothRiemannianMetric I M)
    (C0 D0 : SmoothCcTensor g 2 2) (C1 D1 : SmoothCcTensor g 3 2)
    (W : SmoothCcTensor g 0 2) :
    firstOrderCoefficientAction (I := I) (M := M) g (C0 + D0) (C1 + D1) W =
      firstOrderCoefficientAction (I := I) (M := M) g C0 C1 W +
        firstOrderCoefficientAction (I := I) (M := M) g D0 D1 W := by
  simp only [firstOrderCoefficientAction, operatorFieldApplication_add_left]
  abel

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.edgeLower_add
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.edgeLower_add target :: scope.openDecls } }

def ricciDeTurckLowOrderAction (g g₁ : SmoothRiemannianMetric I M)
    (C₀ : SmoothCcTensor g 2 2) (C₁ : SmoothCcTensor g 3 2)
    (W : SmoothCcTensor g 0 2) : SmoothCcTensor g 0 2 :=
  (rawTensorConnLapSmooth (I := I) g 0 2 W +
      deTurckPrincipalCometricTerm (I := I) (M := M) g g₁ W) +
    firstOrderCoefficientAction (I := I) (M := M) g C₀ C₁ W

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.ricciDeTurckLowOrderAction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.ricciDeTurckLowOrderAction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.ricciDeTurckLowOrderAction ``Submission.DifferentialGeometry.Analysis.Spectral.ricciDeTurckLowOrderAction

omit [SigmaCompactSpace M] in
theorem ricciDeTurckRhsSlope_decomposition
    (g g_bg : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2)
    (hWsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g W x v w =
        smoothCcTensorBilinForm (I := I) g W x w v)
    {δ : Real} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g W) δ)
    (x : M) (v w : TangentSpace I x) {s : Real} (hs : s ∈ Set.Ioo (0 : Real) 1) :
    DeTurckCoefficients.rhsSumSlope (I := I) g g_bg W 0
        hδ_lt hδ (show (0 : Real) < 1 by norm_num)
        (zero_metricPerturbation_bound (I := I) (M := M) g) x v w s =
      unitModel (I := I) (M := M) g 2
        ((rawTensorConnLapSmooth (I := I) g 0 2 W +
            deTurckPrincipalCometricTerm (I := I) (M := M) g
              (metricPerturbationPathFromZero (I := I) (M := M) g W hδ s) W) +
          (backgroundLowOrderAction (I := I) (M := M) g g_bg W +
            metricDependentLowOrderAction (I := I) (M := M) g
              (metricPerturbationPathFromZero (I := I) (M := M) g W hδ s) g_bg W)) x ![v, w] := by
  let gs : SmoothRiemannianMetric I M :=
    metricPerturbationPathFromZero (I := I) (M := M) g W hδ s
  let R0 : SmoothCcTensor g 2 2 :=
    DeTurckCoefficients.ricciDeTurckRemainderZeroOrderCoefficient (I := I) (M := M)
      g g_bg W 0 hδ (zero_metricPerturbation_bound (I := I) (M := M) g) s
  let R1 : SmoothCcTensor g 3 2 :=
    DeTurckCoefficients.ricciDeTurckRemainderFirstOrderCoefficient (I := I) (M := M)
      g g_bg W 0 hδ (zero_metricPerturbation_bound (I := I) (M := M) g) s
  have hlow0 : R0 + metricPrincipalDefectCurvCoeff (I := I) g gs =
      backgroundZeroOrderCoefficient (I := I) (M := M) g g_bg +
        metricDependentZeroOrderCoefficient (I := I) (M := M) g gs g_bg := by
    simp only [R0, gs, metricPerturbationPathFromZero, DeTurckCoefficients.ricciDeTurckRemainderZeroOrderCoefficient,
      linearizedRicciConnectionDifferenceOrder0Coeff, backgroundZeroOrderCoefficient, metricDependentZeroOrderCoefficient]
    abel
  have hlow1 : R1 =
      backgroundFirstOrderCoefficient (I := I) (M := M) g g_bg +
        metricDependentFirstOrderCoefficient (I := I) (M := M) g gs g_bg := by
    simp only [R1, gs, metricPerturbationPathFromZero, DeTurckCoefficients.ricciDeTurckRemainderFirstOrderCoefficient,
      linearizedRicciConnectionDifferenceOrder1Coeff, backgroundFirstOrderCoefficient, metricDependentFirstOrderCoefficient]
    abel
  have htop := principalCoefficientAction_decomposition (I := I) (M := M) g gs W
  have hsmooth :
      operatorFieldApply (I := I) (M := M) g 2 2 R0 W +
          operatorFieldApply (I := I) (M := M) g 3 2 R1
            (iteratedCovGrad (I := I) g 0 2 1 W) +
          operatorFieldApply (I := I) (M := M) g 4 2
            (deTurckMetricPrincipalDefectTotal (I := I) (M := M) g gs)
            (iteratedCovGrad (I := I) g 0 2 2 W) =
        (rawTensorConnLapSmooth (I := I) g 0 2 W +
            deTurckPrincipalCometricTerm (I := I) (M := M) g gs W) +
          (backgroundLowOrderAction (I := I) (M := M) g g_bg W +
            metricDependentLowOrderAction (I := I) (M := M) g gs g_bg W) := by
    rw [htop]
    calc
      operatorFieldApply (I := I) (M := M) g 2 2 R0 W +
            operatorFieldApply (I := I) (M := M) g 3 2 R1
              (iteratedCovGrad (I := I) g 0 2 1 W) +
            ((rawTensorConnLapSmooth (I := I) g 0 2 W +
                deTurckPrincipalCometricTerm (I := I) (M := M) g gs W) +
              operatorFieldApply (I := I) (M := M) g 2 2
                (metricPrincipalDefectCurvCoeff (I := I) g gs) W) =
          (rawTensorConnLapSmooth (I := I) g 0 2 W +
              deTurckPrincipalCometricTerm (I := I) (M := M) g gs W) +
            firstOrderCoefficientAction (I := I) (M := M) g
              (R0 + metricPrincipalDefectCurvCoeff (I := I) g gs) R1 W := by
                simp only [firstOrderCoefficientAction, operatorFieldApplication_add_left]
                abel
      _ = (rawTensorConnLapSmooth (I := I) g 0 2 W +
              deTurckPrincipalCometricTerm (I := I) (M := M) g gs W) +
            firstOrderCoefficientAction (I := I) (M := M) g
              (backgroundZeroOrderCoefficient (I := I) (M := M) g g_bg +
                metricDependentZeroOrderCoefficient (I := I) (M := M) g gs g_bg)
              (backgroundFirstOrderCoefficient (I := I) (M := M) g g_bg +
                metricDependentFirstOrderCoefficient (I := I) (M := M) g gs g_bg) W := by
                  rw [hlow0, hlow1]
      _ = (rawTensorConnLapSmooth (I := I) g 0 2 W +
              deTurckPrincipalCometricTerm (I := I) (M := M) g gs W) +
            (backgroundLowOrderAction (I := I) (M := M) g g_bg W +
              metricDependentLowOrderAction (I := I) (M := M) g gs g_bg W) := by
                  rw [edgeLower_add]
                  rfl
  have hslope := DeTurckCoefficients.ricciDeTurckRemainderSlope_eq_terms
    (I := I) g g_bg W 0 hWsymm (zero_metricPerturbation_symmetric (I := I) (M := M) g)
      hδ_lt hδ (show (0 : Real) < 1 by norm_num)
      (zero_metricPerturbation_bound (I := I) (M := M) g) x v w hs
  simp only [sub_zero, iteratedCovGrad_zero] at hslope
  rw [hslope]
  change unitModel (I := I) (M := M) g 2
      (operatorFieldApply (I := I) (M := M) g 2 2 R0 W +
        operatorFieldApply (I := I) (M := M) g 3 2 R1
          (iteratedCovGrad (I := I) g 0 2 1 W) +
        operatorFieldApply (I := I) (M := M) g 4 2
          (deTurckMetricPrincipalDefectTotal (I := I) (M := M) g gs)
          (iteratedCovGrad (I := I) g 0 2 2 W)) x ![v, w] = _
  rw [hsmooth]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.ricciDeTurckRhsSlope_decomposition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.ricciDeTurckRhsSlope_decomposition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.ricciDeTurckRhsSlope_decomposition ``Submission.DifferentialGeometry.Analysis.Spectral.ricciDeTurckRhsSlope_decomposition

omit [NeZero (Module.finrank Real E)] [BoundarylessManifold I M] in
theorem firstOrderCoefficientAction_pairing_bound
    (g : SmoothRiemannianMetric I M)
    (C₀ : SmoothCcTensor g 2 2) (C₁ : SmoothCcTensor g 3 2)
    (W : SmoothCcTensor g 0 2) {B₀ B₁ : Real}
    (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁)
    (hC₀ : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 2 2 x
        (C₀.toSection x) ≤ B₀ ^ 2)
    (hC₁ : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 3 2 x
        (C₁.toSection x) ≤ B₁ ^ 2) :
    tensorL2Inner (I := I) (M := M) g 0 2 W.toFun
        (firstOrderCoefficientAction (I := I) (M := M) g C₀ C₁ W).toFun ≤
      (1 / 4 : Real) *
          ‖iteratedCovGrad (I := I) g 0 2 1 W‖ ^ 2 +
        (B₀ + B₁ ^ 2) * ‖W‖ ^ 2 := by
  let D : SmoothCcTensor g 0 3 :=
    iteratedCovGrad (I := I) g 0 2 1 W
  let U₀ : SmoothCcTensor g 0 2 :=
    operatorFieldApply (I := I) (M := M) g 2 2 C₀ W
  let U₁ : SmoothCcTensor g 0 2 :=
    operatorFieldApply (I := I) (M := M) g 3 2 C₁ D
  have hU₀ : ‖U₀‖ ≤ B₀ * ‖W‖ := by
    dsimp only [U₀]
    exact operatorFieldApply_l2_le_of_pointwise_fiberNormSq_bound_left
      (I := I) (M := M) g 2 2 C₀ W B₀ hB₀ hC₀
  have hU₁ : ‖U₁‖ ≤ B₁ * ‖D‖ := by
    dsimp only [U₁]
    exact operatorFieldApply_l2_le_of_pointwise_fiberNormSq_bound_left
      (I := I) (M := M) g 3 2 C₁ D B₁ hB₁ hC₁
  have hpair₀ :
      tensorL2Inner (I := I) (M := M) g 0 2 W.toFun U₀.toFun ≤
        B₀ * ‖W‖ ^ 2 := by
    rw [← SmoothCcTensor.inner_def (I := I) (M := M) W U₀]
    calc
      ⟪W, U₀⟫ ≤ ‖W‖ * ‖U₀‖ := real_inner_le_norm W U₀
      _ ≤ ‖W‖ * (B₀ * ‖W‖) :=
        mul_le_mul_of_nonneg_left hU₀ (norm_nonneg W)
      _ = B₀ * ‖W‖ ^ 2 := by ring
  have hpair₁ :
      tensorL2Inner (I := I) (M := M) g 0 2 W.toFun U₁.toFun ≤
        B₁ * ‖W‖ * ‖D‖ := by
    rw [← SmoothCcTensor.inner_def (I := I) (M := M) W U₁]
    calc
      ⟪W, U₁⟫ ≤ ‖W‖ * ‖U₁‖ := real_inner_le_norm W U₁
      _ ≤ ‖W‖ * (B₁ * ‖D‖) :=
        mul_le_mul_of_nonneg_left hU₁ (norm_nonneg W)
      _ = B₁ * ‖W‖ * ‖D‖ := by ring
  have hyoung :
      B₁ * ‖W‖ * ‖D‖ ≤
        (1 / 4 : Real) * ‖D‖ ^ 2 + B₁ ^ 2 * ‖W‖ ^ 2 := by
    nlinarith [sq_nonneg ((1 / 2 : Real) * ‖D‖ - B₁ * ‖W‖)]
  have hadd :
      tensorL2Inner (I := I) (M := M) g 0 2 W.toFun
          (firstOrderCoefficientAction (I := I) (M := M) g C₀ C₁ W).toFun =
        tensorL2Inner (I := I) (M := M) g 0 2 W.toFun U₀.toFun +
          tensorL2Inner (I := I) (M := M) g 0 2 W.toFun U₁.toFun := by
    rw [← SmoothCcTensor.inner_def (I := I) (M := M) W
      (firstOrderCoefficientAction (I := I) (M := M) g C₀ C₁ W),
      ← SmoothCcTensor.inner_def (I := I) (M := M) W U₀,
      ← SmoothCcTensor.inner_def (I := I) (M := M) W U₁]
    simp only [firstOrderCoefficientAction, U₀, U₁, D, inner_add_right]
  rw [hadd]
  dsimp only [D] at hyoung ⊢
  nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.firstOrderCoefficientAction_pairing_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.firstOrderCoefficientAction_pairing_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.firstOrderCoefficientAction_pairing_bound ``Submission.DifferentialGeometry.Analysis.Spectral.firstOrderCoefficientAction_pairing_bound

theorem ricciDeTurckLowOrderAction_pairing_bound
    (g : SmoothRiemannianMetric I M) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (C₀ : SmoothCcTensor g 2 2) (C₁ : SmoothCcTensor g 3 2)
        (W : SmoothCcTensor g 0 2) {B₀ B₁ δ : Real},
        0 ≤ B₀ → 0 ≤ B₁ → δ < 1 / 2 → 0 ≤ δ →
        (∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g.inner y v w +
            ccTensorBilinSymm (I := I) g W y v w) →
        metricCauchySchwarzBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g W) δ →
        ccTensor02Symm (I := I) (M := M) g W = W →
        δ / (1 - δ) + C * δ ≤ 1 / 2 →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 2 2 x
            (C₀.toSection x) ≤ B₀ ^ 2) →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 3 2 x
            (C₁.toSection x) ≤ B₁ ^ 2) →
        tensorL2Inner (I := I) (M := M) g 0 2 W.toFun
            (ricciDeTurckLowOrderAction (I := I) (M := M) g g₁ C₀ C₁ W).toFun ≤
          -(1 / 4 : Real) *
              ‖iteratedCovGrad (I := I) g 0 2 1 W‖ ^ 2 +
            (B₀ + B₁ ^ 2) * ‖W‖ ^ 2 := by
  obtain ⟨C, hC, hprincipal⟩ := principalDifference_pairing_half_bound (I := I) (M := M) g
  refine ⟨C, hC, ?_⟩
  intro g₁ C₀ C₁ W B₀ B₁ δ hB₀ hB₁ hδ hδ0 htie hbound hsymm hsmall hC₀ hC₁
  have hp := hprincipal g₁ W hδ hδ0 htie hbound hsymm hsmall
  rw [SmoothCcTensor.norm_toL2] at hp
  have hlo := firstOrderCoefficientAction_pairing_bound (I := I) (M := M)
    g C₀ C₁ W hB₀ hB₁ hC₀ hC₁
  have hadd :
      tensorL2Inner (I := I) (M := M) g 0 2 W.toFun
          (ricciDeTurckLowOrderAction (I := I) (M := M) g g₁ C₀ C₁ W).toFun =
        tensorL2Inner (I := I) (M := M) g 0 2 W.toFun
            (rawTensorConnLapSmooth (I := I) g 0 2 W +
              deTurckPrincipalCometricTerm (I := I) (M := M) g g₁ W).toFun +
          tensorL2Inner (I := I) (M := M) g 0 2 W.toFun
            (firstOrderCoefficientAction (I := I) (M := M) g C₀ C₁ W).toFun := by
    rw [← SmoothCcTensor.inner_def (I := I) (M := M) W
      (ricciDeTurckLowOrderAction (I := I) (M := M) g g₁ C₀ C₁ W),
      ← SmoothCcTensor.inner_def (I := I) (M := M) W
        (rawTensorConnLapSmooth (I := I) g 0 2 W +
          deTurckPrincipalCometricTerm (I := I) (M := M) g g₁ W),
      ← SmoothCcTensor.inner_def (I := I) (M := M) W
        (firstOrderCoefficientAction (I := I) (M := M) g C₀ C₁ W)]
    simp only [ricciDeTurckLowOrderAction, inner_add_right]
  rw [hadd]
  nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.ricciDeTurckLowOrderAction_pairing_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.ricciDeTurckLowOrderAction_pairing_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.ricciDeTurckLowOrderAction_pairing_bound ``Submission.DifferentialGeometry.Analysis.Spectral.ricciDeTurckLowOrderAction_pairing_bound

end Spectral
end Analysis
end DifferentialGeometry

end
