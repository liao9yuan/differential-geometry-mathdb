import Submission.DifferentialGeometry.Analysis.Integration.L2.Tensor.FiberNormIdentity
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifference.InverseMetricDifferenceCoefficient
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifference.FibreBounds
import Submission.DifferentialGeometry.Analysis.Sobolev.Embedding.Reverse.HebeyToHilbertSobolev
import Submission.DifferentialGeometry.Analysis.Sobolev.Embedding.CovariantDerivative.OrderDropping
import Submission.DifferentialGeometry.Analysis.Integration.L2.Tensor.FiberNormBounds
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorField.Calculus.SlotInsertion
import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Identities.SecondBianchi
import Submission.DifferentialGeometry.Analysis.Sobolev.GagliardoNirenberg.FiberNorm.Basic
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.FiberNorm.NormBridge
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Permutation.FiberNorm
import Submission.DifferentialGeometry.Analysis.Sobolev.AntidiagonalTupleProductGrid
import Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricPerturbation.ComparisonEndomorphismCovariantDerivative
import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Bounds.SlotInsertion
import Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricPerturbation.CovariantOrderCoefficient.SlotFibreNormBound
import Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricPerturbation.CovariantOrderCoefficient.ProductGridRankLeftBound

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Connection.Realization _root_.Submission.DifferentialGeometry.Tensor.Multilinear
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev

open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open _root_.Submission.DifferentialGeometry.TensorRSNabla
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization
  (metricCauchySchwarzBound ccTensorBilinSymm)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

section NormedL2Identity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

private local instance tensorRSRiemannianNormedAddCommGroup
    (r s : ℕ)
    [h : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b)] (b : M) :
    NormedAddCommGroup (TensorRSSpace r s I b) :=
  (h.g.toCore b).toNormedAddCommGroupOfTopology
    (h.g.continuousAt b) (h.g.isVonNBounded b)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.tensorRSRiemannianNormedAddCommGroup
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.tensorRSRiemannianNormedAddCommGroup target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
theorem tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s) :
    tensorL2Norm (I := I) (M := M) g r s S.toFun ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  have hfun : S.toFun = fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
      (r := r) (s := s) (x := x) (S.toSection x) := rfl
  rw [hfun]
  exact tensorL2Norm_sq_eq_integral_riemannianFiberNormSq (I := I) (M := M) g r s _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs ``Submission.DifferentialGeometry.Analysis.Sobolev.tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs

end NormedL2Identity

private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.instCompleteSpace_differentialGeometry_1 : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.instCompleteSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.instCompleteSpace_differentialGeometry_1 target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
theorem norm_le_of_pointwise_fiberNormSq_bound_rs
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (C : SmoothCcTensor g r s) (B : ℝ)
    (hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g r s x (C.toSection x) ≤ B) :
    ‖C‖ ^ 2 ≤ B * (riemannianVolumeMeasure (I := I) (M := M) g Set.univ).toReal := by
  classical
  have : _root_.MeasureTheory.IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  rw [SmoothCcTensor.norm_def (I := I) (M := M) C,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g r s C]
  have hint : MeasureTheory.Integrable
      (fun x => riemannianFiberNormSq (I := I) (M := M) g r s x (C.toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g r s C
  calc ∫ x, riemannianFiberNormSq (I := I) (M := M) g r s x (C.toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)
      ≤ ∫ _x, B ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
        refine MeasureTheory.integral_mono hint (MeasureTheory.integrable_const B)
          (fun x => hpt x)
    _ = B * (riemannianVolumeMeasure (I := I) (M := M) g Set.univ).toReal := by
        rw [MeasureTheory.integral_const, smul_eq_mul,
          MeasureTheory.measureReal_def, mul_comm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.norm_le_of_pointwise_fiberNormSq_bound_rs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.norm_le_of_pointwise_fiberNormSq_bound_rs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.norm_le_of_pointwise_fiberNormSq_bound_rs ``Submission.DifferentialGeometry.Analysis.Sobolev.norm_le_of_pointwise_fiberNormSq_bound_rs

section NormedIntegralBound

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.instCompleteSpace_differentialGeometry_2 : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.instCompleteSpace_differentialGeometry_2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.instCompleteSpace_differentialGeometry_2 target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
theorem normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (C : SmoothCcTensor g r s) (F : M → ℝ)
    (hF_int : MeasureTheory.Integrable F (riemannianVolumeMeasure (I := I) (M := M) g))
    (hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g r s x (C.toSection x) ≤ F x) :
    ‖C‖ ^ 2 ≤ ∫ x, F x ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  rw [SmoothCcTensor.norm_def (I := I) (M := M) C,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g r s C]
  have hint : MeasureTheory.Integrable
      (fun x => riemannianFiberNormSq (I := I) (M := M) g r s x (C.toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g r s C
  exact MeasureTheory.integral_mono hint hF_int (fun x => hpt x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.normSq_le_integral_of_pointwise_fiberNormSq_le_rs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.normSq_le_integral_of_pointwise_fiberNormSq_le_rs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.normSq_le_integral_of_pointwise_fiberNormSq_le_rs ``Submission.DifferentialGeometry.Analysis.Sobolev.normSq_le_integral_of_pointwise_fiberNormSq_le_rs

end NormedIntegralBound

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    [SigmaCompactSpace M] in
theorem riemannianFiberNormSq_inverseMetricDifferenceSlotCoefficient_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : δ < 1 / 2) (hδ0 : 0 ≤ δ)
    (h : ∀ y v w, g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm g₀ T y v w)
    (hbound : metricCauchySchwarzBound (I := I) g₀ (ccTensorBilinSymm g₀ T) δ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        ((inverseMetricDifferenceSlotCoefficient (I := I) g₀ g₁).toSection x) ≤
      ((Module.finrank ℝ E : ℝ)) ^ 2 := by
  have hδ1 : δ < 1 := by linarith
  have hbase := riemannianFiberNormSq_gInvDiffSlotEndo_le (I := I) (M := M) g₀ g₁
    (ccTensorBilinSymm g₀ T) (fun y v w => h y v w) hδ1 hδ0 hbound x
  have hcoeff : (0 : ℝ) < 1 - δ := by linarith
  have hratio : δ / (1 - δ) ≤ 1 := by
    rw [div_le_one hcoeff]; linarith
  have hratio0 : 0 ≤ δ / (1 - δ) := div_nonneg hδ0 (by linarith)
  have hfr0 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  have hmono : ((Module.finrank ℝ E : ℝ) * (δ / (1 - δ))) ^ 2 ≤
      ((Module.finrank ℝ E : ℝ)) ^ 2 := by
    have : (Module.finrank ℝ E : ℝ) * (δ / (1 - δ)) ≤ (Module.finrank ℝ E : ℝ) := by
      calc (Module.finrank ℝ E : ℝ) * (δ / (1 - δ))
          ≤ (Module.finrank ℝ E : ℝ) * 1 := by
            exact mul_le_mul_of_nonneg_left hratio hfr0
        _ = (Module.finrank ℝ E : ℝ) := by rw [mul_one]
    exact pow_le_pow_left₀ (mul_nonneg hfr0 hratio0) this 2
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
          ((inverseMetricDifferenceSlotCoefficient (I := I) g₀ g₁).toSection x)
      = riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
          (show TensorRSSpace 2 2 I x from
            TensorRSSpace.ofCLM (metricComparisonDifferenceSlotEndo (I := I) g₀ g₁ x)) := by rfl
    _ ≤ ((Module.finrank ℝ E : ℝ) * (δ / (1 - δ))) ^ 2 := hbase
    _ ≤ ((Module.finrank ℝ E : ℝ)) ^ 2 := hmono

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.riemannianFiberNormSq_inverseMetricDifferenceSlotCoefficient_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.riemannianFiberNormSq_inverseMetricDifferenceSlotCoefficient_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.riemannianFiberNormSq_inverseMetricDifferenceSlotCoefficient_le ``Submission.DifferentialGeometry.Analysis.Sobolev.riemannianFiberNormSq_inverseMetricDifferenceSlotCoefficient_le

section NormedSlotCoefficientIdentity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.instCompleteSpace_differentialGeometry_3 : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.instCompleteSpace_differentialGeometry_3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.instCompleteSpace_differentialGeometry_3 target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    [SigmaCompactSpace M] in
theorem inverseMetricDifferenceSlotCoefficient_eq_slotInsertEndoCc (g₀ g₁ : SmoothRiemannianMetric I M) :
    inverseMetricDifferenceSlotCoefficient (I := I) g₀ g₁ =
      endoSlotZeroCcTensor (I := I) (M := M) g₀ 1 (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.inverseMetricDifferenceSlotCoefficient_eq_slotInsertEndoCc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.inverseMetricDifferenceSlotCoefficient_eq_slotInsertEndoCc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.inverseMetricDifferenceSlotCoefficient_eq_slotInsertEndoCc ``Submission.DifferentialGeometry.Analysis.Sobolev.inverseMetricDifferenceSlotCoefficient_eq_slotInsertEndoCc

end NormedSlotCoefficientIdentity

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [SigmaCompactSpace M] in
private theorem endoCompSection_contMDiff
    (A B : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) x
        ((A x).comp (B x))) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := E) (V₁ := fun z : M => TangentSpace I z)
    (F₂ := E) (V₂ := fun z : M => TangentSpace I z)
    (φ := fun x => (A x).comp (B x))
  intro Y
  have hBY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y ((B y) (Y y))) :=
    endoApplySection_contMDiff (I := I) (M := M) B Y
  let BY : Cₛ^∞⟮I; E, (fun y : M => TangentSpace I y)⟯ := ⟨fun y : M => (B y) (Y y), hBY⟩
  have hABY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y ((A y) (BY y))) :=
    endoApplySection_contMDiff (I := I) (M := M) A BY
  refine hABY.congr (fun x => ?_)
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.endoCompSection_contMDiff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.endoCompSection_contMDiff target :: scope.openDecls } }

set_option backward.isDefEq.respectTransparency false in
def endoCompField (A B : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) where
  toFun := fun x : M => (A x).comp (B x)
  contMDiff_toFun := endoCompSection_contMDiff (I := I) (M := M) A B

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.endoCompField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.endoCompField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.endoCompField ``Submission.DifferentialGeometry.Analysis.Sobolev.endoCompField

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [SigmaCompactSpace M] in
@[simp] lemma endoCompField_apply
    (A B : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) (x : M) :
    (endoCompField (I := I) (M := M) A B x) = (A x).comp (B x) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.endoCompField_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.endoCompField_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.endoCompField_apply ``Submission.DifferentialGeometry.Analysis.Sobolev.endoCompField_apply

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [SigmaCompactSpace M] in
theorem endoCovariantDerivative_comp
    (g₀ : SmoothRiemannianMetric I M)
    (A B : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x))
    (x : M) (v : TangentSpace I x) :
    ((endoCovariantDerivative (I := I) (M := M) g₀)
        (endoCompField (I := I) (M := M) A B) x v) =
      ((endoCovariantDerivative (I := I) (M := M) g₀) A x v).comp (B x) +
        (A x).comp ((endoCovariantDerivative (I := I) (M := M) g₀) B x v) := by
  classical
  apply ContinuousLinearMap.ext
  intro a
  obtain ⟨Y, hYx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := (TangentSpace I : M → Type _)) x a
  have hBY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y ((B y) (Y y))) :=
    endoApplySection_contMDiff (I := I) (M := M) B Y
  let BY : Cₛ^∞⟮I; E, (fun y : M => TangentSpace I y)⟯ := ⟨fun y : M => (B y) (Y y), hBY⟩
  have hYmd := Y.mdifferentiableAt (x := x)
  have hABcomp := endoCovariantDerivative_apply (I := I) (M := M) g₀
    (endoCompField (I := I) (M := M) A B) Y x v
  have hAonBY := endoCovariantDerivative_apply (I := I) (M := M) g₀ A BY x v
  have hBonY := endoCovariantDerivative_apply (I := I) (M := M) g₀ B Y x v
  have hfun_eq : (fun y : M => (endoCompField (I := I) (M := M) A B y) (Y y)) =
      (fun y : M => (A y) ((B y) (Y y))) := by
    funext y
    rw [endoCompField_apply, ContinuousLinearMap.comp_apply]
  have hcompval : ((endoCovariantDerivative (I := I) (M := M) g₀)
        (endoCompField (I := I) (M := M) A B) x v) (Y x) =
      (LeviCivita (I := I) g₀) (fun y : M => (A y) ((B y) (Y y))) x v -
        (endoCompField (I := I) (M := M) A B x) ((LeviCivita (I := I) g₀) (fun y => Y y) x v) := by
    rw [hABcomp, hfun_eq]
  have hgradY : (LeviCivita (I := I) g₀) (fun y => Y y) x v =
      (LeviCivita (I := I) g₀).toFun (fun y : M => Y y) x v := rfl
  have hBackgroundrad : (LeviCivita (I := I) g₀) (fun y : M => (B y) (Y y)) x v =
      ((endoCovariantDerivative (I := I) (M := M) g₀) B x v) (Y x) +
        (B x) ((LeviCivita (I := I) g₀) (fun y => Y y) x v) := by
    rw [eq_sub_iff_add_eq] at hBonY
    rw [← hBonY]
  have hAonBY' : ((endoCovariantDerivative (I := I) (M := M) g₀) A x v) ((B x) (Y x)) =
      (LeviCivita (I := I) g₀) (fun y : M => (A y) ((B y) (Y y))) x v -
        (A x) ((LeviCivita (I := I) g₀) (fun y : M => (B y) (Y y)) x v) := hAonBY
  rw [← hYx]
  rw [hcompval]
  rw [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, endoCompField_apply, ContinuousLinearMap.comp_apply]
  rw [hAonBY', hBackgroundrad, map_add]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.endoCovariantDerivative_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.endoCovariantDerivative_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.endoCovariantDerivative_comp ``Submission.DifferentialGeometry.Analysis.Sobolev.endoCovariantDerivative_comp

section HilbertFirstDerivativeBound

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.instCompleteSpace_differentialGeometry_4 : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.instCompleteSpace_differentialGeometry_4
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.instCompleteSpace_differentialGeometry_4 target :: scope.openDecls } }

attribute [-instance] Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace in
omit [SigmaCompactSpace M] in
theorem riemannianFiberNormSq_covGrad_inverseMetricDifferenceSlotCoefficient_le
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g₁ : SmoothRiemannianMetric I M)
      (T : SmoothCcTensor g₀ 0 2)
      {δ : ℝ} (_hδ : δ < 1 / 2) (_hδ0 : 0 ≤ δ)
      (_h : ∀ y v w, g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
      (_hbound : metricCauchySchwarzBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
      (x : M),
      letI instTens : Bundle.RiemannianBundle
          (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
        Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g₀ 0 3
      letI : ∀ b : M, NormedAddCommGroup (TensorRSSpace 0 3 I b) :=
        fun b => tensorRSRiemannianNormedAddCommGroup (I := I) 0 3 (h := instTens) b
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 3 x
          ((covGrad (I := I) (M := M) g₀ 2 2 (inverseMetricDifferenceSlotCoefficient (I := I) g₀ g₁)).toSection x) ≤
        C ^ 2 * ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
            Tensor0SBundle.TensorRSSpace 0 3 I x)‖ ^ 2 := by
  classical
  let instTens : Bundle.RiemannianBundle
      (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
    Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g₀ 0 3
  let : ∀ b : M, NormedAddCommGroup (TensorRSSpace 0 3 I b) :=
    fun b => tensorRSRiemannianNormedAddCommGroup (I := I) 0 3 (h := instTens) b
  obtain ⟨C₀, hC₀0, hpw⟩ := sqrt_inner_endoCov_gInvDiffRaisedField_le (I := I) (M := M) g₀
  refine ⟨Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 3) * (4 * C₀), by positivity, ?_⟩
  intro g₁ T δ hδ hδ0 h hbound x
  set Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y) :=
    metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁ with hΛ_def
  set G : ℝ := ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
      Tensor0SBundle.TensorRSSpace 0 3 I x)‖ with hG_def
  have hG_nn : 0 ≤ G := norm_nonneg _
  rw [inverseMetricDifferenceSlotCoefficient_eq_slotInsertEndoCc (I := I) g₀ g₁, ← hΛ_def]
  rw [covGrad_toSection_apply (I := I) (M := M) g₀ 2 2
    (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1 Λ) x]
  refine le_trans
    (Analysis.Sobolev.Tensor.riemannianFiberNormSq_covGradBundleEquiv_le_card_mul_rs
    (I := I) (M := M)
    g₀ 2 2 x _ ((Module.finrank ℝ E : ℝ) ^ 2 * (4 * C₀ * G) ^ 2) ?_) ?_
  · intro v hv
    have hΦ :
        tensorRSCovariantDerivative I M 2 2 (LeviCivita (I := I) g₀)
            (fun y : M => (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1 Λ).toSection y) x v =
          slotInsertEndoFib (I := I) (M := M) 2 0 x
            ((endoCovariantDerivative (I := I) (M := M) g₀) Λ x v) := by
      simpa [tensorCovDerivAt_def] using
        (tensorCovDerivAt_slotInsertEndoCc_eq (I := I) (M := M) g₀ 1 Λ x
          (tangentSpaceModelContinuousLinearEquiv (I := I) x v))
    rw [hΦ]
    refine riemannianFiberNormSq_slotInsertEndoFib_le_card_mul_two (I := I) g₀ x
      ((endoCovariantDerivative (I := I) (M := M) g₀) Λ x v) ((4 * C₀ * G) ^ 2) ?_
    intro a ha
    obtain ⟨Y, hYx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
      (F := E) (V := (TangentSpace I : M → Type _)) x a
    have hbd := hpw g₁ T h hδ hδ0 hbound Y x v
    rw [hYx] at hbd
    have hvroot : Real.sqrt (g₀.inner x v v) = 1 := by rw [hv, Real.sqrt_one]
    have haroot : Real.sqrt (g₀.inner x a a) = 1 := by rw [ha, Real.sqrt_one]
    rw [hvroot, haroot, mul_one, mul_one, ← hG_def] at hbd
    have haa_nn : 0 ≤ g₀.inner x
        (((endoCovariantDerivative (I := I) (M := M) g₀) Λ x v) a)
        (((endoCovariantDerivative (I := I) (M := M) g₀) Λ x v) a) :=
      metric_inner_self_nonneg (I := I) (M := M) g₀ x _
    have hsq := Real.sq_sqrt haa_nn
    nlinarith only [hbd, Real.sqrt_nonneg (g₀.inner x
      (((endoCovariantDerivative (I := I) (M := M) g₀) Λ x v) a)
      (((endoCovariantDerivative (I := I) (M := M) g₀) Λ x v) a)), hsq,
      mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hC₀0) hG_nn]
  · have hsq3 : Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 3) ^ 2 = (Module.finrank ℝ E : ℝ) ^ 3 :=
      Real.sq_sqrt (by positivity)
    have hrhs : (Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 3) * (4 * C₀)) ^ 2 * G ^ 2 =
        (Module.finrank ℝ E : ℝ) ^ 3 * (4 * C₀ * G) ^ 2 := by
      rw [mul_pow, hsq3]; ring
    have hlhs : (Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) ^ 2 * (4 * C₀ * G) ^ 2) =
        (Module.finrank ℝ E : ℝ) ^ 3 * (4 * C₀ * G) ^ 2 := by ring
    rw [hlhs, hrhs]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.riemannianFiberNormSq_covGrad_inverseMetricDifferenceSlotCoefficient_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.riemannianFiberNormSq_covGrad_inverseMetricDifferenceSlotCoefficient_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.riemannianFiberNormSq_covGrad_inverseMetricDifferenceSlotCoefficient_le ``Submission.DifferentialGeometry.Analysis.Sobolev.riemannianFiberNormSq_covGrad_inverseMetricDifferenceSlotCoefficient_le

end HilbertFirstDerivativeBound

attribute [-instance] Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
theorem norm_toSection_eq_sqrt_riemannianFiberNormSq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) (W : SmoothCcTensor g r s) :
    letI instTens : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g r s
    letI : ∀ b : M, NormedAddCommGroup (TensorRSSpace r s I b) :=
      fun b => tensorRSRiemannianNormedAddCommGroup (I := I) r s (h := instTens) b
    ‖(W.toSection x : TensorRSSpace r s I x)‖ =
      Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g r s x (W.toSection x)) := by
  let instTens : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g r s
  let : ∀ b : M, NormedAddCommGroup (TensorRSSpace r s I b) :=
    fun b => tensorRSRiemannianNormedAddCommGroup (I := I) r s (h := instTens) b
  rw [norm_eq_sqrt_tensorInnerPointwise (I := I) (M := M) g r s x (W.toSection x),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (W.toSection x)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.norm_toSection_eq_sqrt_riemannianFiberNormSq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.norm_toSection_eq_sqrt_riemannianFiberNormSq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.norm_toSection_eq_sqrt_riemannianFiberNormSq ``Submission.DifferentialGeometry.Analysis.Sobolev.norm_toSection_eq_sqrt_riemannianFiberNormSq

attribute [-instance] Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace in
omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem norm_iteratedCovGrad_inverseMetricDifferenceSlotCoefficient_le_envelope_zero
    (g₀ g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : δ < 1 / 2) (hδ0 : 0 ≤ δ)
    (h : ∀ y v w, g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    (hbound : metricCauchySchwarzBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ) (x : M)
      (R : ℝ) :
    letI instTens : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 2 2 I b) :=
      Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g₀ 2 2
    letI : ∀ b : M, NormedAddCommGroup (TensorRSSpace 2 2 I b) :=
      fun b => tensorRSRiemannianNormedAddCommGroup (I := I) 2 2 (h := instTens) b
    ‖((iteratedCovGrad (I := I) g₀ 2 2 0 (inverseMetricDifferenceSlotCoefficient (I := I) g₀ g₁)).toSection x :
        TensorRSSpace 2 2 I x)‖ ≤
      (Module.finrank ℝ E : ℝ) * (1 + R) ^ 0 := by
  let instTens : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 2 2 I b) :=
    Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g₀ 2 2
  let : ∀ b : M, NormedAddCommGroup (TensorRSSpace 2 2 I b) :=
    fun b => tensorRSRiemannianNormedAddCommGroup (I := I) 2 2 (h := instTens) b
  rw [iteratedCovGrad_zero, pow_zero, mul_one,
    norm_toSection_eq_sqrt_riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
      (inverseMetricDifferenceSlotCoefficient (I := I) g₀ g₁)]
  have hb := riemannianFiberNormSq_inverseMetricDifferenceSlotCoefficient_le (I := I) (M := M) g₀ g₁ T hδ hδ0 h hbound x
  have hfr0 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  calc Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
          ((inverseMetricDifferenceSlotCoefficient (I := I) g₀ g₁).toSection x))
      ≤ Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 2) := Real.sqrt_le_sqrt hb
    _ = (Module.finrank ℝ E : ℝ) := Real.sqrt_sq hfr0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.norm_iteratedCovGrad_inverseMetricDifferenceSlotCoefficient_le_envelope_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.norm_iteratedCovGrad_inverseMetricDifferenceSlotCoefficient_le_envelope_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.norm_iteratedCovGrad_inverseMetricDifferenceSlotCoefficient_le_envelope_zero ``Submission.DifferentialGeometry.Analysis.Sobolev.norm_iteratedCovGrad_inverseMetricDifferenceSlotCoefficient_le_envelope_zero

section HilbertFirstDerivativeEnvelope

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.instCompleteSpace_differentialGeometry_5 : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.instCompleteSpace_differentialGeometry_5
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.instCompleteSpace_differentialGeometry_5 target :: scope.openDecls } }

attribute [-instance] Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace in
omit [SigmaCompactSpace M] in
theorem norm_iteratedCovGrad_inverseMetricDifferenceSlotCoefficient_le_envelope_one
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
      {δ : ℝ} (_hδ : δ < 1 / 2) (_hδ0 : 0 ≤ δ)
      (_h : ∀ y v w, g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
      (_hbound : metricCauchySchwarzBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ) (x : M)
        {R : ℝ}
      (_hR0 : 0 ≤ R)
      (_hjet : letI inst3 : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 3 I b) :=
          Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g₀ 0 3
        letI : ∀ b : M, NormedAddCommGroup (TensorRSSpace 0 3 I b) :=
          fun b => tensorRSRiemannianNormedAddCommGroup (I := I) 0 3 (h := inst3) b
        ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x : TensorRSSpace 0 3 I x)‖ ≤ R),
      letI inst23 : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 2 3 I b) :=
        Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g₀ 2 3
      letI : ∀ b : M, NormedAddCommGroup (TensorRSSpace 2 3 I b) :=
        fun b => tensorRSRiemannianNormedAddCommGroup (I := I) 2 3 (h := inst23) b
      ‖((iteratedCovGrad (I := I) g₀ 2 2 1 (inverseMetricDifferenceSlotCoefficient (I := I) g₀ g₁)).toSection x :
          TensorRSSpace 2 3 I x)‖ ≤ C * (1 + R) ^ 1 := by
  obtain ⟨C, hC0, hbnd⟩ := riemannianFiberNormSq_covGrad_inverseMetricDifferenceSlotCoefficient_le (I := I) (M := M) g₀
  refine ⟨C, hC0, ?_⟩
  intro g₁ T δ hδ hδ0 h hbound x R hR0 hjet
  let inst3 : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 3 I b) :=
    Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g₀ 0 3
  let : ∀ b : M, NormedAddCommGroup (TensorRSSpace 0 3 I b) :=
    fun b => tensorRSRiemannianNormedAddCommGroup (I := I) 0 3 (h := inst3) b
  let inst23 : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 2 3 I b) :=
    Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g₀ 2 3
  let : ∀ b : M, NormedAddCommGroup (TensorRSSpace 2 3 I b) :=
    fun b => tensorRSRiemannianNormedAddCommGroup (I := I) 2 3 (h := inst23) b
  have hb := hbnd g₁ T hδ hδ0 h hbound x
  have hiter1 : iteratedCovGrad (I := I) g₀ 2 2 1 (inverseMetricDifferenceSlotCoefficient (I := I) g₀ g₁) =
      covGrad (I := I) (M := M) g₀ 2 2 (inverseMetricDifferenceSlotCoefficient (I := I) g₀ g₁) := by
    rw [iteratedCovGrad_succ, iteratedCovGrad_zero]
  rw [pow_one,
    norm_toSection_eq_sqrt_riemannianFiberNormSq (I := I) (M := M) g₀ 2 3 x
      (iteratedCovGrad (I := I) g₀ 2 2 1 (inverseMetricDifferenceSlotCoefficient (I := I) g₀ g₁)), hiter1]
  set G : ℝ := ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x : TensorRSSpace 0 3 I x)‖ with hG
  have hG0 : 0 ≤ G := norm_nonneg _
  have hsqrt_le : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 3 x
      ((covGrad (I := I) (M := M) g₀ 2 2 (inverseMetricDifferenceSlotCoefficient (I := I) g₀ g₁)).toSection x)) ≤
      Real.sqrt (C ^ 2 * G ^ 2) := Real.sqrt_le_sqrt hb
  refine hsqrt_le.trans ?_
  rw [show C ^ 2 * G ^ 2 = (C * G) ^ 2 from by ring, Real.sqrt_sq (mul_nonneg hC0 hG0)]
  have hGR : G ≤ R := hjet
  calc C * G ≤ C * R := mul_le_mul_of_nonneg_left hGR hC0
    _ ≤ C * (1 + R) := by
        refine mul_le_mul_of_nonneg_left ?_ hC0; linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.norm_iteratedCovGrad_inverseMetricDifferenceSlotCoefficient_le_envelope_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.norm_iteratedCovGrad_inverseMetricDifferenceSlotCoefficient_le_envelope_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.norm_iteratedCovGrad_inverseMetricDifferenceSlotCoefficient_le_envelope_one ``Submission.DifferentialGeometry.Analysis.Sobolev.norm_iteratedCovGrad_inverseMetricDifferenceSlotCoefficient_le_envelope_one

end HilbertFirstDerivativeEnvelope

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] in
theorem covGrad_inverseMetricDifferenceSlotCoefficient_eq_covGrad_slotInsertEndoCc
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    covGrad (I := I) (M := M) g₀ 2 2 (inverseMetricDifferenceSlotCoefficient (I := I) g₀ g₁) =
      covGrad (I := I) (M := M) g₀ 2 2
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1 (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁)) := by
  rw [inverseMetricDifferenceSlotCoefficient_eq_slotInsertEndoCc (I := I) g₀ g₁]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.covGrad_inverseMetricDifferenceSlotCoefficient_eq_covGrad_slotInsertEndoCc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.covGrad_inverseMetricDifferenceSlotCoefficient_eq_covGrad_slotInsertEndoCc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.covGrad_inverseMetricDifferenceSlotCoefficient_eq_covGrad_slotInsertEndoCc ``Submission.DifferentialGeometry.Analysis.Sobolev.covGrad_inverseMetricDifferenceSlotCoefficient_eq_covGrad_slotInsertEndoCc

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem covGrad_inverseMetricDifferenceSlotCoefficient_toSection_eval
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 2 I x) (v : Fin 3 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
          (covGrad (I := I) (M := M) g₀ 2 2 (inverseMetricDifferenceSlotCoefficient (I := I) g₀ g₁)).toSection x) D) v =
      Tensor0SSpace.toModel
        ((slotInsertEndoFib (I := I) (M := M) 2 0 x
            ((endoCovariantDerivative (I := I) (M := M) g₀)
              (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁) x (v 0))) D)
        (Matrix.vecTail v) := by
  rw [covGrad_inverseMetricDifferenceSlotCoefficient_eq_covGrad_slotInsertEndoCc (I := I) g₀ g₁]
  exact covGrad_slotInsertEndoCc_toSection_eq (I := I) (M := M) g₀ 1
    (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁) x D v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.covGrad_inverseMetricDifferenceSlotCoefficient_toSection_eval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.covGrad_inverseMetricDifferenceSlotCoefficient_toSection_eval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.covGrad_inverseMetricDifferenceSlotCoefficient_toSection_eval ``Submission.DifferentialGeometry.Analysis.Sobolev.covGrad_inverseMetricDifferenceSlotCoefficient_toSection_eval

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem covGrad_inverseMetricDifferenceSlotCoefficient_endoCov_apply
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v : TangentSpace I x) :
    ((endoCovariantDerivative (I := I) (M := M) g₀)
        (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁) x v) (Y x) =
      - PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (metricComparisonEndomorphism (I := I) g₀ g₁ x (Y x)) v
      + inverseMetricSharpFib (I := I) g₁ x
          (dualToCotangent (I := I)
            (-(cotangentToCLM (I := I) (g0FlatCLM (I := I) g₀ x (Y x))).comp
                ((PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x).flip v)).toLinearMap) :=
  endoCov_gInvDiffRaisedField_apply (I := I) (M := M) g₀ g₁ Y x v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.covGrad_inverseMetricDifferenceSlotCoefficient_endoCov_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.covGrad_inverseMetricDifferenceSlotCoefficient_endoCov_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.covGrad_inverseMetricDifferenceSlotCoefficient_endoCov_apply ``Submission.DifferentialGeometry.Analysis.Sobolev.covGrad_inverseMetricDifferenceSlotCoefficient_endoCov_apply

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma tensor0SOne_apply_add_comp (x : M) (om : Tensor0SSpace 1 I x)
    (a b : TangentSpace I x) :
    om (fun _ : Fin 1 => a + b) = om (fun _ : Fin 1 => a) + om (fun _ : Fin 1 => b) := by
  let φ := continuousMultilinearCurryFin1 ℝ (TangentSpace I x) ℝ
    (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
  have heval (v : TangentSpace I x) :
      (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
        (fun _ : Fin 1 => v) = φ v := by
    have hconst : (fun _ : Fin 1 => v) = Fin.snoc 0 v := by
      funext i
      fin_cases i
      rfl
    rw [hconst]
    exact (continuousMultilinearCurryFin1_apply
      (f := (om : ContinuousMultilinearMap ℝ
        (fun _ : Fin 1 => TangentSpace I x) ℝ)) (x := v)).symm
  change (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
      (fun _ => a + b) = _
  rw [heval (a + b), heval a, heval b, map_add]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.tensor0SOne_apply_add_comp
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.tensor0SOne_apply_add_comp target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma tensor0SOne_apply_smul_comp (x : M) (om : Tensor0SSpace 1 I x)
    (c : ℝ) (a : TangentSpace I x) :
    om (fun _ : Fin 1 => c • a) = c • om (fun _ : Fin 1 => a) := by
  let φ := continuousMultilinearCurryFin1 ℝ (TangentSpace I x) ℝ
    (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
  have heval (v : TangentSpace I x) :
      (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
        (fun _ : Fin 1 => v) = φ v := by
    have hconst : (fun _ : Fin 1 => v) = Fin.snoc 0 v := by
      funext i
      fin_cases i
      rfl
    rw [hconst]
    exact (continuousMultilinearCurryFin1_apply
      (f := (om : ContinuousMultilinearMap ℝ
        (fun _ : Fin 1 => TangentSpace I x) ℝ)) (x := v)).symm
  change (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
      (fun _ => c • a) = _
  rw [heval (c • a), heval a, map_smul]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.tensor0SOne_apply_smul_comp
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.tensor0SOne_apply_smul_comp target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma tensor0SOne_apply_neg_comp (x : M) (om : Tensor0SSpace 1 I x)
    (a : TangentSpace I x) :
    om (fun _ : Fin 1 => -a) = -om (fun _ : Fin 1 => a) := by
  have h := tensor0SOne_apply_smul_comp (I := I) x om (-1) a
  simp only [neg_smul, one_smul] at h
  exact h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.tensor0SOne_apply_neg_comp
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.tensor0SOne_apply_neg_comp target :: scope.openDecls } }

def connectionDifferenceGInvCompositePairing (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) : Tensor0SSpace 2 I x :=
  (show ContinuousMultilinearMap ℝ (fun _ : Fin 2 => TangentSpace I x) ℝ from
    { toFun := fun YZ => om (fun _ : Fin 1 =>
        PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
          (metricComparisonEndomorphism (I := I) g₀ g₁ x (YZ 0)) (YZ 1))
      map_update_add' := by
        have hne10 : (1 : Fin 2) ≠ 0 := by decide
        have hne01 : (0 : Fin 2) ≠ 1 := by decide
        intro _ YZ i Y Y'
        fin_cases i <;>
          · simp only [Fin.isValue, Fin.mk_zero, Fin.mk_one, Function.update_self,
              Function.update_of_ne, ne_eq, hne10, hne01, not_false_eq_true,
              add_apply, map_add]
            rw [tensor0SOne_apply_add_comp (I := I) x om]
      map_update_smul' := by
        have hne10 : (1 : Fin 2) ≠ 0 := by decide
        have hne01 : (0 : Fin 2) ≠ 1 := by decide
        intro _ YZ i c Y
        fin_cases i <;>
          · simp only [Fin.isValue, Fin.mk_zero, Fin.mk_one, Function.update_self,
              Function.update_of_ne, ne_eq, hne10, hne01, not_false_eq_true,
              smul_apply, map_smul]
            rw [tensor0SOne_apply_smul_comp (I := I) x om]
      cont := by
        have hpair : Continuous (fun YZ : Fin 2 → TangentSpace I x => (YZ 0, YZ 1)) :=
          (continuous_apply 0).prodMk (continuous_apply 1)
        have hRaised : Continuous (metricComparisonEndomorphism (I := I) g₀ g₁ x) :=
          (metricComparisonEndomorphism (I := I) g₀ g₁ x).continuous
        have hbil : Continuous (fun YZ : Fin 2 → TangentSpace I x =>
            PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
              (metricComparisonEndomorphism (I := I) g₀ g₁ x (YZ 0)) (YZ 1)) := by
          have hc : Continuous (fun p : TangentSpace I x × TangentSpace I x =>
              PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x p.1 p.2) :=
            (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x).continuous₂
          have hcomp : Continuous (fun YZ : Fin 2 → TangentSpace I x =>
              (metricComparisonEndomorphism (I := I) g₀ g₁ x (YZ 0), YZ 1)) :=
            (hRaised.comp (continuous_apply 0)).prodMk (continuous_apply 1)
          exact hc.comp hcomp
        exact ((ContinuousMultilinearMap.coe_continuous
          (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)).comp
          (continuous_pi (fun _ => hbil))) } : Tensor0SSpace 2 I x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.connectionDifferenceGInvCompositePairing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.connectionDifferenceGInvCompositePairing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.connectionDifferenceGInvCompositePairing ``Submission.DifferentialGeometry.Analysis.Sobolev.connectionDifferenceGInvCompositePairing

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma gInvCompPairing_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) (YZ : Fin 2 → TangentSpace I x) :
    (connectionDifferenceGInvCompositePairing (I := I) g₀ g₁ x om) YZ =
      om (fun _ : Fin 1 =>
        PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
          (metricComparisonEndomorphism (I := I) g₀ g₁ x (YZ 0)) (YZ 1)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.gInvCompPairing_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.gInvCompPairing_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.gInvCompPairing_apply ``Submission.DifferentialGeometry.Analysis.Sobolev.gInvCompPairing_apply

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
lemma gInvCompPairing_add (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (om om' : Tensor0SSpace 1 I x) :
    connectionDifferenceGInvCompositePairing (I := I) g₀ g₁ x (om + om') =
      connectionDifferenceGInvCompositePairing (I := I) g₀ g₁ x om + connectionDifferenceGInvCompositePairing (I := I) g₀ g₁
        x om' := by
  apply ContinuousMultilinearMap.ext
  intro YZ
  exact add_apply om om' _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.gInvCompPairing_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.gInvCompPairing_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.gInvCompPairing_add ``Submission.DifferentialGeometry.Analysis.Sobolev.gInvCompPairing_add

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
lemma gInvCompPairing_smul (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (c : ℝ) (om : Tensor0SSpace 1 I x) :
    connectionDifferenceGInvCompositePairing (I := I) g₀ g₁ x (c • om) =
      c • connectionDifferenceGInvCompositePairing (I := I) g₀ g₁ x om := by
  apply ContinuousMultilinearMap.ext
  intro YZ
  exact smul_apply om c _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.gInvCompPairing_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.gInvCompPairing_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.gInvCompPairing_smul ``Submission.DifferentialGeometry.Analysis.Sobolev.gInvCompPairing_smul

def connectionDifferenceGInvCompositeFib (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    TensorRSSpace 1 2 I x :=
  TensorRSSpace.ofCLM
    (LinearMap.toContinuousLinearMap
      { toFun := fun om => connectionDifferenceGInvCompositePairing (I := I) g₀ g₁ x om
        map_add' := gInvCompPairing_add (I := I) g₀ g₁ x
        map_smul' := gInvCompPairing_smul (I := I) g₀ g₁ x })

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.connectionDifferenceGInvCompositeFib then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.connectionDifferenceGInvCompositeFib"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.connectionDifferenceGInvCompositeFib ``Submission.DifferentialGeometry.Analysis.Sobolev.connectionDifferenceGInvCompositeFib

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma connectionDifferenceGInvCompositeFib_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) :
    (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        connectionDifferenceGInvCompositeFib (I := I) g₀ g₁ x) om =
      connectionDifferenceGInvCompositePairing (I := I) g₀ g₁ x om := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.connectionDifferenceGInvCompositeFib_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.connectionDifferenceGInvCompositeFib_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.connectionDifferenceGInvCompositeFib_apply ``Submission.DifferentialGeometry.Analysis.Sobolev.connectionDifferenceGInvCompositeFib_apply

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [T2Space M]
    [I.Boundaryless] [SigmaCompactSpace M] in
theorem metricComparisonEndomorphism_section_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b
        (metricComparisonEndomorphism (I := I) g₀ g₁ b (Y b))) := by
  refine (inverseMetricSharpFib_g0FlatY_contMDiff (I := I) g₀ g₁ Y).congr (fun b => ?_)
  rw [metricComparisonEndomorphism_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.metricComparisonEndomorphism_section_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.metricComparisonEndomorphism_section_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.metricComparisonEndomorphism_section_contMDiff ``Submission.DifferentialGeometry.Analysis.Sobolev.metricComparisonEndomorphism_section_contMDiff

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem connectionDifferenceGInvCompositeFib_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 1 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 1 2 ℝ E)
        (E := fun z : M => TensorRSSpace 1 2 I z) x
        (connectionDifferenceGInvCompositeFib (I := I) g₀ g₁ x)) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel 1 ℝ E) (V₁ := fun x : M => Tensor0SSpace 1 I x)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SSpace 2 I x)
    (φ := fun x : M => (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
      connectionDifferenceGInvCompositeFib (I := I) g₀ g₁ x))
  intro om
  let := Tensor0SBundle.tensor0SBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
  have hsec : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        (connectionDifferenceGInvCompositePairing (I := I) g₀ g₁ x (om x))) := by
    refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x : M => (connectionDifferenceGInvCompositePairing (I := I) g₀ g₁ x (om x) :
        Bundle.continuousMultilinearMap ℝ 2 E (TangentSpace I) x))).mpr ?_
    intro σ x₀
    set b := Module.finBasis ℝ E with hb
    set e₁ := _root_.FiberBundle.trivializationAt E (TangentSpace I : M → Type _) x₀ with he₁def
    have he₁ : x₀ ∈ e₁.baseSet := _root_.FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x₀
    have hframe := e₁.isLocalFrameOn_localFrame_baseSet I (⊤ : ℕ∞) b
    obtain ⟨Y, hY⟩ := hframe.exists_contMDiffSection_eqOn_nhd e₁.open_baseSet he₁
    have hconn : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
          (((PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x)
            (metricComparisonEndomorphism (I := I) g₀ g₁ x (Y (σ 0) x))) (Y (σ 1) x))) :=
      PDE.DeTurck.connectionDifference_contMDiff (I := I) g₁ g₀
        (metricComparisonEndomorphism_section_contMDiff (I := I) g₀ g₁ (Y (σ 0))) (Y (σ 1)).contMDiff
    have hscalar : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
        (fun x : M => Tensor0SSpace.toModel (om x)
          (fun _ : Fin 1 => ((PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x)
            (metricComparisonEndomorphism (I := I) g₀ g₁ x (Y (σ 0) x))) (Y (σ 1) x))) x₀ :=
      TensorMultilinear.contMDiffAt_section_apply (n := 1) (x₀ := x₀)
        (fun x : M => om x) (om.contMDiff x₀)
        (fun _ : Fin 1 => fun x : M => ((PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x)
          (metricComparisonEndomorphism (I := I) g₀ g₁ x (Y (σ 0) x))) (Y (σ 1) x))
        (fun _ => (hconn x₀))
    refine hscalar.congr_of_eventuallyEq ?_
    have h_base₁ : ∀ᶠ x in 𝓝 x₀, x ∈ e₁.baseSet := e₁.open_baseSet.mem_nhds he₁
    filter_upwards [h_base₁, hY] with x hx₁ hYx
    rw [continuousMultilinearMap_basis_repr]
    have hframe0 : e₁.symmL ℝ x (b (σ 0)) = (Y (σ 0)) x := by
      rw [hYx (σ 0), Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
      exact e₁.symmL_apply hx₁ (b (σ 0))
    have hframe1 : e₁.symmL ℝ x (b (σ 1)) = (Y (σ 1)) x := by
      rw [hYx (σ 1), Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
      exact e₁.symmL_apply hx₁ (b (σ 1))
    change (connectionDifferenceGInvCompositePairing (I := I) g₀ g₁ x (om x))
        (fun j : Fin 2 => e₁.symmL ℝ x (b (σ j))) = _
    rw [gInvCompPairing_apply]
    rw [Tensor0SSpace.toModel, tensor0SSpace_continuousLinearEquiv_apply]
    rw [hframe0, hframe1]
    rfl
  refine hsec.congr ?_
  intro x
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.connectionDifferenceGInvCompositeFib_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.connectionDifferenceGInvCompositeFib_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.connectionDifferenceGInvCompositeFib_contMDiff ``Submission.DifferentialGeometry.Analysis.Sobolev.connectionDifferenceGInvCompositeFib_contMDiff

def connectionDifferenceGInvComposite (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 1 2 where
  toSection :=
    { toFun := fun x : M => connectionDifferenceGInvCompositeFib (I := I) g₀ g₁ x
      contMDiff_toFun := connectionDifferenceGInvCompositeFib_contMDiff (I := I) g₀ g₁ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.connectionDifferenceGInvComposite then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.connectionDifferenceGInvComposite"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.connectionDifferenceGInvComposite ``Submission.DifferentialGeometry.Analysis.Sobolev.connectionDifferenceGInvComposite

omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] [SigmaCompactSpace M] in
@[simp] lemma connectionDifferenceGInvComposite_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (connectionDifferenceGInvComposite (I := I) g₀ g₁).toSection x =
      connectionDifferenceGInvCompositeFib (I := I) g₀ g₁ x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.connectionDifferenceGInvComposite_toSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.connectionDifferenceGInvComposite_toSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.connectionDifferenceGInvComposite_toSection ``Submission.DifferentialGeometry.Analysis.Sobolev.connectionDifferenceGInvComposite_toSection

omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] [SigmaCompactSpace M] in
lemma connectionDifferenceGInvComposite_pairing_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) (YZ : Fin 2 → TangentSpace I x) :
    ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        (connectionDifferenceGInvComposite (I := I) g₀ g₁).toSection x) om) YZ =
      om (fun _ : Fin 1 =>
        PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
          (metricComparisonEndomorphism (I := I) g₀ g₁ x (YZ 0)) (YZ 1)) := by
  rw [connectionDifferenceGInvComposite_toSection, connectionDifferenceGInvCompositeFib_apply, gInvCompPairing_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.connectionDifferenceGInvComposite_pairing_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.connectionDifferenceGInvComposite_pairing_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.connectionDifferenceGInvComposite_pairing_apply ``Submission.DifferentialGeometry.Analysis.Sobolev.connectionDifferenceGInvComposite_pairing_apply

omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem covGrad_inverseMetricDifferenceSlotCoefficient_eq_operatorFieldComposition_composite
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v : TangentSpace I x)
    (om : Tensor0SSpace 1 I x) :
    om (fun _ : Fin 1 =>
        ((endoCovariantDerivative (I := I) (M := M) g₀)
          (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁) x v) (Y x)) =
      - ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
            (connectionDifferenceGInvComposite (I := I) g₀ g₁).toSection x) om)
            (fun j : Fin 2 => if j = 0 then Y x else v)
      + om (fun _ : Fin 1 =>
          inverseMetricSharpFib (I := I) g₁ x
            (dualToCotangent (I := I)
              (-(cotangentToCLM (I := I) (g0FlatCLM (I := I) g₀ x (Y x))).comp
                  ((PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x).flip v)).toLinearMap)) := by
  rw [covGrad_inverseMetricDifferenceSlotCoefficient_endoCov_apply (I := I) g₀ g₁ Y x v]
  rw [tensor0SOne_apply_add_comp (I := I) x om,
    tensor0SOne_apply_neg_comp (I := I) x om]
  rw [connectionDifferenceGInvComposite_pairing_apply (I := I) g₀ g₁ x om
    (fun j : Fin 2 => if j = 0 then Y x else v)]
  simp only [Fin.isValue, if_true, if_neg (by decide : (1 : Fin 2) ≠ 0)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.covGrad_inverseMetricDifferenceSlotCoefficient_eq_operatorFieldComposition_composite then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.covGrad_inverseMetricDifferenceSlotCoefficient_eq_operatorFieldComposition_composite"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.covGrad_inverseMetricDifferenceSlotCoefficient_eq_operatorFieldComposition_composite ``Submission.DifferentialGeometry.Analysis.Sobolev.covGrad_inverseMetricDifferenceSlotCoefficient_eq_operatorFieldComposition_composite

open _root_.Submission.DifferentialGeometry.TensorMultilinear

omit [I.Boundaryless] [SigmaCompactSpace M] in
set_option backward.isDefEq.respectTransparency false in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem endoCov_gInvDiffRaisedField_fibrewise
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v0 w : TangentSpace I x) :
    ((endoCovariantDerivative (I := I) (M := M) g₀)
        (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁) x v0) w =
      - PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (metricComparisonEndomorphism (I := I) g₀ g₁ x w) v0
      + inverseMetricSharpFib (I := I) g₁ x
          (dualToCotangent (I := I)
            (-(cotangentToCLM (I := I) (g0FlatCLM (I := I) g₀ x w)).comp
                ((PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x).flip v0)).toLinearMap) := by
  classical
  obtain ⟨Y, hYx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := (TangentSpace I : M → Type _)) x w
  have hk := covGrad_inverseMetricDifferenceSlotCoefficient_endoCov_apply (I := I) (M := M) g₀ g₁ Y x v0
  rw [hYx] at hk
  exact hk

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.endoCov_gInvDiffRaisedField_fibrewise then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.endoCov_gInvDiffRaisedField_fibrewise"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.endoCov_gInvDiffRaisedField_fibrewise ``Submission.DifferentialGeometry.Analysis.Sobolev.endoCov_gInvDiffRaisedField_fibrewise

end Sobolev
end Analysis
end DifferentialGeometry
