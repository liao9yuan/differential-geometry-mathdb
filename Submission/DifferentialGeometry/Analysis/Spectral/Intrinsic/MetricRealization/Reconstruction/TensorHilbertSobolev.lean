import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.Positivity.PositiveDefinitePerturbation
import Submission.DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.RHS.Section
import Submission.DifferentialGeometry.Tensor.Multilinear.Bundle.Evaluation
import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.Differentiability.Cotangent
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Regularity.SpectralSeriesSecondOrderSobolev
import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Bounds.CovariantTwoTensor.FrameExpansion
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorField.Bounds.SingleSlotFiberNorm

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.Tensor.RicciIdentity
open _root_.Submission.DifferentialGeometry.Tensor.RSTensor
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection

noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle _root_.ContinuousLinearMap _root_.Submission.ContinuousLinearMap _root_.Bundle.ContinuousLinearMap
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Spectral
namespace MetricRealization


open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance tensorRSRiemannianNormedAddCommGroup_local
    (r s : ℕ) [h : Bundle.RiemannianBundle (fun b : M ↦ Tensor0SBundle.TensorRSSpace r s I b)]
    (b : M) : NormedAddCommGroup (Tensor0SBundle.TensorRSSpace r s I b) :=
  (h.g.toCore b).toNormedAddCommGroupOfTopology
    (h.g.continuousAt b) (h.g.isVonNBounded b)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.tensorRSRiemannianNormedAddCommGroup_local
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.MetricRealization.tensorRSRiemannianNormedAddCommGroup_local target :: scope.openDecls } }

def ccTensorMultilinear (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) :
    Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ 2 :=
  MixedSection.toMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
    (E := (TangentSpace I : M → Type _)) ∞ T.toSection

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorMultilinear then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorMultilinear"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorMultilinear ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorMultilinear

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
@[simp] theorem ccTensorMultilinear_apply (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) (x : M) :
    ccTensorMultilinear (I := I) g T x =
      T.toSection x
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorMultilinear_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorMultilinear_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorMultilinear_apply ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorMultilinear_apply

def ccTensorModel (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) (x : M) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ :=
  Tensor0SSpace.toModel
    (ccTensorMultilinear (I := I) g T x : Tensor0SSpace 2 I x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorModel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorModel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorModel ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorModel

def smoothCcTensorBilinForm (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  (DifferentialGeometry.Tensor.Multilinear.biForm₂ToModel E).symm (ccTensorModel (I := I) g T x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.smoothCcTensorBilinForm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.smoothCcTensorBilinForm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.smoothCcTensorBilinForm ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.smoothCcTensorBilinForm

abbrev ccTensorBilin (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  smoothCcTensorBilinForm (I := I) g T x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorBilin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorBilin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorBilin ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorBilin

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem ccTensorBilin_apply (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) (x : M) (v w : TangentSpace I x) :
    smoothCcTensorBilinForm (I := I) g T x v w =
      ccTensorModel (I := I) g T x ![v, w] :=
  DifferentialGeometry.Tensor.Multilinear.biForm₂ToModel_symm_apply E (ccTensorModel (I := I) g T x) v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorBilin_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorBilin_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorBilin_apply ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorBilin_apply

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
@[simp] theorem ccTensorBilin_zero (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    smoothCcTensorBilinForm (I := I) g (0 : SmoothCcTensor g 0 2) x v w = 0 := by
  rw [ccTensorBilin_apply, ccTensorModel]
  rw [show (ccTensorMultilinear (I := I) g (0 : SmoothCcTensor g 0 2) x :
      Tensor0SSpace 2 I x) =
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
      (0 : SmoothCcTensor g 0 2).toSection x)
      (ContinuousMultilinearMap.constOfIsEmpty ℝ
        (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)) from rfl]
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
      (0 : SmoothCcTensor g 0 2).toSection x) = 0 from rfl]
  with_unfolding_all
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorBilin_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorBilin_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorBilin_zero ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorBilin_zero

attribute [-instance] Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem ccTensorBilin_abs_le_fibreNorm_mul_sqrt
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2) (x : M)
    (v w : TangentSpace I x) :
    letI : Bundle.RiemannianBundle
        (fun b : M => Tensor0SBundle.TensorRSSpace 0 2 I b) :=
      Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g₀ 0 2
    |smoothCcTensorBilinForm (I := I) g₀ T x v w| ≤
      ‖(T.toSection x : Tensor0SBundle.TensorRSSpace 0 2 I x)‖ *
        Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) := by
  classical
  let instTens : Bundle.RiemannianBundle
      (fun b : M => Tensor0SBundle.TensorRSSpace 0 2 I b) :=
    Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g₀ 0 2
  obtain ⟨n, e, _hn, horth, hpars, hexpand, hriemannianFiberNormSq⟩ :=
    tangent_frame_expansion (I := I) (M := M) g₀ x
  set B : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
    smoothCcTensorBilinForm (I := I) g₀ T x with hB_def
  set coef : Fin n × Fin n → ℝ :=
    fun p => g₀.inner x (e p.1) v * g₀.inner x (e p.2) w with hcoef_def
  set comp : Fin n × Fin n → ℝ := fun p => B (e p.1) (e p.2) with hcomp_def
  have hexpV : v = ∑ i : Fin n, g₀.inner x (e i) v • e i := hexpand v
  have hexpW : w = ∑ j : Fin n, g₀.inner x (e j) w • e j := hexpand w
  have hvalue : B v w = ∑ p : Fin n × Fin n, coef p * comp p := by
    have hBv : B v = ∑ i : Fin n, g₀.inner x (e i) v • B (e i) := by
      conv_lhs => rw [hexpV]
      rw [map_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [map_smul]
    have hBvw : B v w =
        ∑ i : Fin n, g₀.inner x (e i) v • (B (e i) w) := by
      rw [hBv, sum_apply]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [smul_apply]
    have hBeiw : ∀ i : Fin n, B (e i) w =
        ∑ j : Fin n, g₀.inner x (e j) w • B (e i) (e j) := by
      intro i
      conv_lhs => rw [hexpW]
      rw [map_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [map_smul]
    rw [hBvw]
    have hdouble : (∑ i : Fin n, g₀.inner x (e i) v • (B (e i) w)) =
        ∑ i : Fin n, ∑ j : Fin n,
          (g₀.inner x (e i) v * g₀.inner x (e j) w) • B (e i) (e j) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hBeiw i, Finset.smul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [smul_smul]
    rw [hdouble, ← Fintype.sum_prod_type'
      (f := fun (i j : Fin n) =>
        (g₀.inner x (e i) v * g₀.inner x (e j) w) • B (e i) (e j))]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [hcoef_def, hcomp_def, smul_eq_mul]
  have hCS : (∑ p : Fin n × Fin n, coef p * comp p) ^ 2 ≤
      (∑ p : Fin n × Fin n, coef p ^ 2) * ∑ p : Fin n × Fin n, comp p ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ coef comp
  have hcoefsq : (∑ p : Fin n × Fin n, coef p ^ 2) =
      g₀.inner x v v * g₀.inner x w w := by
    rw [Fintype.sum_prod_type (f := fun p : Fin n × Fin n => coef p ^ 2)]
    rw [show (∑ i : Fin n, ∑ j : Fin n, coef (i, j) ^ 2) =
          (∑ i : Fin n, g₀.inner x (e i) v ^ 2) *
            ∑ j : Fin n, g₀.inner x (e j) w ^ 2 from ?_]
    · rw [hpars v, hpars w]
    · rw [Finset.sum_mul_sum]
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      rw [hcoef_def]
      ring
  have hcomp_fiber : ∀ (K : Fin 0 → Fin n) (i j : Fin n),
      comp (i, j) = fiberNormSqComponent (I := I) (M := M) g₀ x 0 2
        (T.toSection x) n e K (![i, j] : Fin 2 → Fin n) := by
    intro K i j
    have hconst : ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
          (fun k : Fin 0 => g₀.inner x (e (K k))) :
          Tensor0SBundle.Tensor0SSpace 0 I x) =
        ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ) := by
      apply Tensor0SBundle.tensor0SSpace_ext
      intro u
      change ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
          (fun k : Fin 0 => g₀.inner x (e (K k)))) u =
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)) u
      rw [show ((ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)) u : ℝ) = 1 from rfl]
      change (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ)
          (fun k => g₀.inner x (e (K k)) (u k)) = 1
      rw [ContinuousMultilinearMap.mkPiAlgebra_apply]
      exact Finset.prod_of_isEmpty _
    have hcompij : comp (i, j) = ccTensorModel (I := I) g₀ T x ![e i, e j] := by
      rw [hcomp_def, hB_def]
      exact ccTensorBilin_apply (I := I) g₀ T x (e i) (e j)
    rw [hcompij]
    unfold fiberNormSqComponent
    rw [hconst]
    have htuple : (fun k => e ((![i, j] : Fin 2 → Fin n) k)) =
        (![e i, e j] : Fin 2 → TangentSpace I x) := by
      funext k; fin_cases k <;> rfl
    rw [htuple]
    change ccTensorModel (I := I) g₀ T x ![e i, e j] =
      ((T.toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))
        ![e i, e j] : ℝ)
    unfold ccTensorModel
    rw [ccTensorMultilinear_apply]
    rfl
  have hcompsq : (∑ p : Fin n × Fin n, comp p ^ 2) =
      ‖(T.toSection x : Tensor0SBundle.TensorRSSpace 0 2 I x)‖ ^ 2 := by
    rw [← riemannianFiberNormSq_eq_bundle_norm_sq (I := I) (M := M) g₀ 0 2 x
      (T.toSection x)]
    rw [hriemannianFiberNormSq (T.toSection x)]
    rw [Fintype.sum_unique (fun K : Fin 0 → Fin n =>
      ∑ J : Fin 2 → Fin n,
        fiberNormSqSummand (I := I) (M := M) g₀ x 0 2 (T.toSection x) n e K J)]
    refine (Fintype.sum_equiv (finTwoArrowEquiv (Fin n))
      (fun J : Fin 2 → Fin n =>
        fiberNormSqSummand (I := I) (M := M) g₀ x 0 2 (T.toSection x) n e
          (_root_.Inhabited.default : Fin 0 → Fin n) J)
      (fun p : Fin n × Fin n => comp p ^ 2) ?_).symm
    intro J
    have hJ : (![J 0, J 1] : Fin 2 → Fin n) = J := by
      funext k; fin_cases k <;> rfl
    simp only [finTwoArrowEquiv_apply, Equiv.toFun_as_coe, piFinTwoEquiv_apply]
    rw [fiberNormSqSummand_eq_component_sq,
      hcomp_fiber (_root_.Inhabited.default : Fin 0 → Fin n) (J 0) (J 1), hJ]
  have hnorm_nn : 0 ≤ ‖(T.toSection x : Tensor0SBundle.TensorRSSpace 0 2 I x)‖ := norm_nonneg _
  have hvv_nn : 0 ≤ g₀.inner x v v :=
    DifferentialGeometry.metric_inner_self_nonneg (I := I) (M := M) g₀ x v
  have hww_nn : 0 ≤ g₀.inner x w w :=
    DifferentialGeometry.metric_inner_self_nonneg (I := I) (M := M) g₀ x w
  have habs_sq : |B v w| ^ 2 ≤
      ‖(T.toSection x : Tensor0SBundle.TensorRSSpace 0 2 I x)‖ ^ 2 *
        (g₀.inner x v v * g₀.inner x w w) := by
    rw [sq_abs, hvalue]
    calc (∑ p : Fin n × Fin n, coef p * comp p) ^ 2
        ≤ (∑ p : Fin n × Fin n, coef p ^ 2) * ∑ p : Fin n × Fin n, comp p ^ 2 := hCS
      _ = (g₀.inner x v v * g₀.inner x w w) *
            ‖(T.toSection x : Tensor0SBundle.TensorRSSpace 0 2 I x)‖ ^ 2 := by
            rw [hcoefsq, hcompsq]
      _ = ‖(T.toSection x : Tensor0SBundle.TensorRSSpace 0 2 I x)‖ ^ 2 *
            (g₀.inner x v v * g₀.inner x w w) := by ring
  have hrhs_nn : 0 ≤ ‖(T.toSection x : Tensor0SBundle.TensorRSSpace 0 2 I x)‖ *
      Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) :=
    mul_nonneg (mul_nonneg hnorm_nn (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  rw [← Real.sqrt_sq (abs_nonneg (B v w))]
  rw [show ‖(T.toSection x : Tensor0SBundle.TensorRSSpace 0 2 I x)‖ *
        Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) =
      Real.sqrt (‖(T.toSection x : Tensor0SBundle.TensorRSSpace 0 2 I x)‖ ^ 2 *
        (g₀.inner x v v * g₀.inner x w w)) from ?_]
  · exact Real.sqrt_le_sqrt habs_sq
  · rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hnorm_nn,
      Real.sqrt_mul hvv_nn, mul_assoc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorBilin_abs_le_fibreNorm_mul_sqrt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorBilin_abs_le_fibreNorm_mul_sqrt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorBilin_abs_le_fibreNorm_mul_sqrt ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorBilin_abs_le_fibreNorm_mul_sqrt

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem ccTensorBilin_scalar_contMDiff (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2)
    (Y W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => smoothCcTensorBilinForm (I := I) g T x (Y x) (W x)) := by
  have h_eval : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b : M =>
        Tensor0SSpace.toModel (ccTensorMultilinear (I := I) g T b)
          (fun i : Fin 2 => (![fun b => Y b, fun b => W b] : Fin 2 → ∀ b : M,
            TangentSpace I b) i b)) :=
    TensorMultilinear.contMDiff_section_apply
      (n := 2) (ccTensorMultilinear (I := I) g T)
      (ccTensorMultilinear (I := I) g T).contMDiff
      (![fun b => Y b, fun b => W b])
      (by
        intro i
        fin_cases i
        · exact Y.contMDiff
        · exact W.contMDiff)
  refine h_eval.congr ?_
  intro x
  rw [ccTensorBilin_apply]
  change ccTensorModel (I := I) g T x ![Y x, W x] =
    ccTensorModel (I := I) g T x _
  congr 1
  funext i
  fin_cases i <;> rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorBilin_scalar_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorBilin_scalar_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorBilin_scalar_contMDiff ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorBilin_scalar_contMDiff

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem ccTensorBilin_contMDiff (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ)
        b (smoothCcTensorBilinForm (I := I) g T b)) := by
  classical
  apply contMDiff_continuousLinearMap_section_of_apply
    (V₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
    (φ := fun x : M => smoothCcTensorBilinForm (I := I) g T x)
  intro Y
  apply contMDiff_continuousLinearMap_section_of_apply
    (V₂ := fun _ : M => ℝ)
    (φ := fun x : M => smoothCcTensorBilinForm (I := I) g T x (Y x))
  intro W
  have h_scalar := ccTensorBilin_scalar_contMDiff (I := I) g T Y W
  intro x
  rw [_root_.Bundle.contMDiffAt_section]
  refine (h_scalar.contMDiffAt).congr_of_eventuallyEq ?_
  filter_upwards with y
  change smoothCcTensorBilinForm (I := I) g T y (Y y) (W y) =
    (_root_.FiberBundle.trivializationAt ℝ (Bundle.Trivial M ℝ) x
      ⟨y, smoothCcTensorBilinForm (I := I) g T y (Y y) (W y)⟩).2
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorBilin_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorBilin_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorBilin_contMDiff ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorBilin_contMDiff

def ccTensorBilinSymm (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  (1 / 2 : ℝ) • (smoothCcTensorBilinForm (I := I) g T x +
    (smoothCcTensorBilinForm (I := I) g T x).flip)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorBilinSymm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorBilinSymm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorBilinSymm ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorBilinSymm

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
@[simp] theorem ccTensorBilinSymm_apply (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) (x : M) (v w : TangentSpace I x) :
    ccTensorBilinSymm (I := I) g T x v w =
      (1 / 2 : ℝ) *
        (smoothCcTensorBilinForm (I := I) g T x v w +
          smoothCcTensorBilinForm (I := I) g T x w v) := by
  simp only [ccTensorBilinSymm, smul_apply,
    add_apply, ContinuousLinearMap.flip_apply, smul_eq_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorBilinSymm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorBilinSymm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorBilinSymm_apply ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorBilinSymm_apply

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem ccTensorBilinSymm_symm (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) (x : M) (v w : TangentSpace I x) :
    ccTensorBilinSymm (I := I) g T x v w =
      ccTensorBilinSymm (I := I) g T x w v := by
  rw [ccTensorBilinSymm_apply, ccTensorBilinSymm_apply, add_comm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorBilinSymm_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorBilinSymm_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorBilinSymm_symm ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorBilinSymm_symm

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem ccTensorBilinSymm_contMDiff (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ)
        b (ccTensorBilinSymm (I := I) g T b)) := by
  classical
  apply contMDiff_continuousLinearMap_section_of_apply
    (V₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
    (φ := fun x : M => ccTensorBilinSymm (I := I) g T x)
  intro Y
  apply contMDiff_continuousLinearMap_section_of_apply
    (V₂ := fun _ : M => ℝ)
    (φ := fun x : M => ccTensorBilinSymm (I := I) g T x (Y x))
  intro W
  have h_scalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => ccTensorBilinSymm (I := I) g T x (Y x) (W x)) := by
    have h_eq : (fun x : M => ccTensorBilinSymm (I := I) g T x (Y x) (W x))
        = fun x : M => (1 / 2 : ℝ) *
            (smoothCcTensorBilinForm (I := I) g T x (Y x) (W x) +
              smoothCcTensorBilinForm (I := I) g T x (W x) (Y x)) := by
      funext x; rw [ccTensorBilinSymm_apply]
    rw [h_eq]
    exact (contMDiff_const).mul
      ((ccTensorBilin_scalar_contMDiff (I := I) g T Y W).add
        (ccTensorBilin_scalar_contMDiff (I := I) g T W Y))
  intro x
  rw [_root_.Bundle.contMDiffAt_section]
  refine (h_scalar.contMDiffAt).congr_of_eventuallyEq ?_
  filter_upwards with y
  change ccTensorBilinSymm (I := I) g T y (Y y) (W y) =
    (_root_.FiberBundle.trivializationAt ℝ (Bundle.Trivial M ℝ) x
      ⟨y, ccTensorBilinSymm (I := I) g T y (Y y) (W y)⟩).2
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorBilinSymm_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorBilinSymm_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorBilinSymm_contMDiff ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorBilinSymm_contMDiff

def tensorSectionRealizeMetric (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g (ccTensorBilinSymm (I := I) g T) δ) :
    SmoothRiemannianMetric I M :=
  perturbedMetric (I := I) (M := M) g (ccTensorBilinSymm (I := I) g T)
    (ccTensorBilinSymm_symm (I := I) g T)
    (ccTensorBilinSymm_contMDiff (I := I) g T) hδ_lt hδ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.tensorSectionRealizeMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.tensorSectionRealizeMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.tensorSectionRealizeMetric ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.tensorSectionRealizeMetric

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
@[simp] theorem tensorSectionRealizeMetric_inner (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g (ccTensorBilinSymm (I := I) g T) δ)
    (x : M) (v w : TangentSpace I x) :
    (tensorSectionRealizeMetric (I := I) g T hδ_lt hδ).inner x v w =
      g.inner x v w + ccTensorBilinSymm (I := I) g T x v w := by
  unfold tensorSectionRealizeMetric
  rw [perturbedMetric_inner, perturbedInner_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.tensorSectionRealizeMetric_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.tensorSectionRealizeMetric_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.tensorSectionRealizeMetric_inner ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.tensorSectionRealizeMetric_inner

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem exists_smooth_metric_of_smooth_tensor_small
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g (ccTensorBilinSymm (I := I) g T) δ') :
    ∃ g' : SmoothRiemannianMetric I M,
      ∀ (x : M) (v w : TangentSpace I x),
        g'.inner x v w =
          g.inner x v w + ccTensorBilinSymm (I := I) g T x v w :=
  ⟨tensorSectionRealizeMetric (I := I) g T hδ'_lt hδ',
    fun x v w => tensorSectionRealizeMetric_inner (I := I) g T hδ'_lt hδ' x v w⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.exists_smooth_metric_of_smooth_tensor_small then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.exists_smooth_metric_of_smooth_tensor_small"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.exists_smooth_metric_of_smooth_tensor_small ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.exists_smooth_metric_of_smooth_tensor_small

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem ccTensorMultilinear_smul (g : SmoothRiemannianMetric I M)
    (c : ℝ) (T : SmoothCcTensor g 0 2) (x : M) :
    (ccTensorMultilinear (I := I) g (c • T) x : Tensor0SSpace 2 I x)
      = c • (ccTensorMultilinear (I := I) g T x : Tensor0SSpace 2 I x) := by
  unfold ccTensorMultilinear
  rw [SmoothCcTensor.toSection_smul]
  change ((c • T.toSection) x)
      (ContinuousMultilinearMap.constOfIsEmpty ℝ
        (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
    = c • ((T.toSection x)
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))
  rw [ContMDiffSection.coe_smul, Pi.smul_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorMultilinear_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorMultilinear_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorMultilinear_smul ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorMultilinear_smul

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem ccTensorModel_smul (g : SmoothRiemannianMetric I M)
    (c : ℝ) (T : SmoothCcTensor g 0 2) (x : M) :
    ccTensorModel (I := I) g (c • T) x = c • ccTensorModel (I := I) g T x := by
  unfold ccTensorModel
  rw [ccTensorMultilinear_smul, Tensor0SSpace.toModel_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorModel_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorModel_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorModel_smul ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorModel_smul

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem ccTensorBilinSymm_smul (g : SmoothRiemannianMetric I M)
    (c : ℝ) (T : SmoothCcTensor g 0 2) (x : M) (v w : TangentSpace I x) :
    ccTensorBilinSymm (I := I) g (c • T) x v w =
      c * ccTensorBilinSymm (I := I) g T x v w := by
  simp only [ccTensorBilinSymm_apply, ccTensorBilin_apply, ccTensorModel_smul,
    smul_apply, smul_eq_mul]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorBilinSymm_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorBilinSymm_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorBilinSymm_smul ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorBilinSymm_smul

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem ccTensorBilinSymm_zero_apply (g : SmoothRiemannianMetric I M)
    (x : M) (v w : TangentSpace I x) :
    ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2) x v w = 0 := by
  have h := ccTensorBilinSymm_smul
    (I := I) g (0 : ℝ) (0 : SmoothCcTensor g 0 2) x v w
  simpa only [zero_smul, _root_.MulZeroClass.zero_mul] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorBilinSymm_zero_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorBilinSymm_zero_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorBilinSymm_zero_apply ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.ccTensorBilinSymm_zero_apply

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem gFibreOpBound_ccTensorBilinSymm_zero (g : SmoothRiemannianMetric I M) :
    metricCauchySchwarzBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) 0 := by
  intro x v w
  rw [ccTensorBilinSymm_zero_apply]
  simp only [abs_zero, _root_.MulZeroClass.zero_mul, le_refl]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.gFibreOpBound_ccTensorBilinSymm_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.gFibreOpBound_ccTensorBilinSymm_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.gFibreOpBound_ccTensorBilinSymm_zero ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.gFibreOpBound_ccTensorBilinSymm_zero

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem gFibreOpBound_ccTensorBilinSymm_smul (g : SmoothRiemannianMetric I M)
    (c : ℝ) (T : SmoothCcTensor g 0 2) {δ : ℝ}
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g (ccTensorBilinSymm (I := I) g T) δ) :
    metricCauchySchwarzBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (c • T)) (|c| * δ) := by
  intro x v w
  rw [ccTensorBilinSymm_smul, abs_mul]
  have hb := hδ x v w
  have hsqv : 0 ≤ Real.sqrt (g.inner x v v) := Real.sqrt_nonneg _
  have hsqw : 0 ≤ Real.sqrt (g.inner x w w) := Real.sqrt_nonneg _
  calc |c| * |ccTensorBilinSymm (I := I) g T x v w|
      ≤ |c| * (δ * Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w)) :=
        mul_le_mul_of_nonneg_left hb (abs_nonneg c)
    _ = |c| * δ * Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w) := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.gFibreOpBound_ccTensorBilinSymm_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.gFibreOpBound_ccTensorBilinSymm_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.gFibreOpBound_ccTensorBilinSymm_smul ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.gFibreOpBound_ccTensorBilinSymm_smul

def tensorHsBilinFormSymm (g : SmoothRiemannianMetric I M) {σ : ℝ}
    (u : TensorHs (I := I) (M := M) g 0 2 σ)
    (hu_fs : (Function.support u.coeff).Finite) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  ccTensorBilinSymm (I := I) g
    (Analysis.Parabolic.TensorSpectral.tensorHsSmoothRepr
      (I := I) (M := M) u hu_fs) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.tensorHsBilinFormSymm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.tensorHsBilinFormSymm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.tensorHsBilinFormSymm ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.tensorHsBilinFormSymm

theorem exists_smooth_metric_of_tensorHs_small
    (g_bg : SmoothRiemannianMetric I M) {σ : ℝ}
    (u : TensorHs (I := I) (M := M) g_bg 0 2 σ)
    (hu_fs : (Function.support u.coeff).Finite)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g_bg
      (tensorHsBilinFormSymm (I := I) g_bg u hu_fs) δ') :
    ∃ g' : SmoothRiemannianMetric I M,
      ∀ (x : M) (v w : TangentSpace I x),
        g'.inner x v w =
          g_bg.inner x v w + tensorHsBilinFormSymm (I := I) g_bg u hu_fs x v w :=
  exists_smooth_metric_of_smooth_tensor_small (I := I) g_bg
    (Analysis.Parabolic.TensorSpectral.tensorHsSmoothRepr
      (I := I) (M := M) u hu_fs) hδ'_lt hδ'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.exists_smooth_metric_of_tensorHs_small then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.exists_smooth_metric_of_tensorHs_small"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.exists_smooth_metric_of_tensorHs_small ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.exists_smooth_metric_of_tensorHs_small

open scoped _root_.Classical in
noncomputable def realizeMetricMap (g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (u : TensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 2)) :
    SmoothRiemannianMetric I M :=
  if h : ∃ (hu_fs : (Function.support u.coeff).Finite) (δ' : ℝ), δ' < 1 ∧
      metricCauchySchwarzBound (I := I) (M := M) g_bg
        (tensorHsBilinFormSymm (I := I) g_bg u hu_fs) δ' then
    tensorSectionRealizeMetric (I := I) g_bg
      (Analysis.Parabolic.TensorSpectral.tensorHsSmoothRepr
        (I := I) (M := M) u h.choose)
      h.choose_spec.choose_spec.1 h.choose_spec.choose_spec.2
  else
    g_bg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.realizeMetricMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.realizeMetricMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.realizeMetricMap ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.realizeMetricMap

theorem realizeMetricMap_eq_of_small (g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (u : TensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 2))
    (hu_fs : (Function.support u.coeff).Finite)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g_bg
      (tensorHsBilinFormSymm (I := I) g_bg u hu_fs) δ')
    (x : M) (v w : TangentSpace I x) :
    (realizeMetricMap (I := I) g_bg a u).inner x v w =
      g_bg.inner x v w + tensorHsBilinFormSymm (I := I) g_bg u hu_fs x v w := by
  classical
  have hex : ∃ (hu_fs : (Function.support u.coeff).Finite) (δ' : ℝ), δ' < 1 ∧
      metricCauchySchwarzBound (I := I) (M := M) g_bg
        (tensorHsBilinFormSymm (I := I) g_bg u hu_fs) δ' :=
    ⟨hu_fs, δ', hδ'_lt, hδ'⟩
  rw [realizeMetricMap, dif_pos hex]
  unfold tensorSectionRealizeMetric
  change g_bg.inner x v w +
      ccTensorBilinSymm (I := I) g_bg
        (Analysis.Parabolic.TensorSpectral.tensorHsSmoothRepr
          (I := I) (M := M) u hu_fs) x v w = _
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.realizeMetricMap_eq_of_small then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.realizeMetricMap_eq_of_small"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.realizeMetricMap_eq_of_small ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.realizeMetricMap_eq_of_small

end MetricRealization
end Spectral
end Analysis
end DifferentialGeometry

end
