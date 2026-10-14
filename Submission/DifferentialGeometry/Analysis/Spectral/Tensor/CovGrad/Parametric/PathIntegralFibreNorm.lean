import Submission.DifferentialGeometry.Analysis.Integration.L2.Tensor.FiberNormIdentity
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Parametric.CoefficientIntegral
import Submission.DifferentialGeometry.Analysis.Sobolev.Embedding.CovariantDerivative.Cm
import Submission.DifferentialGeometry.Geometry.Metric.PointwiseInner.Algebra
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.FiberNorm.Inner
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Seminorm
import Mathlib.MeasureTheory.Integral.Prod

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection


noncomputable section


open _root_.MeasureTheory _root_.Set _root_.Filter _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators

namespace DifferentialGeometry
namespace Integral
namespace L2


open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral (pathIntegralCoeffField
  pathIntegralCoeffField_toSection pathIntegralFib pathIntegralFib_toModel)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
theorem tensorPointwiseNorm_add_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (S T : TensorRSModel r s ℝ E) :
    tensorPointwiseNorm (I := I) (M := M) g r s x (S + T) ≤
      tensorPointwiseNorm (I := I) (M := M) g r s x S +
        tensorPointwiseNorm (I := I) (M := M) g r s x T := by
  unfold tensorPointwiseNorm
  set qSS := tensorInnerPointwise (I := I) (M := M) g r s x S S with hqSS
  set qTT := tensorInnerPointwise (I := I) (M := M) g r s x T T with hqTT
  set qST := tensorInnerPointwise (I := I) (M := M) g r s x S T with hqST
  have hSS_nn : 0 ≤ qSS := tensorInnerPointwise_nonneg (I := I) (M := M) g r s x S
  have hTT_nn : 0 ≤ qTT := tensorInnerPointwise_nonneg (I := I) (M := M) g r s x T
  have hexpand : tensorInnerPointwise (I := I) (M := M) g r s x (S + T) (S + T) =
      qSS + qST + (qST + qTT) := by
    rw [tensorInnerPointwise_add_left, tensorInnerPointwise_add_right,
      tensorInnerPointwise_add_right]
    have hcomm : tensorInnerPointwise (I := I) (M := M) g r s x T S = qST := by
      rw [hqST, tensorInnerPointwise_symm]
    rw [hcomm]
  have hcs : |qST| ≤ Real.sqrt qSS * Real.sqrt qTT := by
    have := abs_tensorInnerPointwise_le_mul (I := I) (M := M) g r s x S T
    simpa only [tensorPointwiseNorm] using this
  have hqST_le : qST ≤ Real.sqrt qSS * Real.sqrt qTT :=
    le_trans (le_abs_self qST) hcs
  have hsumeq : Real.sqrt qSS + Real.sqrt qTT =
      Real.sqrt ((Real.sqrt qSS + Real.sqrt qTT) ^ 2) :=
    (Real.sqrt_sq (by positivity)).symm
  rw [hexpand, hsumeq]
  refine Real.sqrt_le_sqrt ?_
  have hsq : (Real.sqrt qSS + Real.sqrt qTT) ^ 2 =
      qSS + 2 * (Real.sqrt qSS * Real.sqrt qTT) + qTT := by
    rw [add_pow_two, Real.sq_sqrt hSS_nn, Real.sq_sqrt hTT_nn]; ring
  rw [hsq]
  nlinarith only [hqST_le]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.tensorPointwiseNorm_add_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.tensorPointwiseNorm_add_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.tensorPointwiseNorm_add_le ``Submission.DifferentialGeometry.Integral.L2.tensorPointwiseNorm_add_le

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
theorem tensorPointwiseNorm_smul
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (a : ℝ) (S : TensorRSModel r s ℝ E) :
    tensorPointwiseNorm (I := I) (M := M) g r s x (a • S) =
      |a| * tensorPointwiseNorm (I := I) (M := M) g r s x S := by
  have : NormedSpace ℝ (TensorRSModel r s ℝ E) :=
    Tensor0SBundle.tensorRSModelNormedSpace r s
  unfold tensorPointwiseNorm
  rw [tensorInnerPointwise_smul_left, tensorInnerPointwise_smul_right]
  rw [show a * (a * tensorInnerPointwise (I := I) (M := M) g r s x S S) =
      a ^ 2 * tensorInnerPointwise (I := I) (M := M) g r s x S S from by ring]
  rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.tensorPointwiseNorm_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.tensorPointwiseNorm_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.tensorPointwiseNorm_smul ``Submission.DifferentialGeometry.Integral.L2.tensorPointwiseNorm_smul

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
theorem tensorPointwiseNorm_nonneg
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (S : TensorRSModel r s ℝ E) :
    0 ≤ tensorPointwiseNorm (I := I) (M := M) g r s x S :=
  Real.sqrt_nonneg _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.tensorPointwiseNorm_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.tensorPointwiseNorm_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.tensorPointwiseNorm_nonneg ``Submission.DifferentialGeometry.Integral.L2.tensorPointwiseNorm_nonneg

def tensorPointwiseSeminorm
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) :
    Seminorm ℝ (TensorRSModel r s ℝ E) :=
  Seminorm.of (tensorPointwiseNorm (I := I) (M := M) g r s x)
    (tensorPointwiseNorm_add_le (I := I) (M := M) g r s x)
    (fun a S => by
      rw [tensorPointwiseNorm_smul (I := I) (M := M) g r s x a S, Real.norm_eq_abs])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.tensorPointwiseSeminorm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.tensorPointwiseSeminorm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.tensorPointwiseSeminorm ``Submission.DifferentialGeometry.Integral.L2.tensorPointwiseSeminorm

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
@[simp] theorem tensorPointwiseSeminorm_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (S : TensorRSModel r s ℝ E) :
    tensorPointwiseSeminorm (I := I) (M := M) g r s x S =
      tensorPointwiseNorm (I := I) (M := M) g r s x S := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.tensorPointwiseSeminorm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.tensorPointwiseSeminorm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.tensorPointwiseSeminorm_apply ``Submission.DifferentialGeometry.Integral.L2.tensorPointwiseSeminorm_apply

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
theorem tensorPointwiseNorm_continuous
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) :
    Continuous (tensorPointwiseNorm (I := I) (M := M) g r s x) := by
  have : NormedSpace ℝ (TensorRSModel r s ℝ E) :=
    Tensor0SBundle.tensorRSModelNormedSpace r s
  have : FiniteDimensional ℝ (TensorRSModel r s ℝ E) :=
    Tensor0SBundle.tensorRSModel_finiteDimensional r s
  set b : TensorRSModel r s ℝ E → TensorRSModel r s ℝ E → ℝ :=
    fun S T => tensorInnerPointwise (I := I) (M := M) g r s x S T with hb
  have : IsModuleTopology ℝ (TensorRSModel r s ℝ E) := isModuleTopologyOfFiniteDimensional
  have : IsModuleTopology ℝ ℝ := isModuleTopologyOfFiniteDimensional
  let bl : TensorRSModel r s ℝ E →ₗ[ℝ] TensorRSModel r s ℝ E →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ b
      (fun S₁ S₂ T => tensorInnerPointwise_add_left (I := I) (M := M) g r s x S₁ S₂ T)
      (fun c S T => by
        simp only [hb, smul_eq_mul]
        exact tensorInnerPointwise_smul_left (I := I) (M := M) g r s x c S T)
      (fun S T₁ T₂ => tensorInnerPointwise_add_right (I := I) (M := M) g r s x S T₁ T₂)
      (fun c S T => by
        simp only [hb, smul_eq_mul]
        exact tensorInnerPointwise_smul_right (I := I) (M := M) g r s x c S T)
  have hbil : Continuous
      (fun p : TensorRSModel r s ℝ E × TensorRSModel r s ℝ E => bl p.1 p.2) :=
    IsModuleTopology.continuous_bilinear_of_finite_left bl
  have hdiag : Continuous (fun S : TensorRSModel r s ℝ E => b S S) := by
    have hcomp : Continuous (fun S : TensorRSModel r s ℝ E => bl S S) :=
      hbil.comp (continuous_id.prodMk continuous_id)
    exact hcomp
  unfold tensorPointwiseNorm
  exact Real.continuous_sqrt.comp hdiag

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.tensorPointwiseNorm_continuous then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.tensorPointwiseNorm_continuous"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.tensorPointwiseNorm_continuous ``Submission.DifferentialGeometry.Integral.L2.tensorPointwiseNorm_continuous

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
theorem tensorPointwiseNorm_intervalIntegral_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (f : ℝ → TensorRSModel r s ℝ E)
    (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1)) :
    tensorPointwiseNorm (I := I) (M := M) g r s x (∫ t in (0 : ℝ)..1, f t) ≤
      ∫ t in (0 : ℝ)..1, tensorPointwiseNorm (I := I) (M := M) g r s x (f t) := by
  classical
  set p : Seminorm ℝ (TensorRSModel r s ℝ E) :=
    tensorPointwiseSeminorm (I := I) (M := M) g r s x with hp_def
  have hp_cont : Continuous (p : TensorRSModel r s ℝ E → ℝ) := by
    have hpeq : (p : TensorRSModel r s ℝ E → ℝ) =
        tensorPointwiseNorm (I := I) (M := M) g r s x := rfl
    rw [hpeq]; exact tensorPointwiseNorm_continuous (I := I) (M := M) g r s x
  have hprob : _root_.MeasureTheory.IsProbabilityMeasure (volume.restrict (Set.Ioc (0:ℝ) 1)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ioc]
    norm_num
  have hf_meas : ContinuousOn f (Set.Ioc (0 : ℝ) 1) := hf.mono Set.Ioc_subset_Icc_self
  have hf_int : _root_.MeasureTheory.Integrable f (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
    (hf.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  have hpf_int : _root_.MeasureTheory.Integrable (fun t => p (f t)) (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
    ((hp_cont.comp_continuousOn hf).integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  have hjensen :
      p (∫ t, f t ∂(volume.restrict (Set.Ioc (0:ℝ) 1))) ≤
        ∫ t, p (f t) ∂(volume.restrict (Set.Ioc (0:ℝ) 1)) :=
    p.convexOn.map_integral_le hp_cont.continuousOn isClosed_univ
      (Filter.Eventually.of_forall (fun _ => Set.mem_univ _)) hf_int hpf_int
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  exact hjensen

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.tensorPointwiseNorm_intervalIntegral_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.tensorPointwiseNorm_intervalIntegral_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.tensorPointwiseNorm_intervalIntegral_le ``Submission.DifferentialGeometry.Integral.L2.tensorPointwiseNorm_intervalIntegral_le

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem riemannianFiberNormSq_pathIntegralCoeffField_le_sq
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s) (S : Set ℝ) (hS : IsOpen S)
    (hSI : Set.uIcc (0 : ℝ) 1 ⊆ S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) q.1 ((Φ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S))
    (x : M) (Λ : ℝ)
    (hcont : ContinuousOn (fun t : ℝ => TensorRSSpace.toModel ((Φ t).toSection x))
      (Set.Icc (0 : ℝ) 1))
    (hsup : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ r s x ((Φ t).toSection x)) ≤ Λ) :
    riemannianFiberNormSq (I := I) (M := M) g₀ r s x
        ((pathIntegralCoeffField (I := I) (M := M) g₀ r s Φ S hS hSI hjoint).toSection x) ≤ Λ ^
          2 := by
  classical
  set f : ℝ → TensorRSModel r s ℝ E :=
    fun t => TensorRSSpace.toModel ((Φ t).toSection x) with hf_def
  have hfns : riemannianFiberNormSq (I := I) (M := M) g₀ r s x
      ((pathIntegralCoeffField (I := I) (M := M) g₀ r s Φ S hS hSI hjoint).toSection x) =
      tensorPointwiseNorm (I := I) (M := M) g₀ r s x (∫ t in (0 : ℝ)..1, f t) ^ 2 := by
    rw [riemannianFiberNormSq_eq_tensorInnerPointwise]
    rw [pathIntegralCoeffField_toSection, pathIntegralFib_toModel]
    unfold tensorPointwiseNorm
    rw [Real.sq_sqrt (tensorInnerPointwise_nonneg (I := I) (M := M) g₀ r s x _)]
  rw [hfns]
  have hbound :
      tensorPointwiseNorm (I := I) (M := M) g₀ r s x (∫ t in (0 : ℝ)..1, f t) ≤ Λ := by
    refine le_trans (tensorPointwiseNorm_intervalIntegral_le (I := I) (M := M) g₀ r s x f hcont) ?_
    have hpt : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        tensorPointwiseNorm (I := I) (M := M) g₀ r s x (f t) ≤ Λ := by
      intro t ht
      have hfns_t : tensorPointwiseNorm (I := I) (M := M) g₀ r s x (f t) =
          Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ r s x ((Φ t).toSection x)) := by
        rw [riemannianFiberNormSq_eq_tensorInnerPointwise]; rfl
      rw [hfns_t]; exact hsup t ht
    have hle : (∫ t in (0 : ℝ)..1, tensorPointwiseNorm (I := I) (M := M) g₀ r s x (f t)) ≤
        ∫ _t in (0 : ℝ)..1, Λ := by
      refine intervalIntegral.integral_mono_on (by norm_num) ?_ intervalIntegrable_const ?_
      · exact ((tensorPointwiseNorm_continuous (I := I) (M := M) g₀ r s x).comp_continuousOn
          hcont).intervalIntegrable_of_Icc (by norm_num)
      · exact fun t ht => hpt t ht
    refine le_trans hle ?_
    rw [intervalIntegral.integral_const]; simp
  have hsqnn : 0 ≤ tensorPointwiseNorm (I := I) (M := M) g₀ r s x (∫ t in (0 : ℝ)..1, f t) :=
    tensorPointwiseNorm_nonneg (I := I) (M := M) g₀ r s x _
  have hΛ_nn : 0 ≤ Λ :=
    le_trans (Real.sqrt_nonneg _) (hsup 0 (by simp))
  nlinarith only [hbound, hsqnn, hΛ_nn]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.riemannianFiberNormSq_pathIntegralCoeffField_le_sq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.riemannianFiberNormSq_pathIntegralCoeffField_le_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.riemannianFiberNormSq_pathIntegralCoeffField_le_sq ``Submission.DifferentialGeometry.Integral.L2.riemannianFiberNormSq_pathIntegralCoeffField_le_sq

private theorem sq_intervalIntegral_le_intervalIntegral_sq
    (h : ℝ → ℝ) (hcont : ContinuousOn h (Set.Icc (0 : ℝ) 1)) :
    (∫ t in (0 : ℝ)..1, h t) ^ 2 ≤ ∫ t in (0 : ℝ)..1, (h t) ^ 2 := by
  classical
  have hprob : _root_.MeasureTheory.IsProbabilityMeasure (volume.restrict (Set.Ioc (0:ℝ) 1)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ioc]
    norm_num
  have hcontIoc : ContinuousOn h (Set.Ioc (0 : ℝ) 1) := hcont.mono Set.Ioc_subset_Icc_self
  have hint : _root_.MeasureTheory.Integrable h (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
    (hcont.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  have hintsq : _root_.MeasureTheory.Integrable (fun t => (h t) ^ 2) (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
    (((continuous_pow 2).comp_continuousOn hcont).integrableOn_Icc).mono_set
      Set.Ioc_subset_Icc_self
  have hconvex : ConvexOn ℝ (Set.univ : Set ℝ) (fun x : ℝ => x ^ 2) :=
    Even.convexOn_pow (by decide)
  have hjensen :
      (∫ t, h t ∂(volume.restrict (Set.Ioc (0:ℝ) 1))) ^ 2 ≤
        ∫ t, (h t) ^ 2 ∂(volume.restrict (Set.Ioc (0:ℝ) 1)) := by
    have := hconvex.map_integral_le (f := h) (by fun_prop) isClosed_univ
      (Filter.Eventually.of_forall (fun _ => Set.mem_univ _)) hint hintsq
    simpa using this
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  exact hjensen

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.L2.sq_intervalIntegral_le_intervalIntegral_sq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.L2.sq_intervalIntegral_le_intervalIntegral_sq target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem riemannianFiberNormSq_pathIntegralCoeffField_le_intervalIntegral
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s) (S : Set ℝ) (hS : IsOpen S)
    (hSI : Set.uIcc (0 : ℝ) 1 ⊆ S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) q.1 ((Φ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S))
    (x : M)
    (hcont : ContinuousOn (fun t : ℝ => TensorRSSpace.toModel ((Φ t).toSection x))
      (Set.Icc (0 : ℝ) 1)) :
    riemannianFiberNormSq (I := I) (M := M) g₀ r s x
        ((pathIntegralCoeffField (I := I) (M := M) g₀ r s Φ S hS hSI hjoint).toSection x) ≤
      ∫ t in (0 : ℝ)..1,
        riemannianFiberNormSq (I := I) (M := M) g₀ r s x ((Φ t).toSection x) := by
  classical
  set f : ℝ → TensorRSModel r s ℝ E :=
    fun t => TensorRSSpace.toModel ((Φ t).toSection x) with hf_def
  have hfns : riemannianFiberNormSq (I := I) (M := M) g₀ r s x
      ((pathIntegralCoeffField (I := I) (M := M) g₀ r s Φ S hS hSI hjoint).toSection x) =
      tensorPointwiseNorm (I := I) (M := M) g₀ r s x (∫ t in (0 : ℝ)..1, f t) ^ 2 := by
    rw [riemannianFiberNormSq_eq_tensorInnerPointwise]
    rw [pathIntegralCoeffField_toSection, pathIntegralFib_toModel]
    unfold tensorPointwiseNorm
    rw [Real.sq_sqrt (tensorInnerPointwise_nonneg (I := I) (M := M) g₀ r s x _)]
  have hpt : ∀ t : ℝ,
      tensorPointwiseNorm (I := I) (M := M) g₀ r s x (f t) ^ 2 =
        riemannianFiberNormSq (I := I) (M := M) g₀ r s x ((Φ t).toSection x) := by
    intro t
    rw [riemannianFiberNormSq_eq_tensorInnerPointwise]
    unfold tensorPointwiseNorm
    rw [Real.sq_sqrt (tensorInnerPointwise_nonneg (I := I) (M := M) g₀ r s x _)]
  have hnormcont : ContinuousOn (fun t : ℝ =>
      tensorPointwiseNorm (I := I) (M := M) g₀ r s x (f t)) (Set.Icc (0 : ℝ) 1) :=
    (tensorPointwiseNorm_continuous (I := I) (M := M) g₀ r s x).comp_continuousOn hcont
  rw [hfns]
  have hjensen : tensorPointwiseNorm (I := I) (M := M) g₀ r s x (∫ t in (0 : ℝ)..1, f t) ≤
      ∫ t in (0 : ℝ)..1, tensorPointwiseNorm (I := I) (M := M) g₀ r s x (f t) :=
    tensorPointwiseNorm_intervalIntegral_le (I := I) (M := M) g₀ r s x f hcont
  have hnn : 0 ≤ tensorPointwiseNorm (I := I) (M := M) g₀ r s x (∫ t in (0 : ℝ)..1, f t) :=
    tensorPointwiseNorm_nonneg (I := I) (M := M) g₀ r s x _
  have hsqmono :
      tensorPointwiseNorm (I := I) (M := M) g₀ r s x (∫ t in (0 : ℝ)..1, f t) ^ 2 ≤
        (∫ t in (0 : ℝ)..1, tensorPointwiseNorm (I := I) (M := M) g₀ r s x (f t)) ^ 2 := by
    have hrhs_nn : 0 ≤ ∫ t in (0 : ℝ)..1, tensorPointwiseNorm (I := I) (M := M) g₀ r s x (f t) :=
      le_trans hnn hjensen
    nlinarith only [hjensen, hnn, hrhs_nn]
  have hcs :
      (∫ t in (0 : ℝ)..1, tensorPointwiseNorm (I := I) (M := M) g₀ r s x (f t)) ^ 2 ≤
        ∫ t in (0 : ℝ)..1, tensorPointwiseNorm (I := I) (M := M) g₀ r s x (f t) ^ 2 :=
    sq_intervalIntegral_le_intervalIntegral_sq
      (fun t => tensorPointwiseNorm (I := I) (M := M) g₀ r s x (f t)) hnormcont
  have heqint :
      (∫ t in (0 : ℝ)..1, tensorPointwiseNorm (I := I) (M := M) g₀ r s x (f t) ^ 2) =
        ∫ t in (0 : ℝ)..1,
          riemannianFiberNormSq (I := I) (M := M) g₀ r s x ((Φ t).toSection x) := by
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    exact hpt t
  calc tensorPointwiseNorm (I := I) (M := M) g₀ r s x (∫ t in (0 : ℝ)..1, f t) ^ 2
      ≤ (∫ t in (0 : ℝ)..1, tensorPointwiseNorm (I := I) (M := M) g₀ r s x (f t)) ^ 2 := hsqmono
    _ ≤ ∫ t in (0 : ℝ)..1, tensorPointwiseNorm (I := I) (M := M) g₀ r s x (f t) ^ 2 := hcs
    _ = ∫ t in (0 : ℝ)..1,
          riemannianFiberNormSq (I := I) (M := M) g₀ r s x ((Φ t).toSection x) := heqint

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.riemannianFiberNormSq_pathIntegralCoeffField_le_intervalIntegral then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.riemannianFiberNormSq_pathIntegralCoeffField_le_intervalIntegral"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.riemannianFiberNormSq_pathIntegralCoeffField_le_intervalIntegral ``Submission.DifferentialGeometry.Integral.L2.riemannianFiberNormSq_pathIntegralCoeffField_le_intervalIntegral

open _root_.Submission.DifferentialGeometry.Integral.Measure in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem tensorL2NormSq_pathIntegralCoeffField_le_intervalIntegral_normSq
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s) (S : Set ℝ) (hS : IsOpen S)
    (hSI : Set.uIcc (0 : ℝ) 1 ⊆ S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) q.1 ((Φ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S))
    (hcont : ∀ x : M, ContinuousOn (fun t : ℝ => TensorRSSpace.toModel ((Φ t).toSection x))
      (Set.Icc (0 : ℝ) 1))
    (hjriemannianFiberNormSq : ContinuousOn
      (fun p : ℝ × M =>
        riemannianFiberNormSq (I := I) (M := M) g₀ r s p.2 ((Φ p.1).toSection p.2))
      (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set M))) :
    ‖pathIntegralCoeffField (I := I) (M := M) g₀ r s Φ S hS hSI hjoint‖ ^ 2 ≤
      ∫ t in (0 : ℝ)..1, ‖Φ t‖ ^ 2 := by
  classical
  let : MeasurableSpace M := borel M
  have : BorelSpace M := ⟨rfl⟩
  let : MeasurableSpace ℝ := borel ℝ
  have : BorelSpace ℝ := ⟨rfl⟩
  set μ : _root_.MeasureTheory.Measure M := riemannianVolumeMeasure (I := I) (M := M) g₀ with hμ
  have : _root_.MeasureTheory.IsFiniteMeasure μ :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g₀
  set Ξ := pathIntegralCoeffField (I := I) (M := M) g₀ r s Φ S hS hSI hjoint with hΞ
  set F : ℝ → M → ℝ :=
    fun t x => riemannianFiberNormSq (I := I) (M := M) g₀ r s x ((Φ t).toSection x) with hF
  have hΞnormsq : ‖Ξ‖ ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ r s x (Ξ.toSection x) ∂μ := by
    rw [SmoothCcTensor.norm_def]
    have hbridge := tensorL2Norm_sq_eq_integral_riemannianFiberNormSq
      (I := I) (M := M) g₀ r s (fun x => Ξ.toSection x)
    rw [show Ξ.toFun = fun x => TensorRSSpace.toModel (Ξ.toSection x) from rfl]
    exact hbridge
  have hΦnormsq : ∀ t : ℝ, ‖Φ t‖ ^ 2 = ∫ x, F t x ∂μ := by
    intro t
    rw [SmoothCcTensor.norm_def]
    have hbridge := tensorL2Norm_sq_eq_integral_riemannianFiberNormSq
      (I := I) (M := M) g₀ r s (fun x => (Φ t).toSection x)
    rw [show (Φ t).toFun = fun x => TensorRSSpace.toModel ((Φ t).toSection x) from rfl]
    exact hbridge
  have hperx : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ r s x (Ξ.toSection x) ≤
        ∫ t in (0 : ℝ)..1, F t x := fun x =>
    riemannianFiberNormSq_pathIntegralCoeffField_le_intervalIntegral
      (I := I) (M := M) g₀ r s Φ S hS hSI hjoint x (hcont x)
  have hFnn : ∀ t x, 0 ≤ F t x := fun t x =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ r s x ((Φ t).toSection x)
  have hFcont : ContinuousOn (Function.uncurry F)
      (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set M)) := hjriemannianFiberNormSq
  have hcompact : IsCompact (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set M)) :=
    isCompact_Icc.prod isCompact_univ
  obtain ⟨Cb, hCb⟩ := (hcompact.image_of_continuousOn hFcont.norm).bddAbove
  have huIoc : Set.uIoc (0:ℝ) 1 = Set.Ioc (0:ℝ) 1 := Set.uIoc_of_le (by norm_num)
  have hfintime : _root_.MeasureTheory.IsFiniteMeasure (volume.restrict (Set.uIoc (0:ℝ) 1)) := by
    constructor
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, huIoc, Real.volume_Ioc]
    simp
  have hfinprod : _root_.MeasureTheory.IsFiniteMeasure ((volume.restrict (Set.uIoc (0:ℝ) 1)).prod μ) :=
    inferInstance
  have hprod_eq :
      (volume.restrict (Set.uIoc (0:ℝ) 1)).prod μ
        = (volume.prod μ).restrict (Set.uIoc (0:ℝ) 1 ×ˢ (Set.univ : Set M)) := by
    conv_lhs => rw [← Measure.restrict_univ (μ := μ)]
    rw [Measure.prod_restrict]
  have hmeas : _root_.MeasureTheory.AEStronglyMeasurable (Function.uncurry F)
      ((volume.restrict (Set.uIoc (0:ℝ) 1)).prod μ) := by
    rw [hprod_eq]
    refine ContinuousOn.aestronglyMeasurable ?_ (measurableSet_uIoc.prod MeasurableSet.univ)
    exact hFcont.mono (Set.prod_mono (huIoc ▸ Set.Ioc_subset_Icc_self) (subset_refl _))
  have hint : _root_.MeasureTheory.Integrable (Function.uncurry F)
      ((volume.restrict (Set.uIoc (0:ℝ) 1)).prod μ) := by
    refine Integrable.of_mem_Icc 0 Cb hmeas.aemeasurable ?_
    rw [hprod_eq]
    have hae : ∀ᵐ p ∂((volume.prod μ).restrict
        (Set.uIoc (0:ℝ) 1 ×ˢ (Set.univ : Set M))),
        p ∈ Set.uIoc (0:ℝ) 1 ×ˢ (Set.univ : Set M) :=
      _root_.MeasureTheory.ae_restrict_mem (measurableSet_uIoc.prod MeasurableSet.univ)
    filter_upwards [hae] with p hp
    obtain ⟨hp1, _⟩ := hp
    refine ⟨hFnn p.1 p.2, ?_⟩
    have hmem : p ∈ Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set M) :=
      ⟨(huIoc ▸ Set.Ioc_subset_Icc_self) hp1, Set.mem_univ _⟩
    have hb := hCb (Set.mem_image_of_mem _ hmem)
    rw [Real.norm_eq_abs] at hb
    exact le_trans (le_abs_self _) hb
  have hswap :
      ∫ x, (∫ t in (0 : ℝ)..1, F t x) ∂μ
        = ∫ t in (0 : ℝ)..1, ∫ x, F t x ∂μ :=
    (MeasureTheory.intervalIntegral_integral_swap (μ := μ) (f := F) hint).symm
  have hΞle : (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ r s x (Ξ.toSection x) ∂μ)
      ≤ ∫ x, (∫ t in (0 : ℝ)..1, F t x) ∂μ := by
    refine _root_.MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_
    · exact Filter.Eventually.of_forall (fun x =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ r s x (Ξ.toSection x))
    · have hpr := hint.integral_prod_right
        (μ := volume.restrict (Set.uIoc (0:ℝ) 1)) (ν := μ)
      have heqfun : (fun x => ∫ t, Function.uncurry F (t, x)
            ∂(volume.restrict (Set.uIoc (0:ℝ) 1)))
          = fun x => ∫ t in (0 : ℝ)..1, F t x := by
        funext x
        rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1), ← huIoc]
        rfl
      rw [heqfun] at hpr
      exact hpr
    · exact Filter.Eventually.of_forall hperx
  rw [hΞnormsq]
  calc (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ r s x (Ξ.toSection x) ∂μ)
      ≤ ∫ x, (∫ t in (0 : ℝ)..1, F t x) ∂μ := hΞle
    _ = ∫ t in (0 : ℝ)..1, ∫ x, F t x ∂μ := hswap
    _ = ∫ t in (0 : ℝ)..1, ‖Φ t‖ ^ 2 := by
        refine intervalIntegral.integral_congr (fun t _ => ?_)
        rw [hΦnormsq t]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.tensorL2NormSq_pathIntegralCoeffField_le_intervalIntegral_normSq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.tensorL2NormSq_pathIntegralCoeffField_le_intervalIntegral_normSq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.tensorL2NormSq_pathIntegralCoeffField_le_intervalIntegral_normSq ``Submission.DifferentialGeometry.Integral.L2.tensorL2NormSq_pathIntegralCoeffField_le_intervalIntegral_normSq

open _root_.Submission.DifferentialGeometry.Analysis.Sobolev (iteratedCovGrad)

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem iteratedCovGrad_pathIntegralCoeffField_jetL2_le
    (g₀ : SmoothRiemannianMetric I M) (r sIdx a : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r sIdx) (B : ℝ)
    (S : Set ℝ) (hS : IsOpen S) (hSI : Set.uIcc (0 : ℝ) 1 ⊆ S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r sIdx ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r sIdx ℝ E)
        (E := fun z : M => TensorRSSpace r sIdx I z) q.1 ((Φ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S))
    (hΦ : ∀ s ∈ Set.Icc (0:ℝ) 1,
      (∑ i ∈ Finset.range (a+1),
        ‖iteratedCovGrad g₀ r sIdx i (Φ s)‖ ^ 2) ≤ B ^ 2)
    (hji : ∀ i ∈ Finset.range (a+1),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r (sIdx + i) ℝ E)) ∞
        (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r (sIdx + i) ℝ E)
          (E := fun z : M => TensorRSSpace r (sIdx + i) I z) q.1
          ((iteratedCovGrad g₀ r sIdx i (Φ q.2)).toSection q.1))
        ((Set.univ : Set M) ×ˢ S))
    (hci : ∀ i ∈ Finset.range (a+1), ∀ x : M,
      ContinuousOn (fun t : ℝ =>
        TensorRSSpace.toModel ((iteratedCovGrad g₀ r sIdx i (Φ t)).toSection x))
        (Set.Icc (0 : ℝ) 1))
    (hri : ∀ i ∈ Finset.range (a+1),
      ContinuousOn (fun p : ℝ × M =>
        riemannianFiberNormSq (I := I) (M := M) g₀ r (sIdx + i) p.2
          ((iteratedCovGrad g₀ r sIdx i (Φ p.1)).toSection p.2))
        (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set M)))
    (hii : ∀ i ∈ Finset.range (a+1),
      IntervalIntegrable
        (fun t : ℝ => ‖iteratedCovGrad g₀ r sIdx i (Φ t)‖ ^ 2) _root_.MeasureTheory.MeasureSpace.volume 0 1)
    (hcomm : ∀ (i : ℕ) (hi : i ∈ Finset.range (a+1)),
      iteratedCovGrad g₀ r sIdx i
          (pathIntegralCoeffField (I := I) (M := M) g₀ r sIdx Φ S hS hSI hjoint) =
        pathIntegralCoeffField (I := I) (M := M) g₀ r (sIdx + i)
          (fun t => iteratedCovGrad g₀ r sIdx i (Φ t)) S hS hSI (hji i hi)) :
    (∑ i ∈ Finset.range (a+1),
      ‖iteratedCovGrad g₀ r sIdx i
        (pathIntegralCoeffField (I := I) (M := M) g₀ r sIdx Φ S hS hSI hjoint)‖ ^ 2) ≤ B ^ 2 := by
  classical
  have hperi : ∀ i ∈ Finset.range (a+1),
      ‖iteratedCovGrad g₀ r sIdx i
          (pathIntegralCoeffField (I := I) (M := M) g₀ r sIdx Φ S hS hSI hjoint)‖ ^ 2 ≤
        ∫ t in (0 : ℝ)..1, ‖iteratedCovGrad g₀ r sIdx i (Φ t)‖ ^ 2 := by
    intro i hi
    rw [hcomm i hi]
    exact tensorL2NormSq_pathIntegralCoeffField_le_intervalIntegral_normSq
      (I := I) (M := M) g₀ r (sIdx + i)
      (fun t => iteratedCovGrad g₀ r sIdx i (Φ t)) S hS hSI (hji i hi)
      (hci i hi) (hri i hi)
  have hsumle :
      (∑ i ∈ Finset.range (a+1),
        ‖iteratedCovGrad g₀ r sIdx i
          (pathIntegralCoeffField (I := I) (M := M) g₀ r sIdx Φ S hS hSI hjoint)‖ ^ 2) ≤
      ∑ i ∈ Finset.range (a+1),
        ∫ t in (0 : ℝ)..1, ‖iteratedCovGrad g₀ r sIdx i (Φ t)‖ ^ 2 :=
    Finset.sum_le_sum hperi
  have hsumswap :
      (∑ i ∈ Finset.range (a+1),
        ∫ t in (0 : ℝ)..1, ‖iteratedCovGrad g₀ r sIdx i (Φ t)‖ ^ 2) =
      ∫ t in (0 : ℝ)..1,
        ∑ i ∈ Finset.range (a+1), ‖iteratedCovGrad g₀ r sIdx i (Φ t)‖ ^ 2 :=
    (intervalIntegral.integral_finsetSum (s := Finset.range (a+1)) hii).symm
  have hintsumle :
      (∫ t in (0 : ℝ)..1,
        ∑ i ∈ Finset.range (a+1), ‖iteratedCovGrad g₀ r sIdx i (Φ t)‖ ^ 2) ≤
      ∫ _t in (0 : ℝ)..1, B ^ 2 := by
    refine intervalIntegral.integral_mono_on (by norm_num) ?_ intervalIntegrable_const ?_
    · have hsum := IntervalIntegrable.sum (μ := _root_.MeasureTheory.MeasureSpace.volume) (a := 0) (b := 1)
        (Finset.range (a+1))
        (f := fun i t => ‖iteratedCovGrad g₀ r sIdx i (Φ t)‖ ^ 2)
        (fun i hi => hii i hi)
      have heqfun : (∑ i ∈ Finset.range (a+1),
            fun t : ℝ => ‖iteratedCovGrad g₀ r sIdx i (Φ t)‖ ^ 2)
          = fun t : ℝ => ∑ i ∈ Finset.range (a+1),
              ‖iteratedCovGrad g₀ r sIdx i (Φ t)‖ ^ 2 := by
        funext t
        simp only [Finset.sum_apply]
      rw [heqfun] at hsum
      exact hsum
    · intro t ht
      exact hΦ t ht
  have hconst : (∫ _t in (0 : ℝ)..1, B ^ 2) = B ^ 2 := by
    rw [intervalIntegral.integral_const]; simp
  calc (∑ i ∈ Finset.range (a+1),
          ‖iteratedCovGrad g₀ r sIdx i
            (pathIntegralCoeffField (I := I) (M := M) g₀ r sIdx Φ S hS hSI hjoint)‖ ^ 2)
      ≤ ∑ i ∈ Finset.range (a+1),
          ∫ t in (0 : ℝ)..1, ‖iteratedCovGrad g₀ r sIdx i (Φ t)‖ ^ 2 := hsumle
    _ = ∫ t in (0 : ℝ)..1,
          ∑ i ∈ Finset.range (a+1), ‖iteratedCovGrad g₀ r sIdx i (Φ t)‖ ^ 2 := hsumswap
    _ ≤ ∫ _t in (0 : ℝ)..1, B ^ 2 := hintsumle
    _ = B ^ 2 := hconst

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.iteratedCovGrad_pathIntegralCoeffField_jetL2_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.iteratedCovGrad_pathIntegralCoeffField_jetL2_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.iteratedCovGrad_pathIntegralCoeffField_jetL2_le ``Submission.DifferentialGeometry.Integral.L2.iteratedCovGrad_pathIntegralCoeffField_jetL2_le

end L2
end Integral
end DifferentialGeometry

end
