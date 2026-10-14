import Submission.DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties
import Submission.DifferentialGeometry.Analysis.Integration.L2.SmoothSections.PreHilbert
import Submission.DifferentialGeometry.Tensor.RSTensor.RankZero
import Submission.DifferentialGeometry.Tensor.RSTensor.Coordinates.Field
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.L2Space

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory
open scoped _root_.Manifold _root_.ContDiff _root_.Topology _root_.ENNReal

namespace DifferentialGeometry.Integral.L2.SmoothCcTensor

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

private theorem tensor_eval_scalar0
    (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 0) (x : M) :
    ((S.toFun x) (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E)
      (1 : ℝ))) Fin.elim0 = TensorRSField.scalar0 S.toSection x := by
  unfold TensorRSField.scalar0 TensorRSField.rs0
  simp only [toFun_apply, Tensor0SField.toScalarField]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.L2.SmoothCcTensor.tensor_eval_scalar0
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.L2.SmoothCcTensor.tensor_eval_scalar0 target :: scope.openDecls } }

private theorem tensor_inner_scalar0
    (g : SmoothRiemannianMetric I M) (S T : SmoothCcTensor g 0 0) (x : M) :
    tensorInnerPointwise g 0 0 x (S.toFun x) (T.toFun x) =
      TensorRSField.scalar0 S.toSection x * TensorRSField.scalar0 T.toSection x := by
  unfold tensorInnerPointwise
  rw [tensorInnerPointwise_0s_zero_arity, lowerAllUpperIndices_apply,
    lowerAllUpperIndices_apply]
  have hS : (separableFormAt g x 0
        (fun i : Fin 0 => (Fin.elim0 : Fin 0 → E) (Fin.castAdd 0 i))) =
      ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ) := by
    apply ContinuousMultilinearMap.ext
    intro w
    rw [separableFormAt_apply]
    simp
  rw [hS]
  exact congrArg₂ (· * ·) (tensor_eval_scalar0 g S x) (tensor_eval_scalar0 g T x)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.L2.SmoothCcTensor.tensor_inner_scalar0
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.L2.SmoothCcTensor.tensor_inner_scalar0 target :: scope.openDecls } }

variable [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Integral.L2.SmoothCcTensor.instMeasurableSpace : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.L2.SmoothCcTensor.instMeasurableSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.L2.SmoothCcTensor.instMeasurableSpace target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.L2.SmoothCcTensor.instBorelSpace : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.L2.SmoothCcTensor.instBorelSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.L2.SmoothCcTensor.instBorelSpace target :: scope.openDecls } }

theorem inner_eq_integral_scalar0_mul
    (g : SmoothRiemannianMetric I M) (S T : SmoothCcTensor g 0 0) :
    _root_.Inner.inner ℝ S T = ∫ x, TensorRSField.scalar0 S.toSection x *
      TensorRSField.scalar0 T.toSection x ∂riemannianVolumeMeasure I M g := by
  rw [SmoothCcTensor.inner_def]
  unfold tensorL2Inner
  apply _root_.MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall (tensor_inner_scalar0 g S T)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.SmoothCcTensor.inner_eq_integral_scalar0_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.SmoothCcTensor.inner_eq_integral_scalar0_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.SmoothCcTensor.inner_eq_integral_scalar0_mul ``Submission.DifferentialGeometry.Integral.L2.SmoothCcTensor.inner_eq_integral_scalar0_mul

theorem memLp_scalar0 (g : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g 0 0) (p : ℝ≥0∞) :
    _root_.MeasureTheory.MemLp (TensorRSField.scalar0 S.toSection) p
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  let _ := riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g
  apply (TensorRSField.scalar0_smooth S.toSection).continuous.memLp_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact S.hasCompactSupport
  intro x hx
  apply subset_tsupport S.toFun
  rw [Function.mem_support] at hx ⊢
  intro hzero
  apply hx
  unfold TensorRSField.scalar0 TensorRSField.rs0 Tensor0SField.toScalarField
  change (S.toFun x) (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E)
    (1 : ℝ)) Fin.elim0 = 0
  rw [hzero]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.SmoothCcTensor.memLp_scalar0 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.SmoothCcTensor.memLp_scalar0"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.SmoothCcTensor.memLp_scalar0 ``Submission.DifferentialGeometry.Integral.L2.SmoothCcTensor.memLp_scalar0

theorem norm_eq_scalar0_eLpNorm (g : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g 0 0) :
    ‖S‖ = ENNReal.toReal (_root_.MeasureTheory.eLpNorm (TensorRSField.scalar0 S.toSection)
      2 (riemannianVolumeMeasure (I := I) (M := M) g)) := by
  let f := TensorRSField.scalar0 S.toSection
  have hf := memLp_scalar0 g S 2
  rw [← Lp.norm_toLp f hf]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  rw [inner_eq_integral_scalar0_mul, L2.inner_def]
  apply _root_.MeasureTheory.integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp hf] with x hx
  rw [hx]
  rw [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs, pow_two]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.SmoothCcTensor.norm_eq_scalar0_eLpNorm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.SmoothCcTensor.norm_eq_scalar0_eLpNorm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.SmoothCcTensor.norm_eq_scalar0_eLpNorm ``Submission.DifferentialGeometry.Integral.L2.SmoothCcTensor.norm_eq_scalar0_eLpNorm

end DifferentialGeometry.Integral.L2.SmoothCcTensor

end

noncomputable section

open _root_.MeasureTheory
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Integral.L2.SmoothCcTensor

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

theorem norm_le_mul_sqrt_volume_of_scalar0_bound
    (g : SmoothRiemannianMetric I M)
    [_root_.MeasureTheory.IsFiniteMeasure (riemannianVolumeMeasure I M g)] (S : SmoothCcTensor g 0 0)
    {K : ℝ} (hK : 0 ≤ K)
    (hS : ∀ x : M, |TensorRSField.scalar0 S.toSection x| ≤ K) :
    ‖S‖ ≤ K * Real.sqrt ((riemannianVolumeMeasure I M g).real Set.univ) := by
  have hvol : 0 ≤ (riemannianVolumeMeasure I M g).real Set.univ := ENNReal.toReal_nonneg
  have hsq : ‖S‖ ^ 2 =
      ∫ x, (TensorRSField.scalar0 S.toSection x) ^ 2 ∂riemannianVolumeMeasure I M g := by
    rw [← real_inner_self_eq_norm_sq, inner_eq_integral_scalar0_mul]
    simp only [pow_two]
  have hint : (∫ x, (TensorRSField.scalar0 S.toSection x) ^ 2
        ∂riemannianVolumeMeasure I M g) ≤
      (riemannianVolumeMeasure I M g).real Set.univ * K ^ 2 := by
    have hle := _root_.MeasureTheory.integral_mono_of_nonneg
      (μ := riemannianVolumeMeasure I M g)
      (f := fun x => (TensorRSField.scalar0 S.toSection x) ^ 2)
      (g := fun _ : M => K ^ 2)
      (Filter.Eventually.of_forall (fun x => sq_nonneg (TensorRSField.scalar0 S.toSection x)))
      (_root_.MeasureTheory.integrable_const _)
      (Filter.Eventually.of_forall (fun x => by
        calc
          (TensorRSField.scalar0 S.toSection x) ^ 2 =
              |TensorRSField.scalar0 S.toSection x| ^ 2 := (sq_abs _).symm
          _ ≤ K ^ 2 := (sq_le_sq₀ (abs_nonneg _) hK).2 (hS x)))
    simpa only [_root_.MeasureTheory.integral_const, smul_eq_mul] using hle
  have hfinal : ‖S‖ ^ 2 ≤
      (K * Real.sqrt ((riemannianVolumeMeasure I M g).real Set.univ)) ^ 2 := by
    rw [hsq, mul_pow, Real.sq_sqrt hvol, mul_comm (K ^ 2)]
    exact hint
  have hsqrt := Real.sqrt_le_sqrt hfinal
  rwa [Real.sqrt_sq (norm_nonneg S),
    Real.sqrt_sq (mul_nonneg hK (Real.sqrt_nonneg _))] at hsqrt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.SmoothCcTensor.norm_le_mul_sqrt_volume_of_scalar0_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.SmoothCcTensor.norm_le_mul_sqrt_volume_of_scalar0_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.SmoothCcTensor.norm_le_mul_sqrt_volume_of_scalar0_bound ``Submission.DifferentialGeometry.Integral.L2.SmoothCcTensor.norm_le_mul_sqrt_volume_of_scalar0_bound

theorem exists_norm_le_mul_of_scalar0_bound [CompactSpace M]
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : SmoothCcTensor g 0 0) (K : ℝ), 0 ≤ K →
      (∀ x : M, |TensorRSField.scalar0 S.toSection x| ≤ K) → ‖S‖ ≤ C * K := by
  let _ := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
  refine ⟨Real.sqrt ((riemannianVolumeMeasure I M g).real Set.univ),
    Real.sqrt_nonneg _, ?_⟩
  intro S K hK hS
  simpa only [mul_comm] using norm_le_mul_sqrt_volume_of_scalar0_bound g S hK hS

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.SmoothCcTensor.exists_norm_le_mul_of_scalar0_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.SmoothCcTensor.exists_norm_le_mul_of_scalar0_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.SmoothCcTensor.exists_norm_le_mul_of_scalar0_bound ``Submission.DifferentialGeometry.Integral.L2.SmoothCcTensor.exists_norm_le_mul_of_scalar0_bound

end DifferentialGeometry.Integral.L2.SmoothCcTensor

end
