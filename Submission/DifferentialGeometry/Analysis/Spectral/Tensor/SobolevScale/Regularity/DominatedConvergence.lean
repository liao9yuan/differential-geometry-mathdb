import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Defs
import Mathlib.Analysis.Normed.Group.Tannery

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Manifold _root_.Set _root_.Filter
open scoped _root_.Topology _root_.ContDiff

namespace DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
variable {g : SmoothRiemannianMetric I M} {r s : ℕ} {σ : ℝ}

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral

theorem tendsto_of_coeff_of_summable_bound {α : Type*} {l : Filter α}
    {f : α → TensorHs (I := I) (M := M) g r s σ}
    {v : TensorHs (I := I) (M := M) g r s σ}
    (hcoeff : ∀ i, _root_.Filter.Tendsto (fun x => (f x).coeff i) l (𝓝 (v.coeff i)))
    {B : TensorEigenIdx (I := I) (M := M) g r s → ℝ} (hB : Summable B)
    (hbound : ∀ᶠ x in l, ∀ i,
      tensorSobolevWeight (I := I) (M := M) i σ * ((f x).coeff i) ^ 2 ≤ B i) :
    Tendsto f l (𝓝 v) := by
  have hsum := (hB.mul_left 2).add (v.weighted_summable.mul_left 2)
  have hlim : _root_.Filter.Tendsto
      (fun x => ∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
        ((f x).coeff i - v.coeff i) ^ 2) l (𝓝 (0 : ℝ)) := by
    have hlim := tendsto_tsum_of_dominated_convergence hsum
      (fun i => ((hcoeff i).sub_const (v.coeff i)).pow 2 |>.const_mul
        (tensorSobolevWeight (I := I) (M := M) i σ))
    simp only [sub_self, zero_pow (by decide : 2 ≠ 0), _root_.MulZeroClass.mul_zero, tsum_zero] at hlim
    apply hlim
    filter_upwards [hbound] with x hx i
    have hw := tensorSobolevWeight_nonneg (I := I) (M := M) i σ
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw (sq_nonneg _))]
    have hsq : ((f x).coeff i - v.coeff i) ^ 2 ≤
        2 * ((f x).coeff i) ^ 2 + 2 * (v.coeff i) ^ 2 := by
      nlinarith [sq_nonneg ((f x).coeff i + v.coeff i)]
    nlinarith [mul_le_mul_of_nonneg_left hsq hw, hx i]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hroot := (Real.continuous_sqrt.tendsto 0).comp hlim
  have hsub : ∀ x i, (f x - v).coeff i = (f x).coeff i - v.coeff i := by
    intro x i
    simp only [sub_eq_add_neg, add_coeff, neg_coeff]
  simpa only [Real.sqrt_zero, Function.comp_def, norm_eq_sqrt_tsum, hsub] using hroot

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.tendsto_of_coeff_of_summable_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.tendsto_of_coeff_of_summable_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.tendsto_of_coeff_of_summable_bound ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.tendsto_of_coeff_of_summable_bound

theorem continuousOn_of_coeff_of_summable_bound {α : Type*} [TopologicalSpace α]
    {K : Set α} {f : α → TensorHs (I := I) (M := M) g r s σ}
    (hcoeff : ∀ i, ContinuousOn (fun x => (f x).coeff i) K)
    {B : TensorEigenIdx (I := I) (M := M) g r s → ℝ} (hB : Summable B)
    (hbound : ∀ x ∈ K, ∀ i,
      tensorSobolevWeight (I := I) (M := M) i σ * ((f x).coeff i) ^ 2 ≤ B i) :
    ContinuousOn f K := by
  intro x hx
  exact tendsto_of_coeff_of_summable_bound (fun i => hcoeff i x hx) hB
    (_root_.Filter.mem_of_superset self_mem_nhdsWithin fun y hy => hbound y hy)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.continuousOn_of_coeff_of_summable_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.continuousOn_of_coeff_of_summable_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.continuousOn_of_coeff_of_summable_bound ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.continuousOn_of_coeff_of_summable_bound

end DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs
