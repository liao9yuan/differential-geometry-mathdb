import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.Gradient.QuadraticLowerSemicontinuity
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Filter _root_.Submission.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.NNReal _root_.ENNReal _root_.Topology

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} {ι : Type*} [Fintype ι]

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "F" => EuclideanSpace ℝ ι

theorem integral_sum_norm_sq_weak_gradient_le_liminf_on_subset
    {Ω S : Set E} (hS : MeasurableSet S) (hSΩ : S ⊆ Ω)
    (f : ℕ → E → F) (v : E → F)
    (hs : ∀ n i, DeGiorgi.MemW1pWitness 2 (fun x => f n x i) Ω)
    (hv : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => v x i) Ω)
    (K : ℕ → ℝ≥0) (hf : ∀ n, LipschitzWith (K n) (f n))
    (hrep : ∀ n i j, (fun x => (hs n i).weakGrad x j) =ᵐ[volume.restrict Ω]
      (fun x => fderiv ℝ (fun y => f n y i) x (EuclideanSpace.single j 1)))
    (hweak : ∀ i (z : _root_.MeasureTheory.Lp E 2 (volume.restrict Ω)),
      _root_.Filter.Tendsto (fun n => _root_.Inner.inner ℝ (DeGiorgi.gradLpOfWitness (hs n i)) z) _root_.Filter.atTop
        (𝓝 (_root_.Inner.inner ℝ (DeGiorgi.gradLpOfWitness (hv i)) z))) :
    (∫ x in S, ∑ j : Fin d, ‖WithLp.toLp 2 (fun i => (hv i).weakGrad x j)‖ ^ 2) ≤
      _root_.Filter.liminf (fun n => ∫ x in S, ∑ j : Fin d,
        ‖fderiv ℝ (f n) x (EuclideanSpace.single j 1)‖ ^ 2) atTop := by
  classical
  let B : E → F →L[ℝ] F →L[ℝ] ℝ := S.indicator (fun _ => innerSL ℝ)
  have hm : _root_.MeasureTheory.AEStronglyMeasurable B (volume.restrict Ω) :=
    aestronglyMeasurable_const.indicator hS
  have hb : ∀ᵐ x ∂volume.restrict Ω, ‖B x‖ ≤ (1 : ℝ) := by
    filter_upwards [] with x
    by_cases hx : x ∈ S
    · simpa only [B, _root_.Set.indicator_of_mem hx] using
        (show ‖(innerSL ℝ : F →L[ℝ] F →L[ℝ] ℝ)‖ ≤ 1 from norm_innerSL_le ℝ)
    · rw [show B x = 0 by simp only [B, _root_.Set.indicator_of_notMem hx]]
      rw [ContinuousLinearMap.opNorm_zero]
      exact zero_le_one
  have hp : ∀ᵐ x ∂volume.restrict Ω, ∀ z : F, 0 ≤ B x z z := by
    filter_upwards [] with x
    intro z
    by_cases hx : x ∈ S
    · rw [show B x = innerSL ℝ by simp only [B, _root_.Set.indicator_of_mem hx]]
      change 0 ≤ _root_.Inner.inner ℝ z z
      exact real_inner_self_nonneg
    · simp only [B, _root_.Set.indicator_of_notMem hx, zero_apply, le_refl]
  have heq (w : E → F) :
      (∫ x in Ω, B x (w x) (w x)) = ∫ x in S, ‖w x‖ ^ 2 := by
    have hi : (fun x => B x (w x) (w x)) = S.indicator (fun x => ‖w x‖ ^ 2) := by
      funext x
      by_cases hx : x ∈ S
      · rw [show B x = innerSL ℝ by simp only [B, _root_.Set.indicator_of_mem hx], _root_.Set.indicator_of_mem hx]
        change _root_.Inner.inner ℝ (w x) (w x) = ‖w x‖ ^ 2
        exact real_inner_self_eq_norm_sq _
      · simp only [B, _root_.Set.indicator_of_notMem hx, zero_apply]
    rw [hi, _root_.MeasureTheory.setIntegral_indicator hS, inter_eq_right.mpr hSΩ]
  have hbase := sum_integral_quadratic_gradient_column_le_liminf_of_tendsto_inner
    f v hs hv K hf hrep hweak (fun _ => B) B (fun _ => hm) 1 (fun _ => hb)
    (Eventually.of_forall fun _ => tendsto_const_nhds) (fun _ => hp)
  simp_rw [heq] at hbase
  obtain ⟨A, A₀, hA, hA₀, _⟩ := exists_lp_gradient_columns_of_tendsto_inner
    f v hs hv K hf hrep hweak
  have hvi (j : Fin d) : _root_.MeasureTheory.Integrable (fun x =>
      ‖WithLp.toLp 2 (fun i => (hv i).weakGrad x j)‖ ^ 2) (volume.restrict S) := by
    have hmem : _root_.MeasureTheory.MemLp (fun x => WithLp.toLp 2 (fun i => (hv i).weakGrad x j))
        2 (volume.restrict Ω) := (Lp.memLp (A₀ j)).ae_eq (hA₀ j)
    exact (hmem.mono_measure (Measure.restrict_mono_set _root_.MeasureTheory.MeasureSpace.volume hSΩ)).norm.integrable_sq
  have hfi (n : ℕ) (j : Fin d) : _root_.MeasureTheory.Integrable (fun x =>
      ‖fderiv ℝ (f n) x (EuclideanSpace.single j 1)‖ ^ 2) (volume.restrict S) := by
    have hmem : _root_.MeasureTheory.MemLp (fun x => fderiv ℝ (f n) x (EuclideanSpace.single j 1))
        2 (volume.restrict Ω) := (Lp.memLp (A j n)).ae_eq (hA j n)
    exact (hmem.mono_measure (Measure.restrict_mono_set _root_.MeasureTheory.MeasureSpace.volume hSΩ)).norm.integrable_sq
  have hvsum : (∫ x in S, ∑ j : Fin d,
      ‖WithLp.toLp 2 (fun i => (hv i).weakGrad x j)‖ ^ 2) =
        ∑ j : Fin d, ∫ x in S, ‖WithLp.toLp 2 (fun i => (hv i).weakGrad x j)‖ ^ 2 :=
    _root_.MeasureTheory.integral_finsetSum Finset.univ (fun j _ => hvi j)
  have hfsum (n : ℕ) : (∫ x in S, ∑ j : Fin d,
      ‖fderiv ℝ (f n) x (EuclideanSpace.single j 1)‖ ^ 2) =
        ∑ j : Fin d, ∫ x in S, ‖fderiv ℝ (f n) x (EuclideanSpace.single j 1)‖ ^ 2 :=
    _root_.MeasureTheory.integral_finsetSum Finset.univ (fun j _ => hfi n j)
  simpa only [hvsum, hfsum] using hbase

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_sum_norm_sq_weak_gradient_le_liminf_on_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_sum_norm_sq_weak_gradient_le_liminf_on_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_sum_norm_sq_weak_gradient_le_liminf_on_subset ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_sum_norm_sq_weak_gradient_le_liminf_on_subset

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end
