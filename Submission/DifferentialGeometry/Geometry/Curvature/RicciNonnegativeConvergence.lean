import Submission.DifferentialGeometry.Geometry.Curvature.Algebraic.CurvatureOperatorCone
import Submission.DifferentialGeometry.Geometry.Curvature.Algebraic.TensorMetric
import Submission.DifferentialGeometry.Geometry.Curvature.Bounds.RicciOperatorNorm
import Submission.DifferentialGeometry.Geometry.Curvature.Bochner.OrthonormalFrameTrace
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Pullback
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.Curvature.RicciFromJets
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.Metric.UniformEquivalence
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Filter _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Connection _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators _root_.Topology _root_.ENNReal

namespace DifferentialGeometry.Geometry.Curvature

section Trace
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem ricciTensor_nonnegative_of_curvatureOperator_nonnegative
    (g : SmoothRiemannianMetric I M) (q : M)
    (hRm : metricAlgebraicCurvatureTensorAt g q ∈
      algebraicCurvatureOperatorNonnegativeCone)
    (v : TangentSpace I q) : 0 ≤ ricciTensor g q v v := by
  classical
  have hsec (u w : TangentSpace I q) : 0 ≤ metricRm04StandardAt g q u w w u := by
    have h := (mem_algebraicCurvatureOperatorNonnegativeCone.mp hRm)
      1 (fun _ => 1) (fun _ => u) (fun _ => w)
    simpa only [algebraicCurvatureOperatorQuadraticEval, Fin.sum_univ_one,
      one_mul, metricAlgebraicCurvatureTensorAt_coe, metricRm04StandardAt] using h
  obtain ⟨B, hB⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis g q
  rw [ricciTensor_eq_orthonormal_trace g q v v B hB]
  apply Finset.sum_nonneg
  intro i _
  rw [g.symm q _ _, ← metricRm04StandardAt_eq_inner_riemannOp]
  exact hsec (B i) v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.ricciTensor_nonnegative_of_curvatureOperator_nonnegative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.ricciTensor_nonnegative_of_curvatureOperator_nonnegative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.ricciTensor_nonnegative_of_curvatureOperator_nonnegative ``Submission.DifferentialGeometry.Geometry.Curvature.ricciTensor_nonnegative_of_curvatureOperator_nonnegative

end Trace

section Closure
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

theorem ricciTensor_nonnegative_of_local_metric_jet_convergence
    (gSeq : ℕ → SmoothRiemannianMetric I M)
    (g R : SmoothRiemannianMetric I M) (q : M) (v : TangentSpace I q)
    (hconv : ∀ ε : ℝ, 0 < ε → ∃ k₀ : ℕ, ∀ k ≥ k₀,
      ∀ a : ℕ, a ≤ 2 → metricDerivNorm a (gSeq k) g R q < ε)
    (hnonneg : ∀ᶠ k in _root_.Filter.atTop, 0 ≤ ricciTensor (gSeq k) q v v) :
    0 ≤ ricciTensor g q v v := by
  classical
  by_contra hn
  have hneg : ricciTensor g q v v < 0 := lt_of_not_ge hn
  obtain ⟨c, hc, hlow⟩ := metric_lower_on (I := I) (K := ({q} : Set M))
    isCompact_singleton g R
  let B : ℝ := (∑ a ∈ Finset.range 3, metricCovDerivNorm a g R q) + 1
  have hnorm (a : ℕ) : 0 ≤ metricCovDerivNorm a g R q := Real.sqrt_nonneg _
  have hB : 0 ≤ B := by
    dsimp only [B]
    exact add_nonneg (Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _)) zero_le_one
  have hself (a : ℕ) (ha : a ≤ 2) : metricCovDerivNorm a g R q ≤ B - 1 := by
    dsimp only [B]
    simp only [add_sub_cancel_right]
    exact Finset.single_le_sum (fun i _ => hnorm i)
      (Finset.mem_range.mpr (show a < 3 by omega))
  obtain ⟨C, hC, hRic⟩ := ricciSub_le_dNorm R q (c / 2) B (by positivity) hB v v
  let ε : ℝ := _root_.Min.min (c / 2) (_root_.Min.min 1 (-ricciTensor g q v v / (6 * C)))
  have hε : 0 < ε := by
    dsimp only [ε]
    exact lt_min (by positivity) (lt_min one_pos
      (div_pos (neg_pos.mpr hneg) (mul_pos (by norm_num) hC)))
  have hεc : ε ≤ c / 2 := min_le_left _ _
  have hεone : ε ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hεRic : ε * (6 * C) ≤ -ricciTensor g q v v := by
    apply (le_div_iff₀ (by positivity : 0 < 6 * C)).mp
    exact (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨kc, hkc⟩ := hconv ε hε
  obtain ⟨kn, hkn⟩ := eventually_atTop.1 hnonneg
  let k := _root_.Max.max kc kn
  have hsmall (a : ℕ) (ha : a ≤ 2) : metricDerivNorm a (gSeq k) g R q ≤ ε :=
    (hkc k (le_max_left _ _) a ha).le
  have hRnn (w : TangentSpace I q) : 0 ≤ R.inner q w w := by
    by_cases hw : w = 0
    · simp [hw]
    · exact (R.pos q w hw).le
  have hlowG (w : TangentSpace I q) : (c / 2) * R.inner q w w ≤ g.inner q w w := by
    have hh := hlow q (_root_.Set.mem_singleton q) w
    nlinarith [hRnn w]
  have hlowSeq (w : TangentSpace I q) :
      (c / 2) * R.inner q w w ≤ (gSeq k).inner q w w := by
    have hd := metricDifference_abs_le (gSeq k) g R q w w
    rw [mul_assoc, Real.mul_self_sqrt (hRnn w)] at hd
    have herr := mul_le_mul_of_nonneg_right
      ((hsmall 0 (by omega)).trans hεc) (hRnn w)
    have hlo := (abs_le.mp hd).1
    have hh := hlow q (_root_.Set.mem_singleton q) w
    linarith
  have hbSeq (a : ℕ) (ha : a ≤ 2) : metricCovDerivNorm a (gSeq k) R q ≤ B := by
    have hh := covNorm_le_add a (gSeq k) g R q
    have hs := hself a ha
    have he := (hsmall a ha).trans hεone
    linarith
  have hbG (a : ℕ) (ha : a ≤ 2) : metricCovDerivNorm a g R q ≤ B := by
    linarith [hself a ha]
  have hsum : (∑ a ∈ Finset.range 3, metricDerivNorm a (gSeq k) g R q) ≤ 3 * ε := by
    calc
      _ ≤ ∑ _a ∈ Finset.range 3, ε := Finset.sum_le_sum (fun a ha =>
        hsmall a (by have := Finset.mem_range.mp ha; omega))
      _ = _ := by simp
  have hdiff := hRic (gSeq k) g hlowSeq hlowG hbSeq hbG
  have hu := (abs_le.mp hdiff).2
  have hsumC := mul_le_mul_of_nonneg_left hsum hC.le
  have hpos := hkn k (le_max_right _ _)
  nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.ricciTensor_nonnegative_of_local_metric_jet_convergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.ricciTensor_nonnegative_of_local_metric_jet_convergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.ricciTensor_nonnegative_of_local_metric_jet_convergence ``Submission.DifferentialGeometry.Geometry.Curvature.ricciTensor_nonnegative_of_local_metric_jet_convergence

end Closure
end DifferentialGeometry.Geometry.Curvature

end
