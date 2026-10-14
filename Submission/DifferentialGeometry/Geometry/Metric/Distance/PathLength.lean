import Submission.DifferentialGeometry.Geometry.Comparison.DistanceHessianLocal

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Manifold _root_.Submission.Manifold _root_.Set
open scoped _root_.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Geometry
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem lipschitzOnWith_of_subinterval_lengths
    (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ x y : M, _root_.EDist.edist x y = riemannianEDistOf g x y)
    {gamma : ℝ → M} (hsmooth : ContMDiffOn 𝓘(ℝ, ℝ) I 1 gamma (_root_.Set.Icc (0 : ℝ) 1))
    {rho : ℝ} (hrho : 0 ≤ rho) {L : ℝ≥0} (hL : rho ≤ L)
    (hsub : ∀ a ∈ _root_.Set.Icc (0 : ℝ) 1, ∀ b ∈ _root_.Set.Icc (0 : ℝ) 1,
      metricPathELength g gamma a b = ENNReal.ofReal (b - a) * ENNReal.ofReal rho) :
    LipschitzOnWith L gamma (_root_.Set.Icc (0 : ℝ) 1) := by
  have hordered (a : ℝ) (ha : a ∈ _root_.Set.Icc (0 : ℝ) 1)
      (b : ℝ) (hb : b ∈ _root_.Set.Icc (0 : ℝ) 1) (hab : a ≤ b) :
      dist (gamma a) (gamma b) ≤ (L : ℝ) * _root_.Dist.dist a b := by
    have hC1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1 gamma (_root_.Set.Icc a b) :=
      hsmooth.mono (_root_.Set.Icc_subset_Icc ha.1 hb.2)
    have hbound := edistOf_le_metricPathELength g hab hC1
    rw [← hmetric, edist_dist, hsub a ha b hb,
      ← ENNReal.ofReal_mul (sub_nonneg.mpr hab)] at hbound
    have hreal : _root_.Dist.dist (gamma a) (gamma b) ≤ (b - a) * rho :=
      (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (sub_nonneg.mpr hab) hrho)).mp hbound
    calc
      _ ≤ (b - a) * rho := hreal
      _ ≤ (b - a) * (L : ℝ) := mul_le_mul_of_nonneg_left hL (sub_nonneg.mpr hab)
      _ = _ := by rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hab)]; ring
  apply lipschitzOnWith_iff_dist_le_mul.mpr
  intro a ha b hb
  rcases le_total a b with hab | hba
  · exact hordered a ha b hb hab
  · simpa only [dist_comm] using hordered b hb a ha hba

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.lipschitzOnWith_of_subinterval_lengths then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.lipschitzOnWith_of_subinterval_lengths"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.lipschitzOnWith_of_subinterval_lengths ``Submission.DifferentialGeometry.Geometry.lipschitzOnWith_of_subinterval_lengths

end DifferentialGeometry.Geometry
