import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.ReferenceCurvatureBounds
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardMetricControl
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardLifetime

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Manifold _root_.Submission.Manifold _root_.TopologicalSpace _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Tensor0SBundle _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Metric
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.ENNReal _root_.BigOperators
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.E3 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instSigmaCompactSpaceSubtypeE3MemOpens (U : _root_.TopologicalSpace.Opens E3) : SigmaCompactSpace U :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓡 3) U.isOpen)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instSigmaCompactSpaceSubtypeE3MemOpens
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instSigmaCompactSpaceSubtypeE3MemOpens target :: scope.openDecls } }

theorem exists_uniform_curvature_bound_of_standard_metric_close_on_opens
    (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1) :
    ∃ ε A : ℝ, 0 < ε ∧ 0 < A ∧
      ∀ (U : _root_.TopologicalSpace.Opens E3) (g : SmoothRiemannianMetric (𝓡 3) U)
        (S : StandardSolution) (τ : ℝ), τ ∈ _root_.Set.Icc 0 θ → ∀ x : U,
        (∀ j ≤ 2, metricDerivNorm j g ((S.val.metric τ).restrictOpen U)
          (metric.restrictOpen U) x ≤ ε) →
        Real.sqrt (normSq0S g x 4 (metricRm04 g x)) ≤ A := by
  have hlt : ENNReal.ofReal θ < uniformStandardLifetime := by
    rw [uniformStandardLifetime_eq_one]
    simpa using (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1)).mpr hθ1
  obtain ⟨hlife, K, hK, hRm⟩ := uniformStandardLifetime_slab θ hθ hlt
  obtain ⟨Λ, hΛ, C, L, hC, hL, hstd⟩ :=
    standard_metric_bounds_on_shorter_windows θ K hθ hK
  let ε : ℝ := Λ⁻¹ / 2
  have hΛpos : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  have hε : 0 < ε := half_pos (inv_pos.mpr hΛpos)
  let B : ℝ := ε + (∑ j ∈ Finset.range 3, L j) * θ
  have hsum : 0 ≤ ∑ j ∈ Finset.range 3, L j :=
    Finset.sum_nonneg fun j _ => hL j
  have hB : 0 ≤ B := add_nonneg hε.le (mul_nonneg hsum hθ)
  obtain ⟨P, hP, hcurv⟩ :=
    exists_pos_bound_intrinsic_curvature_derivative_of_metric_jets_on_opens 0 ε B hε hB
  refine ⟨ε, P, hε, hP, ?_⟩
  intro U g S τ hτ x hclose
  obtain ⟨heq, _, htime⟩ := hstd S.val θ hθ le_rfl (hlife S) (hRm S)
  let G := metric.restrictOpen U
  let H := (S.val.metric τ).restrictOpen U
  have hlow (v : TangentSpace (𝓡 3) x) : ε * G.inner x v v ≤ g.inner x v v := by
    have href := (heq τ hτ).2 x.val (_root_.Set.mem_univ _) v |>.1
    change Λ⁻¹ * G.inner x v v ≤ H.inner x v v at href
    have hd := metricDifference_abs_le g H G x v v
    rw [mul_assoc, Real.mul_self_sqrt (metric_inner_self_nonneg G x v)] at hd
    have hd' := hd.trans (mul_le_mul_of_nonneg_right (hclose 0 (by omega))
      (metric_inner_self_nonneg G x v))
    have hb := (abs_le.mp hd').1
    dsimp only [ε] at *
    linarith
  have hj (j : ℕ) (hj : j ≤ 0 + 2) : metricDerivNorm j g G G x ≤ B := by
    have htime' := htime j τ hτ 0 ⟨le_rfl, hθ⟩ x.val
    rw [S.val.initial, sub_zero, abs_of_nonneg hτ.1] at htime'
    have hrest : metricDerivNorm j H G G x ≤ L j * τ := by
      dsimp only [H, G]
      rw [metricDerivNorm_restrictOpen]
      exact htime'
    have hbudget : L j ≤ ∑ k ∈ Finset.range 3, L k :=
      Finset.single_le_sum (fun k _ => hL k) (Finset.mem_range.mpr (by omega))
    have htail := mul_le_mul hbudget hτ.2 hτ.1 hsum
    exact (metricDerivNorm_triangle j g H G G x).trans
      (add_le_add (hclose j hj) (hrest.trans htail))
  exact hcurv U g x hlow hj

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_uniform_curvature_bound_of_standard_metric_close_on_opens then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_uniform_curvature_bound_of_standard_metric_close_on_opens"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_uniform_curvature_bound_of_standard_metric_close_on_opens ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_uniform_curvature_bound_of_standard_metric_close_on_opens

theorem exists_uniform_curvature_derivative_bound_of_standard_metric_close_on_opens
    (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1) (j : ℕ) :
    ∃ ε A : ℝ, 0 < ε ∧ 0 < A ∧
      ∀ (U : _root_.TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 3))) (g : SmoothRiemannianMetric (𝓡 3) U)
        (S : StandardSolution) (τ : ℝ), τ ∈ _root_.Set.Icc 0 θ → ∀ x : U,
        (∀ i ≤ j + 2, metricDerivNorm i g ((S.val.metric τ).restrictOpen U)
          (metric.restrictOpen U) x ≤ ε) →
        curvDerivNormSq j g x ≤ A := by
  have hlt : ENNReal.ofReal θ < uniformStandardLifetime := by
    rw [uniformStandardLifetime_eq_one]
    simpa using (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1)).mpr hθ1
  obtain ⟨hlife, K, hK, hRm⟩ := uniformStandardLifetime_slab θ hθ hlt
  obtain ⟨Λ, hΛ, C, L, hC, hL, hstd⟩ :=
    standard_metric_bounds_on_shorter_windows θ K hθ hK
  let ε : ℝ := Λ⁻¹ / 2
  have hΛpos : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  have hε : 0 < ε := half_pos (inv_pos.mpr hΛpos)
  let B : ℝ := ε + (∑ i ∈ Finset.range (j + 3), L i) * θ
  have hsum : 0 ≤ ∑ i ∈ Finset.range (j + 3), L i :=
    Finset.sum_nonneg fun i _ => hL i
  have hB : 0 ≤ B := add_nonneg hε.le (mul_nonneg hsum hθ)
  obtain ⟨P, hP, hcurv⟩ :=
    exists_pos_bound_intrinsic_curvature_derivative_of_metric_jets_on_opens j ε B hε hB
  refine ⟨ε, P ^ 2, hε, by positivity, ?_⟩
  intro U g S τ hτ x hclose
  obtain ⟨heq, _, htime⟩ := hstd S.val θ hθ le_rfl (hlife S) (hRm S)
  let G := metric.restrictOpen U
  let H := (S.val.metric τ).restrictOpen U
  have hlow (v : TangentSpace (𝓡 3) x) : ε * G.inner x v v ≤ g.inner x v v := by
    have href := (heq τ hτ).2 x.val (_root_.Set.mem_univ _) v |>.1
    change Λ⁻¹ * G.inner x v v ≤ H.inner x v v at href
    have hd := metricDifference_abs_le g H G x v v
    rw [mul_assoc, Real.mul_self_sqrt (metric_inner_self_nonneg G x v)] at hd
    have hd' := hd.trans (mul_le_mul_of_nonneg_right (hclose 0 (by omega))
      (metric_inner_self_nonneg G x v))
    have hb := (abs_le.mp hd').1
    dsimp only [ε] at *
    linarith
  have hj (i : ℕ) (hi : i ≤ j + 2) : metricDerivNorm i g G G x ≤ B := by
    have htime' := htime i τ hτ 0 ⟨le_rfl, hθ⟩ x.val
    rw [S.val.initial, sub_zero, abs_of_nonneg hτ.1] at htime'
    have hrest : metricDerivNorm i H G G x ≤ L i * τ := by
      dsimp only [H, G]
      rw [metricDerivNorm_restrictOpen]
      exact htime'
    have hbudget : L i ≤ ∑ k ∈ Finset.range (j + 3), L k :=
      Finset.single_le_sum (fun k _ => hL k) (Finset.mem_range.mpr (by omega))
    have htail := mul_le_mul hbudget hτ.2 hτ.1 hsum
    exact (metricDerivNorm_triangle i g H G G x).trans
      (add_le_add (hclose i hi) (hrest.trans htail))
  have hjet := hcurv U g x hlow hj
  unfold curvDerivNormSq
  rw [curvCovDeriv_normSq_eq]
  exact (Real.sqrt_le_iff.mp hjet).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_uniform_curvature_derivative_bound_of_standard_metric_close_on_opens then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_uniform_curvature_derivative_bound_of_standard_metric_close_on_opens"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_uniform_curvature_derivative_bound_of_standard_metric_close_on_opens ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_uniform_curvature_derivative_bound_of_standard_metric_close_on_opens

end DifferentialGeometry.PDE.RicciFlow.StandardCap
