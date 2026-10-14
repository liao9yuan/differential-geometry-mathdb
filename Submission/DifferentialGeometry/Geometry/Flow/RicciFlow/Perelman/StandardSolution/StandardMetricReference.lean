import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardMetricControl
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardLifetime
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Norm.ReferenceChange
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Locality
import Submission.DifferentialGeometry.Geometry.Metric.Construction.OpenExtension

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.TopologicalSpace _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Tensor0SBundle _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Metric
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.ENNReal _root_.BigOperators _root_.Topology _root_.Submission.Topology _root_.Submission.DifferentialGeometry.Topology
namespace DifferentialGeometry.PDE.RicciFlow
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.E3 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instSigmaCompactSpaceSubtypeE3MemOpens (U : _root_.TopologicalSpace.Opens E3) : SigmaCompactSpace U :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓡 3) U.isOpen)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instSigmaCompactSpaceSubtypeE3MemOpens
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instSigmaCompactSpaceSubtypeE3MemOpens target :: scope.openDecls } }

theorem exists_uniform_standard_metric_deriv_norm_reference_bound
    (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1) (p : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (U : _root_.TopologicalSpace.Opens E3)
      (S : StandardSolution) (t : ℝ), t ∈ _root_.Set.Icc 0 θ →
      ∀ (A B : SmoothRiemannianMetric (𝓡 3) U) (r : ℕ), r ≤ p → ∀ x : U,
        metricDerivNorm r A B ((S.val.metric t).restrictOpen U) x ≤
          D * ∑ k ∈ Finset.range (p + 1),
            metricDerivNorm k A B (StandardCap.metric.restrictOpen U) x := by
  have hlt : ENNReal.ofReal θ < uniformStandardLifetime := by
    rw [uniformStandardLifetime_eq_one]
    simpa using (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1)).mpr hθ1
  obtain ⟨hlife, K, hK, hRm⟩ := uniformStandardLifetime_slab θ hθ hlt
  obtain ⟨Λ, hΛ, C, L, hC, hL, hstd⟩ := standard_metric_bounds_on_shorter_windows θ K hθ hK
  let Csum := ∑ k ∈ Finset.range (p + 1), C k
  have hCsum : 0 ≤ Csum := Finset.sum_nonneg fun k _ => hC k
  let B₀ := Real.sqrt (Λ ^ (2 + p)) * Csum
  have hB₀ : 0 ≤ B₀ := mul_nonneg (Real.sqrt_nonneg _) hCsum
  obtain ⟨D, hD, hbound⟩ :=
    exists_uniform_metric_deriv_norm_reference_bound (I := 𝓡 3) (M := E3) p hΛ hB₀
  refine ⟨D, hD, ?_⟩
  intro U S t ht A B r hr x
  obtain ⟨heq, hjets, _⟩ := hstd S.val θ hθ le_rfl (hlife S) (hRm S)
  have hjet (y : E3) (j : ℕ) (hj : j ≤ p) :
      Real.sqrt (normSq0S (S.val.metric t) y (2 + j)
        (iterCov StandardCap.metric 2 (metricTensorField (S.val.metric t)) j y)) ≤ B₀ := by
    have hh := (heq t ht).sqrt_normSq0S_le (_root_.Set.mem_univ y)
      (iterCov StandardCap.metric 2 (metricTensorField (S.val.metric t)) j y)
    obtain ⟨b, hb⟩ := exists_orthonormal_basis StandardCap.metric y
    rw [← metricCovDerivNorm_eq_iterCov (S.val.metric t) StandardCap.metric j b
      (metricInverseInBasis_identity_of_orthonormal StandardCap.metric b hb)] at hh
    have hfac : Real.sqrt (Λ ^ (2 + j)) ≤ Real.sqrt (Λ ^ (2 + p)) :=
      Real.sqrt_le_sqrt (pow_le_pow_right₀ hΛ (by omega))
    have hCj : C j ≤ Csum := Finset.single_le_sum (fun k _ => hC k)
      (Finset.mem_range.mpr (by omega))
    exact hh.trans (mul_le_mul hfac ((hjets j t ht y).trans hCj)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  obtain ⟨A', Vₐ, hxa, hVa, hA', _⟩ :=
    exists_smooth_metric_agrees_on_neighborhood_of_is_compact StandardCap.metric U A
      (K := {x.val}) isCompact_singleton (by intro y hy; rw [Set.mem_singleton_iff.mp hy]; exact x.property)
  obtain ⟨B', Vb, hxb, hVb, hB', _⟩ :=
    exists_smooth_metric_agrees_on_neighborhood_of_is_compact StandardCap.metric U B
      (K := {x.val}) isCompact_singleton (by intro y hy; rw [Set.mem_singleton_iff.mp hy]; exact x.property)
  have hAe : ∀ᶠ y in 𝓝 x, ∀ v w : TangentSpace (𝓡 3) y,
      (A'.restrictOpen U).inner y v w = A.inner y v w := by
    filter_upwards [continuous_subtype_val.continuousAt.preimage_mem_nhds
      (Vₐ.isOpen.mem_nhds (hxa (Set.mem_singleton x.val)))] with y hy
    exact hA' y.val hy
  have hBe : ∀ᶠ y in 𝓝 x, ∀ v w : TangentSpace (𝓡 3) y,
      (B'.restrictOpen U).inner y v w = B.inner y v w := by
    filter_upwards [continuous_subtype_val.continuousAt.preimage_mem_nhds
      (Vb.isOpen.mem_nhds (hxb (Set.mem_singleton x.val)))] with y hy
    exact hB' y.val hy
  have hnorm (j : ℕ) (G : SmoothRiemannianMetric (𝓡 3) E3) :
      metricDerivNorm j A' B' G x.val = metricDerivNorm j A B (G.restrictOpen U) x := by
    rw [← metricDerivNorm_restrictOpen A' B' G U j x,
      metricDerivNorm_eq_of_metric_eventuallyEq j (A'.restrictOpen U) A
        (B'.restrictOpen U) (G.restrictOpen U) x hAe,
      metricDerivNorm_symm,
      metricDerivNorm_eq_of_metric_eventuallyEq j (B'.restrictOpen U) B
        A (G.restrictOpen U) x hBe,
      metricDerivNorm_symm]
  have hh := hbound _root_.Set.univ isOpen_univ StandardCap.metric (S.val.metric t)
    ((heq t ht).2) (fun y _ j _ hj => hjet y j hj) A' B' r hr x.val (_root_.Set.mem_univ _)
  simpa only [hnorm] using hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.exists_uniform_standard_metric_deriv_norm_reference_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.exists_uniform_standard_metric_deriv_norm_reference_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.exists_uniform_standard_metric_deriv_norm_reference_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.exists_uniform_standard_metric_deriv_norm_reference_bound

end DifferentialGeometry.PDE.RicciFlow
