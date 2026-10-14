import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ComparisonComposition
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Scaling
import Submission.DifferentialGeometry.Geometry.Metric.DerivativeScaleENorm

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N M : Type*}
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N]
  [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]

private local instance staticRescaleComplete : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.staticRescaleComplete
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.staticRescaleComplete target :: scope.openDecls } }
private local instance staticRescaleOne : IsManifold I 1 N := IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.staticRescaleOne
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.staticRescaleOne target :: scope.openDecls } }

def MetricComparisonOn.rescaleStatic
    {h : SmoothRiemannianMetric I N} {g : SmoothRiemannianMetric I3 M}
    {F : N → M} {K : Set N} {times : Set ℝ} {order : ℕ} {eps : ℝ}
    (C : MetricComparisonOn (fun _ => h) (fun _ => g) F K times order eps)
    {t : ℝ} (ht : t ∈ times) (heps : 0 ≤ eps)
    (c d : ℝ) (hc : 0 < c) (hd : 0 < d) (T : Set ℝ) :
    MetricComparisonOn (fun _ => scaleMetric c hc h) (fun _ => scaleMetric d hd g)
      F K T order
      ((_root_.Max.max 1 (Real.sqrt c)⁻¹) ^ (order + 2) *
        (d * eps + |d - c| * Real.sqrt (Module.finrank ℝ E))) := by
  let A := d • C.jet 0 t + (d - c) • metricTensorField h
  let error := (_root_.Max.max 1 (Real.sqrt c)⁻¹) ^ (order + 2) *
    (d * eps + |d - c| * Real.sqrt (Module.finrank ℝ E))
  have herror : 0 ≤ error := by dsimp only [error]; positivity
  have hzero (y : N) (v : Fin 2 → TangentSpace I y) :
      A y v = (d • C.pullback t) y v - (scaleMetric c hc h).inner y (v 0) (v 1) := by
    simp only [A, ContMDiffSection.coe_add, ContMDiffSection.coe_smul, Pi.add_apply,
      Pi.smul_apply, Tensor0SSpace.add_apply, Tensor0SSpace.smul_apply, smul_eq_mul,
      metricTensorField_apply, scaleMetric_inner, C.jet_zero]
    ring
  have hclose (a : ℕ) (ha : a ≤ order) (y : N) (hy : y ∈ K) :
      tensor02CovDerivNormWith a A (scaleMetric c hc h) (scaleMetric c hc h) y ≤ error := by
    have hmetric : tensor02CovDerivNormWith a (metricTensorField h) h h y ≤
        Real.sqrt (Module.finrank ℝ E) := by
      have heq : tensor02CovDerivNormWith a (metricTensorField h) h h y =
          metricCovDerivNorm a h h y := by
        unfold tensor02CovDerivNormWith metricCovDerivNorm
        rw [tensor02_cov_deriv_eq_cov_deriv_of_field, ← metricCovDeriv_eq_covDerivOfField]
      rw [heq]
      cases a with
      | zero => exact (DifferentialGeometry.Geometry.Metric.metricCovDerivNorm_self_zero h y).le
      | succ a => rw [covNorm_self_succ]; exact Real.sqrt_nonneg _
    have hsum : tensor02CovDerivNormWith a A h h y ≤
        d * eps + |d - c| * Real.sqrt (Module.finrank ℝ E) := by
      apply (tensor02CovDerivNormWith_add_le a (d • C.jet 0 t)
        ((d - c) • metricTensorField h) h h y).trans
      rw [tensor02CovDerivNormWith_smul, tensor02CovDerivNormWith_smul, abs_of_pos hd]
      exact add_le_add (mul_le_mul_of_nonneg_left (C.close a 0 (by omega) t ht y hy) hd.le)
        (mul_le_mul_of_nonneg_left hmetric (abs_nonneg _))
    have hweight : (Real.sqrt c)⁻¹ ^ (a + 2) ≤ (_root_.Max.max 1 (Real.sqrt c)⁻¹) ^ (order + 2) :=
      (pow_le_pow_left₀ (inv_nonneg.mpr (Real.sqrt_nonneg c)) (le_max_right _ _) _).trans
        (pow_le_pow_right₀ (le_max_left _ _) (by omega))
    rw [tensor02CovDerivNormWith_scaleMetric]
    exact (mul_le_mul_of_nonneg_left hsum (by positivity)).trans
      (mul_le_mul_of_nonneg_right hweight (by positivity))
  refine {
    pullback := fun _ => d • C.pullback t
    pullback_eq := ?_
    jet := fun b _ => if b = 0 then A else 0
    jet_zero := ?_
    jet_succ := ?_
    equivalence := ?_
    close := ?_ }
  · intro s y hy v
    simp only [ContMDiffSection.coe_smul, Pi.smul_apply, Tensor0SSpace.smul_apply,
      smul_eq_mul, C.pullback_eq t y hy v, scaleMetric_inner]
  · intro s y v
    exact hzero y v
  · intro b s hs y hy v
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
    simp
  · intro s hs y hy v
    exact quadratic_comparison_of_error_norm (scaleMetric c hc h) (d • C.pullback t)
      A y (hzero y) (hclose 0 (Nat.zero_le order) y hy) v
  · intro a b hab s hs y hy
    split_ifs with hb
    · subst b
      exact hclose a (by omega) y hy
    · have hz : tensor02CovDerivNormWith (I := I) a 0 (scaleMetric c hc h) (scaleMetric c hc h) y = 0 := by
        rw [tensor02CovDerivNormWith, tensor02_cov_deriv_eq_cov_deriv_of_field,
          covDerivOfField_zero_tensor]
        simp only [ContMDiffSection.coe_zero, Pi.zero_apply, normSq0S, inner0S,
          MetricFiberData.inner, map_zero, Real.sqrt_zero]
      exact hz.le.trans herror

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.MetricComparisonOn.rescaleStatic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.MetricComparisonOn.rescaleStatic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.MetricComparisonOn.rescaleStatic ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.MetricComparisonOn.rescaleStatic

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
