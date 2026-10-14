import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Source.BackwardCurvature
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.Derivatives.LocalCompact
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ShrinkingCylinder
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NormalizedConvergence
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Limit.Metric.ScalarConvergence
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Norm.ReferenceChange

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Filter _root_.Bundle _root_.Submission.Bundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology _root_.NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealThreeSpaceHAddOfNat : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealThreeSpaceHAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealThreeSpaceHAddOfNat target :: scope.openDecls } }

theorem exists_curvature_derivative_bounds_before_time_of_cylinder_convergence
    {δ b : ℝ} (hδ : 0 < δ) (hb : b ≤ 0) {D : RealTimeInterval}
    (S : ℕ → SolutionOn (I := NeckCylinderModel) (M := neckBuffer δ) D)
    (hS : ∀ n, IsSolutionOn (S n)) (C : ℝ≥0)
    (hslab : _root_.Set.Icc (b - (12 * ((C : ℝ) + 1))⁻¹) b ⊆ D.carrier)
    (hreg : _root_.Set.Ioo (b - (12 * ((C : ℝ) + 1))⁻¹) b ⊆ D.regular)
    (hconv : ∀ K : Set (neckBuffer δ), IsCompact K → MetricCPConvergenceOn K 2
      (fun n => (S n).base.metric b)
      ((PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) b).restrictOpen (neckBuffer δ))
      (roundCylinderMetric.restrictOpen (neckBuffer δ)))
    (q Q : ℕ → ℝ) (hq : ∀ᶠ n in _root_.Filter.atTop, q n ≤ 1) (hQ : _root_.Filter.Tendsto Q _root_.Filter.atTop _root_.Filter.atTop)
    (hderiv : ∀ K : Set (neckBuffer δ), IsCompact K → ∀ᶠ n in _root_.Filter.atTop,
      ∀ x ∈ K, ∀ t ∈ _root_.Set.Ioo (b - (12 * ((C : ℝ) + 1))⁻¹) b,
        q n < (S n).scalar t x →
        |derivWithin (fun s => (S n).scalar s x) (_root_.Set.Iic t) t| ≤ C * (S n).scalar t x ^ 2)
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (hpinch : ∀ᶠ n in _root_.Filter.atTop, PhiAlmostNonnegative (S n)
      (_root_.Set.Icc (b - (12 * ((C : ℝ) + 1))⁻¹) b) (rescalePinchingFunction (Q n) Phi)) :
    (∀ K : Set (neckBuffer δ), IsCompact K → ∀ᶠ n in _root_.Filter.atTop,
      ∀ t ∈ _root_.Set.Icc (b - (12 * ((C : ℝ) + 1))⁻¹) b, ∀ x ∈ K,
        curvDerivNormSq 0 ((S n).base.metric t) x ≤ (12 * Real.sqrt 3) ^ 2) ∧
    ∀ K : Set (neckBuffer δ), IsCompact K → ∃ B : ℕ → ℝ, (∀ m, 0 ≤ B m) ∧
      ∀ᶠ n in _root_.Filter.atTop, ∀ m : ℕ, ∀ t ∈ _root_.Set.Icc (b - (12 * ((C : ℝ) + 1))⁻¹ / 2) b,
        ∀ x ∈ K, curvDerivNorm m ((S n).base.metric t) x ≤ B m := by
  let _ : SigmaCompactSpace (neckBuffer δ) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen NeckCylinderModel (neckBuffer δ).isOpen)
  let R := (PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) b).restrictOpen (neckBuffer δ)
  let p : neckBuffer δ := ⟨(Geometry.Neck.spherePoint, 0), by
    have := inv_pos.mpr hδ
    constructor <;> linarith⟩
  let F : ℕ → PointedFlowData NeckCylinderModel D := fun n => {
    M := neckBuffer δ
    topology := inferInstance
    charted := inferInstance
    smooth := inferInstance
    sigmaCompact := inferInstance
    t2 := inferInstance
    t2TangentBundle := inferInstance
    basepoint := p
    S := S n
    isSolution := hS n }
  have hzero : ∀ K : Set (neckBuffer δ), IsCompact K → ∀ᶠ n in _root_.Filter.atTop,
      ∀ t ∈ _root_.Set.Icc (b - (12 * ((C : ℝ) + 1))⁻¹) b, ∀ x ∈ K,
        curvDerivNormSq 0 ((S n).base.metric t) x ≤ (12 * Real.sqrt 3) ^ 2 := by
    intro K hK
    have hscalarConv : TendstoUniformlyOn (fun n x => (F n).S.scalar b x)
        (fun _ => (1 - b)⁻¹) _root_.Filter.atTop K := by
      have hc := (hconv K hK).tendstoUniformlyOn_metricScalarAt hK
      have hmodel : (fun x : neckBuffer δ => metricScalarAt R x) = fun _ => (1-b)⁻¹ := by
        funext x
        rw [metricScalarAt_restrictOpen, PDE.RicciFlow.shrinkingCylinderMetric_scalar (hb.trans_lt zero_lt_one)]
      rw [hmodel] at hc
      exact hc
    have hbound := (eventually_riemannNorm_le_on_backward_interval_of_rescaling_tendsto_atTop
      F (fun _ => id) (C := C) (inv_le_one_of_one_le₀ (by linarith : 1 ≤ 1 - b))
      (by simp [Module.finrank_prod]) hslab hscalarConv hq (hderiv K hK) hPhi hQ hpinch).2
    filter_upwards [hbound] with n hn t ht x hx
    have hb := hn x hx t ht
    have hnonneg : 0 ≤ curvDerivNormSq 0 ((S n).base.metric t) x :=
      normSq0S_nonneg _ _ _ _
    have hs := Real.sq_sqrt hnonneg
    change Real.sqrt (curvDerivNormSq 0 ((S n).base.metric t) x) ≤ 12 * Real.sqrt 3 at hb
    nlinarith [Real.sqrt_nonneg (curvDerivNormSq 0 ((S n).base.metric t) x)]
  refine ⟨hzero, ?_⟩
  intro K hK
  have ha : b - (12 * ((C : ℝ) + 1))⁻¹ < b :=
    sub_lt_self _ (by positivity)
  have hterminal : ∀ A : Set (neckBuffer δ), IsCompact A → MetricCPConvergenceOn A 0
      (fun n => (S n).base.metric b) R R := by
    intro A hA ε hε
    obtain ⟨L, hL, hnorm⟩ := exists_metric_deriv_norm_reference_bound hA
      (roundCylinderMetric.restrictOpen (neckBuffer δ)) R 0
    let η := ε / (2 * (L + 1))
    have hη : 0 < η := by dsimp [η]; positivity
    obtain ⟨j, hj⟩ := hconv A hA η hη
    refine ⟨j, fun n hn => ?_⟩
    apply lt_of_le_of_lt (metricDerivNormSupOn_le_of_forall A 0 _ _ _
      (ε / 2) (by positivity) ?_) (by linarith)
    intro m hm x hx
    have hm0 : m = 0 := Nat.eq_zero_of_le_zero hm
    subst m
    have hsource : metricDerivNorm 0 ((S n).base.metric b) R
        (roundCylinderMetric.restrictOpen (neckBuffer δ)) x ≤ η :=
      (derivNorm_le_sup hA (by omega : 0 ≤ 2) _ _ _ hx).trans (hj n hn).le
    have htarget := hnorm ((S n).base.metric b) R 0 le_rfl x hx
    simp only [Nat.zero_add, Finset.sum_range_one] at htarget
    have hscaled : L * η ≤ ε / 2 := by
      have hcancel : (L + 1) * η = ε / 2 := by
        dsimp only [η]
        field_simp
      rw [← hcancel]
      exact mul_le_mul_of_nonneg_right (by linarith) hη.le
    exact htarget.trans ((mul_le_mul_of_nonneg_left hsource hL).trans hscaled)
  have hc := exists_eventually_curvDerivNorm_on_compact_of_terminal_convergence S hS R ha
    hslab hreg hterminal
    (fun A hA => ⟨(12 * Real.sqrt 3) ^ 2, hzero A hA⟩) K hK
  have heq : (b - (12 * ((C : ℝ) + 1))⁻¹ + b) / 2 =
      b - (12 * ((C : ℝ) + 1))⁻¹ / 2 := by ring
  rwa [heq] at hc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_curvature_derivative_bounds_before_time_of_cylinder_convergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_curvature_derivative_bounds_before_time_of_cylinder_convergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_curvature_derivative_bounds_before_time_of_cylinder_convergence ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_curvature_derivative_bounds_before_time_of_cylinder_convergence

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
