import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.InitialWindowBounds
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.WindowScalarBounds
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.ScalarDerivativeBounds
import Submission.DifferentialGeometry.Geometry.Curvature.ScalarGradientTransport
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Scaling.ScalarDerivativeTransport

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Filter _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology _root_.Submission.DifferentialGeometry.Topology

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

universe u

theorem exists_eventually_relative_scalar_derivative_bounds_of_metric_cp_convergence
    {D r : ℝ} (hrD : r < D + 1) {N : ℕ} (hN : 2 ≤ N)
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (J : ℕ → RealTimeInterval) (age : ℕ → ℝ), (∀ i, 0 < age i) →
      ∀ S : ∀ i, SolutionOn (I := ThreeModel) (M := standardCapWindow D) (J i),
      (∀ i, IsSolutionOn (S i)) →
      (∀ i, _root_.Set.Icc (0 : ℝ) (age i) ⊆ (J i).carrier) →
      (∀ i, _root_.Set.Ioo (0 : ℝ) (age i) ⊆ (J i).regular) →
      (∀ i j, j ≤ 2 → ∀ t ∈ _root_.Set.Icc (0 : ℝ) (age i),
        ∀ y : standardCapWindow D, ‖y.val‖ ≤ r → curvDerivNormSq j ((S i).base.metric t) y ≤ B) →
      MetricCPConvergenceOn {y : standardCapWindow D | ‖y.val‖ ≤ r} N
        (fun i => (S i).base.metric (age i))
        (metric.restrictOpen (standardCapWindow D))
        (metric.restrictOpen (standardCapWindow D)) →
      ∀ (X : ℕ → Type u) [∀ i, TopologicalSpace (X i)] [∀ i, ChartedSpace ThreeSpace (X i)]
        [∀ i, IsManifold ThreeModel ∞ (X i)] [∀ i, T2Space (X i)],
      ∀ (gflow : ∀ i, ℝ → SmoothRiemannianMetric ThreeModel (X i))
        (Phi : ∀ i, standardCapWindow D → X i)
        (hPhi : ∀ i, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (Phi i))
        (q birth : ℕ → ℝ) (hq : ∀ i, 0 < q i),
      (∀ i t, t ∈ _root_.Set.Icc (0 : ℝ) (age i) → (S i).base.metric t =
        localPullMetric (scaleMetric (q i) (hq i) (gflow i (birth i + t / q i)))
          (Phi i) (hPhi i)) →
      ∀ᶠ i in _root_.Filter.atTop, ∀ y : standardCapWindow D, ‖y.val‖ ≤ r →
        (∀ w : TangentSpace ThreeModel (Phi i y),
          |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ)
            (metricScalarAt (gflow i (birth i + age i / q i))) (Phi i y) w)| ≤
            C * metricScalarAt (gflow i (birth i + age i / q i)) (Phi i y) *
              Real.sqrt (metricScalarAt (gflow i (birth i + age i / q i)) (Phi i y)) *
              Real.sqrt ((gflow i (birth i + age i / q i)).inner (Phi i y) w w)) ∧
        |derivWithin (fun t => metricScalarAt (gflow i t) (Phi i y))
          (_root_.Set.Iic (birth i + age i / q i)) (birth i + age i / q i)| ≤
            C * metricScalarAt (gflow i (birth i + age i / q i)) (Phi i y) ^ 2 := by
  obtain ⟨C, hC, hbounds⟩ := exists_relative_scalar_derivative_bounds_of_curvature_jets
    (I := ThreeModel) (M := standardCapWindow D) B hB
  refine ⟨C, hC, ?_⟩
  intro J age hage S hS hcarrier hregular hjets hconv X _ _ _ _ gflow Phi hPhi q birth hq hmetric
  have hlower := eventually_half_lt_metricScalarAt_of_metric_cp_convergence hrD hN
    (fun i => (S i).base.metric (age i)) hconv
  filter_upwards [hlower] with i hi
  intro y hy
  have ht : age i ∈ _root_.Set.Icc (0 : ℝ) (age i) := ⟨(hage i).le, le_rfl⟩
  have ht' : age i ∈ _root_.Set.Ioc (0 : ℝ) (age i) := ⟨hage i, le_rfl⟩
  have hR : 1 / 2 ≤ (S i).scalar (age i) y := (hi y hy).le
  have hb := hbounds (J i) (S i) (hS i) 0 (age i) (hcarrier i) (hregular i)
    {z : standardCapWindow D | ‖z.val‖ ≤ r} (hjets i)
  constructor
  · apply scalar_gradient_bound_of_localPull_scaleMetric
      (gflow i (birth i + age i / q i)) (Phi i) (hPhi i) (hq i) y
    have hgradient := hb.1 (age i) ht y hy hR
    change ∀ v : TangentSpace ThreeModel y,
      |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) (metricScalarAt ((S i).base.metric (age i))) y v)| ≤
        C * metricScalarAt ((S i).base.metric (age i)) y *
          Real.sqrt (metricScalarAt ((S i).base.metric (age i)) y) *
          Real.sqrt (((S i).base.metric (age i)).inner y v v) at hgradient
    rwa [hmetric i (age i) ht] at hgradient
  · exact (S i).abs_derivWithin_scalar_le_of_parabolic_localPullMetric (hS i) (gflow i)
      (Phi i) (hPhi i) (hq i) (hmetric i) (hcarrier i) ht' y
      (hb.2 (age i) ht' y hy hR)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_eventually_relative_scalar_derivative_bounds_of_metric_cp_convergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_eventually_relative_scalar_derivative_bounds_of_metric_cp_convergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_eventually_relative_scalar_derivative_bounds_of_metric_cp_convergence ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_eventually_relative_scalar_derivative_bounds_of_metric_cp_convergence

end DifferentialGeometry.PDE.RicciFlow.StandardCap

end

section

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Filter _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology _root_.Submission.DifferentialGeometry.Topology

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

universe u

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instSigmaCompactSpaceSubtypeThreeSpaceMemOpens (U : TopologicalSpace.Opens ThreeSpace) : SigmaCompactSpace U :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel U.isOpen)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instSigmaCompactSpaceSubtypeThreeSpaceMemOpens
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instSigmaCompactSpaceSubtypeThreeSpaceMemOpens target :: scope.openDecls } }

theorem exists_uniform_relative_scalar_derivative_bounds_of_terminal_metric_cp_convergence :
    ∃ C : ℝ, 0 < C ∧ ∀ {D r : ℝ}, r < D + 1 → ∀ {N : ℕ}, 4 ≤ N →
      ∀ (J : ℕ → RealTimeInterval) (age : ℕ → ℝ), (∀ i, 0 < age i) →
      ∀ S : ∀ i, SolutionOn (I := ThreeModel) (M := standardCapWindow D) (J i),
      (∀ i, IsSolutionOn (S i)) →
      (∀ i, _root_.Set.Icc (0 : ℝ) (age i) ⊆ (J i).carrier) →
      (∀ i, _root_.Set.Ioo (0 : ℝ) (age i) ⊆ (J i).regular) →
      MetricCPConvergenceOn {y : standardCapWindow D | ‖y.val‖ ≤ r} N
        (fun i => (S i).base.metric (age i))
        (metric.restrictOpen (standardCapWindow D))
        (metric.restrictOpen (standardCapWindow D)) →
      ∀ (X : ℕ → Type u) [∀ i, TopologicalSpace (X i)] [∀ i, ChartedSpace ThreeSpace (X i)]
        [∀ i, IsManifold ThreeModel ∞ (X i)] [∀ i, T2Space (X i)],
      ∀ (gflow : ∀ i, ℝ → SmoothRiemannianMetric ThreeModel (X i))
        (Phi : ∀ i, standardCapWindow D → X i)
        (hPhi : ∀ i, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (Phi i))
        (q birth : ℕ → ℝ) (hq : ∀ i, 0 < q i),
      (∀ i t, t ∈ _root_.Set.Icc (0 : ℝ) (age i) → (S i).base.metric t =
        localPullMetric (scaleMetric (q i) (hq i) (gflow i (birth i + t / q i)))
          (Phi i) (hPhi i)) →
      ∀ᶠ i in _root_.Filter.atTop, ∀ y : standardCapWindow D, ‖y.val‖ ≤ r →
        (∀ w : TangentSpace ThreeModel (Phi i y),
          |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ)
            (metricScalarAt (gflow i (birth i + age i / q i))) (Phi i y) w)| ≤
            C * metricScalarAt (gflow i (birth i + age i / q i)) (Phi i y) *
              Real.sqrt (metricScalarAt (gflow i (birth i + age i / q i)) (Phi i y)) *
              Real.sqrt ((gflow i (birth i + age i / q i)).inner (Phi i y) w w)) ∧
        |derivWithin (fun t => metricScalarAt (gflow i t) (Phi i y))
          (_root_.Set.Iic (birth i + age i / q i)) (birth i + age i / q i)| ≤
            C * metricScalarAt (gflow i (birth i + age i / q i)) (Phi i y) ^ 2 := by
  obtain ⟨B, hB, hjets⟩ := exists_eventually_window_curvature_derivative_bounds_of_metric_cp_convergence
  obtain ⟨C, hC, hbounds⟩ := exists_relative_scalar_derivative_bounds_of_terminal_curvature_jets
    (E := ThreeSpace) B (zero_le_one.trans hB)
  refine ⟨C, hC, ?_⟩
  intro D r hrD N hN J age hage S hS hcarrier hregular hconv X _ _ _ _ gflow Phi hPhi q birth hq hmetric
  have hlower := eventually_half_lt_metricScalarAt_of_metric_cp_convergence hrD (by omega : 2 ≤ N)
    (fun i => (S i).base.metric (age i)) hconv
  filter_upwards [hlower, hjets D r hrD N hN (fun i => (S i).base.metric (age i)) hconv] with i hi hji
  intro y hy
  have ht : age i ∈ _root_.Set.Icc (0 : ℝ) (age i) := ⟨(hage i).le, le_rfl⟩
  have ht' : age i ∈ _root_.Set.Ioc (0 : ℝ) (age i) := ⟨hage i, le_rfl⟩
  have hR : 1 / 2 ≤ (S i).scalar (age i) y := (hi y hy).le
  have hb := hbounds (J i) (S i) (hS i) 0 (age i) (hage i) (hcarrier i) (hregular i)
    y (fun j hj => hji j hj y hy) hR
  constructor
  · apply scalar_gradient_bound_of_localPull_scaleMetric
      (gflow i (birth i + age i / q i)) (Phi i) (hPhi i) (hq i) y
    have hgradient := hb.1
    change ∀ v : TangentSpace ThreeModel y,
      |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) (metricScalarAt ((S i).base.metric (age i))) y v)| ≤
        C * metricScalarAt ((S i).base.metric (age i)) y *
          Real.sqrt (metricScalarAt ((S i).base.metric (age i)) y) *
          Real.sqrt (((S i).base.metric (age i)).inner y v v) at hgradient
    rwa [hmetric i (age i) ht] at hgradient
  · exact (S i).abs_derivWithin_scalar_le_of_parabolic_localPullMetric (hS i) (gflow i)
      (Phi i) (hPhi i) (hq i) (hmetric i) (hcarrier i) ht' y
      hb.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_uniform_relative_scalar_derivative_bounds_of_terminal_metric_cp_convergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_uniform_relative_scalar_derivative_bounds_of_terminal_metric_cp_convergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_uniform_relative_scalar_derivative_bounds_of_terminal_metric_cp_convergence ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_uniform_relative_scalar_derivative_bounds_of_terminal_metric_cp_convergence

end DifferentialGeometry.PDE.RicciFlow.StandardCap

end
end
