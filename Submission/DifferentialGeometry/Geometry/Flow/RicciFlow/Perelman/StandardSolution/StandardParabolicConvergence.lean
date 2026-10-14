import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardParabolicSequence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardTerminalGeometry
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Scaling

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Submission.Set _root_.Filter _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.E3 target :: scope.openDecls } }

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

@[simp] theorem standardParabolicSequence_atTime_zero
    (B : ℝ) (hB : 0 < B) (S : ℕ → PartialStandardSolution)
    (time : ℕ → ℝ) (point : ℕ → E3)
    (htime : ∀ i, time i ∈ (S i).domain ∧ 3 / 4 ≤ time i ∧ time i < 1) :
    (standardParabolicSequence B hB S time point htime).atTime 0 =
      (⟨fun i => ((S i).pointedFlow.atTime (time i)).repoint (point i)⟩ :
        PointedRiemannianSeq (𝓡 3)).scaleMetric B hB := by
  unfold FlowSequence.atTime PointedRiemannianSeq.scaleMetric
  congr 1
  funext i
  unfold PointedFlowData.atTime PointedRiemannianManifold.repoint
    PointedRiemannianManifold.scaleMetric
  congr 1
  change scaleMetric B hB ((S i).metric (time i + 0 / B)) =
    scaleMetric B hB ((S i).metric (time i))
  rw [zero_div, add_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.standardParabolicSequence_atTime_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.standardParabolicSequence_atTime_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.standardParabolicSequence_atTime_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.standardParabolicSequence_atTime_zero


theorem exists_standard_parabolic_pointed_convergence_within_radius
    (B : ℝ) (hB : 0 < B) (S : ℕ → PartialStandardSolution)
    (time : ℕ → ℝ) (point : ℕ → E3) {rho : ℝ} (hrho : 0 < rho)
    (htime : ∀ i, time i ∈ (S i).domain ∧ 3 / 4 ≤ time i ∧ time i < 1)
    (hscalar : ∀ r : ℝ, 0 < r → r < rho → ∃ A : ℝ, ∀ᶠ i in _root_.Filter.atTop,
      ∀ y ∈ riemannianClosedBallOf ((S i).metric (time i)) (point i) r,
        metricScalarAt ((S i).metric (time i)) y ≤ A) :
    let X := (standardParabolicSequence B hB S time point htime).atTime 0
    ∃ phi : ℕ → ℕ, StrictMono phi ∧ ∃ radius : ℕ → ℝ,
      (∀ k, 0 < radius k ∧ radius k < Real.sqrt B * rho) ∧
      _root_.Filter.Tendsto radius _root_.Filter.atTop (𝓝 (Real.sqrt B * rho)) ∧
      ∃ L : PointedRiemannianManifold (𝓡 3),
      ∃ maps : PointedRiemannianConvergenceMaps X L phi,
      ∃ C : PointedRiemannianConverges X L phi maps,
        (∀ k, C.metrics.domain k = CanonicalMetricCompactness.canonicalSourceData maps k) ∧
        (∀ k, maps.target k = riemannianBallOf (X.obj (phi k)).metric
          (X.obj (phi k)).basepoint (radius k)) ∧
        (∀ x : L.M, riemannianEDistOf L.metric L.basepoint x <
          ENNReal.ofReal (Real.sqrt B * rho)) ∧
        (∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
          ∀ x ∈ maps.source k, ∀ v : TangentSpace (𝓡 3) x,
            (1 - eps) * L.metric.inner x v v ≤
              (X.obj (phi k)).metric.inner (maps.partialDiffeomorph k x)
                (mfderiv (𝓡 3) (𝓡 3) (maps.partialDiffeomorph k) x v)
                (mfderiv (𝓡 3) (𝓡 3) (maps.partialDiffeomorph k) x v) ∧
              (X.obj (phi k)).metric.inner (maps.partialDiffeomorph k x)
                (mfderiv (𝓡 3) (𝓡 3) (maps.partialDiffeomorph k) x v)
                (mfderiv (𝓡 3) (𝓡 3) (maps.partialDiffeomorph k) x v) ≤
              (1 + eps) * L.metric.inner x v v) ∧
        ∀ r : ℝ, 0 ≤ r → r < Real.sqrt B * rho →
          IsCompact (riemannianClosedBallOf L.metric L.basepoint r) := by
  dsimp only
  rw [standardParabolicSequence_atTime_zero]
  obtain ⟨phi, hphi, radius, hrad, hradlim, L, maps, C,
    hcanonical, htargets, hradial, hmetrics, hcompact⟩ :=
    exists_standard_terminal_pointed_convergence_within_radius S time point
      (by norm_num : (0 : ℝ) < 3 / 4) hrho htime hscalar
  have hsqrt : 0 < Real.sqrt B := Real.sqrt_pos.mpr hB
  refine ⟨phi, hphi, fun k => Real.sqrt B * radius k,
    fun k => ⟨mul_pos hsqrt (hrad k).1, mul_lt_mul_of_pos_left (hrad k).2 hsqrt⟩,
    hradlim.const_mul (Real.sqrt B), L.scaleMetric B hB, maps.scaleMetric B hB,
    C.scaleMetric B hB, ?_, ?_, ?_, ?_, ?_⟩
  · exact C.metrics.scaleMetric_domain_eq_canonical hcanonical B hB
  · intro k
    change maps.target k = riemannianBallOf (scaleMetric B hB ((S (phi k)).metric (time (phi k))))
      (point (phi k)) (Real.sqrt B * radius k)
    rw [riemannianBallOf_scaleMetric]
    exact htargets k
  · intro x
    change x ∈ riemannianBallOf (scaleMetric B hB L.metric) L.basepoint (Real.sqrt B * rho)
    rw [riemannianBallOf_scaleMetric]
    exact hradial x
  · intro eps heps
    obtain ⟨N, hN⟩ := hmetrics eps heps
    refine ⟨N, fun k hk x hx v => ?_⟩
    obtain ⟨hlow, hupp⟩ := hN k hk x hx v
    change (1 - eps) * (B * L.metric.inner x v v) ≤
        B * ((S (phi k)).metric (time (phi k))).inner (maps.partialDiffeomorph k x)
          (mfderiv (𝓡 3) (𝓡 3) (maps.partialDiffeomorph k) x v)
          (mfderiv (𝓡 3) (𝓡 3) (maps.partialDiffeomorph k) x v) ∧
      B * ((S (phi k)).metric (time (phi k))).inner (maps.partialDiffeomorph k x)
          (mfderiv (𝓡 3) (𝓡 3) (maps.partialDiffeomorph k) x v)
          (mfderiv (𝓡 3) (𝓡 3) (maps.partialDiffeomorph k) x v) ≤
        (1 + eps) * (B * L.metric.inner x v v)
    constructor
    · simpa only [mul_left_comm B] using mul_le_mul_of_nonneg_left hlow hB.le
    · simpa only [mul_left_comm B] using mul_le_mul_of_nonneg_left hupp hB.le
  · intro r hr hrrho
    change IsCompact (riemannianClosedBallOf (scaleMetric B hB L.metric) L.basepoint r)
    have hcancel : Real.sqrt B * (r / Real.sqrt B) = r := mul_div_cancel₀ r hsqrt.ne'
    have hball := riemannianClosedBallOf_scaleMetric B hB L.metric L.basepoint (r / Real.sqrt B)
    rw [hcancel] at hball
    rw [hball]
    exact hcompact (r / Real.sqrt B) (div_nonneg hr hsqrt.le)
      ((div_lt_iff₀ hsqrt).mpr (by simpa only [mul_comm] using hrrho))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.exists_standard_parabolic_pointed_convergence_within_radius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.exists_standard_parabolic_pointed_convergence_within_radius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.exists_standard_parabolic_pointed_convergence_within_radius ``Submission.DifferentialGeometry.PDE.RicciFlow.exists_standard_parabolic_pointed_convergence_within_radius

end DifferentialGeometry.PDE.RicciFlow
