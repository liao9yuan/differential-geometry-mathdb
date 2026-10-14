import Submission.DifferentialGeometry.Geometry.Comparison.Busemann.Support.HorosphereHessianLimit
import Submission.DifferentialGeometry.Geometry.Comparison.Busemann.Support.LineSupportRiccati

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.MeasureTheory
open scoped _root_.Topology _root_.NNReal _root_.ContDiff _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Variation
open _root_.Submission.DifferentialGeometry.Tensor0SBundle

namespace DifferentialGeometry.Geometry.Topology

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
private theorem laplacian_eq_sum_hessian (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U) {x : M} (hx : x ∈ U)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x))
    (hON : ∀ i j, g.inner x (b i) (b j) = if i = j then 1 else 0) :
    laplacian (I := I) (LeviCivita (I := I) g) g f x =
      ∑ i, hessFun (I := I) g f x (b i) (b i) := by
  classical
  rw [lap_eq_hess_on (I := I) g hU hf hx,
    metricTracePair0SAt_eq_sum_basis (I := I) g b
      (fun i j => if i = j then 1 else 0)
      (metricInverseInBasis_of_orthonormal (I := I) g b hON)]
  simp only [hessTensorAt_apply, ite_mul, one_mul, _root_.MulZeroClass.zero_mul]
  simp

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Topology.laplacian_eq_sum_hessian
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Topology.laplacian_eq_sum_hessian target :: scope.openDecls } }

theorem lineDistanceSupport_laplacian_nonpos
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hRic : ∀ y : M, ∀ w : TangentSpace I y, 0 ≤ ricciTensor (I := I) g y w w)
    (p : M) (u : TangentSpace I p) (hu : g.inner p u u = 1)
    (hiso : Isometry (intrinsicGeodesic (I := I) g hEnorm p u)) (s R : ℝ) (hsR : s < R) :
    let eta := intrinsicGeodesic (I := I) g hEnorm p u
    laplacian (I := I) (LeviCivita (I := I) g) g (lineDistanceSupport eta R) (eta s) ≤ 0 := by
  classical
  let eta := intrinsicGeodesic (I := I) g hEnorm p u
  obtain ⟨L, _, hL, _, htrace⟩ :=
    exists_lineDistanceSupport_opposite_hessian_limits (I := I) g hEnorm hRic p u hu hiso s
  have hb : ∃ b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I (eta s)),
      ∀ i j, g.inner (eta s) (b i) (b j) = if i = j then 1 else 0 :=
    exists_orthonormal_basis (I := I) g (eta s)
  obtain ⟨b, hON⟩ := hb
  have hlim := tendsto_finsetSum Finset.univ (fun i _ => hL (b i) (b i))
  rw [htrace b hON] at hlim
  apply ge_of_tendsto hlim
  filter_upwards [_root_.Filter.eventually_ge_atTop R] with S hS
  obtain ⟨U, hU, hx, hf⟩ := exists_open_smooth_lineDistanceSupport (I := I)
    g hEnorm p u hu hiso s R hsR
  rw [laplacian_eq_sum_hessian g hU hf hx b hON]
  exact Finset.sum_le_sum fun i _ =>
    lineDistanceSupport_hessian_mono (I := I) g hEnorm p u hu hiso s R S hsR hS (b i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.lineDistanceSupport_laplacian_nonpos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.lineDistanceSupport_laplacian_nonpos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.lineDistanceSupport_laplacian_nonpos ``Submission.DifferentialGeometry.Geometry.Topology.lineDistanceSupport_laplacian_nonpos

theorem tendsto_lineDistanceSupport_laplacian_zero
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hRic : ∀ y : M, ∀ w : TangentSpace I y, 0 ≤ ricciTensor (I := I) g y w w)
    (p : M) (u : TangentSpace I p) (hu : g.inner p u u = 1)
    (hiso : Isometry (intrinsicGeodesic (I := I) g hEnorm p u)) (s : ℝ) :
    let eta := intrinsicGeodesic (I := I) g hEnorm p u
    Tendsto (fun R => laplacian (I := I) (LeviCivita (I := I) g) g
      (lineDistanceSupport eta R) (eta s)) _root_.Filter.atTop (𝓝 0) := by
  have hden : _root_.Filter.Tendsto (fun R : ℝ => R - s) _root_.Filter.atTop atTop := by
    refine tendsto_atTop.mpr fun b => ?_
    filter_upwards [_root_.Filter.eventually_ge_atTop (b + s)] with R hR
    linarith
  have hlow : _root_.Filter.Tendsto (fun R : ℝ => -(((Module.finrank ℝ E - 1 : ℕ) : ℝ) / (R - s)))
      atTop (𝓝 0) := by
    simpa only [neg_zero] using (hden.const_div_atTop ((Module.finrank ℝ E - 1 : ℕ) : ℝ)).neg
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds
  · filter_upwards [_root_.Filter.eventually_gt_atTop s] with R hR
    exact lineDistanceSupport_laplacian_ge (I := I) g hEnorm hRic p u hu hiso s R hR
  · filter_upwards [_root_.Filter.eventually_gt_atTop s] with R hR
    exact lineDistanceSupport_laplacian_nonpos (I := I) g hEnorm hRic p u hu hiso s R hR

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.tendsto_lineDistanceSupport_laplacian_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.tendsto_lineDistanceSupport_laplacian_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.tendsto_lineDistanceSupport_laplacian_zero ``Submission.DifferentialGeometry.Geometry.Topology.tendsto_lineDistanceSupport_laplacian_zero

theorem lineDistanceSupport_hessian_energy_bounds
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hRic : ∀ y : M, ∀ w : TangentSpace I y, 0 ≤ ricciTensor (I := I) g y w w)
    (p : M) (u : TangentSpace I p) (hu : g.inner p u u = 1)
    (hiso : Isometry (intrinsicGeodesic (I := I) g hEnorm p u))
    (a b R : ℝ) (hab : a ≤ b) (hbR : b < R) :
    let eta := intrinsicGeodesic (I := I) g hEnorm p u
    0 ≤ (∫ s in a..b, chartHessFrobeniusSq (I := I) g (lineDistanceSupport eta R) (eta s)) ∧
    (∫ s in a..b, chartHessFrobeniusSq (I := I) g (lineDistanceSupport eta R) (eta s)) ≤
      ((Module.finrank ℝ E - 1 : ℕ) : ℝ) / (R - b) := by
  constructor
  · exact intervalIntegral.integral_nonneg hab fun s hs =>
      lineDistanceSupport_hessianNorm_nonneg (I := I) g hEnorm p u hu hiso s R (hs.2.trans_lt hbR)
  · have henergy := integral_lineDistanceSupport_hessianNorm_le (I := I)
      g hEnorm hRic p u hu hiso a b R hab hbR
    have ha := lineDistanceSupport_laplacian_nonpos (I := I)
      g hEnorm hRic p u hu hiso a R (hab.trans_lt hbR)
    have hb := lineDistanceSupport_laplacian_ge (I := I)
      g hEnorm hRic p u hu hiso b R hbR
    dsimp only at henergy ha hb
    linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.lineDistanceSupport_hessian_energy_bounds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.lineDistanceSupport_hessian_energy_bounds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.lineDistanceSupport_hessian_energy_bounds ``Submission.DifferentialGeometry.Geometry.Topology.lineDistanceSupport_hessian_energy_bounds

theorem tendsto_lineDistanceSupport_hessian_energy_zero
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hRic : ∀ y : M, ∀ w : TangentSpace I y, 0 ≤ ricciTensor (I := I) g y w w)
    (p : M) (u : TangentSpace I p) (hu : g.inner p u u = 1)
    (hiso : Isometry (intrinsicGeodesic (I := I) g hEnorm p u))
    (a b : ℝ) (hab : a ≤ b) :
    let eta := intrinsicGeodesic (I := I) g hEnorm p u
    Tendsto (fun R => ∫ s in a..b, chartHessFrobeniusSq (I := I) g
      (lineDistanceSupport eta R) (eta s)) _root_.Filter.atTop (𝓝 0) := by
  have hden : _root_.Filter.Tendsto (fun R : ℝ => R - b) _root_.Filter.atTop atTop := by
    refine tendsto_atTop.mpr fun c => ?_
    filter_upwards [_root_.Filter.eventually_ge_atTop (c + b)] with R hR
    linarith
  apply squeeze_zero' ?_ ?_ (hden.const_div_atTop ((Module.finrank ℝ E - 1 : ℕ) : ℝ))
  · filter_upwards [_root_.Filter.eventually_gt_atTop b] with R hR
    exact (lineDistanceSupport_hessian_energy_bounds (I := I)
      g hEnorm hRic p u hu hiso a b R hab hR).1
  · filter_upwards [_root_.Filter.eventually_gt_atTop b] with R hR
    exact (lineDistanceSupport_hessian_energy_bounds (I := I)
      g hEnorm hRic p u hu hiso a b R hab hR).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.tendsto_lineDistanceSupport_hessian_energy_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.tendsto_lineDistanceSupport_hessian_energy_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.tendsto_lineDistanceSupport_hessian_energy_zero ``Submission.DifferentialGeometry.Geometry.Topology.tendsto_lineDistanceSupport_hessian_energy_zero

end DifferentialGeometry.Geometry.Topology

end
