import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckBusemannInward
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckOutwardAngle

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N] [ConnectedSpace N]
  [RiemannianBundle (fun q : N => TangentSpace I q)]
  [IsContinuousRiemannianBundle E (fun q : N => TangentSpace I q)]
  [IsRiemannianManifold I N]

private local instance outwardBusemannC1 : IsManifold I 1 N :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.outwardBusemannC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.outwardBusemannC1 target :: scope.openDecls } }

namespace SpatialNeckSideData

variable {h : SmoothRiemannianMetric I N} {yStar : SpatialNeckSphere}
  {p : N} {epsilon : ℝ} {W : SpatialNeckWitness h yStar p epsilon}
  (D : SpatialNeckSideData W)

theorem busemann_outward_ge (hEnorm : IsMetricNorm (I := I) h)
    (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (hsec : DifferentialGeometry.Geometry.HasNonnegativeSectionalCurvature (I := I) h)
    {c : ℝ≥0 → N} (hc : Isometry c) {q : N}
    (hq : q ∈ D.upper (5 * Real.pi)) :
    busemann c p + _root_.Dist.dist p q / 4 ≤ busemann c q := by
  have hgap := spatialNeckControlEpsilon_inverse_gap W.epsilon_pos hsmall
  have hs : |5 * Real.pi| < epsilon⁻¹ + 1 := by
    rw [abs_of_pos (by positivity : 0 < 5 * Real.pi)]
    linarith [Real.pi_pos]
  have hevent : ∀ᶠ t in _root_.Filter.atTop,
      busemannApprox c t p - busemannApprox c t q ≤ -(_root_.Dist.dist p q / 4) := by
    filter_upwards [D.ray_eventually_upper hc (5 * Real.pi) hs,
      _root_.Filter.eventually_ge_atTop ((2 * _root_.Dist.dist p q + _root_.Dist.dist (c 0) p).toNNReal)] with t ht htime
    have htimeReal : 2 * _root_.Dist.dist p q + _root_.Dist.dist (c 0) p ≤ (t : ℝ) := by
      have hcast : (((2 * _root_.Dist.dist p q + _root_.Dist.dist (c 0) p).toNNReal : ℝ≥0) : ℝ) ≤ (t : ℝ) := by
        exact_mod_cast htime
      simpa only [Real.coe_toNNReal _ (by positivity : 0 ≤ 2 * dist p q + dist (c 0) p)] using hcast
    have hrad : _root_.Dist.dist (c 0) (c t) = (t : ℝ) := by
      rw [hc.dist_eq]
      change |0 - (t : ℝ)| = (t : ℝ)
      rw [zero_sub, abs_neg, abs_of_nonneg t.coe_nonneg]
    have htriangle := dist_triangle (c 0) p (c t)
    rw [hrad] at htriangle
    have hlarge : 2 * _root_.Dist.dist p q ≤ _root_.Dist.dist p (c t) := by linarith
    have hloss := D.outward_distance_loss hEnorm hsmall hsec ht hq hlarge
    rw [dist_comm (c t) q] at hloss
    dsimp only [busemannApprox]
    linarith
  have hlimit := le_of_tendsto ((tendsto_busemannApprox hc p).sub
    (tendsto_busemannApprox hc q)) hevent
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckSideData.busemann_outward_ge then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckSideData.busemann_outward_ge"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckSideData.busemann_outward_ge ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckSideData.busemann_outward_ge

theorem busemann_outward_lt (hEnorm : IsMetricNorm (I := I) h)
    (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (hsec : DifferentialGeometry.Geometry.HasNonnegativeSectionalCurvature (I := I) h)
    {c : ℝ≥0 → N} (hc : Isometry c) {q : N}
    (hq : q ∈ D.upper (5 * Real.pi)) : busemann c p < busemann c q := by
  have hgap := spatialNeckControlEpsilon_inverse_gap W.epsilon_pos hsmall
  have hs : |5 * Real.pi| < epsilon⁻¹ + 1 := by
    rw [abs_of_pos (by positivity : 0 < 5 * Real.pi)]
    linarith [Real.pi_pos]
  have hp := D.marked_mem_lower (5 * Real.pi) hs (by positivity)
  have hdisjoint := (D.slice_spec (5 * Real.pi) hs).2.2.2.2.1
  have hpq : p ≠ q := by
    intro heq
    have hqlower : q ∈ D.lower (5 * Real.pi) :=
      (congrArg (fun z : N => z ∈ D.lower (5 * Real.pi)) heq).mp hp
    exact Set.disjoint_left.mp hdisjoint hqlower hq
  have hdist : 0 < _root_.Dist.dist p q := dist_pos.mpr hpq
  have hbound := D.busemann_outward_ge hEnorm hsmall hsec hc hq
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckSideData.busemann_outward_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckSideData.busemann_outward_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckSideData.busemann_outward_lt ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckSideData.busemann_outward_lt

end SpatialNeckSideData

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
