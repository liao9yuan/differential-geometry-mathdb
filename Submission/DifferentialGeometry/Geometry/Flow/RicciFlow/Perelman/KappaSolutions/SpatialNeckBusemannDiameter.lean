import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckBusemannLevel
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckBusemannProper

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

theorem spatialNeckControlEpsilon_lt_inverse_five_pi :
    spatialNeckControlEpsilon < (5 * Real.pi)⁻¹ := by
  have h := one_div_lt_one_div_of_lt (by positivity : 0 < 5 * Real.pi)
    (by linarith [Real.pi_pos] : 5 * Real.pi < 100 * (1 + Real.pi))
  simpa only [spatialNeckControlEpsilon, inv_eq_one_div] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckControlEpsilon_lt_inverse_five_pi then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckControlEpsilon_lt_inverse_five_pi"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckControlEpsilon_lt_inverse_five_pi ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckControlEpsilon_lt_inverse_five_pi

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N] [ConnectedSpace N] [NoncompactSpace N]
  [RiemannianBundle (fun q : N => TangentSpace I q)]
  [IsContinuousRiemannianBundle E (fun q : N => TangentSpace I q)]
  [IsRiemannianManifold I N]

private local instance neckDiameterC1 : IsManifold I 1 N :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.neckDiameterC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.neckDiameterC1 target :: scope.openDecls } }

namespace SpatialNeckWitness

theorem busemann_level_diameter_and_proper
    {h : SmoothRiemannianMetric I N} {yStar : SpatialNeckSphere}
    {p : N} {epsilon : ℝ} (W : SpatialNeckWitness h yStar p epsilon)
    (hEnorm : IsMetricNorm (I := I) h)
    (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (hsec : DifferentialGeometry.Geometry.HasPositiveSectionalCurvature (I := I) h)
    {c : ℝ≥0 → N} (hc : Isometry c) :
    11 / 12 * spatialNeckScale h p * Real.pi ≤
      Metric.diam {q : N | busemann c q = busemann c p} ∧
    Metric.diam {q : N | busemann c q = busemann c p} ≤
      11 * Real.pi * spatialNeckScale h p ∧
    IsProperMap (busemann c) ∧ BddBelow (_root_.Set.range (busemann c)) ∧
    ∃ q : N, busemann c q = (⨅ x : N, busemann c x) ∧
      ∀ x : N, busemann c q ≤ busemann c x := by
  obtain ⟨W', _hchoice, _hsphere, _hcore, _himage, ⟨D⟩⟩ :=
    W.exists_ordered_compact_end_sides hsec
  have hnonneg := hsec.toNonnegative
  obtain ⟨hlower, hupper⟩ := D.busemann_level_diam_bounds hEnorm hsmall hnonneg hc
  exact ⟨hlower, hupper, D.busemann_isProperMap hEnorm hsmall hnonneg hc,
    D.busemann_bddBelow hEnorm hsmall hnonneg hc,
    D.exists_busemann_minimum hEnorm hsmall hnonneg hc⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.busemann_level_diameter_and_proper then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.busemann_level_diameter_and_proper"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.busemann_level_diameter_and_proper ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.busemann_level_diameter_and_proper

end SpatialNeckWitness

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
