import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.ClosedIntervalScalarConvergence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RegularPoleRescalings
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.HalfLineExistence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open _root_.Filter _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)
  (hcar : D.carrier = Iic 0) (hreg : D.regular = Iio 0)
  (b : ℝ) (hbmem : b ∈ D.carrier) (tau : ℕ → ℝ) (q : ℕ → F.M)
  (hsigma : ∀ i, 0 < tau i + b)
  {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}

private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instTopologicalSpaceM_3 : TopologicalSpace F.M := F.topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.instTopologicalSpaceM_3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.instTopologicalSpaceM_3 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instChartedSpaceM_3 : ChartedSpace H F.M := F.charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.instChartedSpaceM_3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.instChartedSpaceM_3 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instIsManifoldRealSomeENatTopM_2 : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.instIsManifoldRealSomeENatTopM_2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.instIsManifoldRealSomeENatTopM_2 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instSigmaCompactSpaceM_2 : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.instSigmaCompactSpaceM_2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.instSigmaCompactSpaceM_2 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instT2SpaceM_2 : T2Space F.M := F.t2

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.instT2SpaceM_2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.instT2SpaceM_2 target :: scope.openDecls } }

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

local notation "U" => poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma
local notation "Y" => poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma

theorem HalfLineMetricConvergenceData.tendstoUniformlyOn_poleEndpoint_scalar
    (Phi : PointedCGHMaps Y P phi) (R : SmoothRiemannianMetric I P.M)
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    {a c : ℝ} (ha : 1 ≤ a) {K : Set P.M} (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun k (z : ℝ × P.M) =>
        ((U).term (phi (co.φ k))).S.scalar (-z.1) (Phi.map (co.φ k) z.2))
      (fun z => metricScalarAt (co.gInf (1 - z.1)) z.2) _root_.Filter.atTop (_root_.Set.Icc a c ×ˢ K) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨n, hn⟩ := exists_nat_ge (c - 1)
  have hslab : _root_.Set.Icc (-(n : ℝ)) 0 ⊆ (Y).D.carrier := by
    intro s hs
    change s ∈ ancientTimeInterval.carrier
    simpa only [ancientTimeInterval_carrier, _root_.Set.mem_Iic] using hs.2
  have hregular : _root_.Set.Ico (-(n : ℝ)) 0 ⊆ (Y).D.regular := by
    intro s hs
    change s ∈ ancientTimeInterval.regular
    simpa only [ancientTimeInterval_regular, _root_.Set.mem_Iio] using hs.2
  have hconv := FlowMetricConvergenceData.tendstoUniformlyOn_scalar_on_closed_interval
    Phi R bf hsrc htgt (HalfLineMetricConvergenceData.atWindow Phi co n) hslab hregular hK
  rw [Metric.tendstoUniformlyOn_iff] at hconv ⊢
  intro epsilon hepsilon
  filter_upwards [hconv epsilon hepsilon] with k hk
  rintro ⟨t, x⟩ ⟨ht, hx⟩
  have hs : (1 - t, x) ∈ _root_.Set.Icc (-(n : ℝ)) 0 ×ˢ K := by
    exact ⟨⟨by linarith [ht.2], by linarith [ht.1]⟩, hx⟩
  have hscalar : ((Y).term (phi (co.φ k))).S.scalar (1 - t)
        (Phi.map (co.φ k) x) =
      ((U).term (phi (co.φ k))).S.scalar (-t) (Phi.map (co.φ k) x) := by
    change metricScalarAt (((Y).term (phi (co.φ k))).S.base.metric (1 - t))
        (Phi.map (co.φ k) x) =
      metricScalarAt (((U).term (phi (co.φ k))).S.base.metric (-t))
        (Phi.map (co.φ k) x)
    rw [poleEndpointRescaledFlowSeq_metric_eq_shift]
    have htime : 1 - t - 1 = -t := by ring
    rw [htime]
    rfl
  simpa only [HalfLineMetricConvergenceData.atWindow, Function.comp_apply, hscalar] using
    hk (1 - t, x) hs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.tendstoUniformlyOn_poleEndpoint_scalar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.tendstoUniformlyOn_poleEndpoint_scalar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.tendstoUniformlyOn_poleEndpoint_scalar ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.tendstoUniformlyOn_poleEndpoint_scalar

end DifferentialGeometry.CheegerGromovCompactness
