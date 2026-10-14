import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.SourceScalarContinuity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RegularPoleRescalings

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

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
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
  PointedRiemannianManifold.t2

local notation "U" => poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma
local notation "Y" => poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma

theorem PointedCGHMaps.eventually_continuousOn_poleEndpoint_scalar_in_chart
    (Φ : PointedCGHMaps Y P phi) (η : ℕ → ℕ) (hη : _root_.Filter.Tendsto η _root_.Filter.atTop _root_.Filter.atTop)
    (x : P.M) {K : Set E} (hK : IsCompact K)
    (hKchart : K ⊆ (extChartAt I x).target) {a c : ℝ} (ha : 1 ≤ a) :
    ∀ᶠ k in _root_.Filter.atTop,
      ContinuousOn
        (fun z : E × ℝ =>
          ((U).term (phi (η k))).S.scalar (-z.2)
            (Φ.map (η k) ((extChartAt I x).symm z.1)))
        (K ×ˢ _root_.Set.Icc a c) := by
  have hchart : ContinuousOn (extChartAt I x).symm K :=
    (continuousOn_extChartAt_symm (I := I) x).mono hKchart
  have hcompact : IsCompact ((extChartAt I x).symm '' K) :=
    hK.image_of_continuousOn hchart
  have hsource := Φ.eventually_continuousOn_scalar η hη
    (J := (Y).D.carrier) Subset.rfl hcompact
  filter_upwards [hsource] with k hk
  have hpair : ContinuousOn
      (fun z : E × ℝ => (1 - z.2, (extChartAt I x).symm z.1))
      (K ×ˢ _root_.Set.Icc a c) :=
    (continuousOn_const.sub continuousOn_snd).prodMk
      (hchart.comp continuousOn_fst (fun _ hz => hz.1))
  have hmaps : _root_.Set.MapsTo
      (fun z : E × ℝ => (1 - z.2, (extChartAt I x).symm z.1))
      (K ×ˢ _root_.Set.Icc a c) ((Y).D.carrier ×ˢ ((extChartAt I x).symm '' K)) := by
    intro z hz
    refine ⟨?_, _root_.Set.mem_image_of_mem _ hz.1⟩
    change 1 - z.2 ∈ ancientTimeInterval.carrier
    rw [ancientTimeInterval_carrier]
    change 1 - z.2 ≤ 0
    linarith [hz.2.1]
  have hpull : ContinuousOn
      (fun z : E × ℝ =>
        ((Y).term (phi (η k))).S.scalar (1 - z.2)
          (Φ.map (η k) ((extChartAt I x).symm z.1)))
      (K ×ˢ _root_.Set.Icc a c) := by
    simpa only [Function.comp_def] using hk.comp hpair hmaps
  apply hpull.congr
  intro z _
  change metricScalarAt (((U).term (phi (η k))).S.base.metric (-z.2))
      (Φ.map (η k) ((extChartAt I x).symm z.1)) =
    metricScalarAt (((Y).term (phi (η k))).S.base.metric (1 - z.2))
      (Φ.map (η k) ((extChartAt I x).symm z.1))
  rw [poleEndpointRescaledFlowSeq_metric_eq_shift]
  have htime : 1 - z.2 - 1 = -z.2 := by ring
  rw [htime]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.eventually_continuousOn_poleEndpoint_scalar_in_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.eventually_continuousOn_poleEndpoint_scalar_in_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.eventually_continuousOn_poleEndpoint_scalar_in_chart ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.eventually_continuousOn_poleEndpoint_scalar_in_chart

end DifferentialGeometry.CheegerGromovCompactness
