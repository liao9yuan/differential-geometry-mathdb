import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.HalfLineOrder
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientMetricMonotonicity
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

private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instCompleteSpace_differentialGeometry_1 : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.instCompleteSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.instCompleteSpace_differentialGeometry_1 target :: scope.openDecls } }

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedFlowData.topology PointedFlowData.charted PointedFlowData.smooth
  PointedFlowData.t2 PointedFlowData.sigmaCompact

local notation "U" => poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma
local notation "Y" => poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma

theorem HalfLineMetricConvergenceData.metric_inner_antitoneOn_of_poleEndpointRescaledFlowSeq
    (Phi : PointedCGHMaps Y P phi) {R : SmoothRiemannianMetric I P.M}
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (x : P.M) (v : TangentSpace I x) :
    AntitoneOn (fun s : ℝ => (co.gInf s).inner x v v) (_root_.Set.Iic 0) := by
  intro s hs t ht hst
  change s ≤ 0 at hs
  change t ≤ 0 at ht
  apply co.inner_le_of_eventually_source_inner_le Phi ht hs
  exact Filter.Eventually.of_forall fun k y w => by
    rw [poleEndpointRescaledFlowSeq_metric_eq_shift,
      poleEndpointRescaledFlowSeq_metric_eq_shift]
    have hanti := IsAncientKappaSolution.metric_inner_antitoneOn
      ((U).term (phi (co.φ k))) (hancient (phi (co.φ k))) y w
    exact hanti (by change s - 1 ≤ 0; linarith)
      (by change t - 1 ≤ 0; linarith) (sub_le_sub_right hst 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.metric_inner_antitoneOn_of_poleEndpointRescaledFlowSeq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.metric_inner_antitoneOn_of_poleEndpointRescaledFlowSeq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.metric_inner_antitoneOn_of_poleEndpointRescaledFlowSeq ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.metric_inner_antitoneOn_of_poleEndpointRescaledFlowSeq

theorem HalfLineMetricConvergenceData.metric_inner_le_at_reflected_times
    (Phi : PointedCGHMaps Y P phi) {R : SmoothRiemannianMetric I P.M}
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    {a s : ℝ} (ha : 1 ≤ a) (has : a ≤ s) (x : P.M) (v : TangentSpace I x) :
    (co.gInf (1 - a)).inner x v v ≤ (co.gInf (1 - s)).inner x v v := by
  have hanti := co.metric_inner_antitoneOn_of_poleEndpointRescaledFlowSeq
    F hcar hreg b hbmem tau q hsigma Phi kappa hancient x v
  exact hanti (by change 1 - s ≤ 0; linarith)
    (by change 1 - a ≤ 0; linarith) (sub_le_sub_left has 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.metric_inner_le_at_reflected_times then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.metric_inner_le_at_reflected_times"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.metric_inner_le_at_reflected_times ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.metric_inner_le_at_reflected_times

end DifferentialGeometry.CheegerGromovCompactness

end
