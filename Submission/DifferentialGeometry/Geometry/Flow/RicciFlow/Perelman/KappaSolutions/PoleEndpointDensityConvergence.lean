import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RegularPoleRescalings
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.HalfLineConvergence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Defs
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open _root_.Filter _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
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

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth

local notation "U" => poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma
local notation "Y" => poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma

theorem HalfLineMetricConvergenceData.tendstoLocallyUniformly_poleEndpoint_redDensity
    (Phi : PointedCGHMaps Y P phi) {R : SmoothRiemannianMetric I P.M}
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (p : F.M) (t : ℝ) (ell : P.M → ℝ) (hell : Continuous ell)
    (hconv : TendstoLocallyUniformly
      (fun k y => redLength ((U).term (phi (co.φ k))).S 0 p
        (Phi.map (co.φ k) y) (1 - t)) ell _root_.Filter.atTop) :
    TendstoLocallyUniformly
      (fun k y => redDensity ((U).term (phi (co.φ k))).S 0 p
        (Phi.map (co.φ k) y) (1 - t))
      (fun y => Real.exp (-ell y -
        ((Module.finrank ℝ E : ℝ) / 2) * Real.log (1 - t) -
        ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi))) atTop := by
  let f : ℝ → ℝ := fun r => Real.exp (-r -
    ((Module.finrank ℝ E : ℝ) / 2) * Real.log (1 - t) -
    ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi))
  have hf : Continuous f := by dsimp only [f]; fun_prop
  rw [tendstoLocallyUniformly_iff_forall_tendsto] at hconv ⊢
  intro x
  have hleft : _root_.Filter.Tendsto (fun z : ℕ × P.M => ell z.2) (_root_.Filter.atTop ×ˢ 𝓝 x) (𝓝 (ell x)) :=
    hell.continuousAt.tendsto.comp _root_.Filter.tendsto_snd
  have hright : _root_.Filter.Tendsto
      (fun z : ℕ × P.M => redLength ((U).term (phi (co.φ z.1))).S 0 p
        (Phi.map (co.φ z.1) z.2) (1 - t)) (_root_.Filter.atTop ×ˢ 𝓝 x) (𝓝 (ell x)) :=
    hleft.congr_uniformity (hconv x)
  have hpair := (hf.continuousAt.tendsto.comp hleft).prodMk_nhds
    (hf.continuousAt.tendsto.comp hright)
  simpa only [f, redDensity, Function.comp_def] using
    hpair.mono_right (nhds_le_uniformity (f (ell x)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.tendstoLocallyUniformly_poleEndpoint_redDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.tendstoLocallyUniformly_poleEndpoint_redDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.tendstoLocallyUniformly_poleEndpoint_redDensity ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.tendstoLocallyUniformly_poleEndpoint_redDensity

end DifferentialGeometry.CheegerGromovCompactness

end
