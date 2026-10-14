import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientCurvatureBounds
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ReducedVolumeNormalization
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TensorNormFinrankNeZero
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Monotonicity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolution

open _root_.Filter _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions (intrinsicReducedVolume)
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} {F : PointedFlowData.{u, uE, uH} (I := I) D}

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolution.instTopologicalSpaceM : TopologicalSpace F.M := F.topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolution.instTopologicalSpaceM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolution.instTopologicalSpaceM target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolution.instChartedSpaceM : ChartedSpace H F.M := F.charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolution.instChartedSpaceM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolution.instChartedSpaceM target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolution.instIsManifoldRealSomeENatTopM : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolution.instIsManifoldRealSomeENatTopM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolution.instIsManifoldRealSomeENatTopM target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolution.instT2SpaceM : T2Space F.M := F.t2

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolution.instT2SpaceM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolution.instT2SpaceM target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolution.instSigmaCompactSpaceM : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolution.instSigmaCompactSpaceM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolution.instSigmaCompactSpaceM target :: scope.openDecls } }

theorem reducedVolume_antitone_of_regular_base
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M)
    {T : ℝ} (hT : T ∈ D.regular) :
    AntitoneOn (intrinsicReducedVolume F.S T p) (_root_.Set.Ioi 0) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : NeZero (Module.finrank ℝ E) := by
    obtain ⟨t, _, x, hx⟩ := hF.notFlat
    exact ⟨finrank_ne_zero_of_normSq0S_ne_zero
      (F.S.base.metric t) x (by decide : 0 < 4) (F.S.base.rm04 t x) hx⟩
  let _ : ConnectedSpace F.M := hF.connected
  have hTneg : T < 0 := by simpa only [hF.regular_eq, _root_.Set.mem_Iio] using hT
  have hcomplete : RiemannianMetricComplete (I := I) (F.S.base.metric T) :=
    ⟨hF.complete T (D.regular_subset hT)⟩
  obtain ⟨K, hK⟩ := hF.exists_rmNormSq_le
  intro tau₁ h₁ tau₂ _ h₁₂
  have hslab : _root_.Set.Icc (T - tau₂) T ⊆ D.regular := by
    intro t ht
    simpa only [hF.regular_eq, _root_.Set.mem_Iio] using ht.2.trans_lt hTneg
  exact DifferentialGeometry.PDE.RicciFlow.Perelman.redVolume_anti_of_rm
    (I := I) (D := D) F.S F.isSolution T hcomplete p
    (fun sigma _ hreg => ⟨K, fun t ht x => hK t (D.regular_subset (hreg ht)) x⟩)
    h₁ h₁₂ hslab

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolution.reducedVolume_antitone_of_regular_base then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolution.reducedVolume_antitone_of_regular_base"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolution.reducedVolume_antitone_of_regular_base ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolution.reducedVolume_antitone_of_regular_base

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolution
