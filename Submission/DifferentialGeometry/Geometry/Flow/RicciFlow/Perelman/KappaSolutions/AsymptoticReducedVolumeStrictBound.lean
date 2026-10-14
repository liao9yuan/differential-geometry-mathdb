import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardSliceMass
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientNonflatness
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientCurvatureBounds
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Rigidity.Scalar

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instTopologicalSpaceM : TopologicalSpace F.M := F.topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instTopologicalSpaceM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instTopologicalSpaceM target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instChartedSpaceM : ChartedSpace H F.M := F.charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instChartedSpaceM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instChartedSpaceM target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instIsManifoldRealSomeENatTopM : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instIsManifoldRealSomeENatTopM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instIsManifoldRealSomeENatTopM target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instT2SpaceM : T2Space F.M := F.t2

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instT2SpaceM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instT2SpaceM target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instSigmaCompactSpaceM : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instSigmaCompactSpaceM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instSigmaCompactSpaceM target :: scope.openDecls } }

theorem asymptoticReducedVolume_lt_one_of_ancient
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M)
    {b : ℝ} (hb : b < 0) :
    asymptoticReducedVolume F.S b p < 1 := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : ConnectedSpace F.M := hF.connected
  obtain ⟨t, htb, ht, y, hy⟩ := hF.exists_rmNormSq_ne_zero_before b
  have hsqrt : 0 < Real.sqrt (F.rmNormSq (I := I) t y) := by
    apply Real.sqrt_pos.2
    exact lt_of_le_of_ne
      (by
        simpa only [PointedFlowData.rmNormSq, SolutionOn.family] using
          normSq0S_nonneg (I := I) (F.S.base.metric t) y 4 (F.S.base.rm04 t y))
      (Ne.symm hy)
  have hscalar : 0 < F.S.scalar t y := by
    have hbound := hF.rmNorm_le_scalar t ht y
    by_contra h
    have hnonpos : (Module.finrank ℝ E : ℝ) ^ 2 * F.S.scalar t y ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (le_of_not_gt h)
    exact (not_lt_of_ge (hbound.trans hnonpos)) hsqrt
  let s : ℝ := b - t
  have hs : 0 < s := sub_pos.mpr htb
  have htime : b - s = t := by
    dsimp only [s]
    ring
  have hbmem : b ∈ D.carrier := by
    simpa only [hF.carrier_eq, _root_.Set.mem_Iic] using hb.le
  have hcomplete : RiemannianMetricComplete (I := I) (F.S.base.metric b) :=
    ⟨hF.complete b hbmem⟩
  have hslab : _root_.Set.Icc (b - 2 * s) b ⊆ D.regular := by
    intro u hu
    simpa only [hF.regular_eq, _root_.Set.mem_Iio] using hu.2.trans_lt hb
  obtain ⟨K, hK⟩ := hF.exists_rmNormSq_le
  have hstrict : intrinsicReducedVolume F.S b p (2 * s) < 1 := by
    change redVolume F.S b p (2 * s) < 1
    apply redVolume_lt_one_of_scalar_ne_zero F.S F.isSolution b hcomplete p
      (fun _ _ hreg => ⟨K, fun u hu z => hK u (D.regular_subset (hreg hu)) z⟩)
      hs (by linarith only [hs]) hslab y
    rw [htime]
    exact hscalar.ne'
  have hinf : asymptoticReducedVolume F.S b p ≤
      intrinsicReducedVolume F.S b p (2 * s) :=
    iInf_le (fun tau : _root_.Set.Ioi (0 : ℝ) => intrinsicReducedVolume F.S b p tau)
      ⟨2 * s, mul_pos (by norm_num) hs⟩
  exact hinf.trans_lt hstrict

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.asymptoticReducedVolume_lt_one_of_ancient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.asymptoticReducedVolume_lt_one_of_ancient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.asymptoticReducedVolume_lt_one_of_ancient ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.asymptoticReducedVolume_lt_one_of_ancient

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
