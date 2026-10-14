import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointRicciSoliton
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointTerminalNormalization
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientRegularPoleMonotonicity
import Mathlib.Tactic.Choose
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Monotonicity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open _root_.Filter _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Geometry _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology _root_.ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
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
  PointedRiemannianManifold.t2TangentBundle

namespace HalfLineMetricConvergenceData

theorem poleEndpoint_redLength_limit_exists_terminal_normalized_soliton_of_ancient
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps
      (poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma) P phi)
    (R : SmoothRiemannianMetric I P.M) (hR : RiemannianMetricComplete R)
    (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (hcomplete : MetricComplete
      ({ P with metric := co.gInf 0 } : PointedRiemannianManifold I))
    (hboundary : BoundarylessManifold I P.M)
    (kappa : ℕ → ℝ) (hF : ∀ i, IsAncientKappaSolution (kappa i)
      ((poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma).term i))
    (hb : b < 0) {kappa0 : ℝ} (hAncient : IsAncientKappaSolution kappa0 F)
    (p : F.M) {A : ℝ}
    (hbase : ∀ i, redLength
      ((poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma).term i).S 0 p (q i) 1 ≤ A)
    (hescape : _root_.Filter.Tendsto tau _root_.Filter.atTop _root_.Filter.atTop) (hphi : StrictMono phi)
    (psi : ℕ → ℕ) (hpsi : StrictMono psi) (ellC : C(P.M × _root_.Set.Ici (1 : ℝ), ℝ))
    (hconv : TendstoLocallyUniformly
      (fun k (z : P.M × _root_.Set.Ici (1 : ℝ)) =>
        redLength ((poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma).term
          (phi (co.φ (psi k)))).S 0 p
          (Phi.map (co.φ (psi k)) z.1) z.2) ellC _root_.Filter.atTop) :
    ∃ hf₁ : ContMDiff I 𝓘(ℝ) ∞ (fun x => ellC (x, ⟨1, (le_rfl : (1 : ℝ) ≤ 1)⟩)),
    let f₁ : C^∞⟮I, P.M; ℝ⟯ := ⟨fun x => ellC (x, ⟨1, (le_rfl : (1 : ℝ) ≤ 1)⟩), hf₁⟩
    gradientRicciSoliton (co.gInf 0) f₁ 1 ∧
      hamiltonNormalized (co.gInf 0) f₁ 1 ∧
      IsHamiltonNormalizedPotential (co.gInf 0) f₁ ∧
      normalizedShrinkerMass (co.gInf 0) f₁ = asymptoticReducedVolume F.S b p := by
  classical
  let _ : NeZero (Module.finrank ℝ E) := by
    obtain ⟨t, _, x, hx⟩ := hAncient.notFlat
    exact ⟨DifferentialGeometry.Tensor0SBundle.finrank_ne_zero_of_normSq0S_ne_zero
      (F.S.base.metric t) x (by decide : 0 < 4) (F.S.base.rm04 t x) hx⟩
  let ell : P.M × ℝ → ℝ :=
    fun z => ellC (z.1, ⟨max 1 z.2, (le_max_left (1 : ℝ) z.2)⟩)
  have hagree (y : P.M) (t : ℝ) (ht : 1 ≤ t) :
      ell (y, t) = ellC (y, ⟨t, ht⟩) := by
    simp only [ell, max_eq_right ht]
  have hinterior (t : ℝ) (ht : 1 < t) :
      ∃ hf : ContMDiff I 𝓘(ℝ) ∞ (fun x => ellC (x, ⟨t, ht.le⟩)),
        gradientRicciSoliton (co.gInf (1 - t))
          (⟨fun x => ellC (x, ⟨t, ht.le⟩), hf⟩ : C^∞⟮I, P.M; ℝ⟯) (1 / t) ∧
        hamiltonNormalized (co.gInf (1 - t))
          (⟨fun x => ellC (x, ⟨t, ht.le⟩), hf⟩ : C^∞⟮I, P.M; ℝ⟯) (1 / t) := by
    obtain ⟨hf, hsol, hnormal⟩ :=
      poleEndpoint_redLength_limit_gradientRicciSoliton_and_hamiltonNormalized
        F hcar hreg b hbmem tau q hsigma Phi R hR bf hsrc htgt co
        hcomplete hboundary kappa hF hb hAncient p hbase hescape hphi
        psi hpsi ellC hconv ell hagree ht
    have hslice : (fun x => ell (x, t)) = (fun x => ellC (x, ⟨t, ht.le⟩)) := by
      funext x
      exact hagree x t ht.le
    have hf' : ContMDiff I 𝓘(ℝ) ∞ (fun x => ellC (x, ⟨t, ht.le⟩)) := by
      rwa [hslice] at hf
    have hbundle : (⟨fun x => ell (x, t), hf⟩ : C^∞⟮I, P.M; ℝ⟯) =
        ⟨fun x => ellC (x, ⟨t, ht.le⟩), hf'⟩ := by
      ext x
      exact hagree x t ht.le
    rw [hbundle] at hsol hnormal
    exact ⟨hf', hsol, hnormal⟩
  choose hsmooth hsol hnormal using hinterior
  have hmono : AntitoneOn (intrinsicReducedVolume F.S b p) (_root_.Set.Ioi 0) :=
    hAncient.reducedVolume_antitone_of_regular_base p (by
      rw [hreg]
      exact hb)
  have hindex : _root_.Filter.Tendsto (fun k => phi (co.φ (psi k))) _root_.Filter.atTop atTop :=
    hphi.tendsto_atTop.comp (co.strictMono.tendsto_atTop.comp hpsi.tendsto_atTop)
  have htau := hescape.comp hindex
  have hselected : _root_.Filter.Tendsto (fun k => tau (phi (co.φ (psi k))) + b) _root_.Filter.atTop atTop := by
    apply tendsto_atTop.mpr
    intro C
    filter_upwards [htau.eventually_ge_atTop (C - b)] with k hk
    exact sub_le_iff_le_add.mp hk
  exact poleEndpoint_redLength_limit_exists_terminal_normalized_soliton
    F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hF p hbase hmono
      psi hpsi hselected ellC hconv hcomplete hsmooth hsol
      (fun t ht x => by
        simpa only [normGradSqFun_def, ContMDiffMap.coeFn_mk] using hnormal t ht x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.poleEndpoint_redLength_limit_exists_terminal_normalized_soliton_of_ancient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.poleEndpoint_redLength_limit_exists_terminal_normalized_soliton_of_ancient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.poleEndpoint_redLength_limit_exists_terminal_normalized_soliton_of_ancient ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.poleEndpoint_redLength_limit_exists_terminal_normalized_soliton_of_ancient

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
