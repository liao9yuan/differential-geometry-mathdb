import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.LocalLaplacianPullback
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.GradientPullback
import Submission.DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Differentiability
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RegularPoleLaplacianSupport
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
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.Submission.Topology

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

theorem eventually_exists_poleEndpoint_redLength_upper_support_laplacian_lt
    (Phi : PointedCGHMaps Y P phi) (R : SmoothRiemannianMetric I P.M)
    (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
    (hb : b < 0) (hg : RiemannianMetricComplete (F.S.base.metric b))
    {K : Set P.M} (hK : IsCompact K) :
    ∀ᶠ k in _root_.Filter.atTop, ∀ (p : F.M) (y : P.M), y ∈ K → ∀ s : ℝ, 0 < s →
      ∀ B : ℝ,
      (∀ t ∈ _root_.Set.Icc (b - s / (tau (phi k) + b)⁻¹) b, ∀ z : F.M,
        normSq0S (F.S.base.metric t) z 4 (F.S.base.rm04 t z) ≤ B) →
      ∀ alpha : ℝ → F.M, ContMDiff 𝓘(ℝ, ℝ) I 1 alpha →
        alpha 0 = p → alpha (Real.sqrt s) = Phi.map k y →
      MDifferentiableAt I 𝓘(ℝ, ℝ)
        (fun z => redLength ((U).term (phi k)).S 0 p (Phi.map k z) s) y →
      ∀ epsilon : ℝ, 0 < epsilon →
      ∃ V : Set P.M, IsOpen V ∧ y ∈ V ∧
        ∃ f : P.M → ℝ, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f V ∧
          f y = redLength ((U).term (phi k)).S 0 p (Phi.map k y) s ∧
          (∀ z ∈ V, redLength ((U).term (phi k)).S 0 p (Phi.map k z) s ≤ f z) ∧
          laplacian (LeviCivita (gSeqExt Phi R bf hsrc htgt k (1 - s)))
            (gSeqExt Phi R bf hsrc htgt k (1 - s)) f y <
              (1 / 2 : ℝ) * normGradSqFun (gSeqExt Phi R bf hsrc htgt k (1 - s))
                (fun z => redLength ((U).term (phi k)).S 0 p (Phi.map k z) s) y -
              (1 / 2 : ℝ) * ((U).term (phi k)).S.scalar (-s) (Phi.map k y) +
              ((Module.finrank ℝ E : ℝ) -
                redLength ((U).term (phi k)).S 0 p (Phi.map k y) s) / (2 * s) +
              epsilon := by
  let : TopologicalSpace.MetrizableSpace F.M := Manifold.metrizableSpace I F.M
  let : PseudoMetricSpace F.M := TopologicalSpace.pseudoMetrizableSpacePseudoMetric F.M
  filter_upwards [eventually_gSeqExt_eq_pullback Phi R bf hsrc htgt K hK,
    eventually_laplacian_gSeqExt_comp_map Phi R bf hsrc htgt hK,
    eventually_normGradSqFun_gSeqExt_eq_on_compact Phi R bf hsrc htgt hK]
    with k hk hlap hgrad
  intro p y hy s hs B hB alpha halpha hstart hend hdiff epsilon hepsilon
  obtain ⟨W, hW, hKW, hWs, _⟩ := hk
  have hys : y ∈ Phi.source k := hWs (hKW hy)
  have hlocal := (Phi.partialDiffeomorph k).isLocalDiffeomorphAt I I ∞ hys
  have htarget : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun z => redLength ((U).term (phi k)).S 0 p z s) (Phi.map k y) :=
    hlocal.mdifferentiableAt_of_comp (by simp) hdiff
  obtain ⟨V, hV, hyV, f, hf, hcontact, hupper, _, hbound⟩ :=
    exists_curvatureNormalizedSolution_redLength_upper_support_laplacian_lt
      F.S F.isSolution hreg b (tau (phi k) + b)⁻¹ B hb
      (inv_pos.mpr (hsigma (phi k))) hbmem hg p (Phi.map k y) s hs hB
      alpha halpha hstart hend htarget hepsilon
  have hmetric : ((Y).term (phi k)).S.base.metric (1 - s) =
      ((U).term (phi k)).S.base.metric (-s) := by
    rw [poleEndpointRescaledFlowSeq_metric_eq_shift]
    congr 1
    ring
  have hPhi : ContMDiffOn I I ∞ (Phi.map k) (Phi.source k) :=
    (Phi.partialDiffeomorph k).contMDiffOn
  let V' : Set P.M := Phi.source k ∩ Phi.map k ⁻¹' V
  have hV' : IsOpen V' :=
    hPhi.continuousOn.isOpen_inter_preimage (Phi.source_open k) hV
  have hf' : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (f ∘ Phi.map k) V' :=
    hf.comp (hPhi.mono _root_.Set.inter_subset_left) _root_.Set.inter_subset_right
  refine ⟨V', hV', ⟨hys, hyV⟩, f ∘ Phi.map k, hf', hcontact,
    (fun z hz => hupper (Phi.map k z) hz.2), ?_⟩
  have hlap' := hlap (1 - s) f V hV hf y hy hyV
  have hgrad' := hgrad (1 - s) y hy
    (fun z => redLength ((U).term (phi k)).S 0 p z s) htarget
  rw [hmetric] at hlap' hgrad'
  erw [hlap', hgrad']
  exact hbound

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.eventually_exists_poleEndpoint_redLength_upper_support_laplacian_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.eventually_exists_poleEndpoint_redLength_upper_support_laplacian_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.eventually_exists_poleEndpoint_redLength_upper_support_laplacian_lt ``Submission.DifferentialGeometry.CheegerGromovCompactness.eventually_exists_poleEndpoint_redLength_upper_support_laplacian_lt

end DifferentialGeometry.CheegerGromovCompactness
