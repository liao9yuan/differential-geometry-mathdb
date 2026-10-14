import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointHamiltonJacobiQuadratic
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointJointLipschitz
import Submission.DifferentialGeometry.Analysis.Integration.Integral.LipschitzIntegrationByParts

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology _root_.ENNReal

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

private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.instBorelSpace_differentialGeometry target :: scope.openDecls } }

local notation "U" => poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma
local notation "Y" => poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma

namespace HalfLineMetricConvergenceData

theorem eventually_poleEndpoint_redLength_weak_hamilton_jacobi
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi) (R : SmoothRiemannianMetric I P.M)
    (hR : RiemannianMetricComplete R)
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {J : Set P.M} (hJ : IsCompact J) {A a c : ℝ} (ha : 1 ≤ a)
    (hbase : ∀ᶠ k in _root_.Filter.atTop, redLength ((U).term (phi (co.φ k))).S 0 p
      (q (phi (co.φ k))) 1 ≤ A)
    (x : P.M) {W : Set E} (hW : IsOpen W) (hWt : W ⊆ (extChartAt I x).target)
    (hWJ : _root_.Set.MapsTo (extChartAt I x).symm W J)
    (ψ : E × ℝ → ℝ) (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ)
    (hψW : tsupport ψ ⊆ W ×ˢ _root_.Set.Ioo a c) :
    ∀ᶠ k in _root_.Filter.atTop,
      let ν := (DifferentialGeometry.Integral.Measure.modelHaar (E := E)).prod
        (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ)
      let f := fun z : E × ℝ => redLength ((U).term (phi (co.φ k))).S 0 p
        (Phi.map (co.φ k) ((extChartAt I x).symm z.1)) z.2
      let d := fun z => (fderiv ℝ f z).comp (ContinuousLinearMap.inl ℝ E ℝ)
      ∫ z, f z * fderiv ℝ ψ z (0, 1) ∂ν =
        ∫ z, ((1 / 2 : ℝ) *
          chartGradientBilin (gSeqExt Phi R bf hsrc htgt (co.φ k) (1 - z.2)) x
            ((extChartAt I x).symm z.1) (d z) (d z) -
          (1 / 2 : ℝ) * ((Y).term (phi (co.φ k))).S.scalar (1 - z.2)
            (Phi.map (co.φ k) ((extChartAt I x).symm z.1)) +
          f z / (2 * z.2)) * ψ z ∂ν := by
  have hlip := eventually_locallyLipschitzOn_poleEndpoint_redLength_chart
    F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hJ (c := c) ha hbase
    x hWt hWJ
  have hhj := eventually_ae_poleEndpoint_redLength_hamilton_jacobi_eq_chartGradientBilin
    F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hJ (c := c) ha hbase
    x hW hWt hWJ
  filter_upwards [hlip, hhj] with k hkLip hkHJ
  let ν := (DifferentialGeometry.Integral.Measure.modelHaar (E := E)).prod
    (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ)
  let f := fun z : E × ℝ => redLength ((U).term (phi (co.φ k))).S 0 p
    (Phi.map (co.φ k) ((extChartAt I x).symm z.1)) z.2
  let d := fun z => (fderiv ℝ f z).comp (ContinuousLinearMap.inl ℝ E ℝ)
  let H := fun z => (1 / 2 : ℝ) *
      chartGradientBilin (gSeqExt Phi R bf hsrc htgt (co.φ k) (1 - z.2)) x
        ((extChartAt I x).symm z.1) (d z) (d z) -
      (1 / 2 : ℝ) * ((Y).term (phi (co.φ k))).S.scalar (1 - z.2)
        (Phi.map (co.φ k) ((extChartAt I x).symm z.1)) + f z / (2 * z.2)
  have hf : LocallyLipschitzOn (W ×ˢ _root_.Set.Ioo a c) f :=
    hkLip.mono (Set.prod_mono Subset.rfl _root_.Set.Ioo_subset_Icc_self)
  have hibp := hf.integral_fderiv_mul_eq_neg_mul_fderiv (μ := ν)
    (hW.prod isOpen_Ioo) hψ hψc hψW (0, 1)
  have hnegative : (fun z => fderiv ℝ f z (0, 1) * ψ z) =ᵐ[ν]
      (fun z => -(H z * ψ z)) := by
    filter_upwards [hkHJ] with z hz
    by_cases hψz : ψ z = 0
    · simp only [hψz, _root_.MulZeroClass.mul_zero, neg_zero]
    · have hzw : z ∈ W ×ˢ _root_.Set.Ioo a c := hψW (subset_tsupport ψ hψz)
      have heq : fderiv ℝ f z (0, 1) + H z = 0 := by
        have hsource := hz hzw
        dsimp only at hsource
        dsimp only [H, f, d]
        linarith only [hsource]
      have hd : fderiv ℝ f z (0, 1) = -H z := by linarith
      rw [hd, neg_mul]
  change (∫ z, f z * fderiv ℝ ψ z (0, 1) ∂ν) = ∫ z, H z * ψ z ∂ν
  have heq := _root_.MeasureTheory.integral_congr_ae hnegative
  rw [_root_.MeasureTheory.integral_neg] at heq
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.eventually_poleEndpoint_redLength_weak_hamilton_jacobi then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.eventually_poleEndpoint_redLength_weak_hamilton_jacobi"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.eventually_poleEndpoint_redLength_weak_hamilton_jacobi ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.eventually_poleEndpoint_redLength_weak_hamilton_jacobi

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
