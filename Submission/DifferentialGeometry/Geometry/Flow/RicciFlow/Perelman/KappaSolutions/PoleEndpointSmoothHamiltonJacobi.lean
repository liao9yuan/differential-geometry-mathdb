import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointHamiltonJacobiTimeChart
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.HalfLineGradientCoefficients
import Submission.DifferentialGeometry.Geometry.Operator.TimeLaplacian
import Mathlib.MeasureTheory.Measure.OpenPos

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open _root_.Filter _root_.Set _root_.Submission.Set _root_.TopologicalSpace _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Analysis.Calculus
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology _root_.ENNReal

section Continuity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedFlowSeq (I := I)} {P : PointedRiemannianManifold (I := I)}
  {φ : ℕ → ℕ}

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

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

private local instance covectorNormedAddCommGroupContinuity : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.covectorNormedAddCommGroupContinuity
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.covectorNormedAddCommGroupContinuity target :: scope.openDecls } }

private local instance covectorNormedSpaceContinuity : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.covectorNormedSpaceContinuity
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.covectorNormedSpaceContinuity target :: scope.openDecls } }

private local instance covectorDualNormedAddCommGroupContinuity :
    NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.covectorDualNormedAddCommGroupContinuity
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.covectorDualNormedAddCommGroupContinuity target :: scope.openDecls } }

private local instance covectorDualNormedSpaceContinuity : NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.covectorDualNormedSpaceContinuity
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.covectorDualNormedSpaceContinuity target :: scope.openDecls } }

private local instance covectorBilinNormedAddCommGroupContinuity :
    NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.covectorBilinNormedAddCommGroupContinuity
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.covectorBilinNormedAddCommGroupContinuity target :: scope.openDecls } }

private local instance covectorBilinNormedSpaceContinuity :
    NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.covectorBilinNormedSpaceContinuity
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.covectorBilinNormedSpaceContinuity target :: scope.openDecls } }

private theorem continuousOn_halfLine_hamilton_jacobi_residual
    (Phi : PointedCGHMaps X P φ) {R : SmoothRiemannianMetric I P.M}
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (hYreg : _root_.Set.Iio (0 : ℝ) ⊆ X.D.regular) {a c : ℝ} (ha : 1 < a)
    (x : P.M) {W : Set E} (hW : IsOpen W) (hWt : W ⊆ (extChartAt I x).target)
    {f : ℝ × E → ℝ} (hf : ContDiffOn ℝ ∞ f (_root_.Set.Ioo a c ×ˢ W)) :
    ContinuousOn (fun z : ℝ × E => deriv (fun s => f (s, z.2)) z.1 +
      (1 / 2 : ℝ) * chartGradientBilin (co.gInf (1 - z.1)) x
        ((extChartAt I x).symm z.2)
        (fderiv ℝ (fun y : E => f (z.1, y)) z.2)
        (fderiv ℝ (fun y : E => f (z.1, y)) z.2) -
      (1 / 2 : ℝ) * metricScalarAt (co.gInf (1 - z.1)) ((extChartAt I x).symm z.2) +
      f z / (2 * z.1)) (_root_.Set.Ioo a c ×ˢ W) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let Ω : Set (ℝ × E) := _root_.Set.Ioo a c ×ˢ W
  let d : ℝ × E → E →L[ℝ] ℝ :=
    fun z => fderiv ℝ (fun y : E => f (z.1, y)) z.2
  let B := fun z : ℝ × E => chartGradientBilin (co.gInf (1 - z.1)) x
    ((extChartAt I x).symm z.2)
  let S := fun z : ℝ × E =>
    metricScalarAt (co.gInf (1 - z.1)) ((extChartAt I x).symm z.2)
  let HJ := fun z : ℝ × E => deriv (fun s => f (s, z.2)) z.1 +
    (1 / 2 : ℝ) * B z (d z) (d z) - (1 / 2 : ℝ) * S z + f z / (2 * z.1)
  have hΩ : IsOpen Ω := isOpen_Ioo.prod hW
  have hd : ContinuousOn d Ω :=
    (DifferentialGeometry.Analysis.spatialFDeriv_contDiffOn
      (G := fun t y => f (t, y)) isOpen_Ioo.uniqueDiffOn hW hf).continuousOn
  have hdt : ContinuousOn (fun z : ℝ × E => deriv (fun s => f (s, z.2)) z.1) Ω := by
    have hfd : ContinuousOn (fderiv ℝ f) Ω :=
      hf.continuousOn_fderiv_of_isOpen hΩ (by simp)
    apply (hfd.clm_apply (continuousOn_const (c := (1, (0 : E))))).congr
    intro z hz
    have hdiff := (hf.differentiableOn (by simp) z hz).differentiableAt (hΩ.mem_nhds hz)
    have htime := (hdiff.hasFDerivAt.comp z.1
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) z.1 z.2)).hasDerivAt.deriv
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inl_apply] using htime
  have hlag (z : ℝ × E) (hz : z ∈ Ω) : 1 - z.1 < 0 := by
    have ht : 1 < z.1 := ha.trans hz.1.1
    linarith
  have hB : ContinuousOn B Ω := by
    apply (co.continuousOn_chartGradientBilin (Φ := Phi) hYreg x).comp
      ((continuous_const.sub continuous_fst).prodMk continuous_snd).continuousOn
    intro z hz
    exact ⟨hlag z hz, hWt hz.2⟩
  have hscalar : ContinuousOn (fun z : ℝ × P.M => metricScalarAt (co.gInf z.1) z.2)
      (_root_.Set.Iio (0 : ℝ) ×ˢ _root_.Set.univ) :=
    DifferentialGeometry.PDE.RicciFlow.scalarCont_of_joint co.gInf (_root_.Set.Iio 0)
      isOpen_Iio.uniqueDiffOn
        (HalfLineMetricConvergenceData.gramSmooth (I := I) (Φ := Phi) co hYreg)
  have hS : ContinuousOn S Ω := by
    have hchart : ContinuousOn (fun z : ℝ × E => (extChartAt I x).symm z.2) Ω :=
      (continuousOn_extChartAt_symm (I := I) x).comp continuous_snd.continuousOn
        (fun z hz => hWt hz.2)
    let ψ : ℝ × E → ℝ × P.M := fun z => (1 - z.1, (extChartAt I x).symm z.2)
    have hψ : ContinuousOn ψ Ω :=
      (continuous_const.sub continuous_fst).continuousOn.prodMk hchart
    have hmaps : _root_.Set.MapsTo ψ Ω (_root_.Set.Iio (0 : ℝ) ×ˢ (_root_.Set.univ : Set P.M)) :=
      fun z hz => ⟨hlag z hz, _root_.Set.mem_univ _⟩
    have hcomp := hscalar.comp hψ hmaps
    simpa only [Function.comp_def, ψ, S] using hcomp
  have hquad : ContinuousOn (fun z => B z (d z) (d z)) Ω :=
    (hB.clm_apply hd).clm_apply hd
  have hH : ContinuousOn HJ Ω := by
    apply ((hdt.add (hquad.const_mul (1 / 2))).sub (hS.const_mul (1 / 2))).add
    exact hf.continuousOn.div (continuousOn_const.mul continuous_fst.continuousOn)
      (fun z hz => mul_ne_zero (by norm_num) (ne_of_gt ((zero_lt_one.trans ha).trans hz.1.1)))
  exact hH

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.continuousOn_halfLine_hamilton_jacobi_residual
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.continuousOn_halfLine_hamilton_jacobi_residual target :: scope.openDecls } }

end Continuity

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
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

private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instBorelSpace_differentialGeometry_1 : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

private local instance covectorNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.covectorNormedAddCommGroup
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.covectorNormedAddCommGroup target :: scope.openDecls } }

private local instance covectorNormedSpace : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.covectorNormedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.covectorNormedSpace target :: scope.openDecls } }

private local instance covectorDualNormedAddCommGroup : NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.covectorDualNormedAddCommGroup
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.covectorDualNormedAddCommGroup target :: scope.openDecls } }

private local instance covectorDualNormedSpace : NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.covectorDualNormedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.covectorDualNormedSpace target :: scope.openDecls } }

private local instance covectorBilinNormedAddCommGroup :
    NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.covectorBilinNormedAddCommGroup
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.covectorBilinNormedAddCommGroup target :: scope.openDecls } }

private local instance covectorBilinNormedSpace :
    NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.covectorBilinNormedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.covectorBilinNormedSpace target :: scope.openDecls } }

namespace HalfLineMetricConvergenceData

theorem poleEndpoint_redLength_limit_hamilton_jacobi_of_contMDiffOn
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi)
    (R : SmoothRiemannianMetric I P.M) (hR : RiemannianMetricComplete R)
    (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (hcomplete : MetricComplete
      ({ P with metric := co.gInf 0 } : PointedRiemannianManifold I))
    (hboundary : BoundarylessManifold I P.M)
    (kappa : ℕ → ℝ) (hF : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {J : Set P.M} (hJ : IsCompact J) {a c A : ℝ}
    (ha : 1 < a)
    (hbase : ∀ᶠ k in _root_.Filter.atTop, redLength ((U).term (phi (co.φ k))).S 0
      p (q (phi (co.φ k))) 1 ≤ A)
    (rho : ℕ → ℕ) (hrho : _root_.Filter.Tendsto rho _root_.Filter.atTop _root_.Filter.atTop)
    (ell : P.M × ℝ → ℝ)
    (hconv : ∀ y ∈ J, ∀ t ∈ _root_.Set.Icc a c,
      _root_.Filter.Tendsto (fun k => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) y) t) _root_.Filter.atTop (𝓝 (ell (y, t))))
    (x : P.M) {W : Set E} (hW : IsOpen W)
    (hWt : W ⊆ (extChartAt I x).target)
    (hWJ : _root_.Set.MapsTo (extChartAt I x).symm W J)
    (hell : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × P.M => ell (z.2, z.1)) (_root_.Set.Ioo a c ×ˢ _root_.Set.univ)) :
    ∀ t ∈ _root_.Set.Ioo a c, ∀ y ∈ W,
      2 * deriv (fun s => ell ((extChartAt I x).symm y, s)) t +
        (co.gInf (1 - t)).inner ((extChartAt I x).symm y)
          (gradientFun (I := I) (co.gInf (1 - t)) (fun z => ell (z, t))
            ((extChartAt I x).symm y))
          (gradientFun (I := I) (co.gInf (1 - t)) (fun z => ell (z, t))
            ((extChartAt I x).symm y)) -
        metricScalarAt (co.gInf (1 - t)) ((extChartAt I x).symm y) +
        ell ((extChartAt I x).symm y, t) / t = 0 := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let ν := (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ).prod (modelHaar (E := E))
  let Ω : Set (ℝ × E) := _root_.Set.Ioo a c ×ˢ W
  let f : ℝ × E → ℝ := fun z => ell ((extChartAt I x).symm z.2, z.1)
  let d : ℝ × E → E →L[ℝ] ℝ :=
    fun z => fderiv ℝ (fun y : E => f (z.1, y)) z.2
  let B := fun z : ℝ × E => chartGradientBilin (co.gInf (1 - z.1)) x
    ((extChartAt I x).symm z.2)
  let S := fun z : ℝ × E =>
    metricScalarAt (co.gInf (1 - z.1)) ((extChartAt I x).symm z.2)
  let HJ := fun z : ℝ × E => deriv (fun s => f (s, z.2)) z.1 +
    (1 / 2 : ℝ) * B z (d z) (d z) - (1 / 2 : ℝ) * S z + f z / (2 * z.1)
  have hΩ : IsOpen Ω := isOpen_Ioo.prod hW
  have hYreg : _root_.Set.Iio (0 : ℝ) ⊆ (Y).D.regular := by
    intro s hs
    change s ∈ ancientTimeInterval.regular
    simpa only [ancientTimeInterval_regular] using hs
  have hf : ContDiffOn ℝ ∞ f Ω := by
    have hchart := DifferentialGeometry.Tensor.Coordinates.scalarOnE_contDiffOn_prod
      (I := I) (f := fun t y => ell (y, t)) x hell
    exact hchart.mono (Set.prod_mono Subset.rfl hWt)
  have hH : ContinuousOn HJ Ω :=
    continuousOn_halfLine_hamilton_jacobi_residual Phi co hYreg ha x hW hWt hf
  have hae : ∀ᵐ z ∂ν, z ∈ Ω → HJ z = 0 :=
    ae_poleEndpoint_redLength_limit_hamilton_jacobi_time_chart
      F hcar hreg b hbmem tau q hsigma Phi R hR bf hsrc htgt co hcomplete hboundary
      kappa hF p hJ ha hbase rho hrho ell hconv x hW hWt hWJ
  have hzero : _root_.Set.EqOn HJ (fun _ => (0 : ℝ)) Ω :=
    MeasureTheory.Measure.eqOn_open_of_ae_eq
      ((_root_.MeasureTheory.ae_restrict_iff' hΩ.measurableSet).mpr hae) hΩ hH continuousOn_const
  intro t ht y hy
  have heq := hzero (x := (t, y)) ⟨ht, hy⟩
  have hsmooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun z => ell (z, t)) :=
    hell.comp_contMDiff (contMDiff_const.prodMk contMDiff_id)
      (fun z => ⟨ht, _root_.Set.mem_univ z⟩)
  have hxsource : (extChartAt I x).symm y ∈ (chartAt H x).source := by
    rw [← extChartAt_source_eq_chartAt_source (I := I)]
    exact (extChartAt I x).map_target (hWt hy)
  have hgrad := grad_norm_sq_eq_chartGradientBilin (I := I) (co.gInf (1 - t)) x
    (hsmooth.mdifferentiable (by simp) _) hxsource
  rw [(extChartAt I x).right_inv (hWt hy)] at hgrad
  change (co.gInf (1 - t)).inner ((extChartAt I x).symm y)
      (gradientFun (I := I) (co.gInf (1 - t)) (fun z => ell (z, t))
        ((extChartAt I x).symm y))
      (gradientFun (I := I) (co.gInf (1 - t)) (fun z => ell (z, t))
        ((extChartAt I x).symm y)) = B (t, y) (d (t, y)) (d (t, y)) at hgrad
  rw [hgrad]
  dsimp only [HJ, f, S] at heq
  have htne : t ≠ 0 := (lt_trans (zero_lt_one.trans ha) ht.1).ne'
  field_simp [htne] at heq ⊢
  nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.poleEndpoint_redLength_limit_hamilton_jacobi_of_contMDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.poleEndpoint_redLength_limit_hamilton_jacobi_of_contMDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.poleEndpoint_redLength_limit_hamilton_jacobi_of_contMDiffOn ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.poleEndpoint_redLength_limit_hamilton_jacobi_of_contMDiffOn

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
