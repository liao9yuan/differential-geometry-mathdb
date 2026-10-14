import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointSqrtLipschitz
import Submission.DifferentialGeometry.Geometry.Operator.Gradient.SqrtLipschitz

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open _root_.Filter _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology _root_.ENNReal _root_.NNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
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
private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instT2SpaceM_2 : T2Space F.M := F.t2

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.instT2SpaceM_2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.instT2SpaceM_2 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instSigmaCompactSpaceM_2 : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.instSigmaCompactSpaceM_2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.instSigmaCompactSpaceM_2 target :: scope.openDecls } }

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

local notation "U" => poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma
local notation "Y" => poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma

theorem HalfLineMetricConvergenceData.redLength_limit_gradient_norm_le
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi) {R : SmoothRiemannianMetric I P.M}
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {s : ℝ} (hs : 1 ≤ s)
    (rho : ℕ → ℕ) (hrho : _root_.Filter.Tendsto rho _root_.Filter.atTop _root_.Filter.atTop) (ell : P.M → ℝ)
    (hconv : ∀ y, _root_.Filter.Tendsto (fun k => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
      (Phi.map (co.φ (rho k)) y) s) _root_.Filter.atTop (𝓝 (ell y)))
    (hcomplete : MetricComplete (I := I)
      ({ P with metric := co.gInf (1 - s) } : PointedRiemannianManifold (I := I)))
    (x : P.M) :
    Real.sqrt ((co.gInf (1 - s)).inner x
      (gradientFun (co.gInf (1 - s)) ell x) (gradientFun (co.gInf (1 - s)) ell x)) ≤
      Real.sqrt 3 / Real.sqrt s * Real.sqrt (ell x) := by
  have hs0 : 0 < s := zero_lt_one.trans_le hs
  have hnonneg (y : P.M) : 0 ≤ ell y := by
    apply ge_of_tendsto (hconv y)
    apply Eventually.of_forall
    intro k
    let i := phi (co.φ (rho k))
    obtain ⟨C, hC⟩ := (hancient i).globalScalarBound
    apply div_nonneg _ (by positivity)
    apply lCost_nonneg_of_scalar_nonneg ((U).term i).S 0 hs0.le
    intro r hr z
    simpa only [zero_sub] using (hC (-r) (by
      rw [ancientTimeInterval_carrier]
      exact neg_nonpos.mpr hr.1) z).1
  let L : ℝ≥0 := ⟨Real.sqrt 3 / (2 * Real.sqrt s), by positivity⟩
  have hlip : ∀ y z, _root_.EDist.edist (Real.sqrt (ell y)) (Real.sqrt (ell z)) ≤
      (L : ℝ≥0∞) * riemannianEDistOf (co.gInf (1 - s)) y z := by
    intro y z
    have hyz := co.sqrt_redLength_limit_sub_le_distance F hcar hreg b hbmem tau q hsigma
      Phi kappa hancient p hs rho hrho ell hconv hcomplete y z
    have hzy := co.sqrt_redLength_limit_sub_le_distance F hcar hreg b hbmem tau q hsigma
      Phi kappa hancient p hs rho hrho ell hconv hcomplete z y
    rw [riemannianEDistOf_comm (co.gInf (1 - s)) z y] at hzy
    have hdist : |Real.sqrt (ell y) - Real.sqrt (ell z)| ≤
        (L : ℝ) * (riemannianEDistOf (co.gInf (1 - s)) y z).toReal := by
      change |Real.sqrt (ell y) - Real.sqrt (ell z)| ≤
        Real.sqrt 3 / (2 * Real.sqrt s) * _
      exact abs_le.mpr ⟨by linarith only [hyz], by linarith only [hzy]⟩
    rw [edist_dist, Real.dist_eq]
    have he := ENNReal.ofReal_le_ofReal hdist
    rw [ENNReal.ofReal_mul (NNReal.coe_nonneg L), ENNReal.ofReal_coe_nnreal,
      ENNReal.ofReal_toReal (DifferentialGeometry.riemannianEDistOf_ne_top
        (co.gInf (1 - s)) y z)] at he
    exact he
  have hgrad := gradient_norm_le_of_sqrt_lipschitz (co.gInf (1 - s)) hnonneg hlip x
  have hcoef : 2 * (L : ℝ) = Real.sqrt 3 / Real.sqrt s := by
    change 2 * (Real.sqrt 3 / (2 * Real.sqrt s)) = Real.sqrt 3 / Real.sqrt s
    ring
  rwa [hcoef] at hgrad

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.redLength_limit_gradient_norm_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.redLength_limit_gradient_norm_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.redLength_limit_gradient_norm_le ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.redLength_limit_gradient_norm_le

end DifferentialGeometry.CheegerGromovCompactness
