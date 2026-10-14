import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointGradientBound
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointMetricOrder
import Submission.DifferentialGeometry.Geometry.Metric.Distance.RadialCutoff
import Submission.DifferentialGeometry.Geometry.Operator.Gradient.ChartPairing

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
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Tensor.Coordinates
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

theorem HalfLineMetricConvergenceData.abs_inner_redLength_limit_gradient_radialDistanceCutoff_le
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi) {R : SmoothRiemannianMetric I P.M}
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {a s : ℝ} (ha : 1 ≤ a) (has : a ≤ s)
    (rho : ℕ → ℕ) (hrho : _root_.Filter.Tendsto rho _root_.Filter.atTop _root_.Filter.atTop) (ell : P.M → ℝ)
    (hconv : ∀ y, _root_.Filter.Tendsto (fun k => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
      (Phi.map (co.φ (rho k)) y) s) _root_.Filter.atTop (𝓝 (ell y)))
    (hcomplete : MetricComplete (I := I)
      ({ P with metric := co.gInf (1 - s) } : PointedRiemannianManifold (I := I)))
    (z : P.M) {r : ℝ} (hr : 0 < r) (x : P.M) :
    |(co.gInf (1 - s)).inner x
        (gradientFun (co.gInf (1 - s)) ell x)
        (gradientFun (co.gInf (1 - s))
          (radialDistanceCutoff (co.gInf (1 - a)) z r) x)| ≤
      (Real.sqrt 3 / Real.sqrt a / r) * Real.sqrt (ell x) := by
  have hg := co.redLength_limit_gradient_norm_le F hcar hreg b hbmem tau q hsigma
    Phi kappa hancient p (ha.trans has) rho hrho ell hconv hcomplete x
  have hc := gradient_radialDistanceCutoff_norm_le_of_metric_le
    (co.gInf (1 - a)) (co.gInf (1 - s))
    (co.metric_inner_le_at_reflected_times F hcar hreg b hbmem tau q hsigma
      Phi kappa hancient ha has) z hr x
  have hinner := DifferentialGeometry.Analysis.Laplacian.abs_metric_inner_le_sqrt_metric_quadratic
    (co.gInf (1 - s)) x
    (gradientFun (co.gInf (1 - s)) ell x)
    (gradientFun (co.gInf (1 - s)) (radialDistanceCutoff (co.gInf (1 - a)) z r) x)
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  have hcoef : Real.sqrt 3 / Real.sqrt s ≤ Real.sqrt 3 / Real.sqrt a :=
    div_le_div_of_nonneg_left (Real.sqrt_nonneg 3) (Real.sqrt_pos.mpr ha0)
      (Real.sqrt_le_sqrt has)
  calc
    _ ≤ _ := hinner
    _ ≤ (Real.sqrt 3 / Real.sqrt s * Real.sqrt (ell x)) * (1 / r) :=
      mul_le_mul hg hc (Real.sqrt_nonneg _) (by positivity)
    _ ≤ (Real.sqrt 3 / Real.sqrt a * Real.sqrt (ell x)) * (1 / r) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoef (Real.sqrt_nonneg _)) (by positivity)
    _ = _ := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.abs_inner_redLength_limit_gradient_radialDistanceCutoff_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.abs_inner_redLength_limit_gradient_radialDistanceCutoff_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.abs_inner_redLength_limit_gradient_radialDistanceCutoff_le ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.abs_inner_redLength_limit_gradient_radialDistanceCutoff_le

theorem HalfLineMetricConvergenceData.abs_redDensity_limit_mul_inner_radialDistanceCutoff_le
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi) {R : SmoothRiemannianMetric I P.M}
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {a s : ℝ} (ha : 1 ≤ a) (has : a ≤ s)
    (rho : ℕ → ℕ) (hrho : _root_.Filter.Tendsto rho _root_.Filter.atTop _root_.Filter.atTop) (ell : P.M → ℝ)
    (hconv : ∀ y, _root_.Filter.Tendsto (fun k => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
      (Phi.map (co.φ (rho k)) y) s) _root_.Filter.atTop (𝓝 (ell y)))
    (hcomplete : MetricComplete (I := I)
      ({ P with metric := co.gInf (1 - s) } : PointedRiemannianManifold (I := I)))
    (z : P.M) {r : ℝ} (hr : 0 < r) (x : P.M) :
    |Real.exp (-ell x - ((Module.finrank ℝ E : ℝ) / 2) * Real.log s -
        ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi)) *
      (co.gInf (1 - s)).inner x
        (gradientFun (co.gInf (1 - s)) ell x)
        (gradientFun (co.gInf (1 - s))
          (radialDistanceCutoff (co.gInf (1 - a)) z r) x)| ≤
      (Real.sqrt 3 / Real.sqrt a / r) *
        (Real.sqrt (ell x) * Real.exp (-ell x - ((Module.finrank ℝ E : ℝ) / 2) *
          Real.log s - ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi))) := by
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have hb := co.abs_inner_redLength_limit_gradient_radialDistanceCutoff_le
    F hcar hreg b hbmem tau q hsigma Phi kappa hancient p ha has rho hrho ell
    hconv hcomplete z hr x
  calc
    _ ≤ Real.exp (-ell x - ((Module.finrank ℝ E : ℝ) / 2) * Real.log s -
        ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi)) *
        ((Real.sqrt 3 / Real.sqrt a / r) * Real.sqrt (ell x)) :=
      mul_le_mul_of_nonneg_left hb (Real.exp_nonneg _)
    _ = _ := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.abs_redDensity_limit_mul_inner_radialDistanceCutoff_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.abs_redDensity_limit_mul_inner_radialDistanceCutoff_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.abs_redDensity_limit_mul_inner_radialDistanceCutoff_le ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.abs_redDensity_limit_mul_inner_radialDistanceCutoff_le

theorem HalfLineMetricConvergenceData.abs_chartGradientBilin_redLength_limit_radialDistanceCutoff_le
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi) {R : SmoothRiemannianMetric I P.M}
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {a s : ℝ} (ha : 1 ≤ a) (has : a ≤ s)
    (rho : ℕ → ℕ) (hrho : _root_.Filter.Tendsto rho _root_.Filter.atTop _root_.Filter.atTop) (ell : P.M → ℝ)
    (hconv : ∀ y, _root_.Filter.Tendsto (fun k => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
      (Phi.map (co.φ (rho k)) y) s) _root_.Filter.atTop (𝓝 (ell y)))
    (hcomplete : MetricComplete (I := I)
      ({ P with metric := co.gInf (1 - s) } : PointedRiemannianManifold (I := I)))
    (z alpha : P.M) {r : ℝ} (hr : 0 < r) (x : P.M)
    (hell : MDifferentiableAt I 𝓘(ℝ, ℝ) ell x)
    (hcut : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (radialDistanceCutoff (co.gInf (1 - a)) z r) x)
    (hx : x ∈ (chartAt H alpha).source) :
    |chartGradientBilin (co.gInf (1 - s)) alpha x
        (fderiv ℝ (scalarOnE (I := I) alpha ell) (extChartAt I alpha x))
        (fderiv ℝ (scalarOnE (I := I) alpha
          (radialDistanceCutoff (co.gInf (1 - a)) z r)) (extChartAt I alpha x))| ≤
      (Real.sqrt 3 / Real.sqrt a / r) * Real.sqrt (ell x) := by
  rw [← inner_gradientFun_eq_chartGradientBilin (co.gInf (1 - s)) alpha hell hcut hx]
  exact co.abs_inner_redLength_limit_gradient_radialDistanceCutoff_le
    F hcar hreg b hbmem tau q hsigma Phi kappa hancient p ha has rho hrho ell
    hconv hcomplete z hr x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.abs_chartGradientBilin_redLength_limit_radialDistanceCutoff_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.abs_chartGradientBilin_redLength_limit_radialDistanceCutoff_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.abs_chartGradientBilin_redLength_limit_radialDistanceCutoff_le ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.abs_chartGradientBilin_redLength_limit_radialDistanceCutoff_le

namespace HalfLineMetricConvergenceData

theorem abs_redDensity_limit_mul_chartGradientBilin_radialDistanceCutoff_le
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi) {R : SmoothRiemannianMetric I P.M}
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {a s : ℝ} (ha : 1 ≤ a) (has : a ≤ s)
    (rho : ℕ → ℕ) (hrho : _root_.Filter.Tendsto rho _root_.Filter.atTop _root_.Filter.atTop) (ell : P.M → ℝ)
    (hconv : ∀ y, _root_.Filter.Tendsto (fun k => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
      (Phi.map (co.φ (rho k)) y) s) _root_.Filter.atTop (𝓝 (ell y)))
    (hcomplete : MetricComplete (I := I)
      ({ P with metric := co.gInf (1 - s) } : PointedRiemannianManifold (I := I)))
    (z alpha : P.M) {r : ℝ} (hr : 0 < r) (x : P.M)
    (hell : MDifferentiableAt I 𝓘(ℝ, ℝ) ell x)
    (hcut : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (radialDistanceCutoff (co.gInf (1 - a)) z r) x)
    (hx : x ∈ (chartAt H alpha).source) :
    |Real.exp (-ell x - ((Module.finrank ℝ E : ℝ) / 2) * Real.log s -
        ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi)) *
      chartGradientBilin (co.gInf (1 - s)) alpha x
        (fderiv ℝ (scalarOnE (I := I) alpha ell) (extChartAt I alpha x))
        (fderiv ℝ (scalarOnE (I := I) alpha
          (radialDistanceCutoff (co.gInf (1 - a)) z r)) (extChartAt I alpha x))| ≤
      (Real.sqrt 3 / Real.sqrt a / r) *
        (Real.sqrt (ell x) * Real.exp (-ell x - ((Module.finrank ℝ E : ℝ) / 2) *
          Real.log s - ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi))) := by
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have hb := co.abs_chartGradientBilin_redLength_limit_radialDistanceCutoff_le
    F hcar hreg b hbmem tau q hsigma Phi kappa hancient p ha has rho hrho ell
    hconv hcomplete z alpha hr x hell hcut hx
  calc
    _ ≤ Real.exp (-ell x - ((Module.finrank ℝ E : ℝ) / 2) * Real.log s -
        ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi)) *
        ((Real.sqrt 3 / Real.sqrt a / r) * Real.sqrt (ell x)) :=
      mul_le_mul_of_nonneg_left hb (Real.exp_nonneg _)
    _ = _ := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.abs_redDensity_limit_mul_chartGradientBilin_radialDistanceCutoff_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.abs_redDensity_limit_mul_chartGradientBilin_radialDistanceCutoff_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.abs_redDensity_limit_mul_chartGradientBilin_radialDistanceCutoff_le ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.abs_redDensity_limit_mul_chartGradientBilin_radialDistanceCutoff_le

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
