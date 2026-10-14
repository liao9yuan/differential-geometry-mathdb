import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointDensityConvergence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientSqrtLipschitz
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TensorNormFinrankNeZero
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.HalfLine
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.BallImage

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
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology _root_.ENNReal

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

theorem HalfLineMetricConvergenceData.sqrt_redLength_limit_sub_le_distance
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
    (x y : P.M) :
    Real.sqrt (ell y) ≤ Real.sqrt (ell x) + Real.sqrt 3 / (2 * Real.sqrt s) *
      (riemannianEDistOf (co.gInf (1 - s)) x y).toReal := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : NeZero (Module.finrank ℝ E) := by
    obtain ⟨t, _ht, z, hz⟩ := (hancient 0).notFlat
    exact ⟨Tensor0SBundle.finrank_ne_zero_of_normSq0S_ne_zero
      (((U).term 0).S.base.metric t) z (by norm_num : 0 < 4)
      (((U).term 0).S.base.rm04 t z) hz⟩
  have hs0 : 0 < s := zero_lt_one.trans_le hs
  have ht : 1 - s ≤ 0 := sub_nonpos.mpr hs
  let Q : PointedRiemannianManifold.{u, uE, uH} (I := I) :=
    { P with metric := co.gInf (1 - s) }
  let Psi : PointedRiemannianConvergenceMaps ((Y).atTime (1 - s)) Q (phi ∘ co.φ) :=
    (Phi.compSubseq co.φ co.strictMono).atTimeWithMetric (1 - s) (co.gInf (1 - s))
  obtain ⟨C, _hcanonical, hreference⟩ := co.exists_canonicalMetricConvergenceData Phi ht
  let d := (riemannianEDistOf Q.metric x y).toReal
  have hfinite : riemannianEDistOf Q.metric x y ≠ ⊤ :=
    DifferentialGeometry.riemannianEDistOf_ne_top Q.metric x y
  have hxBall : x ∈ riemannianClosedBallOf Q.metric x d := by
    change riemannianEDistOf Q.metric x x ≤ ENNReal.ofReal d
    rw [riemannianEDistOf_self]
    exact bot_le
  have hyBall : y ∈ riemannianClosedBallOf Q.metric x d := by
    change riemannianEDistOf Q.metric x y ≤ ENNReal.ofReal d
    rw [ENNReal.ofReal_toReal hfinite]
  let A := Real.sqrt 3 / (2 * Real.sqrt s)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hbound (L : ℝ) (hL : 1 < L) :
      Real.sqrt (ell y) - Real.sqrt (ell x) ≤ A * d * L := by
    have hmaps := Psi.eventually_edist_map_le_on_closed_ball C hreference hcomplete x
      (ENNReal.toReal_nonneg : 0 ≤ d) hL
    apply le_of_tendsto ((hconv y).sqrt.sub (hconv x).sqrt)
    filter_upwards [hrho.eventually hmaps] with k hk
    let i := phi (co.φ (rho k))
    let _ : ConnectedSpace ((U).term i).M := (hancient i).connected
    have hlip := sqrt_redLength_sub_le_distance_of_continuous_and_minimizers
      ((U).term i) (hancient i) p (Phi.map (co.φ (rho k)) x)
      (Phi.map (co.φ (rho k)) y) hs0
      (continuous_redLength_of_ancient ((U).term i) (hancient i) p hs0)
      (fun z => exists_lRegularized_minimizer_of_ancient ((U).term i) (hancient i) p z hs0)
    have hdist := hk.2 x hxBall y hyBall
    change riemannianEDistOf (((Y).term i).S.base.metric (1 - s))
      (Phi.map (co.φ (rho k)) x) (Phi.map (co.φ (rho k)) y) ≤
        ENNReal.ofReal L * riemannianEDistOf Q.metric x y at hdist
    rw [poleEndpointRescaledFlowSeq_metric_eq_shift,
      show (1 - s) - 1 = -s by ring] at hdist
    have hsourceFinite := DifferentialGeometry.riemannianEDistOf_ne_top
      (((U).term i).S.base.metric (-s))
      (Phi.map (co.φ (rho k)) x) (Phi.map (co.φ (rho k)) y)
    have hreal := (ENNReal.toReal_le_toReal hsourceFinite (by finiteness)).2 hdist
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (zero_lt_one.trans hL).le] at hreal
    calc
      _ ≤ A * (riemannianEDistOf (((U).term i).S.base.metric (-s))
          (Phi.map (co.φ (rho k)) x) (Phi.map (co.φ (rho k)) y)).toReal := by
        linarith only [hlip]
      _ ≤ A * (L * d) := mul_le_mul_of_nonneg_left hreal hA
      _ = A * d * L := by ring
  have hlim : _root_.Filter.Tendsto (fun L : ℝ => A * d * L) (𝓝[>] (1 : ℝ)) (𝓝 (A * d)) := by
    have hid : _root_.Filter.Tendsto (fun L : ℝ => L) (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℝ)) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa only [mul_one] using
      (tendsto_const_nhds.mul hid :
        _root_.Filter.Tendsto (fun L : ℝ => A * d * L) (𝓝[>] (1 : ℝ)) (𝓝 (A * d * 1)))
  have hLgt : ∀ᶠ L : ℝ in 𝓝[>] (1 : ℝ), 1 < L := self_mem_nhdsWithin
  have hfinal := ge_of_tendsto hlim (hLgt.mono fun L hL => hbound L hL)
  change Real.sqrt (ell y) ≤ Real.sqrt (ell x) + A * d
  linarith only [hfinal]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.sqrt_redLength_limit_sub_le_distance then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.sqrt_redLength_limit_sub_le_distance"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.sqrt_redLength_limit_sub_le_distance ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.sqrt_redLength_limit_sub_le_distance

end DifferentialGeometry.CheegerGromovCompactness
