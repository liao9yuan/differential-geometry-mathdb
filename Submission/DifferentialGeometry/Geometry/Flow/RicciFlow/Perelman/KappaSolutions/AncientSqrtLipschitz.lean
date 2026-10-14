import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientScalarMonotonicity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientCostContinuity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientTerminalMinimizer
import Submission.DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientCostSupport
import Submission.DifferentialGeometry.Geometry.Comparison.Distance.SqrtSupport

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Set _root_.Submission.Set _root_.Filter
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance lipschitzTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lipschitzTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lipschitzTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lipschitzTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lipschitzTopology
local instance lipschitzCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lipschitzCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lipschitzCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lipschitzCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lipschitzCharted
local instance lipschitzSmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lipschitzSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lipschitzSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lipschitzSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lipschitzSmooth
local instance lipschitzT2 : T2Space F.M := F.t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lipschitzT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lipschitzT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lipschitzT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lipschitzT2
local instance lipschitzSigma : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lipschitzSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lipschitzSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lipschitzSigma ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lipschitzSigma

theorem sqrt_redLength_sub_le_distance_of_continuous_and_minimizers
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p x y : F.M) {tau : ℝ} (htau : 0 < tau)
    (hcont : Continuous (fun z ↦ redLength F.S 0 p z tau))
    (hmin : ∀ z : F.M, ∃ alpha : ℝ → F.M,
      ContMDiff 𝓘(ℝ, ℝ) I 1 alpha ∧ alpha 0 = p ∧ alpha (Real.sqrt tau) = z ∧
      IsLRegularizedGeodesicOn F.S 0 alpha (_root_.Set.Ioc 0 (Real.sqrt tau)) ∧
      lRegularizedAction F.S 0 alpha 0 (Real.sqrt tau) =
        lCost F.S 0 p (alpha (Real.sqrt tau)) tau) :
    Real.sqrt (redLength F.S 0 p y tau) ≤ Real.sqrt (redLength F.S 0 p x tau) +
      Real.sqrt 3 / (2 * Real.sqrt tau) * (riemannianEDistOf (F.S.base.metric (-tau)) x y).toReal := by
  let _ : ConnectedSpace F.M := hF.connected
  have htime : -tau ∈ ancientTimeInterval.carrier := by
    simpa only [ancientTimeInterval_carrier, _root_.Set.mem_Iic] using neg_nonpos.mpr htau.le
  apply DifferentialGeometry.Geometry.sqrt_sub_le_distance_of_geodesic_upper_support
    (F.S.base.metric (-tau)) ⟨MetricComplete.complete (F.atTime (-tau)) (hF.complete (-tau) htime)⟩ hcont
    (by positivity : 0 ≤ Real.sqrt 3 / (2 * Real.sqrt tau)) ?_ x y
    (DifferentialGeometry.riemannianEDistOf_ne_top _ _ _)
  intro gamma t hgamma _hpos
  let beta : ℝ → F.M := fun r ↦ gamma (r + t)
  have hbeta : IsGeodesicAt (I := I) (F.S.base.metric (-tau)) beta 0 := by
    simpa only [sub_self] using DifferentialGeometry.Geometry.isGeodesicAt_comp_add hgamma t
  obtain ⟨alpha, halpha, halpha0, hend, hgeo, hcost⟩ := hmin (gamma t)
  have hbeta0 : beta 0 = alpha (Real.sqrt tau) := by simpa only [beta, zero_add] using hend.symm
  obtain ⟨phi, d, heq, hupper, hd, hbound⟩ :=
    exists_redLength_upper_support_of_ancient_minimizer F hF p htau alpha beta
      halpha halpha0 hgeo hcost hbeta hbeta0
  have hshift : _root_.Filter.Tendsto (fun r : ℝ ↦ r - t) (𝓝 t) (𝓝 (0 : ℝ)) := by
    have hh : Continuous (fun r : ℝ ↦ r - t) := continuous_id.sub continuous_const
    simpa only [sub_self] using hh.tendsto t
  have hupper' : (fun r ↦ redLength F.S 0 p (gamma r) tau) ≤ᶠ[𝓝 t]
      (fun r ↦ phi (r - t)) := by
    filter_upwards [hshift hupper] with r hr
    change redLength F.S 0 p (gamma ((r - t) + t)) tau ≤ phi (r - t) at hr
    simpa only [sub_add_cancel] using hr
  have hderiv : HasDerivAt (fun r ↦ phi (r - t)) d t := by
    have hd' : HasDerivAt phi d (t - t) := by simpa only [sub_self] using hd
    have hp := HasDerivAt.comp t (h₂ := phi) (h := fun r : ℝ ↦ r - t) hd' ((hasDerivAt_id t).sub_const t)
    convert hp using 1 <;> first | rfl | simp only [mul_one]
  have hgammaDiff : MDifferentiableAt 𝓘(ℝ, ℝ) I gamma (0 + t) := by
    simpa only [zero_add] using (DifferentialGeometry.Geometry.contMDiffAt_of_isGeodesicAt hgamma).mdifferentiableAt (by simp)
  have hvelocity : lVelocity (I := I) beta 0 = mfderiv 𝓘(ℝ, ℝ) I gamma t 1 := by
    have hv := DifferentialGeometry.Geometry.mfderiv_comp_add_apply_one 0 t hgammaDiff
    have hm : (mfderiv 𝓘(ℝ, ℝ) I gamma (0 + t) (1 : ℝ) : E) =
        (mfderiv 𝓘(ℝ, ℝ) I gamma t (1 : ℝ) : E) :=
      congrArg (fun s : ℝ ↦ (mfderiv 𝓘(ℝ, ℝ) I gamma s (1 : ℝ) : E)) (zero_add t)
    rw [hm] at hv
    exact hv
  refine ⟨fun r ↦ phi (r - t), d, ?_, hupper'.filter_mono nhdsWithin_le_nhds, hderiv, ?_⟩
  · simpa only [sub_self, beta, zero_add] using heq
  · have hbound' : d ≤ Real.sqrt 3 / Real.sqrt tau * Real.sqrt (redLength F.S 0 p (gamma t) tau) *
      Real.sqrt ((F.S.base.metric (-tau)).inner (gamma t)
        (mfderiv 𝓘(ℝ, ℝ) I gamma t 1) (mfderiv 𝓘(ℝ, ℝ) I gamma t 1)) := by
      simp only [hvelocity] at hbound
      have hbase : beta 0 = gamma t := congrArg gamma (zero_add t)
      have hmetric : (F.S.base.metric (-tau)).inner (beta 0) =
          (F.S.base.metric (-tau)).inner (gamma t) := congrArg _ hbase
      rw [hmetric, hbase] at hbound
      exact hbound
    have hfactor : 2 * (Real.sqrt 3 / (2 * Real.sqrt tau)) = Real.sqrt 3 / Real.sqrt tau := by ring
    rw [hfactor]
    exact hbound'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.sqrt_redLength_sub_le_distance_of_continuous_and_minimizers then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.sqrt_redLength_sub_le_distance_of_continuous_and_minimizers"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.sqrt_redLength_sub_le_distance_of_continuous_and_minimizers ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.sqrt_redLength_sub_le_distance_of_continuous_and_minimizers

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

private local instance topology : TopologicalSpace F.M := F.topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.topology
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.topology target :: scope.openDecls } }
private local instance charted : ChartedSpace H F.M := F.charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.charted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.charted target :: scope.openDecls } }
private local instance smooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.smooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.smooth target :: scope.openDecls } }
private local instance t2 : T2Space F.M := F.t2

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.t2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.t2 target :: scope.openDecls } }
private local instance sigma : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.sigma
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.sigma target :: scope.openDecls } }

theorem abs_sqrt_redLength_sub_le_rescaled_distance
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p x y : F.M) {tau : ℝ} (htau : 0 < tau) :
    |Real.sqrt (redLength F.S 0 p x tau) - Real.sqrt (redLength F.S 0 p y tau)| ≤
      Real.sqrt 3 / 2 * (riemannianEDistOf
        (scaleMetric tau⁻¹ (inv_pos.mpr htau) (F.S.base.metric (-tau))) x y).toReal := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : T2Space (TangentBundle I F.M) := F.t2TangentBundle
  let _ : NeZero (Module.finrank ℝ E) := by
    obtain ⟨t, _ht, z, hz⟩ := hF.notFlat
    exact ⟨Tensor0SBundle.finrank_ne_zero_of_normSq0S_ne_zero
      (F.S.base.metric t) z (by norm_num : 0 < 4) _ hz⟩
  have hroot (a b : F.M) := sqrt_redLength_sub_le_distance_of_continuous_and_minimizers
    F hF p a b htau (continuous_redLength_of_ancient F hF p htau)
    (fun z => exists_lRegularized_minimizer_of_ancient F hF p z htau)
  have hxy := hroot x y
  have hyx := hroot y x
  rw [riemannianEDistOf_comm] at hyx
  rw [edistOf_scale, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _), Real.sqrt_inv]
  have heq : Real.sqrt 3 / 2 * ((Real.sqrt tau)⁻¹ *
      (riemannianEDistOf (F.S.base.metric (-tau)) x y).toReal) =
      Real.sqrt 3 / (2 * Real.sqrt tau) *
        (riemannianEDistOf (F.S.base.metric (-tau)) x y).toReal := by ring
  rw [heq]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.abs_sqrt_redLength_sub_le_rescaled_distance then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.abs_sqrt_redLength_sub_le_rescaled_distance"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.abs_sqrt_redLength_sub_le_rescaled_distance ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.abs_sqrt_redLength_sub_le_rescaled_distance

theorem redLength_le_of_rescaled_distance_le
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p q x : F.M) {tau A D : ℝ} (htau : 0 < tau) (hD : 0 ≤ D)
    (hbase : redLength F.S 0 p q tau ≤ A)
    (hdist : riemannianEDistOf
      (scaleMetric tau⁻¹ (inv_pos.mpr htau) (F.S.base.metric (-tau))) q x ≤
      ENNReal.ofReal D) :
    redLength F.S 0 p x tau ≤ (Real.sqrt A + Real.sqrt 3 / 2 * D) ^ 2 := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : T2Space (TangentBundle I F.M) := F.t2TangentBundle
  let _ : NeZero (Module.finrank ℝ E) := by
    obtain ⟨t, _ht, z, hz⟩ := hF.notFlat
    exact ⟨Tensor0SBundle.finrank_ne_zero_of_normSq0S_ne_zero
      (F.S.base.metric t) z (by norm_num : 0 < 4) _ hz⟩
  have hnonneg : 0 ≤ redLength F.S 0 p x tau := by
    obtain ⟨C, hC⟩ := hF.globalScalarBound
    apply div_nonneg _ (by positivity)
    apply lCost_nonneg_of_scalar_nonneg F.S 0 htau.le
    intro s hs y
    simpa only [zero_sub] using (hC (-s) (by
      rw [ancientTimeInterval_carrier]
      exact neg_nonpos.mpr hs.1) y).1
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hdist
  rw [edistOf_scale, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _), ENNReal.toReal_ofReal hD,
    Real.sqrt_inv] at hreal
  have hroot := sqrt_redLength_sub_le_distance_of_continuous_and_minimizers
    F hF p q x htau (continuous_redLength_of_ancient F hF p htau)
    (fun y ↦ exists_lRegularized_minimizer_of_ancient F hF p y htau)
  have hterm : Real.sqrt 3 / (2 * Real.sqrt tau) *
      (riemannianEDistOf (F.S.base.metric (-tau)) q x).toReal ≤
      Real.sqrt 3 / 2 * D := by
    calc
      _ = (Real.sqrt 3 / 2) * ((Real.sqrt tau)⁻¹ *
          (riemannianEDistOf (F.S.base.metric (-tau)) q x).toReal) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hreal (by positivity)
  have hbound : Real.sqrt (redLength F.S 0 p x tau) ≤
      Real.sqrt A + Real.sqrt 3 / 2 * D :=
    hroot.trans (add_le_add (Real.sqrt_le_sqrt hbase) hterm)
  have hsq := (sq_le_sq₀ (Real.sqrt_nonneg (redLength F.S 0 p x tau))
    (by positivity : 0 ≤ Real.sqrt A + Real.sqrt 3 / 2 * D)).2 hbound
  rwa [Real.sq_sqrt hnonneg] at hsq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.redLength_le_of_rescaled_distance_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.redLength_le_of_rescaled_distance_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.redLength_le_of_rescaled_distance_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.redLength_le_of_rescaled_distance_le

theorem scalar_le_on_past_of_rescaled_distance_le
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p q x : F.M) {tau A D s : ℝ} (htau : 0 < tau) (hD : 0 ≤ D)
    (hbase : redLength F.S 0 p q tau ≤ A)
    (hdist : riemannianEDistOf
      (scaleMetric tau⁻¹ (inv_pos.mpr htau) (F.S.base.metric (-tau))) q x ≤
      ENNReal.ofReal D) (hs : s ≤ -tau) :
    tau * F.S.scalar s x ≤ 3 * (Real.sqrt A + Real.sqrt 3 / 2 * D) ^ 2 := by
  have hterminal := (le_div_iff₀ htau).mp
    (scalar_le_three_mul_redLength_div_of_ancient F hF p x htau)
  have hlength := redLength_le_of_rescaled_distance_le F hF p q x htau hD hbase hdist
  have hmon := ancientKappa_scalar_monotoneOn F hF x
    (hs.trans (neg_nonpos.mpr htau.le)) (neg_nonpos.mpr htau.le) hs
  nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalar_le_on_past_of_rescaled_distance_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalar_le_on_past_of_rescaled_distance_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalar_le_on_past_of_rescaled_distance_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalar_le_on_past_of_rescaled_distance_le

theorem rmNorm_le_on_past_of_rescaled_distance_le
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p q x : F.M) {tau A D s : ℝ} (htau : 0 < tau) (hD : 0 ≤ D)
    (hbase : redLength F.S 0 p q tau ≤ A)
    (hdist : riemannianEDistOf
      (scaleMetric tau⁻¹ (inv_pos.mpr htau) (F.S.base.metric (-tau))) q x ≤
      ENNReal.ofReal D) (hs : s ≤ -tau) :
    let g := scaleMetric tau⁻¹ (inv_pos.mpr htau) (F.S.base.metric s)
    Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 4 (metricRm04At (I := I) g x)) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 *
        (3 * (Real.sqrt A + Real.sqrt 3 / 2 * D) ^ 2) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let g := scaleMetric tau⁻¹ (inv_pos.mpr htau) (F.S.base.metric s)
  change Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 4 (metricRm04At (I := I) g x)) ≤ _
  have hop : metricAlgebraicCurvatureTensorAt (I := I) g x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := F.M) := by
    dsimp only [g]
    rw [metricAlgebraicCurvatureTensorAt_scaleMetric]
    apply algebraicCurvatureOperatorNonnegativeCone.smul_mem ?_ (inv_pos.mpr htau).le
    apply (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
      (I := I) (F.S.base.metric s) x).mpr
    intro n c v w
    simpa only [SolutionFamily.rm04, metricRm04StandardAt_apply, metricRm04_apply] using
      hF.nonnegativeCurvatureOperator s (hs.trans (neg_nonpos.mpr htau.le)) x n c v w
  have hscalar : metricScalarAt (I := I) g x ≤
      3 * (Real.sqrt A + Real.sqrt 3 / 2 * D) ^ 2 := by
    dsimp only [g]
    rw [metricScalarAt_scaleMetric, inv_inv]
    exact scalar_le_on_past_of_rescaled_distance_le F hF p q x htau hD hbase hdist hs
  exact (sqrt_metricRm_normSq_le_finrank_sq_mul_scalar g x hop).trans
    (mul_le_mul_of_nonneg_left hscalar (sq_nonneg _))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.rmNorm_le_on_past_of_rescaled_distance_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.rmNorm_le_on_past_of_rescaled_distance_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.rmNorm_le_on_past_of_rescaled_distance_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.rmNorm_le_on_past_of_rescaled_distance_le

theorem scalar_le_of_rescaled_distance_le
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p q x : F.M) {tau A D : ℝ} (htau : 0 < tau) (hD : 0 ≤ D)
    (hbase : redLength F.S 0 p q tau ≤ A)
    (hdist : riemannianEDistOf
      (scaleMetric tau⁻¹ (inv_pos.mpr htau) (F.S.base.metric (-tau))) q x ≤
      ENNReal.ofReal D) :
    tau * F.S.scalar (-tau) x ≤ 3 * (Real.sqrt A + Real.sqrt 3 / 2 * D) ^ 2 := by
  exact scalar_le_on_past_of_rescaled_distance_le F hF p q x htau hD hbase hdist le_rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalar_le_of_rescaled_distance_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalar_le_of_rescaled_distance_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalar_le_of_rescaled_distance_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalar_le_of_rescaled_distance_le

theorem rmNorm_le_of_rescaled_distance_le
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p q x : F.M) {tau A D : ℝ} (htau : 0 < tau) (hD : 0 ≤ D)
    (hbase : redLength F.S 0 p q tau ≤ A)
    (hdist : riemannianEDistOf
      (scaleMetric tau⁻¹ (inv_pos.mpr htau) (F.S.base.metric (-tau))) q x ≤
      ENNReal.ofReal D) :
    let g := scaleMetric tau⁻¹ (inv_pos.mpr htau) (F.S.base.metric (-tau))
    Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 4 (metricRm04At (I := I) g x)) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 *
        (3 * (Real.sqrt A + Real.sqrt 3 / 2 * D) ^ 2) := by
  exact rmNorm_le_on_past_of_rescaled_distance_le F hF p q x htau hD hbase hdist le_rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.rmNorm_le_of_rescaled_distance_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.rmNorm_le_of_rescaled_distance_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.rmNorm_le_of_rescaled_distance_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.rmNorm_le_of_rescaled_distance_le

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
