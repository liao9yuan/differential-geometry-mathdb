import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientMetricMonotonicity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Integrability
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Continuity.CarrierBaseTime
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Compactness.Range
import Submission.DifferentialGeometry.Geometry.Metric.Comparison.CurveCompactness
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TensorNormFinrankNeZero

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Function _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology


universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
local instance terminalEnergyTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalEnergyTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalEnergyTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalEnergyTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalEnergyTopology
local instance terminalEnergyCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalEnergyCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalEnergyCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalEnergyCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalEnergyCharted
local instance terminalEnergySmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalEnergySmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalEnergySmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalEnergySmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalEnergySmooth
local instance terminalEnergyC1 : IsManifold I 1 F.M := IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalEnergyC1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalEnergyC1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalEnergyC1 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalEnergyC1
local instance terminalEnergyT2 : T2Space F.M := F.t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalEnergyT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalEnergyT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalEnergyT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalEnergyT2
local instance terminalEnergySigma : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalEnergySigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalEnergySigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalEnergySigma ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalEnergySigma

private theorem lagrangian_continuousOn_terminal_interval
    (alpha : ℝ → F.M) (halpha : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha) (a b : ℝ) :
    ContinuousOn (lRegularizedLagrangian F.S 0 alpha) (_root_.Set.Icc a b) := by
  apply (lRegularizedLagrangian_continuousOn_carrier F.S F.isSolution alpha halpha).comp
    (continuous_const.prodMk continuous_id).continuousOn
  intro r hr
  change (0 : ℝ) - r ^ 2 ∈ ancientTimeInterval.carrier
  simpa only [ancientTimeInterval_carrier, _root_.Set.mem_Iic, zero_sub] using neg_nonpos.mpr (sq_nonneg r)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lagrangian_continuousOn_terminal_interval
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lagrangian_continuousOn_terminal_interval target :: scope.openDecls } }

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem curveEnergy_terminal_le_two_mul_action_of_ancient
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (alpha : ℝ → F.M) (halpha : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha)
    {a b : ℝ} (hab : a ≤ b) :
    curveEnergy (F.S.base.metric 0) alpha a b ≤ 2 * lRegularizedAction F.S 0 alpha a b := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hE := integrableOn_riemannianMetric_inner_lVelocity_self_of_contMDiff_one
    (F.S.base.metric 0) alpha halpha a b
  have hEint : IntervalIntegrable (fun s => (F.S.base.metric 0).inner (alpha s)
      (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s)) _root_.MeasureTheory.MeasureSpace.volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    exact hE
  have hLag : IntervalIntegrable (lRegularizedLagrangian F.S 0 alpha) _root_.MeasureTheory.MeasureSpace.volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [_root_.Set.uIcc_of_le hab]
    exact lagrangian_continuousOn_terminal_interval F alpha halpha a b
  have hpoint : ∀ s ∈ _root_.Set.Icc a b,
      (F.S.base.metric 0).inner (alpha s) (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s) ≤
        2 * lRegularizedLagrangian F.S 0 alpha s := by
    intro s hs
    have hcomp := ancientModel_metric_zero_le F hF (neg_nonpos.mpr (sq_nonneg s))
      (alpha s) (lVelocity (I := I) alpha s)
    have hscalar : 0 ≤ F.S.scalar (-s ^ 2) (alpha s) := by
      obtain ⟨C, hC⟩ := hF.globalScalarBound
      exact (hC (-s^2) (by simpa only [ancientTimeInterval_carrier, _root_.Set.mem_Iic] using neg_nonpos.mpr (sq_nonneg s)) (alpha s)).1
    dsimp only [lRegularizedLagrangian]
    rw [zero_sub]
    nlinarith [mul_nonneg (sq_nonneg s) hscalar]
  have hint := intervalIntegral.integral_mono_on hab hEint (hLag.const_mul 2) hpoint
  rw [intervalIntegral.integral_const_mul] at hint
  exact hint

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.curveEnergy_terminal_le_two_mul_action_of_ancient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.curveEnergy_terminal_le_two_mul_action_of_ancient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.curveEnergy_terminal_le_two_mul_action_of_ancient ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.curveEnergy_terminal_le_two_mul_action_of_ancient

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianEDist_terminal_le_of_action_le
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (alpha : ℝ → F.M) (halpha : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha)
    {a s t b A : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b)
    (hA : lRegularizedAction F.S 0 alpha a b ≤ A) :
    riemannianEDistOf (F.S.base.metric 0) (alpha s) (alpha t) ≤
      ENNReal.ofReal (Real.sqrt (t-s) * Real.sqrt (2*A)) := by
  have hE := integrableOn_riemannianMetric_inner_lVelocity_self_of_contMDiff_one
    (F.S.base.metric 0) alpha halpha a b
  have henergy := (curveEnergy_terminal_le_two_mul_action_of_ancient F hF alpha halpha
    (has.trans (hst.trans htb))).trans (mul_le_mul_of_nonneg_left hA (by norm_num))
  exact edistOf_le_budget (F.S.base.metric 0) hst halpha.contMDiffOn
    (hE.mono_set (_root_.Set.Icc_subset_Icc has htb))
    ((curveEnergy_mono (F.S.base.metric 0) has hst htb hE).trans henergy)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.riemannianEDist_terminal_le_of_action_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.riemannianEDist_terminal_le_of_action_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.riemannianEDist_terminal_le_of_action_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.riemannianEDist_terminal_le_of_action_le

theorem exists_compact_range_of_ancient_action_le
    [I.Boundaryless]
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (alpha : ℕ → ℝ → F.M) (halpha : ∀ n, ContMDiff 𝓘(ℝ, ℝ) I 1 (alpha n))
    (x : F.M) {a b A : ℝ}
    (hstart : ∀ n, alpha n a = x) (hA : ∀ n, lRegularizedAction F.S 0 (alpha n) a b ≤ A) :
    ∃ K : Set F.M, IsCompact K ∧ ∀ n, alpha n '' _root_.Set.Icc a b ⊆ K := by
  let _ : T2Space (TangentBundle I F.M) := F.t2TangentBundle
  let _ : NeZero (Module.finrank ℝ E) := by
    obtain ⟨t, ht, x, hx⟩ := hF.notFlat
    exact ⟨Tensor0SBundle.finrank_ne_zero_of_normSq0S_ne_zero
      (F.S.base.metric t) x (by norm_num : 0 < 4) _ hx⟩
  have hg : RiemannianMetricComplete (F.S.base.metric 0) :=
    ⟨hF.complete 0 (by simp only [ancientTimeInterval_carrier, _root_.Set.mem_Iic, le_refl])⟩
  refine ⟨{y | riemannianEDistOf (F.S.base.metric 0) x y ≤
      ENNReal.ofReal (Real.sqrt (b-a) * Real.sqrt (2*A))},
    hg.closedEBall_isCompact x (Real.sqrt (b-a) * Real.sqrt (2*A)), ?_⟩
  intro n y hy
  obtain ⟨r, hr, rfl⟩ := hy
  have hdist := riemannianEDist_terminal_le_of_action_le F hF (alpha n) (halpha n)
    le_rfl hr.1 hr.2 (hA n)
  rw [hstart n] at hdist
  exact hdist.trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by linarith [hr.2])) (Real.sqrt_nonneg _)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_compact_range_of_ancient_action_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_compact_range_of_ancient_action_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_compact_range_of_ancient_action_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_compact_range_of_ancient_action_le


theorem exists_uniform_subseq_of_ancient_action_le_of_tendsto_endpoint
    [I.Boundaryless]
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (alpha : ℕ → ℝ → F.M) (halpha : ∀ n, ContMDiff 𝓘(ℝ, ℝ) I 1 (alpha n))
    (x y : F.M) {a b A : ℝ} (hab : a ≤ b)
    (hstart : ∀ n, alpha n a = x)
    (hend : _root_.Filter.Tendsto (fun n => alpha n b) _root_.Filter.atTop (𝓝 y))
    (hA : ∀ n, lRegularizedAction F.S 0 (alpha n) a b ≤ A) :
    letI : TopologicalSpace.MetrizableSpace F.M := Manifold.metrizableSpace I F.M
    letI : PseudoMetricSpace F.M := TopologicalSpace.pseudoMetrizableSpacePseudoMetric F.M
    ∃ K : Set F.M, ∃ phi : ℕ → ℕ, ∃ g : C(_root_.Set.Icc a b, F.M),
      IsCompact K ∧ StrictMono phi ∧
      (∀ n, alpha (phi n) '' _root_.Set.Icc a b ⊆ K) ∧
      TendstoUniformly (fun n (s : _root_.Set.Icc a b) => alpha (phi n) s.1) g _root_.Filter.atTop ∧
      (∀ s, g s ∈ K) ∧
      g ⟨a, le_rfl, hab⟩ = x ∧ g ⟨b, hab, le_rfl⟩ = y := by
  let : TopologicalSpace.MetrizableSpace F.M := Manifold.metrizableSpace I F.M
  let : PseudoMetricSpace F.M := TopologicalSpace.pseudoMetrizableSpacePseudoMetric F.M
  obtain ⟨K, hK, hKrange⟩ :=
    exists_compact_range_of_ancient_action_le F hF alpha halpha x hstart hA
  let B : ℝ := 2 * A
  have henergy : ∀ n, curveEnergy (F.S.base.metric 0) (alpha n) a b ≤ B := by
    intro n
    exact (curveEnergy_terminal_le_two_mul_action_of_ancient F hF (alpha n) (halpha n) hab).trans
      (mul_le_mul_of_nonneg_left (hA n) (by norm_num))
  obtain ⟨phi, g, hphi, hconv⟩ :=
    DifferentialGeometry.Geometry.Riemannian.exists_strictMono_tendstoUniformly_of_curveEnergy_le
      (I := I) (F.S.base.metric 0) a b B alpha
      (fun n => (halpha n).contMDiffOn) henergy K hK
      (fun n s => hKrange n ⟨s.1, s.2, rfl⟩)
  have hga : g ⟨a, le_rfl, hab⟩ = x := by
    have hlim := hconv.tendsto_at (⟨a, le_rfl, hab⟩ : _root_.Set.Icc a b)
    have hlim' : _root_.Filter.Tendsto (fun _ : ℕ => x) _root_.Filter.atTop (𝓝 (g ⟨a, le_rfl, hab⟩)) := by
      simpa only [hstart] using hlim
    exact tendsto_nhds_unique hlim' tendsto_const_nhds
  have hgb : g ⟨b, hab, le_rfl⟩ = y :=
    tendsto_nhds_unique (hconv.tendsto_at ⟨b, hab, le_rfl⟩)
      (hend.comp hphi.tendsto_atTop)
  refine ⟨K, phi, g, hK, hphi, (fun n => hKrange (phi n)), hconv, ?_, hga, hgb⟩
  intro s
  exact hK.isClosed.mem_of_tendsto (hconv.tendsto_at s)
    (Filter.Eventually.of_forall (fun n => hKrange (phi n) ⟨s.1, s.2, rfl⟩))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_uniform_subseq_of_ancient_action_le_of_tendsto_endpoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_uniform_subseq_of_ancient_action_le_of_tendsto_endpoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_uniform_subseq_of_ancient_action_le_of_tendsto_endpoint ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_uniform_subseq_of_ancient_action_le_of_tendsto_endpoint

theorem exists_uniform_subseq_of_ancient_action_le
    [I.Boundaryless]
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (alpha : ℕ → ℝ → F.M) (halpha : ∀ n, ContMDiff 𝓘(ℝ, ℝ) I 1 (alpha n))
    (x y : F.M) {a b A : ℝ} (hab : a ≤ b)
    (hstart : ∀ n, alpha n a = x) (hend : ∀ n, alpha n b = y)
    (hA : ∀ n, lRegularizedAction F.S 0 (alpha n) a b ≤ A) :
    letI : TopologicalSpace.MetrizableSpace F.M := Manifold.metrizableSpace I F.M
    letI : PseudoMetricSpace F.M := TopologicalSpace.pseudoMetrizableSpacePseudoMetric F.M
    ∃ K : Set F.M, ∃ phi : ℕ → ℕ, ∃ g : C(_root_.Set.Icc a b, F.M),
      IsCompact K ∧ StrictMono phi ∧
      (∀ n, alpha (phi n) '' _root_.Set.Icc a b ⊆ K) ∧
      TendstoUniformly (fun n (s : _root_.Set.Icc a b) => alpha (phi n) s.1) g _root_.Filter.atTop ∧
      (∀ s, g s ∈ K) ∧
      g ⟨a, le_rfl, hab⟩ = x ∧ g ⟨b, hab, le_rfl⟩ = y := by
  apply exists_uniform_subseq_of_ancient_action_le_of_tendsto_endpoint F hF alpha halpha x y hab hstart
    (by simpa only [hend] using (tendsto_const_nhds : _root_.Filter.Tendsto (fun _ : ℕ => y) _root_.Filter.atTop (𝓝 y))) hA

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_uniform_subseq_of_ancient_action_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_uniform_subseq_of_ancient_action_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_uniform_subseq_of_ancient_action_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_uniform_subseq_of_ancient_action_le

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
