import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ReducedVolumeNormalization
import Mathlib.Topology.Order.MonotoneConvergence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardSliceSequence
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Scaling

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Filter _root_.Set _root_.Submission.Set
open scoped _root_.Topology _root_.Submission.Topology _root_.ENNReal

private theorem tendsto_antitoneOn_mul_atTop {V : ℝ → ℝ≥0∞}
    (hV : AntitoneOn V (_root_.Set.Ioi 0)) {tau : ℕ → ℝ}
    (htau : ∀ i, 0 < tau i) (hescape : _root_.Filter.Tendsto tau _root_.Filter.atTop _root_.Filter.atTop)
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun i => V (tau i * a)) _root_.Filter.atTop (𝓝 (⨅ t : _root_.Set.Ioi (0 : ℝ), V t)) := by
  have hm : Antitone (fun t : _root_.Set.Ioi (0 : ℝ) => V t) :=
    fun x y hxy => hV x.property y.property hxy
  have hesc : _root_.Filter.Tendsto (fun i => (⟨tau i * a, mul_pos (htau i) ha⟩ : _root_.Set.Ioi (0 : ℝ)))
      atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [(hescape.atTop_mul_const ha).eventually_ge_atTop (b : ℝ)] with i hi
    exact hi
  exact (tendsto_atTop_iInf hm).comp hesc

run_cmd do
  let target := ``Submission.tendsto_antitoneOn_mul_atTop
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `tendsto_antitoneOn_mul_atTop target :: scope.openDecls } }

private theorem eventually_antitoneOn_mul_le {V : ℝ → ℝ≥0∞}
    (hV : AntitoneOn V (_root_.Set.Ioi 0)) {tau : ℕ → ℝ}
    (htau : ∀ i, 0 < tau i) (hescape : _root_.Filter.Tendsto tau _root_.Filter.atTop _root_.Filter.atTop)
    {a : ℝ} (ha : 0 < a) {b : ℝ≥0∞}
    (hb : (⨅ t : _root_.Set.Ioi (0 : ℝ), V t) < b) :
    ∀ᶠ i in _root_.Filter.atTop, ∀ θ ∈ _root_.Set.Ici a,
      (⨅ t : _root_.Set.Ioi (0 : ℝ), V t) ≤ V (tau i * θ) ∧ V (tau i * θ) < b := by
  have hlim := tendsto_antitoneOn_mul_atTop hV htau hescape ha
  filter_upwards [hlim.eventually (gt_mem_nhds hb)] with i hi
  intro θ hθ
  have hp : 0 < tau i * θ := mul_pos (htau i) (ha.trans_le hθ)
  exact ⟨iInf_le (fun t : _root_.Set.Ioi (0 : ℝ) => V t) ⟨tau i * θ, hp⟩,
    (hV (mul_pos (htau i) ha) hp (mul_le_mul_of_nonneg_left hθ (htau i).le)).trans_lt hi⟩

run_cmd do
  let target := ``Submission.eventually_antitoneOn_mul_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `eventually_antitoneOn_mul_le target :: scope.openDecls } }

noncomputable section

open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.MeasureTheory _root_.Submission.MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instMeasurableSpace_differentialGeometry : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instBorelSpace_differentialGeometry : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instBorelSpace_differentialGeometry target :: scope.openDecls } }

theorem normalizedShrinkerMass_scaleMetric (g : SmoothRiemannianMetric I M)
    (f : M → ℝ) {c : ℝ} (hc : 0 < c) :
    normalizedShrinkerMass (scaleMetric c hc g) f =
      ENNReal.ofReal (Real.sqrt c) ^ Module.finrank ℝ E * normalizedShrinkerMass g f := by
  unfold normalizedShrinkerMass
  rw [volume_scaleMetric, _root_.MeasureTheory.lintegral_smul_measure, smul_eq_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedShrinkerMass_scaleMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedShrinkerMass_scaleMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedShrinkerMass_scaleMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedShrinkerMass_scaleMetric

theorem normalizedShrinkerMass_backward_slice_eq_intrinsicReducedVolume
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (T : ℝ) (p : M) {tau : ℝ} (htau : 0 < tau) :
    normalizedShrinkerMass
      (scaleMetric tau⁻¹ (inv_pos.mpr htau) (S.base.metric (T - tau)))
      (fun x => lCost S T p x tau / (2 * Real.sqrt tau)) =
        intrinsicReducedVolume S T p tau := by
  rw [normalizedShrinkerMass_scaleMetric]
  have hfactor : (Real.sqrt tau⁻¹) ^ Module.finrank ℝ E =
      Real.exp (-((Module.finrank ℝ E : ℝ) / 2) * Real.log tau) := by
    rw [← Real.exp_log (pow_pos (Real.sqrt_pos.mpr (inv_pos.mpr htau)) _),
      Real.log_pow, Real.log_sqrt (inv_nonneg.mpr htau.le), Real.log_inv]
    congr 1
    ring
  rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _) _, hfactor]
  unfold normalizedShrinkerMass intrinsicReducedVolume
  rw [← _root_.MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply _root_.MeasureTheory.lintegral_congr
  intro x
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
  congr 2
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedShrinkerMass_backward_slice_eq_intrinsicReducedVolume then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedShrinkerMass_backward_slice_eq_intrinsicReducedVolume"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedShrinkerMass_backward_slice_eq_intrinsicReducedVolume ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedShrinkerMass_backward_slice_eq_intrinsicReducedVolume

def asymptoticReducedVolume {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (p : M) : ℝ≥0∞ :=
  ⨅ tau : _root_.Set.Ioi (0 : ℝ), intrinsicReducedVolume S T p tau

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.asymptoticReducedVolume then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.asymptoticReducedVolume"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.asymptoticReducedVolume ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.asymptoticReducedVolume

theorem intrinsicReducedVolume_tendsto_mul_atTop_of_antitone
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (p : M)
    (hmono : AntitoneOn (intrinsicReducedVolume S T p) (_root_.Set.Ioi 0))
    {tau : ℕ → ℝ} (htau : ∀ i, 0 < tau i) (hescape : _root_.Filter.Tendsto tau _root_.Filter.atTop _root_.Filter.atTop)
    {a : ℝ} (ha : 0 < a) :
    _root_.Filter.Tendsto (fun i => intrinsicReducedVolume S T p (tau i * a))
      atTop (𝓝 (asymptoticReducedVolume S T p)) :=
  tendsto_antitoneOn_mul_atTop hmono htau hescape ha

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.intrinsicReducedVolume_tendsto_mul_atTop_of_antitone then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.intrinsicReducedVolume_tendsto_mul_atTop_of_antitone"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.intrinsicReducedVolume_tendsto_mul_atTop_of_antitone ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.intrinsicReducedVolume_tendsto_mul_atTop_of_antitone

theorem eventually_intrinsicReducedVolume_mul_lt_of_antitone
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (p : M)
    (hmono : AntitoneOn (intrinsicReducedVolume S T p) (_root_.Set.Ioi 0))
    {tau : ℕ → ℝ} (htau : ∀ i, 0 < tau i) (hescape : _root_.Filter.Tendsto tau _root_.Filter.atTop _root_.Filter.atTop)
    {a : ℝ} (ha : 0 < a) {b : ℝ≥0∞} (hb : asymptoticReducedVolume S T p < b) :
    ∀ᶠ i in _root_.Filter.atTop, ∀ θ ∈ _root_.Set.Ici a,
      asymptoticReducedVolume S T p ≤ intrinsicReducedVolume S T p (tau i * θ) ∧
      intrinsicReducedVolume S T p (tau i * θ) < b :=
  eventually_antitoneOn_mul_le hmono htau hescape ha hb

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.eventually_intrinsicReducedVolume_mul_lt_of_antitone then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.eventually_intrinsicReducedVolume_mul_lt_of_antitone"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.eventually_intrinsicReducedVolume_mul_lt_of_antitone ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.eventually_intrinsicReducedVolume_mul_lt_of_antitone

theorem intrinsicReducedVolume_sub_tendsto_zero_of_antitone
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (p : M)
    (hmono : AntitoneOn (intrinsicReducedVolume S T p) (_root_.Set.Ioi 0))
    {tau : ℕ → ℝ} (htau : ∀ i, 0 < tau i) (hescape : _root_.Filter.Tendsto tau _root_.Filter.atTop _root_.Filter.atTop)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    _root_.Filter.Tendsto (fun i => intrinsicReducedVolume S T p (tau i * a) -
      intrinsicReducedVolume S T p (tau i * b)) _root_.Filter.atTop (𝓝 0) := by
  by_cases htop : asymptoticReducedVolume S T p = ⊤
  · have hval (r : ℝ) (hr : 0 < r) : intrinsicReducedVolume S T p r = ⊤ := by
      apply top_unique
      rw [← htop]
      exact iInf_le (fun t : _root_.Set.Ioi (0 : ℝ) => intrinsicReducedVolume S T p t) ⟨r, hr⟩
    simpa only [hval _ (mul_pos (htau _) ha), hval _ (mul_pos (htau _) hb), tsub_self]
      using (tendsto_const_nhds : _root_.Filter.Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) _root_.Filter.atTop (𝓝 0))
  · have h := ENNReal.Tendsto.sub
      (intrinsicReducedVolume_tendsto_mul_atTop_of_antitone S T p hmono htau hescape ha)
      (intrinsicReducedVolume_tendsto_mul_atTop_of_antitone S T p hmono htau hescape hb)
      (Or.inl htop)
    simpa only [tsub_self] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.intrinsicReducedVolume_sub_tendsto_zero_of_antitone then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.intrinsicReducedVolume_sub_tendsto_zero_of_antitone"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.intrinsicReducedVolume_sub_tendsto_zero_of_antitone ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.intrinsicReducedVolume_sub_tendsto_zero_of_antitone

section BackwardSlice

variable [CompleteSpace E]
  {D : RealTimeInterval} (F : CheegerGromovCompactness.PointedFlowData (I := I) D)

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

theorem backwardSliceSequence_normalizedShrinkerMass_tendsto
    (p : F.M) (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M)
    (hescape : _root_.Filter.Tendsto tau _root_.Filter.atTop _root_.Filter.atTop)
    (hmono : AntitoneOn (intrinsicReducedVolume F.S 0 p) (_root_.Set.Ioi 0)) :
    _root_.Filter.Tendsto (fun i => normalizedShrinkerMass
      ((backwardSliceSequence F tau htau q).obj i).metric
      (fun x => lCost F.S 0 p x (tau i) / (2 * Real.sqrt (tau i))))
      atTop (𝓝 (asymptoticReducedVolume F.S 0 p)) := by
  have heq (i : ℕ) : normalizedShrinkerMass
      ((backwardSliceSequence F tau htau q).obj i).metric
      (fun x => lCost F.S 0 p x (tau i) / (2 * Real.sqrt (tau i))) =
        intrinsicReducedVolume F.S 0 p (tau i) := by
    simpa only [zero_sub] using
      normalizedShrinkerMass_backward_slice_eq_intrinsicReducedVolume F.S 0 p (htau i)
  simp_rw [heq]
  simpa only [mul_one] using intrinsicReducedVolume_tendsto_mul_atTop_of_antitone
    F.S 0 p hmono htau hescape (a := 1) zero_lt_one

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceSequence_normalizedShrinkerMass_tendsto then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceSequence_normalizedShrinkerMass_tendsto"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceSequence_normalizedShrinkerMass_tendsto ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceSequence_normalizedShrinkerMass_tendsto

end BackwardSlice

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
