import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoff
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RecenterAux
import Submission.DifferentialGeometry.Geometry.Metric.Family.JointSmoothness
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.Metric.Parameter
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalScalarCurvature
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NeckSpatialBridge

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.Set _root_.Filter
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {δ : ℝ} {k : ℕ}
    {N : NormalizedNeck (H.event i).terminal.metric δ k} {r : ℝ}

theorem IncomingBackwardNeck.metric_closeness_continuousOn
    (B : IncomingBackwardNeck H i N r) (j : ℕ) :
    ContinuousOn (fun v => metricDerivNormSupOn (neckClosedTest δ) j (B.metric v)
      (roundCylinderMetric.restrictOpen (neckBuffer δ))
      (roundCylinderMetric.restrictOpen (neckBuffer δ))) (_root_.Set.Icc (-1 : ℝ) 0) := by
  let gRef := roundCylinderMetric.restrictOpen (neckBuffer δ)
  have hg := metricCLMSection_jointContMDiffOn_of_local_coefficients
    B.metric (_root_.Set.Icc (-1 : ℝ) 0) B.metric_smooth
  apply metricDerivNormSupOn_continuousOn B.metric (fun _ => gRef) (fun _ => gRef)
    (U := _root_.Set.univ) _ (isCompact_neckClosedTest δ) (_root_.Set.subset_univ _) j
  intro x _
  refine ⟨(extChartAt NeckCylinderModel x).target, isOpen_extChartAt_target x,
    (extChartAt NeckCylinderModel x).map_source (mem_extChartAt_source x), Subset.rfl, ?_⟩
  intro a b
  refine ⟨chartGramOnE_joint_contDiffOn B.metric (_root_.Set.Icc (-1 : ℝ) 0) hg x a b, ?_, ?_⟩
  · exact (chartGramOnE_contDiffOn gRef x a b).comp contDiffOn_snd (fun q hq => hq.2)
  · exact (chartGramOnE_contDiffOn gRef x a b).comp contDiffOn_snd (fun q hq => hq.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.IncomingBackwardNeck.metric_closeness_continuousOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.IncomingBackwardNeck.metric_closeness_continuousOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.IncomingBackwardNeck.metric_closeness_continuousOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.IncomingBackwardNeck.metric_closeness_continuousOn

private theorem IncomingBackwardNeck.exists_normalizedNeck_at_time_of_scalar_normalized_closeness
    (B : IncomingBackwardNeck H i N r) {t : ℝ}
    (ht : t ∈ _root_.Set.Ico (H.time i.castSucc) (H.time i.succ))
    (hwindow : H.time i.succ - r ^ 2 ≤ t)
    (hQ : 0 < metricScalarAt ((H.event i).incoming.flow.base.metric t) N.center.val)
    (hclose : metricDerivNormSupOn (neckClosedTest δ) k
      (scaleMetric (r ^ 2 * metricScalarAt ((H.event i).incoming.flow.base.metric t) N.center.val)
        (mul_pos (sq_pos_of_pos B.radius_pos) hQ)
        (B.metric ((t - H.time i.succ) / r ^ 2)))
      (roundCylinderMetric.restrictOpen (neckBuffer δ))
      (roundCylinderMetric.restrictOpen (neckBuffer δ)) < δ) :
    ∃ A : NormalizedNeck ((H.event i).incoming.flow.base.metric t) δ k,
      A.center = N.center.val ∧ A.sphereMark = N.sphereMark ∧
      (∀ z : neckBuffer δ, A.chart z = (N.chart z).val) ∧
      A.normalizedMetric = scaleMetric
        (r ^ 2 * metricScalarAt ((H.event i).incoming.flow.base.metric t) N.center.val)
        (mul_pos (sq_pos_of_pos B.radius_pos) hQ)
        (B.metric ((t - H.time i.succ) / r ^ 2)) := by
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos B.radius_pos
  have htime : H.time i.succ + r ^ 2 * ((t - H.time i.succ) / r ^ 2) = t := by
    field_simp [B.radius_pos.ne']
    ring
  have hv : (t - H.time i.succ) / r ^ 2 ∈ _root_.Set.Ico (-1 : ℝ) 0 := by
    refine ⟨(le_div_iff₀ hr2).mpr ?_, div_neg_of_neg_of_pos (sub_neg.mpr ht.2) hr2⟩
    linarith
  have ha : H.time i.succ - r ^ 2 < H.time i.succ := by linarith
  let chart := B.stageChart i le_rfl ha
  have hchart : ∀ z : neckBuffer δ, chart z = (N.chart z).val :=
    B.terminal_chart ha
  let Q := metricScalarAt ((H.event i).incoming.flow.base.metric t) N.center.val
  let gN := scaleMetric (r ^ 2 * Q) (mul_pos hr2 hQ)
    (B.metric ((t - H.time i.succ) / r ^ 2))
  refine ⟨{
    delta_pos := N.delta_pos
    delta_lt_one := N.delta_lt_one
    sphereMark := N.sphereMark
    center := N.center.val
    chart := chart
    chart_smooth := B.stageChart_smooth i le_rfl ha
    marked := (hchart _).trans (congrArg Subtype.val N.marked)
    scale := Q
    scale_pos := hQ
    scale_scalar := rfl
    normalizedMetric := gN
    normalized_inner := ?_
    closeness := hclose }, rfl, rfl, hchart, rfl⟩
  intro z V W
  have hB := B.metric_on_slab i le_rfl ha _ hv
    (htime.symm ▸ ht.1) (htime.symm ▸ ht.2) z V W
  rw [htime] at hB
  change (scaleMetric (r ^ 2 * Q) (mul_pos hr2 hQ)
    (B.metric ((t - H.time i.succ) / r ^ 2))).inner z V W = _
  rw [scaleMetric_inner, hB]
  dsimp only [chart]
  field_simp [B.radius_pos.ne']

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.IncomingBackwardNeck.exists_normalizedNeck_at_time_of_scalar_normalized_closeness
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.IncomingBackwardNeck.exists_normalizedNeck_at_time_of_scalar_normalized_closeness target :: scope.openDecls } }

theorem IncomingBackwardNeck.eventually_exists_normalizedNeck
    (B : IncomingBackwardNeck H i N r) (hscale : N.scale = (r ^ 2)⁻¹) :
    ∀ᶠ t in 𝓝[<] H.time i.succ,
      ∃ A : NormalizedNeck ((H.event i).incoming.flow.base.metric t) δ k,
        A.center = N.center.val ∧ A.sphereMark = N.sphereMark ∧
        ∀ z : neckBuffer δ, A.chart z = (N.chart z).val := by
  let s := H.time i.succ
  let Q := fun t => metricScalarAt ((H.event i).incoming.flow.base.metric t) N.center.val
  let v := fun t => (t - s) / r ^ 2
  let gRef := roundCylinderMetric.restrictOpen (neckBuffer δ)
  let err := fun v => metricDerivNormSupOn (neckClosedTest δ) k (B.metric v) gRef gRef
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos B.radius_pos
  have hwin : ∀ᶠ t in 𝓝[<] s, t ∈ _root_.Set.Ioo (_root_.Max.max (H.time i.castSucc) (s - r ^ 2)) s :=
    Ioo_mem_nhdsLT (max_lt (H.time_strictMono i.castSucc_lt_succ) (by linarith))
  have hv : ∀ᶠ t in 𝓝[<] s, v t ∈ _root_.Set.Ico (-1 : ℝ) 0 := by
    filter_upwards [hwin] with t ht
    constructor
    · dsimp [v]
      apply (le_div_iff₀ hr2).mpr
      linarith [le_max_right (H.time i.castSucc) (s - r ^ 2), ht.1]
    · exact div_neg_of_neg_of_pos (sub_neg.mpr ht.2) hr2
  have hvt : _root_.Filter.Tendsto v (𝓝[<] s) (𝓝[_root_.Set.Icc (-1 : ℝ) 0] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, hv.mono (fun t ht => ⟨ht.1, ht.2.le⟩)⟩
    have hh : _root_.Filter.Tendsto (fun t : ℝ => (t - s) / r ^ 2) (𝓝 s) (𝓝 ((s - s) / r ^ 2)) :=
      (continuous_id.sub continuous_const).continuousAt.tendsto.div_const (r ^ 2)
    simpa only [sub_self, zero_div] using hh.mono_left nhdsWithin_le_nhds
  have herror : _root_.Filter.Tendsto (fun t => err (v t)) (𝓝[<] s) (𝓝 (err 0)) :=
    ((B.metric_closeness_continuousOn k 0 (by norm_num)).tendsto).comp hvt
  have hQ : _root_.Filter.Tendsto Q (𝓝[<] s) (𝓝 N.scale) := by
    simpa only [N.scale_scalar] using (H.event i).terminal.tendsto_metricScalarAt N.center
  have hfac : _root_.Filter.Tendsto (fun t => r ^ 2 * Q t) (𝓝[<] s) (𝓝 1) := by
    have hh := hQ.const_mul (r ^ 2)
    rw [hscale, mul_inv_cancel₀ hr2.ne'] at hh
    exact hh
  have hterm : _root_.Filter.Tendsto (fun t => r ^ 2 * Q t * err (v t) +
        |r ^ 2 * Q t - 1| * Real.sqrt (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) : ℝ))
      (𝓝[<] s) (𝓝 (err 0)) := by
    have hh := (hfac.mul herror).add (((hfac.sub_const 1).abs).mul_const
      (Real.sqrt (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) : ℝ)))
    simpa only [one_mul, sub_self, abs_zero, _root_.MulZeroClass.zero_mul, add_zero] using hh
  have hzero : err 0 < δ := by
    dsimp [err]
    rw [B.terminal_metric]
    exact N.closeness
  have hbound := hterm.eventually_lt_const hzero
  have hpos := hQ.eventually (Ioi_mem_nhds N.scale_pos)
  filter_upwards [hwin, hv, hbound, hpos] with t ht hvt hbt hQt
  have hclose : metricDerivNormSupOn (neckClosedTest δ) k
      (scaleMetric (r ^ 2 * Q t) (mul_pos hr2 hQt) (B.metric (v t))) gRef gRef < δ :=
    (metricDerivNormSupOn_scaleMetric_left_le (isCompact_neckClosedTest δ) k
      (r ^ 2 * Q t) (mul_pos hr2 hQt) (B.metric (v t)) gRef).trans_lt hbt
  have hat : H.time i.castSucc ≤ t :=
    (le_max_left (H.time i.castSucc) (s - r ^ 2)).trans ht.1.le
  have hleft : H.time i.succ - r ^ 2 ≤ t :=
    (le_max_right (H.time i.castSucc) (s - r ^ 2)).trans ht.1.le
  obtain ⟨A, hcenter, hmark, hchart, _⟩ :=
    B.exists_normalizedNeck_at_time_of_scalar_normalized_closeness ⟨hat, ht.2⟩ hleft hQt hclose
  exact ⟨A, hcenter, hmark, hchart⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.IncomingBackwardNeck.eventually_exists_normalizedNeck then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.IncomingBackwardNeck.eventually_exists_normalizedNeck"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.IncomingBackwardNeck.eventually_exists_normalizedNeck ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.IncomingBackwardNeck.eventually_exists_normalizedNeck

theorem IncomingBackwardNeck.eventually_exists_spatialNeck
    (B : IncomingBackwardNeck H i N r) (hscale : N.scale = (r ^ 2)⁻¹)
    {eps : ℝ} (heps : δ ≤ eps) (hsmall : eps < 1 / 11) (hk : ⌈eps⁻¹⌉₊ ≤ k) :
    ∀ᶠ t in 𝓝[<] H.time i.succ,
      ∃ nk : SpatialNeck ((H.event i).incoming.flow.base.metric t) eps N.center.val,
        nk.center = N.sphereMark ∧
        ∀ z : neckBuffer δ, nk.map z.val = (N.chart z).val := by
  filter_upwards [B.eventually_exists_normalizedNeck hscale] with t ht
  obtain ⟨A, hcenter, hmark, hchart⟩ := ht
  obtain ⟨nk, hnmark, hnchart⟩ := A.exists_spatialNeck heps hsmall hk
  have hout : ∃ nk : SpatialNeck ((H.event i).incoming.flow.base.metric t) eps A.center,
      nk.center = N.sphereMark ∧
      ∀ z : neckBuffer δ, nk.map z.val = (N.chart z).val :=
    ⟨nk, hnmark.trans hmark, fun z => (hnchart z).trans (hchart z)⟩
  rw [hcenter] at hout
  exact hout

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.IncomingBackwardNeck.eventually_exists_spatialNeck then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.IncomingBackwardNeck.eventually_exists_spatialNeck"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.IncomingBackwardNeck.eventually_exists_spatialNeck ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.IncomingBackwardNeck.eventually_exists_spatialNeck

theorem GeometricCutoffRecord.eventually_exists_spatialNeck
    {parameters : CutoffParameters} (R : GeometricCutoffRecord H i parameters)
    {eps : ℝ} (hsmall : eps < 1 / 11)
    (heps : ∀ j, R.delta j ≤ eps) :
    ∀ᶠ t in 𝓝[<] H.time i.succ,
      ∀ j : (H.event i).transition.trace.tubes.Index,
        ∃ nk : SpatialNeck ((H.event i).incoming.flow.base.metric t) eps (R.neck j).center.val,
          nk.center = (R.neck j).sphereMark ∧
          ∀ q : TubeDomain, nk.map (q.1, q.2.val) =
            (H.event i).transition.trace.tubes.tube j q := by
  apply (_root_.Filter.eventually_all).2
  intro j
  have hk : ⌈eps⁻¹⌉₊ ≤ R.order j := by
    have hceil : ⌈eps⁻¹⌉₊ ≤ ⌈(R.delta j)⁻¹⌉₊ :=
      Nat.ceil_mono (inv_anti₀ (R.delta_pos j) (heps j))
    have hf := Nat.ceil_le_floor_add_one ((R.delta j)⁻¹)
    have horder := (le_max_right (parameters.modelOrder + 6)
      (2 * ⌊(R.delta j)⁻¹⌋₊ + 4)).trans (R.order_lower j)
    omega
  filter_upwards [(R.backward j).eventually_exists_spatialNeck (R.scale_eq j)
    (heps j) hsmall hk] with t ht
  obtain ⟨nk, hcenter, hmap⟩ := ht
  refine ⟨nk, hcenter, ?_⟩
  intro q
  exact (hmap ⟨(q.1, q.2.val), R.tube_in_buffer j q⟩).trans
    (R.tube_eq j q (R.tube_in_buffer j q)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.eventually_exists_spatialNeck then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.eventually_exists_spatialNeck"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.eventually_exists_spatialNeck ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.eventually_exists_spatialNeck

theorem GeometricCutoffRecord.exists_late_spatialNecks
    {parameters : CutoffParameters} (R : GeometricCutoffRecord H i parameters)
    {eps : ℝ} (hsmall : eps < 1 / 11)
    (heps : ∀ j, R.delta j ≤ eps) :
    ∃ d ∈ _root_.Set.Ico (H.time i.castSucc) (H.time i.succ), ∀ t ∈ _root_.Set.Ioo d (H.time i.succ),
      ∀ j : (H.event i).transition.trace.tubes.Index,
        ∃ nk : SpatialNeck ((H.event i).incoming.flow.base.metric t) eps (R.neck j).center.val,
          nk.center = (R.neck j).sphereMark ∧
          ∀ q : TubeDomain, nk.map (q.1, q.2.val) =
            (H.event i).transition.trace.tubes.tube j q := by
  exact (mem_nhdsLT_iff_exists_mem_Ico_Ioo_subset
    (H.time_strictMono i.castSucc_lt_succ)).mp (R.eventually_exists_spatialNeck hsmall heps)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.exists_late_spatialNecks then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.exists_late_spatialNecks"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.exists_late_spatialNecks ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.exists_late_spatialNecks

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
