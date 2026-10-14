import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Quotient
import Submission.DifferentialGeometry.Topology.Manifold.BallChartTransport
import Submission.DifferentialGeometry.Topology.Manifold.EmbeddedBallContraction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Metric _root_.Submission.Metric _root_.Manifold _root_.Submission.Manifold _root_.Filter
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.Pointwise

namespace DifferentialGeometry.Topology

universe u

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.E3 target :: scope.openDecls } }

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
  [T2Space M]

omit [IsManifold (𝓡 3) ∞ M] [T2Space M] in
theorem exists_pos_forall_image_smul_closedBall_subset (c : BallChart 3 (𝓡 3) M)
    {V : Set M} (hV : V ∈ 𝓝 (c.chart (0 : E3))) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a : ℝ, 0 < a → a < ε →
      c.chart '' (a • Metric.closedBall (0 : E3) 2) ⊆ V := by
  have h0 : (0 : E3) ∈ c.chart.source :=
    c.closedBall_subset_source (Metric.mem_closedBall_self (by norm_num))
  have hcont : ContinuousAt (c.chart : E3 → M) 0 :=
    (c.chart.contMDiffOn_toFun.continuousOn.continuousAt
      (c.chart.open_source.mem_nhds h0))
  obtain ⟨ε₀, hε₀, hε₀V⟩ := Metric.mem_nhds_iff.mp (hcont hV)
  refine ⟨ε₀ / 4, by linarith, fun a ha0 ha => ?_⟩
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨z, hz, rfl⟩ := Set.mem_smul_set.mp hx
  refine hε₀V ?_
  rw [_root_.Metric.mem_ball, dist_eq_norm, sub_zero]
  have hz' : ‖z‖ ≤ 2 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  have hnorm : ‖a • z‖ = a * ‖z‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha0]
  rw [hnorm]
  nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_pos_forall_image_smul_closedBall_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_pos_forall_image_smul_closedBall_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_pos_forall_image_smul_closedBall_subset ``Submission.DifferentialGeometry.Topology.exists_pos_forall_image_smul_closedBall_subset

namespace ScaleModel

def scaleDiffeomorph (a : ℝ) (ha : a ≠ 0) : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞ where
  toEquiv :=
    { toFun := fun x => a • x
      invFun := fun x => a⁻¹ • x
      left_inv := fun x => by simp only [smul_smul, inv_mul_cancel₀ ha, one_smul]
      right_inv := fun x => by simp only [smul_smul, mul_inv_cancel₀ ha, one_smul] }
  contMDiff_toFun := (contDiff_const_smul a).contMDiff
  contMDiff_invFun := (contDiff_const_smul a⁻¹).contMDiff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ScaleModel.scaleDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ScaleModel.scaleDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ScaleModel.scaleDiffeomorph ``Submission.DifferentialGeometry.Topology.ScaleModel.scaleDiffeomorph

theorem scaleDiffeomorph_apply (a : ℝ) (ha : a ≠ 0) (x : E3) :
    scaleDiffeomorph a ha x = a • x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ScaleModel.scaleDiffeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ScaleModel.scaleDiffeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ScaleModel.scaleDiffeomorph_apply ``Submission.DifferentialGeometry.Topology.ScaleModel.scaleDiffeomorph_apply

theorem scaleDiffeomorph_toPartialDiffeomorph_apply (a : ℝ) (ha : a ≠ 0) (x : E3) :
    (scaleDiffeomorph a ha).toPartialDiffeomorph x = a • x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ScaleModel.scaleDiffeomorph_toPartialDiffeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ScaleModel.scaleDiffeomorph_toPartialDiffeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ScaleModel.scaleDiffeomorph_toPartialDiffeomorph_apply ``Submission.DifferentialGeometry.Topology.ScaleModel.scaleDiffeomorph_toPartialDiffeomorph_apply

end ScaleModel

namespace BallChart

omit [IsManifold (𝓡 3) ∞ M] [T2Space M] in
theorem scale_apply (c : BallChart 3 (𝓡 3) M) (a : ℝ) (ha : 0 < a) (x : E3) :
    ((ScaleModel.scaleDiffeomorph a (ne_of_gt ha)).toPartialDiffeomorph.trans c.chart : E3 → M)
        x = c.chart (a • x) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.scale_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.scale_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.scale_apply ``Submission.DifferentialGeometry.Topology.BallChart.scale_apply

omit [IsManifold (𝓡 3) ∞ M] [T2Space M] in
theorem scale_target (c : BallChart 3 (𝓡 3) M) (a : ℝ) (ha : 0 < a) :
    ((ScaleModel.scaleDiffeomorph a (ne_of_gt ha)).toPartialDiffeomorph.trans c.chart).target
      = c.chart.target := by
  change ((ScaleModel.scaleDiffeomorph a (ne_of_gt ha)).toPartialDiffeomorph.toOpenPartialHomeomorph.trans
    c.chart.toOpenPartialHomeomorph).target = c.chart.target
  rw [OpenPartialHomeomorph.trans_target]
  have htarget : (ScaleModel.scaleDiffeomorph a (ne_of_gt ha)).toPartialDiffeomorph.toOpenPartialHomeomorph.target
      = Set.univ := rfl
  rw [htarget, Set.preimage_univ, Set.inter_univ]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.scale_target then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.scale_target"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.scale_target ``Submission.DifferentialGeometry.Topology.BallChart.scale_target

omit [IsManifold (𝓡 3) ∞ M] [T2Space M] in
def scale (c : BallChart 3 (𝓡 3) M) (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    BallChart 3 (𝓡 3) M where
  chart := (ScaleModel.scaleDiffeomorph a (ne_of_gt ha)).toPartialDiffeomorph.trans c.chart
  closedBall_subset_source := by
    intro x hx
    change x ∈ ((ScaleModel.scaleDiffeomorph a (ne_of_gt ha)).toPartialDiffeomorph.toOpenPartialHomeomorph.trans
      c.chart.toOpenPartialHomeomorph).source
    rw [OpenPartialHomeomorph.trans_source]
    refine ⟨Set.mem_univ _, ?_⟩
    refine c.closedBall_subset_source ?_
    change _root_.Dist.dist (a • x) 0 ≤ 2
    rw [dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
    have hx2 : ‖x‖ ≤ 2 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hx
    nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.scale then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.scale"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.scale ``Submission.DifferentialGeometry.Topology.BallChart.scale

omit [IsManifold (𝓡 3) ∞ M] [T2Space M] in
theorem scale_apply' (c : BallChart 3 (𝓡 3) M) (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (x : E3) :
    (c.scale a ha ha1).chart x = c.chart (a • x) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.scale_apply' then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.scale_apply'"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.scale_apply' ``Submission.DifferentialGeometry.Topology.BallChart.scale_apply'

omit [IsManifold (𝓡 3) ∞ M] [T2Space M] in
theorem scale_target' (c : BallChart 3 (𝓡 3) M) (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    (c.scale a ha ha1).chart.target = c.chart.target :=
  scale_target c a ha

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.scale_target' then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.scale_target'"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.scale_target' ``Submission.DifferentialGeometry.Topology.BallChart.scale_target'

end BallChart

omit [IsManifold (𝓡 3) ∞ M] in
theorem ballChartTransport_scale (c : BallChart 3 (𝓡 3) M) (a : ℝ) (ha : 0 < a)
    (ha1 : a ≤ 1) : Manifold.BallChartTransport c (c.scale a ha ha1) := by
  obtain ⟨J, -, -, -, hJ, -⟩ :=
    Manifold.exists_diffeomorphs_contracting_embedded_closedBall c.chart (r := 2) (by norm_num)
      c.closedBall_subset_source (V := Set.univ) isOpen_univ (_root_.Set.subset_univ _)
  refine ⟨J (-Real.log a), fun x hx => ?_⟩
  rw [BallChart.scale_apply', hJ (-Real.log a) x (by linarith [Real.log_nonpos ha.le ha1]) hx]
  congr 1
  rw [neg_neg, Real.exp_log ha]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ballChartTransport_scale then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ballChartTransport_scale"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ballChartTransport_scale ``Submission.DifferentialGeometry.Topology.ballChartTransport_scale

variable {X : Type*} [TopologicalSpace X] [ChartedSpace E3 X] [T2Space X]

omit [T2Space X] in
theorem exists_pos_image_ball_subset (c : BallChart 3 (𝓡 3) X) {V : Set X}
    (hV : V ∈ 𝓝 (c.chart (0 : E3))) :
    ∃ ρ : ℝ, 0 < ρ ∧ c.chart '' Metric.ball (0 : E3) ρ ⊆ V := by
  have h0 : (0 : E3) ∈ c.chart.source :=
    c.closedBall_subset_source (Metric.mem_closedBall_self (by norm_num))
  have hcont : ContinuousAt (c.chart : E3 → X) 0 :=
    (c.chart.contMDiffOn_toFun.continuousOn.continuousAt
      (c.chart.open_source.mem_nhds h0))
  obtain ⟨ε₀, hε₀, hε₀V⟩ := Metric.mem_nhds_iff.mp (hcont hV)
  refine ⟨ε₀ / 2, by linarith, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  refine hε₀V ?_
  rw [_root_.Metric.mem_ball, dist_eq_norm, sub_zero]
  rw [_root_.Metric.mem_ball, dist_eq_norm, sub_zero] at hx
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_pos_image_ball_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_pos_image_ball_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_pos_image_ball_subset ``Submission.DifferentialGeometry.Topology.exists_pos_image_ball_subset

omit [T2Space X] in
theorem extendChartById_chartSymm_of_target (c : BallChart 3 (𝓡 3) X) (f : E3 → E3)
    {y : X} (hy : y ∈ c.chart.target) :
    Manifold.extendChartById c.chart.symm.toOpenPartialHomeomorph f y
      = c.chart (f (c.chart.symm y)) := by
  rw [Manifold.extendChartById]
  have hsrc : y ∈ c.chart.symm.toOpenPartialHomeomorph.source := hy
  rw [if_pos hsrc]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.extendChartById_chartSymm_of_target then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.extendChartById_chartSymm_of_target"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.extendChartById_chartSymm_of_target ``Submission.DifferentialGeometry.Topology.extendChartById_chartSymm_of_target

theorem exists_diffeomorph_eqOn_of_modelDiffeomorph (c c' : BallChart 3 (𝓡 3) X)
    {D : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞} {K S : Set E3}
    (hK : IsCompact K) (hKt : K ⊆ c'.chart.source)
    (hfix : ∀ z, z ∉ K → D z = z ∧ D.symm z = z)
    (hover : ∀ x ∈ S, c.chart x ∈ c'.chart.target)
    (hact : ∀ x ∈ S, D (c'.chart.symm (c.chart x)) = x) :
    ∃ Φ : Diffeomorph (𝓡 3) (𝓡 3) X X ∞, ∀ x ∈ S, Φ (c.chart x) = c'.chart x := by
  obtain ⟨J, -, -, hJe, -, -, -⟩ :=
    Manifold.exists_diffeomorph_extension_of_partial_chart_family
      (P := Unit) c'.chart.symm.toOpenPartialHomeomorph
      c'.chart.contMDiffOn_invFun c'.chart.contMDiffOn_toFun
      (fun _ : Unit => D)
      (D.contDiff.comp contDiff_snd) ((D.symm).contDiff.comp contDiff_snd)
      hK hKt (fun _ z hz => hfix z hz)
  refine ⟨J (), fun x hx => ?_⟩
  rw [(hJe () (c.chart x)).1, extendChartById_chartSymm_of_target c' D (hover x hx),
    hact x hx]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_diffeomorph_eqOn_of_modelDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_diffeomorph_eqOn_of_modelDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_diffeomorph_eqOn_of_modelDiffeomorph ``Submission.DifferentialGeometry.Topology.exists_diffeomorph_eqOn_of_modelDiffeomorph


theorem exists_pos_image_ball_subset_of_continuousAt {f : E3 → E3} (hf : ContinuousAt f 0)
    (hf0 : f 0 = 0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ρ : ℝ, 0 < ρ ∧ f '' Metric.ball (0 : E3) ρ ⊆ Metric.ball (0 : E3) δ := by
  have hpre : f ⁻¹' Metric.ball (f 0) δ ∈ 𝓝 (0 : E3) :=
    hf (Metric.ball_mem_nhds (f 0) hδ)
  rw [hf0] at hpre
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp hpre
  refine ⟨ρ, hρ, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  exact hρsub hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_pos_image_ball_subset_of_continuousAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_pos_image_ball_subset_of_continuousAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_pos_image_ball_subset_of_continuousAt ``Submission.DifferentialGeometry.Topology.exists_pos_image_ball_subset_of_continuousAt


end DifferentialGeometry.Topology
