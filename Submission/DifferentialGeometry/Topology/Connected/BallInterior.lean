import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.LocallyConvex.WithSeminorms

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section

open _root_.Set _root_.Metric

namespace DifferentialGeometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem joinedIn_ball_inter_of_isPreconnected_closedBall_inter
    {R : ℝ} (hR : 0 < R) {U : Set E} (hU : IsOpen U)
    (hconn : IsPreconnected (_root_.Metric.closedBall (0 : E) R ∩ U))
    {x y : E} (hx : x ∈ _root_.Metric.ball (0 : E) R ∩ U) (hy : y ∈ _root_.Metric.ball (0 : E) R ∩ U) :
    JoinedIn (_root_.Metric.ball (0 : E) R ∩ U) x y := by
  let D := _root_.Metric.closedBall (0 : E) R
  let : LocallyPathConnectedSpace D := (convex_closedBall (0 : E) R).locallyPathConnectedSpace
  let S : Set D := Subtype.val ⁻¹' U
  have hS : IsOpen S := hU.preimage continuous_subtype_val
  have himage : Subtype.val '' S = _root_.Metric.closedBall (0 : E) R ∩ U := by
    ext z
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.property, hz⟩
    · rintro ⟨hzD, hzU⟩
      exact ⟨⟨z, hzD⟩, hzU, rfl⟩
  have hSc : IsPreconnected S :=
    Topology.IsInducing.subtypeVal.isPreconnected_image.mp (himage.symm ▸ hconn)
  let xD : D := ⟨x, _root_.Metric.ball_subset_closedBall hx.1⟩
  let yD : D := ⟨y, _root_.Metric.ball_subset_closedBall hy.1⟩
  have hpath := hS.isConnected_iff_isPathConnected.mp ⟨⟨xD, hx.2⟩, hSc⟩
  obtain ⟨γ, hγ⟩ := hpath.joinedIn xD hx.2 yD hy.2
  let γE : Path x y := γ.map continuous_subtype_val
  have hγD (t : unitInterval) : γE t ∈ _root_.Metric.closedBall (0 : E) R := (γ t).property
  have hγU (t : unitInterval) : γE t ∈ U := hγ t
  obtain ⟨δ, hδ, hthick⟩ := (isCompact_range γE.continuous).exists_thickening_subset_open
    hU (range_subset_iff.mpr hγU)
  let θ := _root_.Min.min (1 / 2 : ℝ) (δ / (2 * R))
  have hθ : 0 < θ := lt_min (by norm_num) (div_pos hδ (by positivity))
  have hθhalf : θ ≤ 1 / 2 := min_le_left _ _
  have hθδ : θ * R < δ := by
    have hle : θ ≤ δ / (2 * R) := min_le_right _ _
    have hh := (le_div_iff₀ (by positivity : 0 < 2 * R)).mp hle
    nlinarith
  let kappa := 1 - θ
  have hkappa : 0 < kappa := by dsimp only [kappa]; linarith
  have hkappa1 : kappa < 1 := by dsimp only [kappa]; linarith
  have hdist (z : E) (hz : z ∈ _root_.Metric.closedBall (0 : E) R) : _root_.Dist.dist (kappa • z) z < δ := by
    rw [dist_eq_norm, show kappa • z - z = (kappa - 1) • z by
      simp only [sub_smul, one_smul], norm_smul, Real.norm_eq_abs]
    have habs : |kappa - 1| = θ := by rw [abs_of_neg (by linarith)]; dsimp only [kappa]; ring
    rw [habs]
    exact (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hz) hθ.le).trans_lt hθδ
  have hshrink (z : E) (hz : z ∈ _root_.Metric.closedBall (0 : E) R) : kappa • z ∈ _root_.Metric.ball (0 : E) R := by
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hkappa]
    exact (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hz) hkappa.le).trans_lt
      (by nlinarith)
  have hkappaU (t : unitInterval) : kappa • γE t ∈ U :=
    hthick ((_root_.Metric.ball_subset_thickening (show γE t ∈ _root_.Set.range γE from ⟨t, rfl⟩) δ) (hdist _ (hγD t)))
  have hkappapath : JoinedIn (_root_.Metric.ball (0 : E) R ∩ U) (kappa • x) (kappa • y) := by
    refine ⟨γE.map (continuous_const.smul continuous_id), ?_⟩
    intro t
    exact ⟨hshrink _ (hγD t), hkappaU t⟩
  have hjoin (z : E) (hz : z ∈ _root_.Metric.ball (0 : E) R ∩ U) (hzrange : z ∈ _root_.Set.range γE) :
      JoinedIn (_root_.Metric.ball (0 : E) R ∩ U) z (kappa • z) := by
    apply JoinedIn.of_segment_subset
    exact _root_.Set.subset_inter
      ((convex_ball (0 : E) R).segment_subset hz.1 (hshrink z (_root_.Metric.ball_subset_closedBall hz.1)))
      (((convex_ball z δ).segment_subset (_root_.Metric.mem_ball_self hδ)
        (hdist z (_root_.Metric.ball_subset_closedBall hz.1))).trans
          ((_root_.Metric.ball_subset_thickening hzrange δ).trans hthick))
  exact (hjoin x hx ⟨0, γE.source⟩).trans
    (hkappapath.trans (hjoin y hy ⟨1, γE.target⟩).symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.joinedIn_ball_inter_of_isPreconnected_closedBall_inter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.joinedIn_ball_inter_of_isPreconnected_closedBall_inter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.joinedIn_ball_inter_of_isPreconnected_closedBall_inter ``Submission.DifferentialGeometry.Topology.joinedIn_ball_inter_of_isPreconnected_closedBall_inter

theorem isPreconnected_ball_inter_of_isPreconnected_closedBall_inter
    {R : ℝ} (hR : 0 < R) {U : Set E} (hU : IsOpen U)
    (hconn : IsPreconnected (_root_.Metric.closedBall (0 : E) R ∩ U)) :
    IsPreconnected (_root_.Metric.ball (0 : E) R ∩ U) := by
  apply isPreconnected_of_forall_pair
  intro x hx y hy
  obtain ⟨γ, hγ⟩ := joinedIn_ball_inter_of_isPreconnected_closedBall_inter hR hU hconn hx hy
  exact ⟨range γ, range_subset_iff.mpr hγ, ⟨0, γ.source⟩, ⟨1, γ.target⟩,
    (isConnected_range γ.continuous).isPreconnected⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isPreconnected_ball_inter_of_isPreconnected_closedBall_inter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isPreconnected_ball_inter_of_isPreconnected_closedBall_inter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isPreconnected_ball_inter_of_isPreconnected_closedBall_inter ``Submission.DifferentialGeometry.Topology.isPreconnected_ball_inter_of_isPreconnected_closedBall_inter


end DifferentialGeometry.Topology

open _root_.Submission.DifferentialGeometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open _root_.ContinuousOn in
theorem ContinuousOn.isPreconnected_ball_gt_of_closedBall
    {R : ℝ} (hR : 0 < R) {f : E → ℝ}
    (hf : ContinuousOn f (_root_.Metric.closedBall (0 : E) R)) {a : ℝ}
    (hconn : IsPreconnected (_root_.Metric.closedBall (0 : E) R ∩ {x | a < f x})) :
    IsPreconnected (_root_.Metric.ball (0 : E) R ∩ {x | a < f x}) := by
  let D := _root_.Metric.closedBall (0 : E) R
  have hopen : IsOpen {x : D | a < f x} :=
    isOpen_lt continuous_const (hf.domRestrict)
  obtain ⟨U, hU, hUS⟩ := _root_.Topology.IsInducing.subtypeVal.isOpen_iff.mp hopen
  have heq (x : E) (hx : x ∈ _root_.Metric.closedBall (0 : E) R) : x ∈ U ↔ a < f x := by
    exact Set.ext_iff.mp hUS ⟨x, hx⟩
  have hc : _root_.Metric.closedBall (0 : E) R ∩ U = _root_.Metric.closedBall (0 : E) R ∩ {x | a < f x} := by
    ext x
    exact and_congr_right (heq x)
  have ho : _root_.Metric.ball (0 : E) R ∩ U = _root_.Metric.ball (0 : E) R ∩ {x | a < f x} := by
    ext x
    exact and_congr_right (fun hx => heq x (_root_.Metric.ball_subset_closedBall hx))
  rw [← ho]
  exact isPreconnected_ball_inter_of_isPreconnected_closedBall_inter hR hU (hc.symm ▸ hconn)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.ContinuousOn
  let env ← Lean.getEnv
  if env.contains `ContinuousOn.isPreconnected_ball_gt_of_closedBall then
    throwError "Refusing to shadow existing declaration ContinuousOn.isPreconnected_ball_gt_of_closedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousOn.isPreconnected_ball_gt_of_closedBall ``Submission.ContinuousOn.isPreconnected_ball_gt_of_closedBall

open _root_.ContinuousOn in
theorem ContinuousOn.isPreconnected_ball_lt_of_closedBall
    {R : ℝ} (hR : 0 < R) {f : E → ℝ}
    (hf : ContinuousOn f (_root_.Metric.closedBall (0 : E) R)) {a : ℝ}
    (hconn : IsPreconnected (_root_.Metric.closedBall (0 : E) R ∩ {x | f x < a})) :
    IsPreconnected (_root_.Metric.ball (0 : E) R ∩ {x | f x < a}) := by
  have h := hf.neg.isPreconnected_ball_gt_of_closedBall hR (a := -a)
  simpa only [Pi.neg_apply, neg_lt_neg_iff] using
    h (by simpa only [Pi.neg_apply, neg_lt_neg_iff] using hconn)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousOn.isPreconnected_ball_lt_of_closedBall then
    throwError "Refusing to shadow existing declaration ContinuousOn.isPreconnected_ball_lt_of_closedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousOn.isPreconnected_ball_lt_of_closedBall ``Submission.ContinuousOn.isPreconnected_ball_lt_of_closedBall

end

end
