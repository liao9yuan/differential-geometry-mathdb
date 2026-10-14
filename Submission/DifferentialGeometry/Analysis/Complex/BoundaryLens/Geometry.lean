import Submission.DifferentialGeometry.Analysis.Convex.GaugeRescale.Lipschitz
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.ConstMulAction
import Submission.DifferentialGeometry.Analysis.Complex.CircleArc
import Mathlib.Analysis.Normed.Module.Normalize
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.LoopSpace.SpanningDisk

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Metric
open scoped _root_.Pointwise _root_.NNReal _root_.Topology

namespace DifferentialGeometry.Analysis

def boundaryLens (ρ : ℝ) : Set ℂ :=
  _root_.Metric.closedBall (-1) ρ ∩ _root_.Metric.closedBall 0 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.boundaryLens then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.boundaryLens"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.boundaryLens ``Submission.DifferentialGeometry.Analysis.boundaryLens

def boundaryLensCenter (ρ : ℝ) : ℂ := ((-1 + ρ / 2 : ℝ) : ℂ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.boundaryLensCenter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.boundaryLensCenter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.boundaryLensCenter ``Submission.DifferentialGeometry.Analysis.boundaryLensCenter

def normalizedBoundaryLens (ρ : ℝ) : Set ℂ :=
  (fun z => boundaryLensCenter ρ + ρ • z) ⁻¹' boundaryLens ρ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.normalizedBoundaryLens then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.normalizedBoundaryLens"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.normalizedBoundaryLens ``Submission.DifferentialGeometry.Analysis.normalizedBoundaryLens

theorem normalizedBoundaryLens_convex (ρ : ℝ) : Convex ℝ (normalizedBoundaryLens ρ) := by
  let f : ℂ →ᵃ[ℝ] ℂ :=
    (AffineMap.const ℝ ℂ (boundaryLensCenter ρ)) +
      (ρ • (LinearMap.id : ℂ →ₗ[ℝ] ℂ)).toAffineMap
  exact ((convex_closedBall (-1 : ℂ) ρ).inter (convex_closedBall 0 1)).affine_preimage f

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.normalizedBoundaryLens_convex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.normalizedBoundaryLens_convex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.normalizedBoundaryLens_convex ``Submission.DifferentialGeometry.Analysis.normalizedBoundaryLens_convex

theorem normalizedBoundaryLens_isClosed (ρ : ℝ) : IsClosed (normalizedBoundaryLens ρ) :=
  (isClosed_closedBall.inter _root_.Metric.isClosed_closedBall).preimage (by fun_prop)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.normalizedBoundaryLens_isClosed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.normalizedBoundaryLens_isClosed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.normalizedBoundaryLens_isClosed ``Submission.DifferentialGeometry.Analysis.normalizedBoundaryLens_isClosed

private theorem boundaryLensCenter_norm {ρ : ℝ} (hρ1 : ρ ≤ 1) :
    ‖boundaryLensCenter ρ‖ = 1 - ρ / 2 := by
  rw [boundaryLensCenter, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonpos (by linarith)]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.boundaryLensCenter_norm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.boundaryLensCenter_norm target :: scope.openDecls } }

private theorem boundaryLensCenter_add_one_norm {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ‖boundaryLensCenter ρ + 1‖ = ρ / 2 := by
  have heq : boundaryLensCenter ρ + 1 = ((ρ / 2 : ℝ) : ℂ) := by
    simp only [boundaryLensCenter, Complex.ofReal_add, Complex.ofReal_neg,
      Complex.ofReal_one]
    ring
  rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.boundaryLensCenter_add_one_norm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.boundaryLensCenter_add_one_norm target :: scope.openDecls } }

theorem closedBall_subset_normalizedBoundaryLens {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    closedBall (0 : ℂ) (1 / 2) ⊆ normalizedBoundaryLens ρ := by
  intro z hz
  have hz' : ‖z‖ ≤ 1 / 2 := by simpa only [_root_.Metric.mem_closedBall, dist_zero_right] using hz
  have hsz : ‖ρ • z‖ ≤ ρ / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
    nlinarith
  constructor
  · change _root_.Dist.dist (boundaryLensCenter ρ + ρ • z) (-1) ≤ ρ
    rw [dist_eq_norm, sub_neg_eq_add,
      show boundaryLensCenter ρ + ρ • z + 1 = (boundaryLensCenter ρ + 1) + ρ • z by abel]
    exact (norm_add_le _ _).trans (by rw [boundaryLensCenter_add_one_norm hρ.le]; linarith)
  · change _root_.Dist.dist (boundaryLensCenter ρ + ρ • z) 0 ≤ 1
    rw [dist_zero_right]
    exact (norm_add_le _ _).trans (by rw [boundaryLensCenter_norm hρ1]; linarith)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.closedBall_subset_normalizedBoundaryLens then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.closedBall_subset_normalizedBoundaryLens"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.closedBall_subset_normalizedBoundaryLens ``Submission.DifferentialGeometry.Analysis.closedBall_subset_normalizedBoundaryLens

theorem normalizedBoundaryLens_subset_closedBall {ρ : ℝ} (hρ : 0 < ρ) :
    normalizedBoundaryLens ρ ⊆ _root_.Metric.closedBall (0 : ℂ) (3 / 2) := by
  intro z hz
  have hz' : ‖(boundaryLensCenter ρ + ρ • z) + 1‖ ≤ ρ := by
    simpa only [_root_.Metric.mem_closedBall, dist_eq_norm, sub_neg_eq_add] using hz.1
  have hdist : ‖ρ • z‖ ≤ ρ + ρ / 2 := by
    calc
      ‖ρ • z‖ = ‖((boundaryLensCenter ρ + ρ • z) + 1) - (boundaryLensCenter ρ + 1)‖ := by
        congr 1
        abel
      _ ≤ ‖(boundaryLensCenter ρ + ρ • z) + 1‖ + ‖boundaryLensCenter ρ + 1‖ := norm_sub_le _ _
      _ ≤ ρ + ρ / 2 := by
        rw [boundaryLensCenter_add_one_norm hρ.le]
        exact add_le_add hz' le_rfl
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ] at hdist
  rw [_root_.Metric.mem_closedBall, dist_zero_right]
  nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.normalizedBoundaryLens_subset_closedBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.normalizedBoundaryLens_subset_closedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.normalizedBoundaryLens_subset_closedBall ``Submission.DifferentialGeometry.Analysis.normalizedBoundaryLens_subset_closedBall

theorem normalizedBoundaryLens_uniform_bounds {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    _root_.Metric.closedBall (0 : ℂ) (1 / 4) ⊆ normalizedBoundaryLens ρ ∧
      normalizedBoundaryLens ρ ⊆ _root_.Metric.closedBall (0 : ℂ) (3 / 2) :=
  ⟨(_root_.Metric.closedBall_subset_closedBall (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2)).trans
      (closedBall_subset_normalizedBoundaryLens hρ hρ1),
    normalizedBoundaryLens_subset_closedBall hρ⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.normalizedBoundaryLens_uniform_bounds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.normalizedBoundaryLens_uniform_bounds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.normalizedBoundaryLens_uniform_bounds ``Submission.DifferentialGeometry.Analysis.normalizedBoundaryLens_uniform_bounds

theorem normalizedBoundaryLens_gaugeRescale_lipschitz {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    LipschitzWith 12 (gaugeRescale (_root_.Metric.ball (0 : ℂ) 1) (normalizedBoundaryLens ρ)) ∧
      LipschitzWith 12 (gaugeRescale (normalizedBoundaryLens ρ) (_root_.Metric.ball (0 : ℂ) 1)) := by
  have hb := normalizedBoundaryLens_uniform_bounds hρ hρ1
  have hin : _root_.Metric.ball (0 : ℂ) (1 / 4) ⊆ normalizedBoundaryLens ρ :=
    ball_subset_closedBall.trans hb.1
  constructor
  · have h := lipschitzWith_gaugeRescale_from_unitBall (r := (1 / 4 : ℝ≥0))
      (R := (3 / 2 : ℝ≥0)) (normalizedBoundaryLens_convex ρ) (by norm_num) (by norm_num)
      (by simpa using hin) (by simpa using hb.2)
    norm_num at h ⊢
    exact h
  · have h := lipschitzWith_gaugeRescale_to_unitBall (r := (1 / 4 : ℝ≥0))
      (normalizedBoundaryLens_convex ρ) (by norm_num) (by simpa using hin)
    norm_num at h ⊢
    exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.normalizedBoundaryLens_gaugeRescale_lipschitz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.normalizedBoundaryLens_gaugeRescale_lipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.normalizedBoundaryLens_gaugeRescale_lipschitz ``Submission.DifferentialGeometry.Analysis.normalizedBoundaryLens_gaugeRescale_lipschitz

theorem exists_normalizedBoundaryLens_bilipschitz_homeomorph {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ e : ℂ ≃ₜ ℂ,
      (∀ z, e z = gaugeRescale (_root_.Metric.ball (0 : ℂ) 1) (normalizedBoundaryLens ρ) z) ∧
      LipschitzWith 12 e ∧ LipschitzWith 12 e.symm ∧
      e '' _root_.Metric.closedBall (0 : ℂ) 1 = normalizedBoundaryLens ρ := by
  have hb := normalizedBoundaryLens_uniform_bounds hρ hρ1
  have hnb : normalizedBoundaryLens ρ ∈ 𝓝 (0 : ℂ) :=
    Filter.mem_of_superset (_root_.Metric.closedBall_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 4)) hb.1
  have hbound : Bornology.IsBounded (normalizedBoundaryLens ρ) :=
    Metric.isBounded_closedBall.subset hb.2
  let e := gaugeRescaleHomeomorph (_root_.Metric.ball (0 : ℂ) 1) (normalizedBoundaryLens ρ)
    (convex_ball 0 1) (_root_.Metric.ball_mem_nhds _ zero_lt_one) (NormedSpace.isVonNBounded_ball ℝ ℂ 1)
    (normalizedBoundaryLens_convex ρ) hnb (NormedSpace.isVonNBounded_of_isBounded ℝ hbound)
  have hlip := normalizedBoundaryLens_gaugeRescale_lipschitz hρ hρ1
  refine ⟨e, fun _ => rfl, hlip.1, hlip.2, ?_⟩
  have heq := image_gaugeRescaleHomeomorph_closure
    (convex_ball (0 : ℂ) 1) (_root_.Metric.ball_mem_nhds _ zero_lt_one)
    (NormedSpace.isVonNBounded_ball ℝ ℂ 1)
    (normalizedBoundaryLens_convex ρ) hnb (NormedSpace.isVonNBounded_of_isBounded ℝ hbound)
  simpa only [closure_ball _ (by norm_num : (1 : ℝ) ≠ 0),
    (normalizedBoundaryLens_isClosed ρ).closure_eq] using heq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_normalizedBoundaryLens_bilipschitz_homeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_normalizedBoundaryLens_bilipschitz_homeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_normalizedBoundaryLens_bilipschitz_homeomorph ``Submission.DifferentialGeometry.Analysis.exists_normalizedBoundaryLens_bilipschitz_homeomorph

end DifferentialGeometry.Analysis

end

noncomputable section

open _root_.Set _root_.Metric
open scoped _root_.NNReal _root_.Topology

namespace DifferentialGeometry.Analysis

theorem boundaryLens_convex (ρ : ℝ) : Convex ℝ (boundaryLens ρ) :=
  (convex_closedBall (-1 : ℂ) ρ).inter (convex_closedBall 0 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.boundaryLens_convex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.boundaryLens_convex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.boundaryLens_convex ``Submission.DifferentialGeometry.Analysis.boundaryLens_convex

theorem exists_boundaryLens_bilipschitz_homeomorph {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ e : ℂ ≃ₜ ℂ,
      (∀ z, e z = boundaryLensCenter ρ +
        ρ • gaugeRescale (_root_.Metric.ball (0 : ℂ) 1) (normalizedBoundaryLens ρ) z) ∧
      LipschitzWith (Real.toNNReal (12 * ρ)) e ∧
      LipschitzWith (Real.toNNReal (12 / ρ)) e.symm ∧
      e '' _root_.Metric.closedBall (0 : ℂ) 1 = boundaryLens ρ ∧
      e '' _root_.Metric.sphere (0 : ℂ) 1 = frontier (boundaryLens ρ) := by
  obtain ⟨e₀, he₀, hL₀, hLi₀, himage₀⟩ :=
    exists_normalizedBoundaryLens_bilipschitz_homeomorph hρ hρ1
  let f : ℂ ≃ₜ ℂ := (Homeomorph.smulOfNeZero ρ hρ.ne').trans
    (Homeomorph.addLeft (boundaryLensCenter ρ))
  let e : ℂ ≃ₜ ℂ := e₀.trans f
  have he (z : ℂ) : e z = boundaryLensCenter ρ + ρ • e₀ z := rfl
  have hei (z : ℂ) : e.symm z = e₀.symm (ρ⁻¹ • (z - boundaryLensCenter ρ)) := by
    apply e.injective
    rw [e.apply_symm_apply, he, e₀.apply_symm_apply, smul_smul, mul_inv_cancel₀ hρ.ne',
      one_smul, add_sub_cancel]
  have hLe : LipschitzWith (Real.toNNReal (12 * ρ)) e := by
    apply LipschitzWith.of_dist_le'
    intro x y
    rw [he, he, dist_add_left, dist_eq_norm, ← smul_sub, norm_smul,
      Real.norm_eq_abs, abs_of_pos hρ, ← dist_eq_norm]
    have h := mul_le_mul_of_nonneg_left (hL₀.dist_le_mul x y) hρ.le
    norm_num only [NNReal.coe_ofNat] at h
    nlinarith
  have hLei : LipschitzWith (Real.toNNReal (12 / ρ)) e.symm := by
    apply LipschitzWith.of_dist_le'
    intro x y
    rw [hei, hei]
    have h := hLi₀.dist_le_mul (ρ⁻¹ • (x - boundaryLensCenter ρ))
      (ρ⁻¹ • (y - boundaryLensCenter ρ))
    have hd : _root_.Dist.dist (ρ⁻¹ • (x - boundaryLensCenter ρ))
        (ρ⁻¹ • (y - boundaryLensCenter ρ)) = ρ⁻¹ * _root_.Dist.dist x y := by
      rw [dist_eq_norm, ← smul_sub, sub_sub_sub_cancel_right, norm_smul,
        Real.norm_eq_abs, abs_inv, abs_of_pos hρ, ← dist_eq_norm]
    rw [hd] at h
    simpa only [NNReal.coe_ofNat, div_eq_mul_inv, mul_assoc] using h
  have himage : e '' _root_.Metric.closedBall (0 : ℂ) 1 = boundaryLens ρ := by
    change (f ∘ e₀) '' _root_.Metric.closedBall (0 : ℂ) 1 = boundaryLens ρ
    rw [Set.image_comp]
    rw [himage₀]
    change f '' (f ⁻¹' boundaryLens ρ) = boundaryLens ρ
    exact f.surjective.image_preimage _
  refine ⟨e, fun z => by rw [he, he₀], hLe, hLei, himage, ?_⟩
  have hf := e.image_frontier (_root_.Metric.closedBall (0 : ℂ) 1)
  rw [frontier_closedBall _ one_ne_zero, himage] at hf
  exact hf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_boundaryLens_bilipschitz_homeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_boundaryLens_bilipschitz_homeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_boundaryLens_bilipschitz_homeomorph ``Submission.DifferentialGeometry.Analysis.exists_boundaryLens_bilipschitz_homeomorph

end DifferentialGeometry.Analysis

end

noncomputable section

open _root_.Set _root_.Metric _root_.NormedSpace
open scoped _root_.Topology

namespace DifferentialGeometry.Analysis

theorem gaugeRescale_unitBall_normalize_eq_of_gauge_eq_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} {y : E} (hy : gauge K y = 1) :
    gaugeRescale (_root_.Metric.ball (0 : E) 1) K (NormedSpace.normalize y) = y := by
  have hy0 : y ≠ 0 := by
    intro h
    rw [h, gauge_zero] at hy
    norm_num at hy
  rw [NormedSpace.normalize,
    gaugeRescale_smul (_root_.Metric.ball (0 : E) 1) K (inv_nonneg.mpr (norm_nonneg y)),
    gaugeRescale, gauge_unit_ball, hy, div_one, smul_smul,
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy0), one_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.gaugeRescale_unitBall_normalize_eq_of_gauge_eq_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.gaugeRescale_unitBall_normalize_eq_of_gauge_eq_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.gaugeRescale_unitBall_normalize_eq_of_gauge_eq_one ``Submission.DifferentialGeometry.Analysis.gaugeRescale_unitBall_normalize_eq_of_gauge_eq_one

theorem boundaryLens_gaugeRescale_normalize_eq {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {x : ℂ} (hx : x ∈ frontier (boundaryLens ρ)) :
    boundaryLensCenter ρ + ρ •
      gaugeRescale (_root_.Metric.ball (0 : ℂ) 1) (normalizedBoundaryLens ρ)
        (NormedSpace.normalize (x - boundaryLensCenter ρ)) = x := by
  let f : ℂ ≃ₜ ℂ := (Homeomorph.smulOfNeZero ρ hρ.ne').trans
    (Homeomorph.addLeft (boundaryLensCenter ρ))
  let y : ℂ := ρ⁻¹ • (x - boundaryLensCenter ρ)
  have hfy : f y = x := by
    change boundaryLensCenter ρ + ρ • (ρ⁻¹ • (x - boundaryLensCenter ρ)) = x
    rw [smul_smul, mul_inv_cancel₀ hρ.ne', one_smul, add_sub_cancel]
  have hy : y ∈ frontier (normalizedBoundaryLens ρ) := by
    change y ∈ frontier (f ⁻¹' boundaryLens ρ)
    rw [← f.preimage_frontier]
    change f y ∈ frontier (boundaryLens ρ)
    rwa [hfy]
  have hb := normalizedBoundaryLens_uniform_bounds hρ hρ1
  have hnb : normalizedBoundaryLens ρ ∈ 𝓝 (0 : ℂ) :=
    Filter.mem_of_superset (_root_.Metric.closedBall_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 4)) hb.1
  have hg : gauge (normalizedBoundaryLens ρ) y = 1 :=
    (gauge_eq_one_iff_mem_frontier (normalizedBoundaryLens_convex ρ) hnb).mpr hy
  have hn : NormedSpace.normalize y = NormedSpace.normalize (x - boundaryLensCenter ρ) :=
    _root_.NormedSpace.normalize_smul_of_pos (inv_pos.mpr hρ) _
  rw [← hn, gaugeRescale_unitBall_normalize_eq_of_gauge_eq_one hg]
  exact hfy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.boundaryLens_gaugeRescale_normalize_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.boundaryLens_gaugeRescale_normalize_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.boundaryLens_gaugeRescale_normalize_eq ``Submission.DifferentialGeometry.Analysis.boundaryLens_gaugeRescale_normalize_eq

private theorem mem_frontier_boundaryLens_of_left_sphere {ρ : ℝ} {x : ℂ}
    (hx : x ∈ _root_.Metric.sphere (-1) ρ) (hunit : x ∈ _root_.Metric.closedBall 0 1) :
    x ∈ frontier (boundaryLens ρ) := by
  change x ∈ frontier (_root_.Metric.closedBall (-1 : ℂ) ρ ∩ _root_.Metric.closedBall 0 1)
  rw [(isClosed_closedBall.inter _root_.Metric.isClosed_closedBall).frontier_eq]
  refine ⟨⟨sphere_subset_closedBall hx, hunit⟩, ?_⟩
  intro hi
  have hb := interior_mono (_root_.Set.inter_subset_left : boundaryLens ρ ⊆ _root_.Metric.closedBall (-1 : ℂ) ρ) hi
  rw [interior_closedBall' (-1 : ℂ) ρ] at hb
  exact (not_lt_of_ge (by exact (show _root_.Dist.dist x (-1) = ρ from hx).ge)) hb

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.mem_frontier_boundaryLens_of_left_sphere
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.mem_frontier_boundaryLens_of_left_sphere target :: scope.openDecls } }

private theorem mem_frontier_boundaryLens_of_right_sphere {ρ : ℝ} {x : ℂ}
    (hx : x ∈ _root_.Metric.sphere 0 1) (hcap : x ∈ _root_.Metric.closedBall (-1) ρ) :
    x ∈ frontier (boundaryLens ρ) := by
  change x ∈ frontier (_root_.Metric.closedBall (-1 : ℂ) ρ ∩ _root_.Metric.closedBall 0 1)
  rw [(isClosed_closedBall.inter _root_.Metric.isClosed_closedBall).frontier_eq]
  refine ⟨⟨hcap, _root_.Metric.sphere_subset_closedBall hx⟩, ?_⟩
  intro hi
  have hb := interior_mono (_root_.Set.inter_subset_right : boundaryLens ρ ⊆ _root_.Metric.closedBall (0 : ℂ) 1) hi
  rw [interior_closedBall' (0 : ℂ) 1] at hb
  exact (not_lt_of_ge (by exact (show _root_.Dist.dist x 0 = 1 from hx).ge)) hb

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.mem_frontier_boundaryLens_of_right_sphere
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.mem_frontier_boundaryLens_of_right_sphere target :: scope.openDecls } }

theorem circleMap_inner_mem_frontier_boundaryLens {ρ θ : ℝ}
    (hρ : 0 ≤ ρ) (hρ2 : ρ ≤ 2)
    (hθ : θ ∈ _root_.Set.Icc (-Real.arccos (ρ / 2)) (Real.arccos (ρ / 2))) :
    circleMap (-1) ρ θ ∈ frontier (boundaryLens ρ) :=
  mem_frontier_boundaryLens_of_left_sphere (circleMap_mem_sphere (-1) hρ θ)
    (Complex.circleMap_neg_one_mem_closedBall ρ hρ hρ2 hθ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.circleMap_inner_mem_frontier_boundaryLens then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.circleMap_inner_mem_frontier_boundaryLens"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.circleMap_inner_mem_frontier_boundaryLens ``Submission.DifferentialGeometry.Analysis.circleMap_inner_mem_frontier_boundaryLens

theorem circleMap_outer_mem_frontier_boundaryLens {ρ θ : ℝ}
    (hρ : 0 ≤ ρ) (hρ2 : ρ ≤ 2)
    (hθ : θ ∈ _root_.Set.Icc (2 * Real.arccos (ρ / 2))
      (2 * Real.pi - 2 * Real.arccos (ρ / 2))) :
    circleMap 0 1 θ ∈ frontier (boundaryLens ρ) := by
  have hcos : Real.cos (2 * Real.arccos (ρ / 2)) = ρ ^ 2 / 2 - 1 := by
    rw [Real.cos_two_mul, Real.cos_arccos (by linarith : -1 ≤ ρ / 2)
      (by linarith : ρ / 2 ≤ 1)]
    ring
  have hcosle : Real.cos θ ≤ ρ ^ 2 / 2 - 1 := by
    by_cases hθpi : θ ≤ Real.pi
    · exact (Real.cos_le_cos_of_nonneg_of_le_pi
        (mul_nonneg (by norm_num) (Real.arccos_nonneg _)) hθpi hθ.1).trans_eq hcos
    · have href := Real.cos_le_cos_of_nonneg_of_le_pi
        (mul_nonneg (by norm_num) (Real.arccos_nonneg _))
        (show 2 * Real.pi - θ ≤ Real.pi by linarith)
        (show 2 * Real.arccos (ρ / 2) ≤ 2 * Real.pi - θ by linarith [hθ.2])
      rwa [Real.cos_two_pi_sub, hcos] at href
  apply mem_frontier_boundaryLens_of_right_sphere (circleMap_mem_sphere 0 zero_le_one θ)
  rw [_root_.Metric.mem_closedBall, dist_eq_norm, sub_neg_eq_add]
  have hsq : ‖circleMap 0 1 θ + 1‖ ^ 2 = 2 + 2 * Real.cos θ := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
      circleMap_zero_re, circleMap_zero_im, one_mul, add_zero]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  nlinarith [norm_nonneg (circleMap 0 1 θ + 1)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.circleMap_outer_mem_frontier_boundaryLens then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.circleMap_outer_mem_frontier_boundaryLens"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.circleMap_outer_mem_frontier_boundaryLens ``Submission.DifferentialGeometry.Analysis.circleMap_outer_mem_frontier_boundaryLens

end DifferentialGeometry.Analysis

end

noncomputable section

open _root_.Set _root_.Metric
open _root_.Submission.DifferentialGeometry.Topology

namespace DifferentialGeometry.Analysis

private theorem norm_add_one_sq (z : ℂ) :
    ‖z + 1‖ ^ 2 = ‖z‖ ^ 2 + 2 * z.re + 1 := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.add_re,
    Complex.add_im, Complex.one_re, Complex.one_im]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.norm_add_one_sq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.norm_add_one_sq target :: scope.openDecls } }

private theorem arg_abs_le_of_cos_le {x : ℂ} {a : ℝ} (ha0 : 0 ≤ a) (hapi : a ≤ Real.pi)
    (hcos : Real.cos a ≤ Real.cos x.arg) : |x.arg| ≤ a := by
  have h := Real.arccos_le_arccos hcos
  rw [← Real.cos_abs x.arg, Real.arccos_cos (abs_nonneg _) (Complex.abs_arg_le_pi x),
    Real.arccos_cos ha0 hapi] at h
  exact h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.arg_abs_le_of_cos_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.arg_abs_le_of_cos_le target :: scope.openDecls } }

theorem sphere_inter_closedDisk_eq_inner_arc_image {ρ : ℝ} (hρ : 0 < ρ) (hρ2 : ρ ≤ 2) :
    _root_.Metric.sphere (-1 : ℂ) ρ ∩ _root_.Metric.closedBall (0 : ℂ) 1 =
      circleMap (-1) ρ '' _root_.Set.Icc (-Real.arccos (ρ / 2)) (Real.arccos (ρ / 2)) := by
  ext z
  constructor
  · rintro ⟨hzρ, hzD⟩
    have hnorm : ‖z + 1‖ = ρ := by
      simpa only [_root_.Metric.mem_sphere, dist_eq_norm, sub_neg_eq_add] using hzρ
    have hzn : ‖z‖ ≤ 1 := by simpa only [_root_.Metric.mem_closedBall, dist_zero_right] using hzD
    have hne : z + 1 ≠ 0 := norm_ne_zero_iff.mp (hnorm.trans_ne hρ.ne')
    have hsq := norm_add_one_sq z
    rw [hnorm] at hsq
    have hcos : ρ / 2 ≤ Real.cos (z + 1).arg := by
      rw [Complex.cos_arg hne, hnorm]
      apply (le_div_iff₀ hρ).mpr
      simp only [Complex.add_re, Complex.one_re]
      nlinarith [norm_nonneg z]
    have ha : |(z + 1).arg| ≤ Real.arccos (ρ / 2) :=
      arg_abs_le_of_cos_le (Real.arccos_nonneg _) (Real.arccos_le_pi _)
        (by rwa [Real.cos_arccos (by linarith : -1 ≤ ρ / 2) (by linarith : ρ / 2 ≤ 1)])
    refine ⟨(z + 1).arg, abs_le.mp ha, ?_⟩
    have he := Complex.norm_mul_exp_arg_mul_I (z + 1)
    rw [hnorm] at he
    change -1 + (ρ : ℂ) * Complex.exp (↑(z + 1).arg * Complex.I) = z
    rw [he]
    ring
  · rintro ⟨θ, hθ, rfl⟩
    exact ⟨circleMap_mem_sphere (-1) hρ.le θ,
      Complex.circleMap_neg_one_mem_closedBall ρ hρ.le hρ2 hθ⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.sphere_inter_closedDisk_eq_inner_arc_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.sphere_inter_closedDisk_eq_inner_arc_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.sphere_inter_closedDisk_eq_inner_arc_image ``Submission.DifferentialGeometry.Analysis.sphere_inter_closedDisk_eq_inner_arc_image

theorem unit_sphere_inter_closedBall_eq_outer_arc_image {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hρ2 : ρ ≤ 2) :
    _root_.Metric.sphere (0 : ℂ) 1 ∩ _root_.Metric.closedBall (-1 : ℂ) ρ =
      circleMap 0 1 '' _root_.Set.Icc (2 * Real.arccos (ρ / 2))
        (2 * Real.pi - 2 * Real.arccos (ρ / 2)) := by
  ext z
  constructor
  · rintro ⟨hzS, hzρ⟩
    have hzn : ‖z‖ = 1 := by simpa only [_root_.Metric.mem_sphere, dist_zero_right] using hzS
    have hzne : z ≠ 0 := norm_ne_zero_iff.mp (hzn.trans_ne one_ne_zero)
    have hnorm : ‖z + 1‖ ≤ ρ := by
      simpa only [_root_.Metric.mem_closedBall, dist_eq_norm, sub_neg_eq_add] using hzρ
    let a := Real.arccos (ρ / 2)
    let φ := (-z).arg
    have ha0 : 0 ≤ a := Real.arccos_nonneg _
    have hapi : a ≤ Real.pi / 2 := Real.arccos_le_pi_div_two.mpr (by positivity)
    have hcos : Real.cos (Real.pi - 2 * a) ≤ Real.cos (-z).arg := by
      rw [Real.cos_pi_sub, Real.cos_two_mul, Real.cos_arccos (by linarith : -1 ≤ ρ / 2)
        (by linarith : ρ / 2 ≤ 1), Complex.cos_arg (neg_ne_zero.mpr hzne), norm_neg, hzn,
        Complex.neg_re, div_one]
      have hs := norm_add_one_sq z
      rw [hzn] at hs
      nlinarith [norm_nonneg (z + 1)]
    have hφ : |φ| ≤ Real.pi - 2 * a :=
      arg_abs_le_of_cos_le (by linarith) (by linarith) hcos
    refine ⟨Real.pi + φ, ⟨by linarith [(abs_le.mp hφ).1], by linarith [(abs_le.mp hφ).2]⟩, ?_⟩
    have he := Complex.norm_mul_exp_arg_mul_I (-z)
    rw [norm_neg, hzn, Complex.ofReal_one, one_mul] at he
    simp only [circleMap, zero_add, Complex.ofReal_one, one_mul]
    rw [Complex.ofReal_add, add_mul, Complex.exp_add, Complex.exp_pi_mul_I, he]
    ring
  · rintro ⟨θ, hθ, rfl⟩
    have hfront := circleMap_outer_mem_frontier_boundaryLens hρ hρ2 hθ
    have hclosed : IsClosed (boundaryLens ρ) := isClosed_closedBall.inter _root_.Metric.isClosed_closedBall
    have hmem : circleMap 0 1 θ ∈ boundaryLens ρ :=
      hclosed.closure_eq ▸ frontier_subset_closure hfront
    exact ⟨circleMap_mem_sphere 0 (by norm_num : (0 : ℝ) ≤ 1) θ, hmem.1⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.unit_sphere_inter_closedBall_eq_outer_arc_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.unit_sphere_inter_closedBall_eq_outer_arc_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.unit_sphere_inter_closedBall_eq_outer_arc_image ``Submission.DifferentialGeometry.Analysis.unit_sphere_inter_closedBall_eq_outer_arc_image

private theorem outer_arc_endpoints_dist {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ2 : ρ ≤ 2) :
    _root_.Dist.dist (circleMap 0 1 (2 * Real.arccos (ρ / 2))) (-1) = ρ ∧
      dist (circleMap 0 1 (2 * Real.pi - 2 * Real.arccos (ρ / 2))) (-1) = ρ := by
  rw [← circleMap_neg_one_arccos (by linarith : -2 ≤ ρ) hρ2,
    ← circleMap_neg_one_neg_arccos (by linarith : -2 ≤ ρ) hρ2]
  exact ⟨circleMap_mem_sphere (-1) hρ _, circleMap_mem_sphere (-1) hρ _⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.outer_arc_endpoints_dist
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.outer_arc_endpoints_dist target :: scope.openDecls } }

theorem unit_sphere_inter_ball_eq_outer_open_arc_image {ρ : ℝ}
    (hρ : 0 < ρ) (hρ2 : ρ < 2) :
    _root_.Metric.sphere (0 : ℂ) 1 ∩ _root_.Metric.ball (-1 : ℂ) ρ =
      circleMap 0 1 '' _root_.Set.Ioo (2 * Real.arccos (ρ / 2))
        (2 * Real.pi - 2 * Real.arccos (ρ / 2)) := by
  ext z
  constructor
  · rintro ⟨hzS, hzρ⟩
    obtain ⟨θ, hθ, heq⟩ :=
      (show z ∈ circleMap 0 1 '' _root_.Set.Icc (2 * Real.arccos (ρ / 2))
          (2 * Real.pi - 2 * Real.arccos (ρ / 2)) by
        rw [← unit_sphere_inter_closedBall_eq_outer_arc_image hρ.le hρ2.le]
        exact ⟨hzS, _root_.Metric.ball_subset_closedBall hzρ⟩)
    have hend := outer_arc_endpoints_dist hρ.le hρ2.le
    have hlo : 2 * Real.arccos (ρ / 2) < θ := lt_of_le_of_ne hθ.1 (by
      intro h
      have hh := hend.1
      rw [h, heq] at hh
      exact (ne_of_lt hzρ) hh)
    have hhi : θ < 2 * Real.pi - 2 * Real.arccos (ρ / 2) := lt_of_le_of_ne hθ.2 (by
      intro h
      have hh := hend.2
      rw [← h, heq] at hh
      exact (ne_of_lt hzρ) hh)
    exact ⟨θ, ⟨hlo, hhi⟩, heq⟩
  · rintro ⟨θ, hθ, rfl⟩
    have hcos : Real.cos (2 * Real.arccos (ρ / 2)) = ρ ^ 2 / 2 - 1 := by
      rw [Real.cos_two_mul, Real.cos_arccos (by linarith : -1 ≤ ρ / 2)
        (by linarith : ρ / 2 ≤ 1)]
      ring
    have hcoslt : Real.cos θ < ρ ^ 2 / 2 - 1 := by
      by_cases hθpi : θ ≤ Real.pi
      · exact (Real.cos_lt_cos_of_nonneg_of_le_pi (by nlinarith [Real.arccos_nonneg (ρ / 2)] :
          0 ≤ 2 * Real.arccos (ρ / 2)) hθpi hθ.1).trans_eq hcos
      · have hh := Real.cos_lt_cos_of_nonneg_of_le_pi (by nlinarith [Real.arccos_nonneg (ρ / 2)] :
          0 ≤ 2 * Real.arccos (ρ / 2)) (show 2 * Real.pi - θ ≤ Real.pi by linarith)
          (show 2 * Real.arccos (ρ / 2) < 2 * Real.pi - θ by linarith [hθ.2])
        rwa [Real.cos_two_pi_sub, hcos] at hh
    refine ⟨circleMap_mem_sphere 0 (by norm_num : (0 : ℝ) ≤ 1) θ, ?_⟩
    have hs := norm_add_one_sq (circleMap 0 1 θ)
    simp only [norm_circleMap_zero, abs_one, circleMap_zero_re, one_mul] at hs
    change _root_.Dist.dist (circleMap 0 1 θ) (-1) < ρ
    rw [dist_eq_norm, sub_neg_eq_add]
    nlinarith [norm_nonneg (circleMap 0 1 θ + 1)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.unit_sphere_inter_ball_eq_outer_open_arc_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.unit_sphere_inter_ball_eq_outer_open_arc_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.unit_sphere_inter_ball_eq_outer_open_arc_image ``Submission.DifferentialGeometry.Analysis.unit_sphere_inter_ball_eq_outer_open_arc_image

theorem diskBoundary_mem_ball_iff_mem_outer_arc {ρ : ℝ} (hρ : 0 < ρ) (hρ2 : ρ < 2)
    (x : loopCircle) :
    (diskBoundary x : ℂ) ∈ _root_.Metric.ball (-1 : ℂ) ρ ↔
      x ∈ (fun t : ℝ => (t : loopCircle)) ''
        Ioo (Real.arccos (ρ / 2) / Real.pi) (1 - Real.arccos (ρ / 2) / Real.pi) := by
  constructor
  · intro hx
    have hs : (diskBoundary x : ℂ) ∈ _root_.Metric.sphere (0 : ℂ) 1 := by
      rw [_root_.Metric.mem_sphere, dist_zero_right]
      change ‖(AddCircle.toCircle x : ℂ)‖ = 1
      exact Circle.norm_coe _
    have hmem : (diskBoundary x : ℂ) ∈ circleMap 0 1 ''
        Ioo (2 * Real.arccos (ρ / 2)) (2 * Real.pi - 2 * Real.arccos (ρ / 2)) := by
      rw [← unit_sphere_inter_ball_eq_outer_open_arc_image hρ hρ2]
      exact ⟨hs, hx⟩
    obtain ⟨θ, hθ, he⟩ := hmem
    refine ⟨θ / (2 * Real.pi), ⟨?_, ?_⟩, ?_⟩
    · apply (lt_div_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr
      have hc : Real.arccos (ρ / 2) / Real.pi * (2 * Real.pi) = 2 * Real.arccos (ρ / 2) := by
        field_simp
      rw [hc]
      exact hθ.1
    · apply (div_lt_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr
      have hc : (1 - Real.arccos (ρ / 2) / Real.pi) * (2 * Real.pi) =
          2 * Real.pi - 2 * Real.arccos (ρ / 2) := by field_simp
      rw [hc]
      exact hθ.2
    · apply AddCircle.injective_toCircle (by norm_num : (1 : ℝ) ≠ 0)
      apply Subtype.ext
      change (diskBoundary ((θ / (2 * Real.pi) : ℝ) : loopCircle) : ℂ) = (diskBoundary x : ℂ)
      rw [diskBoundary_coe]
      have hc : 2 * Real.pi * (θ / (2 * Real.pi)) = θ := by field_simp
      simpa only [hc, circleMap, Complex.ofReal_one, one_mul, zero_add] using he
  · rintro ⟨t, ht, rfl⟩
    have hθ : 2 * Real.pi * t ∈ _root_.Set.Ioo (2 * Real.arccos (ρ / 2))
        (2 * Real.pi - 2 * Real.arccos (ρ / 2)) := by
      constructor
      · have h := (div_lt_iff₀ Real.pi_pos).mp ht.1
        nlinarith
      · have h := (lt_sub_iff_add_lt).mp ht.2
        have h' := mul_lt_mul_of_pos_right h Real.pi_pos
        have heq : Real.arccos (ρ / 2) / Real.pi * Real.pi = Real.arccos (ρ / 2) :=
          div_mul_cancel₀ _ Real.pi_ne_zero
        rw [add_mul, heq] at h'
        nlinarith
    have hmem : circleMap 0 1 (2 * Real.pi * t) ∈ _root_.Metric.sphere (0 : ℂ) 1 ∩ _root_.Metric.ball (-1 : ℂ) ρ := by
      rw [unit_sphere_inter_ball_eq_outer_open_arc_image hρ hρ2]
      exact _root_.Set.mem_image_of_mem _ hθ
    simpa only [diskBoundary_coe, circleMap, Complex.ofReal_one, one_mul, zero_add] using hmem.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.diskBoundary_mem_ball_iff_mem_outer_arc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.diskBoundary_mem_ball_iff_mem_outer_arc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.diskBoundary_mem_ball_iff_mem_outer_arc ``Submission.DifferentialGeometry.Analysis.diskBoundary_mem_ball_iff_mem_outer_arc

end DifferentialGeometry.Analysis

end
