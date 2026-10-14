import Submission.DifferentialGeometry.Analysis.Sobolev.Tools.Mollification.Kernel

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory _root_.Metric _root_.Filter _root_.Topology _root_.Set _root_.Function
open scoped _root_.ENNReal _root_.NNReal _root_.Convolution _root_.Pointwise

namespace DifferentialGeometry.Analysis.Sobolev

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
lemma exists_norm_bound_of_continuous_compactSupport
    {η : E → ℝ} (hη_cont : Continuous η) (hη_compact : HasCompactSupport η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y, ‖η y‖ ≤ C := by
  rcases hη_cont.bounded_above_of_compact_support hη_compact with ⟨C, hC⟩
  refine ⟨max C 0, le_max_right _ _, fun y => ?_⟩
  exact (hC y).trans (le_max_left _ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.exists_norm_bound_of_continuous_compactSupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.exists_norm_bound_of_continuous_compactSupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.exists_norm_bound_of_continuous_compactSupport ``Submission.DifferentialGeometry.Analysis.Sobolev.exists_norm_bound_of_continuous_compactSupport

omit [NeZero d] in
lemma lipschitz_of_contDiff_compactSupport
    {η : E → ℝ} (hη_C1 : ContDiff ℝ 1 η) (hη_compact : HasCompactSupport η) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x y, ‖η x - η y‖ ≤ L * ‖x - y‖ := by
  have hfderiv_cont : Continuous (fderiv ℝ η) := hη_C1.continuous_fderiv (by simp)
  have hfderiv_compact : HasCompactSupport (fderiv ℝ η) := hη_compact.fderiv ℝ
  rcases hfderiv_cont.bounded_above_of_compact_support hfderiv_compact with ⟨C, hC⟩
  refine ⟨max C 0, le_max_right _ _, fun x y => ?_⟩
  have hbnd : ∀ z, ‖fderiv ℝ η z‖ ≤ _root_.Max.max C 0 := fun z =>
    (hC z).trans (le_max_left _ _)
  have hbnd_nn : ∀ z, ‖fderiv ℝ η z‖₊ ≤
      NNReal.mk (_root_.Max.max C 0) (le_max_right _ _) := by
    intro z
    change ‖fderiv ℝ η z‖ ≤ _root_.Max.max C 0
    exact hbnd z
  have hLip : LipschitzWith (NNReal.mk (_root_.Max.max C 0) (le_max_right _ _)) η :=
    lipschitzWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
      (hη_C1.differentiable (by norm_cast)) hbnd_nn
  have hdist : _root_.Dist.dist (η x) (η y) ≤ _root_.Max.max C 0 * _root_.Dist.dist x y := by
    have := hLip.dist_le_mul x y
    change _root_.Dist.dist (η x) (η y) ≤ _root_.Max.max C 0 * _root_.Dist.dist x y at this
    exact this
  rw [show ‖η x - η y‖ = _root_.Dist.dist (η x) (η y) from (Real.dist_eq _ _).symm,
    show ‖x - y‖ = _root_.Dist.dist x y from (dist_eq_norm _ _).symm]
  exact hdist

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.lipschitz_of_contDiff_compactSupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.lipschitz_of_contDiff_compactSupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.lipschitz_of_contDiff_compactSupport ``Submission.DifferentialGeometry.Analysis.Sobolev.lipschitz_of_contDiff_compactSupport

omit [NeZero d] in
private lemma measurePreserving_constSub (z : E) :
    MeasurePreserving (fun t : E => z - t) _root_.MeasureTheory.MeasureSpace.volume volume := by
  have h_neg : _root_.MeasureTheory.MeasurePreserving (fun t : E => -t) _root_.MeasureTheory.MeasureSpace.volume volume :=
    Measure.measurePreserving_neg _root_.MeasureTheory.MeasureSpace.volume
  have h_addL : _root_.MeasureTheory.MeasurePreserving (fun t : E => z + t) _root_.MeasureTheory.MeasureSpace.volume volume :=
    _root_.MeasureTheory.measurePreserving_add_left _root_.MeasureTheory.MeasureSpace.volume z
  have heq : (fun t : E => z - t) = (fun t : E => z + (-t)) := by
    funext t; rw [sub_eq_add_neg]
  rw [heq]
  exact h_addL.comp h_neg

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.measurePreserving_constSub
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.measurePreserving_constSub target :: scope.openDecls } }

omit [NeZero d] in
theorem convolution_sup_le_holder
    {f η : E → ℝ}
    (hf_int : _root_.MeasureTheory.Integrable f _root_.MeasureTheory.MeasureSpace.volume)
    (hη_meas : _root_.MeasureTheory.AEStronglyMeasurable η _root_.MeasureTheory.MeasureSpace.volume)
    {M : ℝ} (hη_bnd : ∀ y, ‖η y‖ ≤ M) (x : E) :
    ‖(f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, _root_.MeasureTheory.MeasureSpace.volume] η) x‖ ≤
      M * ∫ t, ‖f t‖ ∂volume := by
  classical
  have hη_meas_sub :
      AEStronglyMeasurable (fun t : E => η (x - t)) volume :=
    hη_meas.comp_measurePreserving (measurePreserving_constSub (d := d) x)
  have hpt : ∀ t : E, ‖f t • η (x - t)‖ ≤ M * ‖f t‖ := by
    intro t
    rw [norm_smul, mul_comm M ‖f t‖]
    exact mul_le_mul_of_nonneg_left (hη_bnd _) (norm_nonneg _)
  have hint_smul :
      Integrable (fun t : E => f t • η (x - t)) volume := by
    refine Integrable.mono' (g := fun t => M * ‖f t‖) ?_ ?_ ?_
    · exact hf_int.norm.const_mul M
    · exact hf_int.aestronglyMeasurable.smul hη_meas_sub
    · filter_upwards with t
      exact hpt t
  have hconv_eq :
      (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, _root_.MeasureTheory.MeasureSpace.volume] η) x =
        ∫ t, f t • η (x - t) ∂volume := by
    simp [MeasureTheory.convolution_def, ContinuousLinearMap.lsmul_apply]
  rw [hconv_eq]
  refine (_root_.MeasureTheory.norm_integral_le_integral_norm _).trans ?_
  have hint_pt :
      ∫ t, ‖f t • η (x - t)‖ ∂volume ≤
        ∫ t, M * ‖f t‖ ∂volume := by
    refine _root_.MeasureTheory.integral_mono_ae hint_smul.norm
      (hf_int.norm.const_mul M) ?_
    filter_upwards with t using hpt t
  refine hint_pt.trans ?_
  rw [_root_.MeasureTheory.integral_const_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.convolution_sup_le_holder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.convolution_sup_le_holder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.convolution_sup_le_holder ``Submission.DifferentialGeometry.Analysis.Sobolev.convolution_sup_le_holder

omit [NeZero d] in
theorem convolution_continuous_of_compact_support
    {f η : E → ℝ}
    (hf_local : _root_.MeasureTheory.LocallyIntegrable f _root_.MeasureTheory.MeasureSpace.volume)
    (hη_cont : Continuous η) (hη_compact : HasCompactSupport η) :
    Continuous (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, _root_.MeasureTheory.MeasureSpace.volume] η : E → ℝ) :=
  hη_compact.continuous_convolution_right
    (L := ContinuousLinearMap.lsmul ℝ ℝ) hf_local hη_cont

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.convolution_continuous_of_compact_support then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.convolution_continuous_of_compact_support"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.convolution_continuous_of_compact_support ``Submission.DifferentialGeometry.Analysis.Sobolev.convolution_continuous_of_compact_support

omit [NeZero d] in
theorem convolution_lipschitz_with
    {f η : E → ℝ}
    (hf_int : _root_.MeasureTheory.Integrable f _root_.MeasureTheory.MeasureSpace.volume)
    (hη_cont : Continuous η) (hη_compact : HasCompactSupport η)
    {L : ℝ}
    (hη_lip : ∀ x y, ‖η x - η y‖ ≤ L * ‖x - y‖) (x y : E) :
    ‖(f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, _root_.MeasureTheory.MeasureSpace.volume] η) x -
      (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, _root_.MeasureTheory.MeasureSpace.volume] η) y‖ ≤
      L * (∫ t, ‖f t‖ ∂volume) * ‖x - y‖ := by
  classical
  rcases exists_norm_bound_of_continuous_compactSupport (d := d)
      hη_cont hη_compact with ⟨M, hM_nn, hη_bnd⟩
  have hη_meas : _root_.MeasureTheory.AEStronglyMeasurable η volume := hη_cont.aestronglyMeasurable
  have hη_meas_sub : ∀ z : E,
      AEStronglyMeasurable (fun t : E => η (z - t)) volume := fun z =>
    hη_meas.comp_measurePreserving (measurePreserving_constSub (d := d) z)
  have hint_smul : ∀ z : E,
      Integrable (fun t : E => f t • η (z - t)) volume := by
    intro z
    refine Integrable.mono' (g := fun t => M * ‖f t‖) ?_ ?_ ?_
    · exact hf_int.norm.const_mul M
    · exact hf_int.aestronglyMeasurable.smul (hη_meas_sub z)
    · filter_upwards with t
      have : ‖f t • η (z - t)‖ ≤ M * ‖f t‖ := by
        rw [norm_smul, mul_comm M ‖f t‖]
        exact mul_le_mul_of_nonneg_left (hη_bnd _) (norm_nonneg _)
      exact this
  have hconv_eq : ∀ z : E,
      (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, _root_.MeasureTheory.MeasureSpace.volume] η) z =
        ∫ t, f t • η (z - t) ∂volume := by
    intro z
    simp [MeasureTheory.convolution_def, ContinuousLinearMap.lsmul_apply]
  rw [hconv_eq x, hconv_eq y, ← _root_.MeasureTheory.integral_sub (hint_smul x) (hint_smul y)]
  have hpt : ∀ t : E,
      ‖f t • η (x - t) - f t • η (y - t)‖ ≤ L * ‖x - y‖ * ‖f t‖ := by
    intro t
    rw [show f t • η (x - t) - f t • η (y - t) =
      f t • (η (x - t) - η (y - t)) from by rw [smul_sub]]
    rw [norm_smul]
    have h1 : ‖η (x - t) - η (y - t)‖ ≤ L * ‖(x - t) - (y - t)‖ :=
      hη_lip (x - t) (y - t)
    have hxy : (x - t) - (y - t) = x - y := by abel
    rw [hxy] at h1
    calc
      ‖f t‖ * ‖η (x - t) - η (y - t)‖ ≤ ‖f t‖ * (L * ‖x - y‖) :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = L * ‖x - y‖ * ‖f t‖ := by ring
  have hint_diff :
      _root_.MeasureTheory.Integrable (fun t : E =>
        f t • η (x - t) - f t • η (y - t)) volume :=
    (hint_smul x).sub (hint_smul y)
  refine (_root_.MeasureTheory.norm_integral_le_integral_norm _).trans ?_
  have hint_pt :
      ∫ t, ‖f t • η (x - t) - f t • η (y - t)‖ ∂volume ≤
        ∫ t, L * ‖x - y‖ * ‖f t‖ ∂volume := by
    refine _root_.MeasureTheory.integral_mono_ae hint_diff.norm
      (hf_int.norm.const_mul (L * ‖x - y‖)) ?_
    filter_upwards with t using hpt t
  refine hint_pt.trans ?_
  rw [_root_.MeasureTheory.integral_const_mul]
  rw [mul_assoc L ‖x - y‖ _, mul_comm ‖x - y‖ _, ← mul_assoc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.convolution_lipschitz_with then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.convolution_lipschitz_with"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.convolution_lipschitz_with ``Submission.DifferentialGeometry.Analysis.Sobolev.convolution_lipschitz_with

end DifferentialGeometry.Analysis.Sobolev
