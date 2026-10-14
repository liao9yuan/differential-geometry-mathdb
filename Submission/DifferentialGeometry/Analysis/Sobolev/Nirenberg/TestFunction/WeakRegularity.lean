import Submission.DifferentialGeometry.Analysis.Sobolev.Nirenberg.TestFunction.Basic
import Submission.DifferentialGeometry.Analysis.Sobolev.Nirenberg.TestFunction.CutoffDiffQuot

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory _root_.Metric _root_.Filter _root_.Topology _root_.Set _root_.Function
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open scoped _root_.ENNReal _root_.NNReal _root_.Convolution _root_.Pointwise _root_.BigOperators

namespace DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction

variable {d : ℕ} [NeZero d]

local notation "EuclN" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
private lemma locallyIntegrable_continuous_mul
    {η f : EuclN → ℝ} (hη : Continuous η)
    (hf_localInt : _root_.MeasureTheory.LocallyIntegrable f (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) :
    LocallyIntegrable (fun x => η x * f x) (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
  rw [← _root_.MeasureTheory.locallyIntegrableOn_univ] at hf_localInt ⊢
  have hcl : IsLocallyClosed (Set.univ : Set EuclN) :=
    isClosed_univ.isLocallyClosed
  exact LocallyIntegrableOn.continuousOn_mul hf_localInt hη.continuousOn hcl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.locallyIntegrable_continuous_mul
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.locallyIntegrable_continuous_mul target :: scope.openDecls } }

omit [NeZero d] in
private lemma locallyIntegrable_of_restrict_univ
    {f : EuclN → ℝ}
    (hf : _root_.MeasureTheory.LocallyIntegrable f ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict Set.univ)) :
    LocallyIntegrable f (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
  rwa [Measure.restrict_univ] at hf

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.locallyIntegrable_of_restrict_univ
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.locallyIntegrable_of_restrict_univ target :: scope.openDecls } }

omit [NeZero d] in
private lemma locallyIntegrable_to_restrict_univ
    {f : EuclN → ℝ} (hf : _root_.MeasureTheory.LocallyIntegrable f (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) :
    LocallyIntegrable f ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict Set.univ) := by
  rwa [Measure.restrict_univ]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.locallyIntegrable_to_restrict_univ
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.locallyIntegrable_to_restrict_univ target :: scope.openDecls } }

omit [NeZero d] in
theorem hasWeakPartialDeriv_nirenbergTestFunction
    (k j : Fin d) (h : ℝ) {η u g_j : EuclN → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hu_localInt :
      _root_.MeasureTheory.LocallyIntegrable u ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict Set.univ))
    (hg_j_localInt :
      _root_.MeasureTheory.LocallyIntegrable g_j ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict Set.univ))
    (hwp : DeGiorgi.HasWeakPartialDeriv (d := d) j g_j u Set.univ) :
    DeGiorgi.HasWeakPartialDeriv (d := d) j
      (diffQuot k (-h)
        (fun y =>
          (η y)^2 * diffQuot k h g_j y +
          2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
            diffQuot k h u y))
      (nirenbergTestFunction k h η u) Set.univ := by
  have hη_cont : Continuous η := hη.continuous
  have hη_sq_cont : Continuous (fun y : EuclN => (η y)^2) := hη_cont.pow 2
  have hη_diff : Differentiable ℝ η := hη.differentiable (by simp)
  have hpartial_η_cont : Continuous
      (fun y : EuclN => (fderiv ℝ η y) (EuclideanSpace.single j 1)) :=
    (hη.continuous_fderiv (by simp)).clm_apply continuous_const
  have h_2η_partial_cont : Continuous
      (fun y : EuclN => 2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1)) :=
    (continuous_const.mul hη_cont).mul hpartial_η_cont
  have hu_localInt' : _root_.MeasureTheory.LocallyIntegrable u (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) :=
    locallyIntegrable_of_restrict_univ (d := d) hu_localInt
  have hg_j_localInt' : _root_.MeasureTheory.LocallyIntegrable g_j (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) :=
    locallyIntegrable_of_restrict_univ (d := d) hg_j_localInt
  have h_dq_u_localInt : _root_.MeasureTheory.LocallyIntegrable (diffQuot k h u)
      (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) :=
    locallyIntegrable_diffQuot (d := d) k h hu_localInt'
  have h_dq_g_localInt : _root_.MeasureTheory.LocallyIntegrable (diffQuot k h g_j)
      (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) :=
    locallyIntegrable_diffQuot (d := d) k h hg_j_localInt'
  have h_F_localInt : _root_.MeasureTheory.LocallyIntegrable
      (fun y => (η y)^2 * diffQuot k h u y) (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) :=
    locallyIntegrable_continuous_mul (d := d) hη_sq_cont h_dq_u_localInt
  have h_F_localInt_restrict : _root_.MeasureTheory.LocallyIntegrable
      (fun y => (η y)^2 * diffQuot k h u y)
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict Set.univ) :=
    locallyIntegrable_to_restrict_univ (d := d) h_F_localInt
  have h_term1_localInt : _root_.MeasureTheory.LocallyIntegrable
      (fun y => (η y)^2 * diffQuot k h g_j y) (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) :=
    locallyIntegrable_continuous_mul (d := d) hη_sq_cont h_dq_g_localInt
  have h_term2_localInt : _root_.MeasureTheory.LocallyIntegrable
      (fun y => 2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
          diffQuot k h u y)
      (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) :=
    locallyIntegrable_continuous_mul (d := d) h_2η_partial_cont h_dq_u_localInt
  have h_partial_localInt : _root_.MeasureTheory.LocallyIntegrable
      (fun y => (η y)^2 * diffQuot k h g_j y +
        2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
          diffQuot k h u y)
      (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) :=
    h_term1_localInt.add h_term2_localInt
  have h_partial_localInt_restrict : _root_.MeasureTheory.LocallyIntegrable
      (fun y => (η y)^2 * diffQuot k h g_j y +
        2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
          diffQuot k h u y)
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict Set.univ) :=
    locallyIntegrable_to_restrict_univ (d := d) h_partial_localInt
  have h_inner_wp :
      DeGiorgi.HasWeakPartialDeriv (d := d) j
        (fun y => (η y)^2 * diffQuot k h g_j y +
          ((fderiv ℝ (fun z => (η z)^2) y) (EuclideanSpace.single j 1)) *
            diffQuot k h u y)
        (fun y => (η y)^2 * diffQuot k h u y) Set.univ :=
    hasWeakPartialDeriv_cutoff_sq_mul_diffQuot (d := d) k j h hη
      hu_localInt hg_j_localInt hwp
  have h_eq :
      (fun y : EuclN =>
        (η y)^2 * diffQuot k h g_j y +
          ((fderiv ℝ (fun z => (η z)^2) y) (EuclideanSpace.single j 1)) *
            diffQuot k h u y) =
      (fun y : EuclN =>
        (η y)^2 * diffQuot k h g_j y +
          2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
            diffQuot k h u y) := by
    funext y
    rw [fderiv_fun_pow 2 (hη_diff y)]
    rw [smul_apply]
    have h1 : (η y) ^ ((2 : ℕ) - 1) = η y := by norm_num
    rw [h1]
    have h_two : ((2 : ℕ) • η y) = 2 * η y := by
      rw [two_smul]; ring
    rw [h_two, smul_eq_mul]
  rw [h_eq] at h_inner_wp
  unfold nirenbergTestFunction
  exact hasWeakPartialDeriv_diffQuot (d := d) k j (-h)
    h_F_localInt_restrict h_partial_localInt_restrict h_inner_wp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.hasWeakPartialDeriv_nirenbergTestFunction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.hasWeakPartialDeriv_nirenbergTestFunction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.hasWeakPartialDeriv_nirenbergTestFunction ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.hasWeakPartialDeriv_nirenbergTestFunction

omit [NeZero d] in
private lemma eLpNorm_const_mul
    (c : ℝ) (f : EuclN → ℝ) :
    _root_.MeasureTheory.eLpNorm (fun x => c * f x) 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) =
      ENNReal.ofReal |c| * _root_.MeasureTheory.eLpNorm f 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
  have h_eq : (fun x => c * f x) = c • f := by
    funext x; rw [Pi.smul_apply, smul_eq_mul]
  rw [h_eq]
  rw [_root_.MeasureTheory.eLpNorm_const_smul c f]
  simp [Real.enorm_eq_ofReal_abs]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.eLpNorm_const_mul
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.eLpNorm_const_mul target :: scope.openDecls } }

omit [NeZero d] in
private lemma eLpNorm_translate_eq (k : Fin d) (h : ℝ) (F : EuclN → ℝ) :
    _root_.MeasureTheory.eLpNorm (translate k h F) 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) =
      eLpNorm F 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
  set τ : EuclN ≃ₜ EuclN :=
    Homeomorph.addRight (h • EuclideanSpace.single k 1) with hτ_def
  have hMP : _root_.MeasureTheory.MeasurePreserving τ _root_.MeasureTheory.MeasureSpace.volume volume := by
    rw [show (τ : EuclN → EuclN) = fun x => x + h • EuclideanSpace.single k 1
      from rfl]
    exact _root_.MeasureTheory.measurePreserving_add_right _root_.MeasureTheory.MeasureSpace.volume _
  have hτ_emb : MeasurableEmbedding τ := τ.measurableEmbedding
  have h_eq : translate k h F = F ∘ (τ : EuclN → EuclN) := rfl
  rw [h_eq]
  rw [show _root_.MeasureTheory.eLpNorm F 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) =
      _root_.MeasureTheory.eLpNorm F 2 (Measure.map τ _root_.MeasureTheory.MeasureSpace.volume) from by rw [hMP.map_eq]]
  exact (hτ_emb.eLpNorm_map_measure (g := F) (p := 2)).symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.eLpNorm_translate_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.eLpNorm_translate_eq target :: scope.openDecls } }

omit [NeZero d] in
private lemma eLpNorm_diffQuot_neg_le
    (k : Fin d) {h : ℝ} (hh : h ≠ 0) {F : EuclN → ℝ}
    (hF_aesm : _root_.MeasureTheory.AEStronglyMeasurable F (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) :
    _root_.MeasureTheory.eLpNorm (diffQuot k (-h) F) 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) ≤
      (2 / ENNReal.ofReal |h|) * _root_.MeasureTheory.eLpNorm F 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
  have hnh : (-h) ≠ 0 := neg_ne_zero.mpr hh
  have h_dq_eq : diffQuot k (-h) F =
      fun x => (-h)⁻¹ * (translate k (-h) F x - F x) := by
    funext x
    rw [diffQuot_apply_of_ne (d := d) k hnh F x]
    change (F (x + (-h) • EuclideanSpace.single k 1) - F x) / (-h) =
      (-h)⁻¹ * (F (x + (-h) • EuclideanSpace.single k 1) - F x)
    field_simp
  rw [h_dq_eq]
  have h_eq2 : (fun x => (-h)⁻¹ * (translate k (-h) F x - F x)) =
      fun x => (-h)⁻¹ * ((translate k (-h) F - F) x) := by
    funext x; simp [Pi.sub_apply]
  rw [h_eq2, eLpNorm_const_mul (-h)⁻¹ (translate k (-h) F - F)]
  have hτF_aesm : _root_.MeasureTheory.AEStronglyMeasurable (translate k (-h) F)
      (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
    have hMP : _root_.MeasureTheory.MeasurePreserving
        (fun x : EuclN => x + (-h) • EuclideanSpace.single k 1)
        volume volume :=
      _root_.MeasureTheory.measurePreserving_add_right _root_.MeasureTheory.MeasureSpace.volume _
    exact hF_aesm.comp_measurePreserving hMP
  have h_minkowski : _root_.MeasureTheory.eLpNorm (translate k (-h) F - F) 2
      (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) ≤
        _root_.MeasureTheory.eLpNorm (translate k (-h) F) 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) +
          eLpNorm F 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) :=
    _root_.MeasureTheory.eLpNorm_sub_le hτF_aesm hF_aesm (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have h_τF_eq : _root_.MeasureTheory.eLpNorm (translate k (-h) F) 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) =
      eLpNorm F 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) :=
    eLpNorm_translate_eq (d := d) k (-h) F
  rw [h_τF_eq] at h_minkowski
  have h_step : _root_.MeasureTheory.eLpNorm (translate k (-h) F - F) 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) ≤
      2 * _root_.MeasureTheory.eLpNorm F 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
    rw [two_mul]; exact h_minkowski
  have h_inv_abs : |(-h)⁻¹| = |h|⁻¹ := by
    rw [abs_inv, abs_neg]
  have habs_h_pos : 0 < |h| := abs_pos.mpr hh
  have h_ofReal_inv :
      ENNReal.ofReal |(-h)⁻¹| = (ENNReal.ofReal |h|)⁻¹ := by
    rw [h_inv_abs]
    exact ENNReal.ofReal_inv_of_pos habs_h_pos
  rw [h_ofReal_inv]
  calc (ENNReal.ofReal |h|)⁻¹ *
        _root_.MeasureTheory.eLpNorm (translate k (-h) F - F) 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)
      ≤ (ENNReal.ofReal |h|)⁻¹ * (2 * _root_.MeasureTheory.eLpNorm F 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) := by
        gcongr
    _ = 2 / ENNReal.ofReal |h| * _root_.MeasureTheory.eLpNorm F 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
        rw [← mul_assoc]
        congr 1
        rw [ENNReal.div_eq_inv_mul]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.eLpNorm_diffQuot_neg_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.eLpNorm_diffQuot_neg_le target :: scope.openDecls } }

omit [NeZero d] in
private lemma eLpNorm_eta_sq_diffQuot_le
    (k : Fin d) (h : ℝ) {η u : EuclN → ℝ}
    {M_η : ℝ} (_hM_η_nn : 0 ≤ M_η) (hM_η : ∀ x, |η x| ≤ M_η) :
    _root_.MeasureTheory.eLpNorm (fun y => (η y)^2 * diffQuot k h u y) 2
        (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) ≤
      ENNReal.ofReal (M_η^2) *
        eLpNorm (diffQuot k h u) 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
  classical
  have h2_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2_ne_top : (2 : ℝ≥0∞) ≠ ∞ := by norm_num
  have h2_toReal : ((2 : ℝ≥0∞)).toReal = 2 := by show ENNReal.toReal 2 = 2; rfl
  have h_pow_eq : ∀ a : ℝ≥0∞, a ^ (2 : ℝ) = a ^ (2 : ℕ) := by
    intro a
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]
  have h_pt : ∀ y : EuclN,
      (‖(η y)^2 * diffQuot k h u y‖ₑ : ℝ≥0∞)^(2 : ℕ) ≤
        ENNReal.ofReal (M_η^4) * (‖diffQuot k h u y‖ₑ : ℝ≥0∞)^(2 : ℕ) := by
    intro y
    have h_real : ((η y)^2 * diffQuot k h u y)^2 ≤
        M_η^4 * (diffQuot k h u y)^2 := by
      have h_eta_sq_le : (η y)^2 ≤ M_η^2 := by
        have hY := hM_η y
        have h_abs_sq : (η y)^2 = |η y|^2 := by rw [sq_abs]
        rw [h_abs_sq]
        exact pow_le_pow_left₀ (abs_nonneg _) hY 2
      have h_eta_sq_sq_le : ((η y)^2)^2 ≤ (M_η^2)^2 := by
        have h_sq_nn : 0 ≤ (η y)^2 := sq_nonneg _
        exact pow_le_pow_left₀ h_sq_nn h_eta_sq_le 2
      have h_dq_sq_nn : 0 ≤ (diffQuot k h u y)^2 := sq_nonneg _
      have h_step : ((η y)^2 * diffQuot k h u y)^2 =
          ((η y)^2)^2 * (diffQuot k h u y)^2 := by ring
      have hM4 : (M_η^2)^2 = M_η^4 := by ring
      calc ((η y)^2 * diffQuot k h u y)^2
          = ((η y)^2)^2 * (diffQuot k h u y)^2 := h_step
        _ ≤ (M_η^2)^2 * (diffQuot k h u y)^2 :=
            mul_le_mul_of_nonneg_right h_eta_sq_sq_le h_dq_sq_nn
        _ = M_η^4 * (diffQuot k h u y)^2 := by rw [hM4]
    have h_lhs_eq :
        (‖(η y)^2 * diffQuot k h u y‖ₑ : ℝ≥0∞)^(2 : ℕ) =
          ENNReal.ofReal (((η y)^2 * diffQuot k h u y)^2) := by
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _) 2,
        sq_abs]
    have h_rhs_eq :
        (‖diffQuot k h u y‖ₑ : ℝ≥0∞)^(2 : ℕ) =
          ENNReal.ofReal ((diffQuot k h u y)^2) := by
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _) 2,
        sq_abs]
    rw [h_lhs_eq, h_rhs_eq]
    have hM4_nn : 0 ≤ M_η^4 := by positivity
    rw [show ENNReal.ofReal (M_η^4) *
        ENNReal.ofReal ((diffQuot k h u y)^2) =
      ENNReal.ofReal (M_η^4 * (diffQuot k h u y)^2) from
      (ENNReal.ofReal_mul hM4_nn).symm]
    exact ENNReal.ofReal_le_ofReal h_real
  have h_lint_le :
      ∫⁻ y : EuclN, (‖(η y)^2 * diffQuot k h u y‖ₑ : ℝ≥0∞)^(2 : ℕ)
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) ≤
        ENNReal.ofReal (M_η^4) *
          ∫⁻ y : EuclN, (‖diffQuot k h u y‖ₑ : ℝ≥0∞)^(2 : ℕ)
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
    calc ∫⁻ y : EuclN, (‖(η y)^2 * diffQuot k h u y‖ₑ : ℝ≥0∞)^(2 : ℕ)
        ≤ ∫⁻ y : EuclN, ENNReal.ofReal (M_η^4) *
            (‖diffQuot k h u y‖ₑ : ℝ≥0∞)^(2 : ℕ) := by
          refine _root_.MeasureTheory.lintegral_mono_ae ?_
          filter_upwards with y using h_pt y
      _ = ENNReal.ofReal (M_η^4) *
            ∫⁻ y : EuclN, (‖diffQuot k h u y‖ₑ : ℝ≥0∞)^(2 : ℕ) := by
          rw [_root_.MeasureTheory.lintegral_const_mul']
          exact ENNReal.ofReal_ne_top
  rw [_root_.MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal h2_ne_zero h2_ne_top,
    _root_.MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal h2_ne_zero h2_ne_top]
  rw [h2_toReal]
  have h_lhs_pow_eq :
      (∫⁻ y : EuclN, (‖(η y)^2 * diffQuot k h u y‖ₑ : ℝ≥0∞)^(2 : ℝ)
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) =
        ∫⁻ y : EuclN, (‖(η y)^2 * diffQuot k h u y‖ₑ : ℝ≥0∞)^(2 : ℕ)
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
    refine _root_.MeasureTheory.lintegral_congr_ae ?_
    filter_upwards with y using h_pow_eq _
  have h_rhs_pow_eq :
      (∫⁻ y : EuclN, (‖diffQuot k h u y‖ₑ : ℝ≥0∞)^(2 : ℝ)
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) =
        ∫⁻ y : EuclN, (‖diffQuot k h u y‖ₑ : ℝ≥0∞)^(2 : ℕ)
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
    refine _root_.MeasureTheory.lintegral_congr_ae ?_
    filter_upwards with y using h_pow_eq _
  rw [h_lhs_pow_eq, h_rhs_pow_eq]
  refine le_trans (ENNReal.rpow_le_rpow h_lint_le (by norm_num : (0 : ℝ) ≤ 1/2)) ?_
  have h_pull :
      (ENNReal.ofReal (M_η^4) *
          ∫⁻ y : EuclN, (‖diffQuot k h u y‖ₑ : ℝ≥0∞)^(2 : ℕ)) ^ ((1 : ℝ) / 2) =
        (ENNReal.ofReal (M_η^4))^((1 : ℝ) / 2) *
          (∫⁻ y : EuclN, (‖diffQuot k h u y‖ₑ : ℝ≥0∞)^(2 : ℕ))^((1 : ℝ) / 2) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1/2)]
  rw [h_pull]
  have h_sqrt_M4 :
      (ENNReal.ofReal (M_η^4))^((1 : ℝ) / 2) = ENNReal.ofReal (M_η^2) := by
    have hM2_nn : 0 ≤ M_η^2 := sq_nonneg _
    have h_M4_to_pow :
        ENNReal.ofReal (M_η^4) = (ENNReal.ofReal (M_η^2))^(2 : ℕ) := by
      rw [show M_η^4 = (M_η^2)^(2 : ℕ) from by ring,
        ENNReal.ofReal_pow hM2_nn 2]
    rw [h_M4_to_pow]
    rw [← ENNReal.rpow_natCast (ENNReal.ofReal (M_η^2)) 2,
      ← ENNReal.rpow_mul]
    have h_calc : ((2 : ℕ) : ℝ) * (1 / 2) = 1 := by norm_num
    rw [h_calc, ENNReal.rpow_one]
  rw [h_sqrt_M4]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.eLpNorm_eta_sq_diffQuot_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.eLpNorm_eta_sq_diffQuot_le target :: scope.openDecls } }

omit [NeZero d] in
theorem eLpNorm_nirenbergTestFunction_le
    (k : Fin d) {h : ℝ} (hh : h ≠ 0)
    {η u : EuclN → ℝ}
    (hη_cont : Continuous η)
    (hu_aesm : _root_.MeasureTheory.AEStronglyMeasurable u (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN))
    {M_η : ℝ} (hM_η_nn : 0 ≤ M_η) (hM_η : ∀ x, |η x| ≤ M_η) :
    _root_.MeasureTheory.eLpNorm (nirenbergTestFunction k h η u) 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) ≤
      (2 / ENNReal.ofReal |h|) * ENNReal.ofReal (M_η^2) *
        eLpNorm (diffQuot k h u) 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
  set F : EuclN → ℝ := fun y => (η y)^2 * diffQuot k h u y with hF_def
  have hF_aesm : _root_.MeasureTheory.AEStronglyMeasurable F (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
    rw [hF_def]
    have h1 : _root_.MeasureTheory.AEStronglyMeasurable (fun y : EuclN => (η y)^2)
        (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) :=
      (hη_cont.pow 2).aestronglyMeasurable
    have h2 : _root_.MeasureTheory.AEStronglyMeasurable (diffQuot k h u) (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) :=
      aestronglyMeasurable_diffQuot (d := d) k h hu_aesm
    exact h1.mul h2
  have h_step_A : _root_.MeasureTheory.eLpNorm (diffQuot k (-h) F) 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) ≤
      (2 / ENNReal.ofReal |h|) * _root_.MeasureTheory.eLpNorm F 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) :=
    eLpNorm_diffQuot_neg_le (d := d) k hh hF_aesm
  have h_step_B : _root_.MeasureTheory.eLpNorm F 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) ≤
      ENNReal.ofReal (M_η^2) *
        eLpNorm (diffQuot k h u) 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
    rw [hF_def]
    exact eLpNorm_eta_sq_diffQuot_le (d := d) k h hM_η_nn hM_η
  have h_lhs_unfold : nirenbergTestFunction k h η u = diffQuot k (-h) F := rfl
  rw [h_lhs_unfold]
  calc _root_.MeasureTheory.eLpNorm (diffQuot k (-h) F) 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)
      ≤ (2 / ENNReal.ofReal |h|) * _root_.MeasureTheory.eLpNorm F 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := h_step_A
    _ ≤ (2 / ENNReal.ofReal |h|) *
          (ENNReal.ofReal (M_η^2) *
            eLpNorm (diffQuot k h u) 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) := by
          gcongr
    _ = (2 / ENNReal.ofReal |h|) * ENNReal.ofReal (M_η^2) *
          eLpNorm (diffQuot k h u) 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
        rw [mul_assoc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.eLpNorm_nirenbergTestFunction_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.eLpNorm_nirenbergTestFunction_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.eLpNorm_nirenbergTestFunction_le ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.eLpNorm_nirenbergTestFunction_le

end DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction
