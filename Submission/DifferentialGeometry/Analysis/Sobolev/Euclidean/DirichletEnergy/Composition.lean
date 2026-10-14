import Submission.DifferentialGeometry.Analysis.Integration.Measure.LipschitzDistortion
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.Calculus.MeanValue

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.MeasureTheory _root_.Filter
open scoped _root_.ENNReal _root_.NNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {μ : Measure E} [Measure.IsAddHaarMeasure μ]

omit [FiniteDimensional ℝ E] [Measure.IsAddHaarMeasure μ] in
open _root_.LipschitzWith in
theorem LipschitzWith.integrableOn_norm_fderiv_sq
    {f : E → F} {K : ℝ≥0} (hf : LipschitzWith K f) {s : Set E} (hs : μ s ≠ ∞) :
    IntegrableOn (fun x => ‖fderiv ℝ f x‖ ^ 2) s μ := by
  apply (_root_.MeasureTheory.integrableOn_const (C := (K : ℝ) ^ 2) hs).mono'
    ((measurable_fderiv ℝ f).norm.pow_const 2).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact (sq_le_sq₀ (norm_nonneg _) K.coe_nonneg).mpr
      (norm_fderiv_le_of_lipschitz ℝ hf)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LipschitzWith.integrableOn_norm_fderiv_sq then
    throwError "Refusing to shadow existing declaration LipschitzWith.integrableOn_norm_fderiv_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `LipschitzWith.integrableOn_norm_fderiv_sq ``Submission.LipschitzWith.integrableOn_norm_fderiv_sq

open _root_.Homeomorph in
theorem Homeomorph.integral_norm_fderiv_comp_sq_le
    (e : E ≃ₜ E) {L K : ℝ≥0} (he : LipschitzWith L e) (hei : LipschitzWith K e.symm)
    {f : E → F} {D : ℝ≥0} (hf : LipschitzWith D f)
    {s : Set E} (hs : MeasurableSet s) (hsμ : μ s ≠ ∞) :
    (∫ x in e ⁻¹' s, ‖fderiv ℝ (f ∘ e) x‖ ^ 2 ∂μ) ≤
      (L : ℝ) ^ 2 * (K : ℝ) ^ Module.finrank ℝ E *
        ∫ x in s, ‖fderiv ℝ f x‖ ^ 2 ∂μ := by
  have ha : AntilipschitzWith K e := by
    intro x y
    simpa only [e.symm_apply_apply] using hei (e x) (e y)
  have hq : Measure.QuasiMeasurePreserving e μ μ :=
    ⟨e.continuous.measurable,
      Measure.absolutelyContinuous_of_le_smul (ha.map_addHaar_le μ e.continuous.measurable)⟩
  have hpre : μ (e ⁻¹' s) ≠ ∞ :=
    ne_top_of_le_ne_top (by finiteness) (ha.addHaar_preimage_le μ s)
  have hif := hf.integrableOn_norm_fderiv_sq hsμ
  have hic := (hf.comp he).integrableOn_norm_fderiv_sq hpre
  have hip : _root_.MeasureTheory.IntegrableOn (fun x => ‖fderiv ℝ f (e x)‖ ^ 2) (e ⁻¹' s) μ := by
    have hm : _root_.MeasureTheory.AEStronglyMeasurable (fun x => ‖fderiv ℝ f (e x)‖ ^ 2)
        (μ.restrict (e ⁻¹' s)) := by
      have hm' := (((measurable_fderiv ℝ f).comp e.continuous.measurable).norm.pow_const 2)
      exact hm'.aestronglyMeasurable
    apply (_root_.MeasureTheory.integrableOn_const (C := (D : ℝ) ^ 2) hpre).mono'
      hm
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact (sq_le_sq₀ (norm_nonneg _) D.coe_nonneg).mpr
        (norm_fderiv_le_of_lipschitz ℝ hf)
  have hpoint : ∀ᵐ x ∂μ,
      ‖fderiv ℝ (f ∘ e) x‖ ^ 2 ≤ (L : ℝ) ^ 2 * ‖fderiv ℝ f (e x)‖ ^ 2 := by
    filter_upwards [he.ae_differentiableAt, hq.ae hf.ae_differentiableAt] with x hx hfx
    rw [fderiv_comp x hfx hx]
    have hnorm : ‖(fderiv ℝ f (e x)).comp (fderiv ℝ e x)‖ ≤
        ‖fderiv ℝ f (e x)‖ * L :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (norm_fderiv_le_of_lipschitz ℝ he) (norm_nonneg _))
    have hsq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) L.coe_nonneg)).mpr hnorm
    simpa only [mul_pow, mul_comm] using hsq
  have hfirst := _root_.MeasureTheory.integral_mono_ae hic (hip.const_mul ((L : ℝ) ^ 2))
    (_root_.MeasureTheory.ae_restrict_of_ae hpoint)
  rw [_root_.MeasureTheory.integral_const_mul] at hfirst
  have hsecond := e.setIntegral_comp_le_of_lipschitz_symm μ hei hs hif
    (Filter.Eventually.of_forall fun x => sq_nonneg (‖fderiv ℝ f x‖))
  exact hfirst.trans ((mul_le_mul_of_nonneg_left hsecond (sq_nonneg (L : ℝ))).trans_eq
    (mul_assoc _ _ _).symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Homeomorph.integral_norm_fderiv_comp_sq_le then
    throwError "Refusing to shadow existing declaration Homeomorph.integral_norm_fderiv_comp_sq_le"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.integral_norm_fderiv_comp_sq_le ``Submission.Homeomorph.integral_norm_fderiv_comp_sq_le

section Complex

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

open _root_.ContinuousLinearMap in
theorem ContinuousLinearMap.norm_sq_le_norm_one_sq_add_norm_I_sq (A : ℂ →L[ℝ] G) :
    ‖A‖ ^ 2 ≤ ‖A 1‖ ^ 2 + ‖A Complex.I‖ ^ 2 := by
  let S := ‖A 1‖ ^ 2 + ‖A Complex.I‖ ^ 2
  have hS : 0 ≤ S := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hnorm : ‖A‖ ≤ Real.sqrt S := by
    apply A.opNorm_le_bound (Real.sqrt_nonneg S)
    intro z
    have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
      simpa only [Complex.real_smul, mul_one] using (Complex.re_add_im z).symm
    have hAz : ‖A z‖ ≤ |z.re| * ‖A 1‖ + |z.im| * ‖A Complex.I‖ := by
      have heq := congrArg A hz
      rw [map_add, map_smul, map_smul] at heq
      rw [heq]
      simpa only [norm_smul, Real.norm_eq_abs] using
        norm_add_le (z.re • A 1) (z.im • A Complex.I)
    have hzsq : |z.re| ^ 2 + |z.im| ^ 2 = ‖z‖ ^ 2 := by
      rw [sq_abs, sq_abs, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      ring
    have hprod : (|z.re| * ‖A 1‖ + |z.im| * ‖A Complex.I‖) ^ 2 ≤
        (Real.sqrt S * ‖z‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hS, ← hzsq]
      dsimp only [S]
      nlinarith [sq_nonneg (|z.re| * ‖A Complex.I‖ - |z.im| * ‖A 1‖)]
    exact hAz.trans ((sq_le_sq₀ (by positivity) (by positivity)).mp hprod)
  exact (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg S)).mpr hnorm |>.trans_eq
    (Real.sq_sqrt hS)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.ContinuousLinearMap
  let env ← Lean.getEnv
  if env.contains `ContinuousLinearMap.norm_sq_le_norm_one_sq_add_norm_I_sq then
    throwError "Refusing to shadow existing declaration ContinuousLinearMap.norm_sq_le_norm_one_sq_add_norm_I_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousLinearMap.norm_sq_le_norm_one_sq_add_norm_I_sq ``Submission.ContinuousLinearMap.norm_sq_le_norm_one_sq_add_norm_I_sq

private theorem plane_energy_le_norm_sq (A : ℂ →L[ℝ] G) :
    (‖A 1‖ ^ 2 + ‖A Complex.I‖ ^ 2) / 2 ≤ ‖A‖ ^ 2 := by
  have h1 : ‖A 1‖ ≤ ‖A‖ := by simpa using A.le_opNorm (1 : ℂ)
  have hI : ‖A Complex.I‖ ≤ ‖A‖ := by simpa using A.le_opNorm Complex.I
  have hs1 := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr h1
  have hsI := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hI
  linarith

run_cmd do
  let target := ``Submission.plane_energy_le_norm_sq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `plane_energy_le_norm_sq target :: scope.openDecls } }

variable [FiniteDimensional ℝ G]

private theorem integrable_plane_energy {f : ℂ → G} {D : ℝ≥0} (hf : LipschitzWith D f)
    {s : Set ℂ} (hs : _root_.MeasureTheory.MeasureSpace.volume s ≠ ∞) :
    _root_.MeasureTheory.IntegrableOn (fun x => (‖fderiv ℝ f x 1‖ ^ 2 +
      ‖fderiv ℝ f x Complex.I‖ ^ 2) / 2) s := by
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  apply (hf.integrableOn_norm_fderiv_sq hs).mono'
  · have h1 : Measurable (fun x => fderiv ℝ f x 1) :=
      (ContinuousLinearMap.apply ℝ G (1 : ℂ)).continuous.measurable.comp (measurable_fderiv ℝ f)
    have hI : Measurable (fun x => fderiv ℝ f x Complex.I) :=
      (ContinuousLinearMap.apply ℝ G Complex.I).continuous.measurable.comp
        (measurable_fderiv ℝ f)
    exact ((h1.norm.pow_const 2).add (hI.norm.pow_const 2)).div_const
      2 |>.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (by positivity)]
      exact plane_energy_le_norm_sq _

run_cmd do
  let target := ``Submission.integrable_plane_energy
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `integrable_plane_energy target :: scope.openDecls } }

open _root_.Homeomorph in
theorem Homeomorph.integral_plane_dirichlet_energy_comp_le
    (e : ℂ ≃ₜ ℂ) {L K : ℝ≥0} (he : LipschitzWith L e) (hei : LipschitzWith K e.symm)
    {f : ℂ → G} {D : ℝ≥0} (hf : LipschitzWith D f)
    {s : Set ℂ} (hs : MeasurableSet s) (hsμ : _root_.MeasureTheory.MeasureSpace.volume s ≠ ∞) :
    (∫ x in e ⁻¹' s, (‖fderiv ℝ (f ∘ e) x 1‖ ^ 2 +
      ‖fderiv ℝ (f ∘ e) x Complex.I‖ ^ 2) / 2) ≤
      2 * (L : ℝ) ^ 2 * (K : ℝ) ^ 2 *
        ∫ x in s, (‖fderiv ℝ f x 1‖ ^ 2 + ‖fderiv ℝ f x Complex.I‖ ^ 2) / 2 := by
  have ha : AntilipschitzWith K e := by
    intro x y
    simpa only [e.symm_apply_apply] using hei (e x) (e y)
  have hpre : _root_.MeasureTheory.MeasureSpace.volume (e ⁻¹' s) ≠ ∞ :=
    ne_top_of_le_ne_top (by finiteness) (ha.addHaar_preimage_le _root_.MeasureTheory.MeasureSpace.volume s)
  have hfirst := _root_.MeasureTheory.integral_mono_ae (integrable_plane_energy (hf.comp he) hpre)
    ((hf.comp he).integrableOn_norm_fderiv_sq hpre)
    (Filter.Eventually.of_forall fun x => plane_energy_le_norm_sq (fderiv ℝ (f ∘ e) x))
  have hsecond := e.integral_norm_fderiv_comp_sq_le he hei hf hs hsμ
  rw [Complex.finrank_real_complex] at hsecond
  have hthird : (∫ x in s, ‖fderiv ℝ f x‖ ^ 2) ≤
      2 * ∫ x in s, (‖fderiv ℝ f x 1‖ ^ 2 + ‖fderiv ℝ f x Complex.I‖ ^ 2) / 2 := by
    rw [← _root_.MeasureTheory.integral_const_mul]
    apply _root_.MeasureTheory.integral_mono_ae (hf.integrableOn_norm_fderiv_sq hsμ)
      ((integrable_plane_energy hf hsμ).const_mul 2)
    exact Filter.Eventually.of_forall fun x => by
      have h := (fderiv ℝ f x).norm_sq_le_norm_one_sq_add_norm_I_sq
      linarith
  have h := hfirst.trans (hsecond.trans
    (mul_le_mul_of_nonneg_left hthird (by positivity)))
  nlinarith only [h]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Homeomorph.integral_plane_dirichlet_energy_comp_le then
    throwError "Refusing to shadow existing declaration Homeomorph.integral_plane_dirichlet_energy_comp_le"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.integral_plane_dirichlet_energy_comp_le ``Submission.Homeomorph.integral_plane_dirichlet_energy_comp_le

end Complex

end

noncomputable section

open _root_.Set _root_.MeasureTheory _root_.Filter _root_.Metric
open scoped _root_.NNReal _root_.ENNReal _root_.Topology

section Postcomposition

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]

private theorem integrable_plane_energy_of_lipschitz
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    {u : ℂ → Y} {K : ℝ≥0} (hu : LipschitzWith K u)
    {s : Set ℂ} (hs : _root_.MeasureTheory.MeasureSpace.volume s ≠ (∞ : ℝ≥0∞)) :
    _root_.MeasureTheory.IntegrableOn (fun x => (‖fderiv ℝ u x 1‖ ^ 2 +
      ‖fderiv ℝ u x Complex.I‖ ^ 2) / 2) s := by
  borelize Y
  have h1 : _root_.MeasureTheory.IntegrableOn (fun x => ‖fderiv ℝ u x 1‖ ^ 2) s := by
    apply (hu.integrableOn_norm_fderiv_sq hs).mono'
      ((measurable_fderiv_apply_const ℝ u 1).norm.pow_const 2).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (by simpa using (fderiv ℝ u x).le_opNorm 1) 2
  have hI : _root_.MeasureTheory.IntegrableOn (fun x => ‖fderiv ℝ u x Complex.I‖ ^ 2) s := by
    apply (hu.integrableOn_norm_fderiv_sq hs).mono'
      ((measurable_fderiv_apply_const ℝ u Complex.I).norm.pow_const 2).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _)
        (by simpa using (fderiv ℝ u x).le_opNorm Complex.I) 2
  exact (h1.add hI).div_const 2

run_cmd do
  let target := ``Submission.integrable_plane_energy_of_lipschitz
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `integrable_plane_energy_of_lipschitz target :: scope.openDecls } }

open _root_.Differentiable in
theorem Differentiable.integral_plane_dirichlet_energy_comp_le
    {T : F → G} (hT : Differentiable ℝ T) {L : ℝ≥0}
    (hL : ∀ y, ‖fderiv ℝ T y‖ ≤ L) {f : ℂ → F} {D : ℝ≥0}
    (hf : LipschitzWith D f) {s : Set ℂ} (hs : _root_.MeasureTheory.MeasureSpace.volume s ≠ (∞ : ℝ≥0∞)) :
    (∫ x in s, (‖fderiv ℝ (T ∘ f) x 1‖ ^ 2 +
      ‖fderiv ℝ (T ∘ f) x Complex.I‖ ^ 2) / 2) ≤
      (L : ℝ) ^ 2 * ∫ x in s,
        (‖fderiv ℝ f x 1‖ ^ 2 + ‖fderiv ℝ f x Complex.I‖ ^ 2) / 2 := by
  have hLip : LipschitzWith L T :=
    lipschitzWith_of_nnnorm_fderiv_le hT hL
  rw [← _root_.MeasureTheory.integral_const_mul]
  apply _root_.MeasureTheory.integral_mono_ae (integrable_plane_energy_of_lipschitz (hLip.comp hf) hs)
    ((integrable_plane_energy_of_lipschitz hf hs).const_mul ((L : ℝ) ^ 2))
  filter_upwards [_root_.MeasureTheory.ae_restrict_of_ae (s := s) hf.ae_differentiableAt] with x hx
  rw [fderiv_comp x (hT (f x)) hx]
  have hdir (v : ℂ) :
      ‖fderiv ℝ T (f x) (fderiv ℝ f x v)‖ ^ 2 ≤ (L : ℝ) ^ 2 * ‖fderiv ℝ f x v‖ ^ 2 := by
    have h := ((fderiv ℝ T (f x)).le_opNorm (fderiv ℝ f x v)).trans
      (mul_le_mul_of_nonneg_right (hL (f x)) (norm_nonneg _))
    simpa only [mul_pow] using
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg L.coe_nonneg (norm_nonneg _))).mpr h
  have h1 := hdir 1
  have hI := hdir Complex.I
  simp only [ContinuousLinearMap.comp_apply]
  nlinarith

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.Differentiable
  let env ← Lean.getEnv
  if env.contains `Differentiable.integral_plane_dirichlet_energy_comp_le then
    throwError "Refusing to shadow existing declaration Differentiable.integral_plane_dirichlet_energy_comp_le"
  Lean.modifyEnv fun env => Lean.addAlias env `Differentiable.integral_plane_dirichlet_energy_comp_le ``Submission.Differentiable.integral_plane_dirichlet_energy_comp_le

end Postcomposition

end
