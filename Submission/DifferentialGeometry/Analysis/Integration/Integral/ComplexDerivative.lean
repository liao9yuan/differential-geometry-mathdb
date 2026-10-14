import Submission.DifferentialGeometry.Analysis.Integration.Lp.Bilinear
import Submission.DifferentialGeometry.Analysis.Integration.Measure.EuclideanPlane
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Filter
open scoped _root_.Topology _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Analysis

variable {ι : Type*} [Fintype ι]

private theorem integrableOn_target_energy_column
    {f : ℂ → EuclideanSpace ℝ ι} {C : ℝ≥0} (hf : LipschitzWith C f)
    {K : Set (EuclideanSpace ℝ ι)} (hK : IsCompact K)
    (A : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : ContinuousOn A K) {a : ℝ}
    (hfK : _root_.Set.MapsTo f (Metric.closedBall (0 : ℂ) a) K) (v : ℂ) :
    _root_.MeasureTheory.IntegrableOn (fun z => A (f z) (fderiv ℝ f z v) (fderiv ℝ f z v))
      (Metric.ball (0 : ℂ) a) := by
  have hc := (hA.comp hf.continuous.continuousOn hfK).mono Metric.ball_subset_closedBall
  have hm : _root_.MeasureTheory.AEStronglyMeasurable (fun z => A (f z))
      (volume.restrict (Metric.ball (0 : ℂ) a)) :=
    hc.aestronglyMeasurable Metric.isOpen_ball.measurableSet
  have hnormc : ContinuousOn (fun y => ‖A y‖) K :=
    (@continuous_norm (EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ)
      inferInstance).comp_continuousOn hA
  obtain ⟨Λ, hΛ⟩ := hK.bddAbove_image hnormc
  have hb : ∀ᵐ z ∂volume.restrict (Metric.ball (0 : ℂ) a), ‖A (f z)‖ ≤ Λ := by
    filter_upwards [_root_.MeasureTheory.ae_restrict_mem Metric.isOpen_ball.measurableSet] with z hz
    exact hΛ (_root_.Set.mem_image_of_mem _ (hfK (Metric.ball_subset_closedBall hz)))
  let : _root_.MeasureTheory.IsFiniteMeasure (volume.restrict (Metric.ball (0 : ℂ) a)) :=
    isFiniteMeasure_restrict.mpr
      ((_root_.MeasureTheory.measure_mono Metric.ball_subset_closedBall).trans_lt
        (_root_.ProperSpace.isCompact_closedBall (0 : ℂ) a).measure_lt_top).ne
  have hd : _root_.MeasureTheory.MemLp (fun z => fderiv ℝ f z v) 2 (volume.restrict (Metric.ball (0 : ℂ) a)) :=
    MemLp.of_bound (measurable_fderiv_apply_const ℝ f v).aestronglyMeasurable
      ((C : ℝ) * ‖v‖) (Eventually.of_forall fun z =>
        ((fderiv ℝ f z).le_opNorm v).trans
          (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hf) (norm_nonneg v)))
  exact integrable_bilinear_of_apply_aestronglyMeasurable (fun z => A (f z))
    (fun v w => (hm.apply_continuousLinearMap v).apply_continuousLinearMap w) hb hd hd

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.integrableOn_target_energy_column
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.integrableOn_target_energy_column target :: scope.openDecls } }

theorem sum_integral_target_energy_comp_complex_repr_symm
    {f : ℂ → EuclideanSpace ℝ ι} {C : ℝ≥0} (hf : LipschitzWith C f)
    {K : Set (EuclideanSpace ℝ ι)} (hK : IsCompact K)
    (A : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : ContinuousOn A K) {a : ℝ} (hfK : _root_.Set.MapsTo f (Metric.closedBall (0 : ℂ) a) K) :
    (∑ j : Fin 2, ∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) a,
      A (f (Complex.orthonormalBasisOneI.repr.symm x))
        (fderiv ℝ (fun y => f (Complex.orthonormalBasisOneI.repr.symm y))
          x (EuclideanSpace.single j 1))
        (fderiv ℝ (fun y => f (Complex.orthonormalBasisOneI.repr.symm y))
          x (EuclideanSpace.single j 1))) =
      2 * ∫ z in Metric.ball (0 : ℂ) a,
        (A (f z) (fderiv ℝ f z 1) (fderiv ℝ f z 1) +
          A (f z) (fderiv ℝ f z Complex.I) (fderiv ℝ f z Complex.I)) / 2 := by
  let e := Complex.orthonormalBasisOneI.repr.symm
  have hpre : e ⁻¹' Metric.ball (0 : ℂ) a = Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) a := by
    ext x
    simp only [_root_.Set.mem_preimage, Metric.mem_ball, dist_zero_right, LinearIsometryEquiv.norm_map]
  have hd (j : Fin 2) (x : EuclideanSpace ℝ (Fin 2)) :
      fderiv ℝ (fun y => f (e y)) x (EuclideanSpace.single j 1) =
        fderiv ℝ f (e x) (Complex.orthonormalBasisOneI j) := by
    rw [show (fun y => f (e y)) = f ∘ e.toContinuousLinearEquiv by rfl,
      e.toContinuousLinearEquiv.comp_right_fderiv]
    change fderiv ℝ f (e x) (e (EuclideanSpace.single j 1)) = _
    congr 1
    exact Complex.orthonormalBasisOneI.repr_symm_single j
  have he (j : Fin 2) :
      (∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) a,
        A (f (e x)) (fderiv ℝ (fun y => f (e y)) x (EuclideanSpace.single j 1))
          (fderiv ℝ (fun y => f (e y)) x (EuclideanSpace.single j 1))) =
      ∫ z in Metric.ball (0 : ℂ) a,
        A (f z) (fderiv ℝ f z (Complex.orthonormalBasisOneI j))
          (fderiv ℝ f z (Complex.orthonormalBasisOneI j)) := by
    simp_rw [hd]
    have h := e.measurePreserving.setIntegral_preimage_emb
      e.toHomeomorph.toMeasurableEquiv.measurableEmbedding (fun z =>
        A (f z) (fderiv ℝ f z (Complex.orthonormalBasisOneI j))
          (fderiv ℝ f z (Complex.orthonormalBasisOneI j))) (Metric.ball (0 : ℂ) a)
    rwa [hpre] at h
  change (∑ j : Fin 2, ∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) a,
    A (f (e x)) (fderiv ℝ (fun y => f (e y)) x (EuclideanSpace.single j 1))
      (fderiv ℝ (fun y => f (e y)) x (EuclideanSpace.single j 1))) = _
  simp_rw [he]
  rw [Fin.sum_univ_two, _root_.MeasureTheory.integral_div,
    _root_.MeasureTheory.integral_add (integrableOn_target_energy_column hf hK A hA hfK 1)
      (integrableOn_target_energy_column hf hK A hA hfK Complex.I)]
  simp only [Complex.coe_orthonormalBasisOneI, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.sum_integral_target_energy_comp_complex_repr_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.sum_integral_target_energy_comp_complex_repr_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.sum_integral_target_energy_comp_complex_repr_symm ``Submission.DifferentialGeometry.Analysis.sum_integral_target_energy_comp_complex_repr_symm

end DifferentialGeometry.Analysis

end

noncomputable section
open _root_.Set _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.Topology _root_.ENNReal _root_.NNReal _root_.ContDiff

namespace DifferentialGeometry.Analysis

variable {ι : Type*} [Fintype ι]

theorem integral_opNorm_sq_le_two_sum_columns
    {u : ℂ → EuclideanSpace ℝ ι} {C : ℝ≥0} (hu : LipschitzWith C u)
    {S : Set ℂ} {R : ℝ}
    (hSball : S ⊆ Metric.closedBall (0 : ℂ) R) :
    (∫ z in S, ‖fderiv ℝ u z‖ ^ 2) ≤
      2 * ∫ z in S,
        ‖fderiv ℝ u z 1‖ ^ 2 + ‖fderiv ℝ u z Complex.I‖ ^ 2 := by
  let : _root_.MeasureTheory.IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.mpr
    ((_root_.MeasureTheory.measure_mono hSball).trans_lt (_root_.ProperSpace.isCompact_closedBall (0 : ℂ) R).measure_lt_top).ne
  have hd : _root_.MeasureTheory.MemLp (fderiv ℝ u) 2 (volume.restrict S) :=
    MemLp.of_bound (measurable_fderiv ℝ u).aestronglyMeasurable C
      (Eventually.of_forall fun _ => norm_fderiv_le_of_lipschitz ℝ hu)
  have hcol (v : ℂ) : _root_.MeasureTheory.MemLp (fun z => fderiv ℝ u z v) 2 (volume.restrict S) := by
    apply MemLp.of_bound (measurable_fderiv_apply_const ℝ u v).aestronglyMeasurable
      ((C : ℝ) * ‖v‖)
    exact Eventually.of_forall fun z => ((fderiv ℝ u z).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hu) (norm_nonneg _))
  rw [← _root_.MeasureTheory.integral_const_mul]
  refine _root_.MeasureTheory.integral_mono_ae hd.norm.integrable_sq
    (((hcol 1).norm.integrable_sq.add (hcol Complex.I).norm.integrable_sq).const_mul 2) ?_
  exact Eventually.of_forall fun z => by
    let A := fderiv ℝ u z
    have hn : ‖A‖ ≤ ‖A 1‖ + ‖A Complex.I‖ := by
      apply A.opNorm_le_bound (add_nonneg (norm_nonneg _) (norm_nonneg _))
      intro w
      have hw : w = w.re • (1 : ℂ) + w.im • Complex.I := by
        simpa only [Complex.real_smul, mul_one] using w.re_add_im.symm
      have hAw := congrArg A hw
      simp only [map_add, map_smul] at hAw
      calc
        ‖A w‖ ≤ |w.re| * ‖A 1‖ + |w.im| * ‖A Complex.I‖ := by
          rw [hAw]
          simpa only [norm_smul, Real.norm_eq_abs] using
            norm_add_le (w.re • A 1) (w.im • A Complex.I)
        _ ≤ ‖w‖ * ‖A 1‖ + ‖w‖ * ‖A Complex.I‖ := by
          gcongr
          · exact Complex.abs_re_le_norm w
          · exact Complex.abs_im_le_norm w
        _ = _ := by ring
    have hs := pow_le_pow_left₀ (norm_nonneg A) hn 2
    dsimp only [A] at hs
    nlinarith [sq_nonneg (‖A 1‖ - ‖A Complex.I‖)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.integral_opNorm_sq_le_two_sum_columns then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.integral_opNorm_sq_le_two_sum_columns"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.integral_opNorm_sq_le_two_sum_columns ``Submission.DifferentialGeometry.Analysis.integral_opNorm_sq_le_two_sum_columns

end DifferentialGeometry.Analysis

end
