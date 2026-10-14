import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Classical
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Normed.Operator.NormedSpace

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.ENNReal _root_.Topology

namespace DeGiorgi
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin d)

theorem MemW1pWitness.weakGrad_ae_eq_smoothGradField
    {p : ℝ≥0∞} (hp : 1 ≤ p) {u : V → ℝ} {Ω : Set V} (hΩ : IsOpen Ω)
    (hu : MemW1pWitness p u Ω) (hc : ContDiffOn ℝ 1 u Ω) :
    hu.weakGrad =ᵐ[volume.restrict Ω] smoothGradField u := by
  have hcomp (j : Fin d) : (fun x => hu.weakGrad x j) =ᵐ[volume.restrict Ω]
      (fun x => fderiv ℝ u x (EuclideanSpace.single j 1)) := by
    let D := fun x => fderiv ℝ u x (EuclideanSpace.single j 1)
    have hDc : ContinuousOn D Ω :=
      (hc.continuousOn_fderiv_of_isOpen hΩ le_rfl).clm_apply continuousOn_const
    have hGl : _root_.MeasureTheory.LocallyIntegrableOn (fun x => hu.weakGrad x j) Ω volume :=
      _root_.MeasureTheory.locallyIntegrableOn_of_locallyIntegrable_restrict
        ((hu.weakGrad_component_memLp j).locallyIntegrable hp)
    have hDl : _root_.MeasureTheory.LocallyIntegrableOn D Ω volume := hDc.locallyIntegrableOn hΩ.measurableSet
    have htest := hasWeakPartialDeriv_of_contDiffOn hΩ hc j
    have hzero : ∀ᵐ x ∂volume, x ∈ Ω → hu.weakGrad x j - D x = 0 := by
      apply hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hGl.sub hDl)
      intro φ hφ hφc hφs
      have h₁ := hu.isWeakGrad j φ hφ hφc hφs
      have h₂ := htest φ hφ hφc hφs
      have hI {f : V → ℝ} (hf : _root_.MeasureTheory.LocallyIntegrableOn f Ω _root_.MeasureTheory.MeasureSpace.volume) :
          Integrable (fun x => φ x * f x) volume := by
        have hi : _root_.MeasureTheory.IntegrableOn (fun x => φ x * f x) (tsupport φ) := by
          simpa only [mul_comm] using
            (hf.integrableOn_compact_subset hφs hφc).mul_continuousOn hφ.continuous.continuousOn hφc
        exact (_root_.MeasureTheory.integrableOn_iff_integrable_of_support_subset
          ((Function.support_mul_subset_left φ f).trans (subset_tsupport φ))).mp hi
      have hset (f : V → ℝ) : (∫ x in Ω, f x * φ x) = ∫ x, φ x * f x := by
        rw [_root_.MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
        · exact _root_.MeasureTheory.integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
        · intro x hx
          rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (hφs ht)), _root_.MulZeroClass.mul_zero]
      rw [hset] at h₁ h₂
      change (∫ x, φ x * (hu.weakGrad x j - D x)) = 0
      simp_rw [mul_sub]
      rw [_root_.MeasureTheory.integral_sub (hI hGl) (hI hDl)]
      linarith
    rw [Filter.EventuallyEq, _root_.MeasureTheory.ae_restrict_iff' hΩ.measurableSet]
    exact hzero.mono fun x hx hxm => sub_eq_zero.mp (hx hxm)
  filter_upwards [ae_all_iff.mpr hcomp] with x hx
  ext j
  exact hx j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.MemW1pWitness.weakGrad_ae_eq_smoothGradField then
    throwError "Refusing to shadow existing declaration DeGiorgi.MemW1pWitness.weakGrad_ae_eq_smoothGradField"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.MemW1pWitness.weakGrad_ae_eq_smoothGradField ``Submission.DeGiorgi.MemW1pWitness.weakGrad_ae_eq_smoothGradField

end DeGiorgi

end

noncomputable section

open _root_.Set _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.ENNReal _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

private theorem norm_le_sum_norm_columns
    {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] F) :
    ‖A‖ ≤ ∑ j : Fin d, ‖A (EuclideanSpace.single j 1)‖ := by
  classical
  apply A.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  intro x
  have hx : x = ∑ j : Fin d, x j • EuclideanSpace.single j (1 : ℝ) := by
    ext i
    simp [EuclideanSpace.single, Pi.single_apply, smul_eq_mul]
  calc
    ‖A x‖ = ‖∑ j : Fin d, x j • A (EuclideanSpace.single j 1)‖ := by
      apply congrArg _root_.Norm.norm
      simpa only [map_sum, map_smul] using congrArg A hx
    _ ≤ ∑ j : Fin d, ‖x j • A (EuclideanSpace.single j 1)‖ := norm_sum_le _ _
    _ = ∑ j : Fin d, ‖x j‖ * ‖A (EuclideanSpace.single j 1)‖ := by simp only [norm_smul]
    _ ≤ ∑ j : Fin d, ‖x‖ * ‖A (EuclideanSpace.single j 1)‖ := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right (PiLp.norm_apply_le x j) (norm_nonneg _)
    _ = (∑ j : Fin d, ‖A (EuclideanSpace.single j 1)‖) * ‖x‖ := by
      rw [← Finset.mul_sum, mul_comm]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.norm_le_sum_norm_columns
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Euclidean.norm_le_sum_norm_columns target :: scope.openDecls } }

variable {d : ℕ} {ι : Type*} [Fintype ι]

theorem memLp_fderiv_of_contDiffOn_of_memW1p
    {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω)
    {v : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ ι}
    (hv : ∀ i, DeGiorgi.MemW1pWitness p (fun x => v x i) Ω)
    (hvc : ContDiffOn ℝ 1 v Ω) :
    MemLp (fderiv ℝ v) p (volume.restrict Ω) := by
  classical
  let G (j : Fin d) (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ ι :=
    WithLp.toLp 2 fun i => (hv i).weakGrad x j
  have hgrad (i : ι) : (hv i).weakGrad =ᵐ[volume.restrict Ω]
      DeGiorgi.smoothGradField (fun x => v x i) :=
    (hv i).weakGrad_ae_eq_smoothGradField hp hΩ
      ((contDiff_piLp_apply (p := 2) (i := i)).comp_contDiffOn hvc)
  have hcols : ∀ᵐ x ∂volume.restrict Ω, ∀ j,
      G j x = fderiv ℝ v x (EuclideanSpace.single j 1) := by
    filter_upwards [ae_all_iff.mpr hgrad, _root_.MeasureTheory.ae_restrict_mem hΩ.measurableSet] with x hx hxΩ
    intro j
    ext i
    have hd : DifferentiableAt ℝ v x :=
      (hvc.contDiffAt (hΩ.mem_nhds hxΩ)).differentiableAt one_ne_zero
    let L : EuclideanSpace ℝ ι →L[ℝ] ℝ := PiLp.proj 2 (fun _ : ι => ℝ) i
    have hh := L.hasFDerivAt.comp x hd.hasFDerivAt
    change (hv i).weakGrad x j = (fderiv ℝ v x (EuclideanSpace.single j 1)) i
    rw [hx i]
    change fderiv ℝ (L ∘ v) x (EuclideanSpace.single j 1) = _
    rw [hh.fderiv]
    rfl
  have hG (j : Fin d) : _root_.MeasureTheory.MemLp (G j) p (volume.restrict Ω) :=
    MemLp.of_eval_piLp fun i => (hv i).weakGrad_component_memLp j
  have hpartial (j : Fin d) :
      MemLp (fun x => fderiv ℝ v x (EuclideanSpace.single j 1)) p (volume.restrict Ω) :=
    (hG j).ae_eq (hcols.mono fun x hx => hx j)
  have hsum : _root_.MeasureTheory.MemLp (fun x => ∑ j : Fin d, ‖fderiv ℝ v x (EuclideanSpace.single j 1)‖)
      p (volume.restrict Ω) := _root_.MeasureTheory.memLp_finsetSum _ fun j _ => (hpartial j).norm
  exact hsum.mono' (measurable_fderiv ℝ v).aestronglyMeasurable
    (Eventually.of_forall fun x => norm_le_sum_norm_columns (fderiv ℝ v x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.memLp_fderiv_of_contDiffOn_of_memW1p then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.memLp_fderiv_of_contDiffOn_of_memW1p"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.memLp_fderiv_of_contDiffOn_of_memW1p ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.memLp_fderiv_of_contDiffOn_of_memW1p

theorem integrableOn_norm_fderiv_sq_of_contDiffOn_of_memW12
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω)
    {v : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ ι}
    (hv : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => v x i) Ω)
    (hvc : ContDiffOn ℝ 1 v Ω) :
    IntegrableOn (fun x => ‖fderiv ℝ v x‖ ^ 2) Ω :=
  (memLp_fderiv_of_contDiffOn_of_memW1p (by norm_num) hΩ hv hvc).norm.integrable_sq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.integrableOn_norm_fderiv_sq_of_contDiffOn_of_memW12 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.integrableOn_norm_fderiv_sq_of_contDiffOn_of_memW12"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.integrableOn_norm_fderiv_sq_of_contDiffOn_of_memW12 ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.integrableOn_norm_fderiv_sq_of_contDiffOn_of_memW12

theorem integrableOn_norm_fderiv_comp_complex_repr_sq_of_contDiffOn_of_memW12
    {v : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ ι} {R : ℝ}
    (hv : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => v x i) (Metric.ball 0 R))
    (hvc : ContDiffOn ℝ 1 v (Metric.ball 0 R)) :
    _root_.MeasureTheory.IntegrableOn (fun z => ‖fderiv ℝ (v ∘ Complex.orthonormalBasisOneI.repr) z‖ ^ 2)
      (Metric.ball (0 : ℂ) R) := by
  let e := Complex.orthonormalBasisOneI.repr
  have hpre : e ⁻¹' Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R = Metric.ball (0 : ℂ) R := by
    ext x
    simp only [_root_.Set.mem_preimage, Metric.mem_ball, dist_zero_right, e.norm_map]
  have hmp : _root_.MeasureTheory.MeasurePreserving e (volume.restrict (Metric.ball (0 : ℂ) R))
      (volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R)) := by
    have h := e.measurePreserving.restrict_preimage
      (s := Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R)
      Metric.isOpen_ball.measurableSet
    rwa [hpre] at h
  have hi := hmp.integrable_comp_of_integrable
    (integrableOn_norm_fderiv_sq_of_contDiffOn_of_memW12 Metric.isOpen_ball hv hvc)
  have heq (z : ℂ) : ‖fderiv ℝ (v ∘ e) z‖ = ‖fderiv ℝ v (e z)‖ := by
    have hd : fderiv ℝ (v ∘ e) z = (fderiv ℝ v (e z)).comp e.toContinuousLinearMap :=
      e.toContinuousLinearEquiv.comp_right_fderiv (f := v) (x := z)
    rw [hd]
    exact ContinuousLinearMap.opNorm_comp_linearIsometryEquiv _ e
  change _root_.MeasureTheory.Integrable (fun z => ‖fderiv ℝ (v ∘ e) z‖ ^ 2)
    (volume.restrict (Metric.ball (0 : ℂ) R))
  apply hi.congr
  exact Eventually.of_forall fun z => (congrArg (fun t : ℝ => t ^ 2) (heq z)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.integrableOn_norm_fderiv_comp_complex_repr_sq_of_contDiffOn_of_memW12 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.integrableOn_norm_fderiv_comp_complex_repr_sq_of_contDiffOn_of_memW12"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.integrableOn_norm_fderiv_comp_complex_repr_sq_of_contDiffOn_of_memW12 ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.integrableOn_norm_fderiv_comp_complex_repr_sq_of_contDiffOn_of_memW12

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end
