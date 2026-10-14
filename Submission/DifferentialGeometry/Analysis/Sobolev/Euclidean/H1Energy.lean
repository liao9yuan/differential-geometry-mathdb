import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.Density
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolevQuant
import Mathlib.MeasureTheory.Function.L2Space

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.MeasureTheory _root_.Set
open scoped _root_.ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

private theorem integral_sq_eq_eLpNorm_sq {X : Type*} [MeasurableSpace X]
    {μ : _root_.MeasureTheory.Measure X} {f : X → ℝ} (hf : _root_.MeasureTheory.MemLp f 2 μ) :
    (∫ x, f x ^ 2 ∂μ) = (_root_.MeasureTheory.eLpNorm f 2 μ).toReal ^ 2 := by
  calc
    (∫ x, f x ^ 2 ∂μ) = ∫ x, _root_.Inner.inner ℝ (hf.toLp f x) (hf.toLp f x) ∂μ := by
      apply _root_.MeasureTheory.integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with x hx
      simp [hx]
    _ = _root_.Inner.inner ℝ (hf.toLp f) (hf.toLp f) := rfl
    _ = ‖hf.toLp f‖ ^ 2 := real_inner_self_eq_norm_sq _
    _ = (_root_.MeasureTheory.eLpNorm f 2 μ).toReal ^ 2 := by rw [Lp.norm_toLp]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_sq_eq_eLpNorm_sq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_sq_eq_eLpNorm_sq target :: scope.openDecls } }

theorem integral_smooth_h1_energy_le_wkpNorm_sq
    {d : ℕ} {Ω K : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω)
    (hKΩ : K ⊆ Ω) {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfW : MemWkp 1 2 f Ω) :
    (∫ x in K, f x ^ 2 +
      ∑ i, (fderiv ℝ f x (EuclideanSpace.single i 1)) ^ 2) ≤
        (iteratedWeakSobolevNorm 1 2 f Ω).toReal ^ 2 := by
  classical
  have hf1 := MemWkp.one_iff_memW1p.mp hfW
  let D := fun i : Fin d => fun x => fderiv ℝ f x (EuclideanSpace.single i 1)
  have hD : ∀ i, _root_.MeasureTheory.MemLp (D i) 2 (volume.restrict Ω) := fun i =>
    (chosenWeakPartialOrZero_memLp_of_mem hf1 i).ae_eq
      (chosenWeakPartial_smooth_ae_eq (by norm_num) hΩ hf hf1 i)
  have hDf : ∀ i, _root_.MeasureTheory.eLpNorm (D i) 2 (volume.restrict Ω) =
      eLpNorm (chosenWeakPartialOrZero 2 i f Ω) 2 (volume.restrict Ω) := fun i =>
    (_root_.MeasureTheory.eLpNorm_congr_ae
      (chosenWeakPartial_smooth_ae_eq (by norm_num) hΩ hf hf1 i)).symm
  have hW : (iteratedWeakSobolevNorm 1 2 f Ω).toReal =
      (_root_.MeasureTheory.eLpNorm f 2 (volume.restrict Ω)).toReal +
        ∑ i, (_root_.MeasureTheory.eLpNorm (D i) 2 (volume.restrict Ω)).toReal := by
    rw [wkpNorm_succ_eq_eLpNorm_add_sum_partial 0 2 Ω f]
    simp only [wkpNorm_zero, ← hDf]
    rw [ENNReal.toReal_add hf1.1.2.ne (ENNReal.sum_ne_top.mpr fun i _ => (hD i).2.ne),
      ENNReal.toReal_sum]
    exact fun i _ => (hD i).2.ne
  have hI : _root_.MeasureTheory.Integrable (fun x => f x ^ 2 + ∑ i, D i x ^ 2) (volume.restrict Ω) :=
    hf1.1.integrable_sq.add (_root_.MeasureTheory.integrable_finsetSum _ fun i _ => (hD i).integrable_sq)
  have hmono := _root_.MeasureTheory.integral_mono_measure (Measure.restrict_mono_set _root_.MeasureTheory.MeasureSpace.volume hKΩ)
    (Filter.Eventually.of_forall fun x =>
      add_nonneg (sq_nonneg (f x)) (Finset.sum_nonneg fun i _ => sq_nonneg (D i x))) hI
  refine hmono.trans ?_
  rw [_root_.MeasureTheory.integral_add hf1.1.integrable_sq (_root_.MeasureTheory.integrable_finsetSum _ fun i _ => (hD i).integrable_sq),
    _root_.MeasureTheory.integral_finsetSum _ fun i _ => (hD i).integrable_sq, integral_sq_eq_eLpNorm_sq hf1.1]
  simp only [integral_sq_eq_eLpNorm_sq (hD _)]
  rw [hW]
  have hs := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := Finset.univ) (fun i _ => ENNReal.toReal_nonneg
      (a := _root_.MeasureTheory.eLpNorm (D i) 2 (volume.restrict Ω)))
  have hf0 : 0 ≤ (_root_.MeasureTheory.eLpNorm f 2 (volume.restrict Ω)).toReal := ENNReal.toReal_nonneg
  have hs0 : 0 ≤ ∑ i, (_root_.MeasureTheory.eLpNorm (D i) 2 (volume.restrict Ω)).toReal :=
    Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
  nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_smooth_h1_energy_le_wkpNorm_sq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_smooth_h1_energy_le_wkpNorm_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_smooth_h1_energy_le_wkpNorm_sq ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_smooth_h1_energy_le_wkpNorm_sq

theorem integral_smooth_h1_energy_le_wkpNorm_sq_of_tsupport_subset
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω)
    (K : Set (EuclideanSpace ℝ (Fin d))) {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f) (hfs : tsupport f ⊆ Ω) :
    (∫ x in K, f x ^ 2 +
      ∑ i, (fderiv ℝ f x (EuclideanSpace.single i 1)) ^ 2) ≤
        (iteratedWeakSobolevNorm 1 2 f Ω).toReal ^ 2 := by
  have hfW := MemWkp_of_smooth_compactSupport hΩ hf hfc hfs (by norm_num : (1 : ℝ≥0∞) ≤ 2) 1
  have hfu := hfW.extend_zero (by norm_num) hΩ isOpen_univ (_root_.Set.subset_univ _) hfs hfc
  have h := integral_smooth_h1_energy_le_wkpNorm_sq isOpen_univ (_root_.Set.subset_univ K) hf hfu
  rwa [wkpNorm_extend_zero (by norm_num) hΩ isOpen_univ (_root_.Set.subset_univ _) hfW hfs hfc] at h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_smooth_h1_energy_le_wkpNorm_sq_of_tsupport_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_smooth_h1_energy_le_wkpNorm_sq_of_tsupport_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_smooth_h1_energy_le_wkpNorm_sq_of_tsupport_subset ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_smooth_h1_energy_le_wkpNorm_sq_of_tsupport_subset

end DifferentialGeometry.Analysis.Sobolev.Euclidean
