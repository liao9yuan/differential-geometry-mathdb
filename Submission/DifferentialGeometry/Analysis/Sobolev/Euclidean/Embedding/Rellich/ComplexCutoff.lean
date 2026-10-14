import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.ZeroTrace.LipschitzCutoff
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.Rellich.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section

open _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter _root_.Metric
open scoped _root_.ENNReal _root_.NNReal _root_.Topology _root_.ContDiff

namespace DifferentialGeometry.Analysis.Sobolev

theorem rellich_kondrachov_seq_complex_cutoff_of_lipschitz
    {η : ℂ → ℝ} (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hηball : tsupport η ⊆ _root_.Metric.ball (0 : ℂ) 1)
    (f : ℕ → ℂ → ℝ) (hf : ∀ n, ∃ K : ℝ≥0, LipschitzWith K (f n))
    {A B : ℝ} (hA : ∀ n, (∫ z in _root_.Metric.ball (0 : ℂ) 1, f n z ^ 2) ≤ A)
    (hB : ∀ n, (∫ z in _root_.Metric.ball (0 : ℂ) 1, ‖fderiv ℝ (f n) z‖ ^ 2) ≤ B) :
    let e := Complex.orthonormalBasisOneI.repr.symm
    ∃ (φ : ℕ → ℕ) (v : EuclideanSpace ℝ (Fin 2) → ℝ),
      StrictMono φ ∧ _root_.MeasureTheory.MemLp v 2 (volume.restrict (_root_.Metric.ball 0 1)) ∧
      _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x => η (e x) * f (φ n) (e x) - v x)
        2 (volume.restrict (_root_.Metric.ball 0 1))) _root_.Filter.atTop (𝓝 0) := by
  let e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm
  let u : ℕ → EuclideanSpace ℝ (Fin 2) → ℝ := fun n x => η (e x) * f n (e x)
  obtain ⟨C, hC, hcut⟩ := exists_memW01p_complex_cutoff_bounds_of_lipschitz hη hηc hηball
  let D := C * (Real.sqrt A + Real.sqrt B)
  have hD : 0 ≤ D := mul_nonneg hC (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hu (n : ℕ) :
      DeGiorgi.MemW01p 2 (u n) (_root_.Metric.ball 0 1) ∧
      _root_.MeasureTheory.eLpNorm (u n) 2 (volume.restrict (_root_.Metric.ball 0 1)) ≤ ENNReal.ofReal D ∧
      ∀ hw : DeGiorgi.MemW1pWitness 2 (u n) (_root_.Metric.ball 0 1), ∀ i : Fin 2,
        _root_.MeasureTheory.eLpNorm (fun x => hw.weakGrad x i) 2 (volume.restrict (_root_.Metric.ball 0 1)) ≤
          ENNReal.ofReal D := by
    obtain ⟨K, hK⟩ := hf n
    exact hcut hK (hA n) (hB n)
  have hmem (n : ℕ) : DeGiorgi.MemW01p 2 (u n) (_root_.Metric.ball 0 1) := (hu n).1
  have hfun (n : ℕ) :
      eLpNorm (u n) 2 (volume.restrict (_root_.Metric.ball 0 1)) ≤ ENNReal.ofReal (2 * D) :=
    (hu n).2.1.trans (ENNReal.ofReal_le_ofReal (by nlinarith))
  have hgrad (n : ℕ) :
      ∑ i : Fin 2,
        _root_.MeasureTheory.eLpNorm (fun x => (Classical.choose (hmem n).2).weakGrad x i)
          2 (volume.restrict (_root_.Metric.ball 0 1)) ≤ ENNReal.ofReal (2 * D) := by
    calc
      _ ≤ ∑ _i : Fin 2, ENNReal.ofReal D :=
        Finset.sum_le_sum fun i _ => (hu n).2.2 (Classical.choose (hmem n).2) i
      _ = _ := by
        simp only [Fin.sum_univ_two]
        rw [two_mul, ENNReal.ofReal_add hD hD]
  obtain ⟨φ, hφ, v, hv, hlim⟩ := rellich_kondrachov_W01p_seq
    _root_.Metric.isOpen_ball _root_.Metric.isBounded_ball (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hmem hfun hgrad
  exact ⟨φ, v, hφ, hv, hlim⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.rellich_kondrachov_seq_complex_cutoff_of_lipschitz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.rellich_kondrachov_seq_complex_cutoff_of_lipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.rellich_kondrachov_seq_complex_cutoff_of_lipschitz ``Submission.DifferentialGeometry.Analysis.Sobolev.rellich_kondrachov_seq_complex_cutoff_of_lipschitz

end DifferentialGeometry.Analysis.Sobolev

end

end
