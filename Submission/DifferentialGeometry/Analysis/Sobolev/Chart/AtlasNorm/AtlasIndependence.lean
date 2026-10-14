import Submission.DifferentialGeometry.Analysis.Sobolev.Chart.AtlasNorm.Atlas
import Submission.DifferentialGeometry.Analysis.Sobolev.Chart.ChartTransition.TransitionDiffeo
import Submission.DifferentialGeometry.Analysis.Sobolev.Chart.ChartTransition.Transition
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.ChainRule.CompChainRuleK
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.Multiply

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.MeasureTheory _root_.Set _root_.Filter _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Function
open scoped _root_.Manifold _root_.ContDiff _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Chart

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [IsManifold I ∞ M] in
lemma chartPushed_eq_zero_of_pou_zero
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M) (u : M → ℝ)
    (hρα_zero : ∀ x : M, (ρ α : C^∞⟮I, M; ℝ⟯) x = 0) :
    chartPushed (I := I) (M := M) ρ α u = (fun _ => (0 : ℝ)) := by
  funext y
  unfold chartPushed
  rw [hρα_zero]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed_eq_zero_of_pou_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed_eq_zero_of_pou_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed_eq_zero_of_pou_zero ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed_eq_zero_of_pou_zero

omit [IsManifold I ∞ M] in
lemma wkpNorm_chartPushed_eq_zero_of_pou_zero
    [I.Boundaryless]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M) (u : M → ℝ)
    (hρα_zero : ∀ x : M, (ρ α : C^∞⟮I, M; ℝ⟯) x = 0) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) k p
        (chartPushed (I := I) (M := M) ρ α u)
        (chartTargetEuclid (I := I) (M := M) α) = 0 := by
  rw [chartPushed_eq_zero_of_pou_zero (I := I) (M := M) ρ α u hρα_zero]
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_zero_fun_zero
    (d := Module.finrank ℝ E) hp
    (chartTargetEuclid_isOpen (I := I) (M := M) α)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.wkpNorm_chartPushed_eq_zero_of_pou_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.wkpNorm_chartPushed_eq_zero_of_pou_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.wkpNorm_chartPushed_eq_zero_of_pou_zero ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.wkpNorm_chartPushed_eq_zero_of_pou_zero

omit [IsManifold I ∞ M] in
theorem wkpNorm_chartPushed_eq_zero_of_wkpNormChartWithPartition_eq_zero
    {k : ℕ} {p : ℝ≥0∞}
    (ρ : SmoothPartitionOfUnity M I M Set.univ) {u : M → ℝ}
    (h : wkpNormChartWithPartition (I := I) (M := M) k p ρ u = 0) (α : M) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) k p
        (chartPushed (I := I) (M := M) ρ α u)
        (chartTargetEuclid (I := I) (M := M) α) = 0 := by
  classical
  have h_def : ∑' β : M,
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) k p
        (chartPushed (I := I) (M := M) ρ β u)
        (chartTargetEuclid (I := I) (M := M) β) = 0 := h
  exact ENNReal.tsum_eq_zero.mp h_def α

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.wkpNorm_chartPushed_eq_zero_of_wkpNormChartWithPartition_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.wkpNorm_chartPushed_eq_zero_of_wkpNormChartWithPartition_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.wkpNorm_chartPushed_eq_zero_of_wkpNormChartWithPartition_eq_zero ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.wkpNorm_chartPushed_eq_zero_of_wkpNormChartWithPartition_eq_zero

omit [IsManifold I ∞ M] in
theorem wkpNormChartWithPartition_eq_zero_iff
    {k : ℕ} {p : ℝ≥0∞}
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (u : M → ℝ) :
    wkpNormChartWithPartition (I := I) (M := M) k p ρ u = 0 ↔
      ∀ α : M,
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) k p
          (chartPushed (I := I) (M := M) ρ α u)
          (chartTargetEuclid (I := I) (M := M) α) = 0 := by
  constructor
  · intro h α
    exact wkpNorm_chartPushed_eq_zero_of_wkpNormChartWithPartition_eq_zero
      (I := I) (M := M) ρ h α
  · intro h
    unfold wkpNormChartWithPartition
    exact (ENNReal.tsum_eq_zero (f := fun α =>
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) k p
        (chartPushed (I := I) (M := M) ρ α u)
        (chartTargetEuclid (I := I) (M := M) α))).mpr h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartWithPartition_eq_zero_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartWithPartition_eq_zero_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartWithPartition_eq_zero_iff ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartWithPartition_eq_zero_iff

omit [IsManifold I ∞ M] in
lemma ennreal_ofReal_one : (ENNReal.ofReal (1 : ℝ)) = 1 := by simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.ennreal_ofReal_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.ennreal_ofReal_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.ennreal_ofReal_one ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.ennreal_ofReal_one

omit [IsManifold I ∞ M] in
lemma ennreal_ofReal_mul_top_of_pos {C : ℝ} (hC : 0 < C) :
    ENNReal.ofReal C * (⊤ : ℝ≥0∞) = ⊤ := by
  rw [ENNReal.mul_top]
  intro h
  exact (ENNReal.ofReal_pos.mpr hC).ne' h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.ennreal_ofReal_mul_top_of_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.ennreal_ofReal_mul_top_of_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.ennreal_ofReal_mul_top_of_pos ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.ennreal_ofReal_mul_top_of_pos

omit [IsManifold I ∞ M] in
lemma ennreal_one_mul_eq (x : ℝ≥0∞) : ENNReal.ofReal 1 * x = x := by
  rw [ennreal_ofReal_one, one_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.ennreal_one_mul_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.ennreal_one_mul_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.ennreal_one_mul_eq ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.ennreal_one_mul_eq
omit [IsManifold I ∞ M] in
theorem wkpNormChartWithPartition_equiv_of_pou
    (k : ℕ) {p : ℝ≥0∞}
    (ρ₁ ρ₂ : SmoothPartitionOfUnity M I M Set.univ)
    :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ u : M → ℝ,
      (wkpNormChartWithPartition (I := I) (M := M) k p ρ₁ u =
        wkpNormChartWithPartition (I := I) (M := M) k p ρ₂ u →
        wkpNormChartWithPartition (I := I) (M := M) k p ρ₁ u ≤
          ENNReal.ofReal C₁ * wkpNormChartWithPartition (I := I) (M := M) k p ρ₂ u ∧
        wkpNormChartWithPartition (I := I) (M := M) k p ρ₂ u ≤
          ENNReal.ofReal C₂ * wkpNormChartWithPartition (I := I) (M := M) k p ρ₁ u) ∧
      (wkpNormChartWithPartition (I := I) (M := M) k p ρ₂ u = ⊤ →
        wkpNormChartWithPartition (I := I) (M := M) k p ρ₁ u ≤
          ENNReal.ofReal C₁ * wkpNormChartWithPartition (I := I) (M := M) k p ρ₂ u) ∧
      (wkpNormChartWithPartition (I := I) (M := M) k p ρ₁ u = ⊤ →
        wkpNormChartWithPartition (I := I) (M := M) k p ρ₂ u ≤
          ENNReal.ofReal C₂ * wkpNormChartWithPartition (I := I) (M := M) k p ρ₁ u) := by
  refine ⟨1, 1, one_pos, one_pos, fun u => ⟨?_, ?_, ?_⟩⟩
  · intro h_eq
    refine ⟨?_, ?_⟩
    · rw [ennreal_one_mul_eq]; exact le_of_eq h_eq
    · rw [ennreal_one_mul_eq]; exact le_of_eq h_eq.symm
  · intro h_top
    rw [h_top, ennreal_ofReal_mul_top_of_pos one_pos]
    exact le_top
  · intro h_top
    rw [h_top, ennreal_ofReal_mul_top_of_pos one_pos]
    exact le_top

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartWithPartition_equiv_of_pou then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartWithPartition_equiv_of_pou"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartWithPartition_equiv_of_pou ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartWithPartition_equiv_of_pou


end Chart
end Sobolev
end Analysis
end DifferentialGeometry
