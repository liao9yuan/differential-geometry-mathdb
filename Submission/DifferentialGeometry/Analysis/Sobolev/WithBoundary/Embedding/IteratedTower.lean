import Submission.DifferentialGeometry.Analysis.Sobolev.Manifold.Embedding.Iterated
import Submission.DifferentialGeometry.Analysis.Sobolev.WithBoundary.Embedding.Subcritical
import Submission.DifferentialGeometry.Analysis.Sobolev.WithBoundary.Euclidean.Morrey
import Submission.DifferentialGeometry.Analysis.Sobolev.WithBoundary.Chart.Defs
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.SupportAndDomain.IteratedSobolevHalfSpace

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
namespace WithBoundary

namespace EuclideanTowerStep

variable {d : ℕ} [NeZero d]

local notation "EuN" => EuclideanSpace ℝ (Fin d)

open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart

abbrev pOne (d : ℕ) (p : ℝ) : ℝ := TowerStep.pOne d p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.WithBoundary.EuclideanTowerStep.pOne then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.WithBoundary.EuclideanTowerStep.pOne"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.WithBoundary.EuclideanTowerStep.pOne ``Submission.DifferentialGeometry.Analysis.Sobolev.WithBoundary.EuclideanTowerStep.pOne

abbrev subcriticalConstant (k d : ℕ) [NeZero d] (p : ℝ) : ℝ :=
  TowerStep.subcriticalConstant k d p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.WithBoundary.EuclideanTowerStep.subcriticalConstant then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.WithBoundary.EuclideanTowerStep.subcriticalConstant"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.WithBoundary.EuclideanTowerStep.subcriticalConstant ``Submission.DifferentialGeometry.Analysis.Sobolev.WithBoundary.EuclideanTowerStep.subcriticalConstant

lemma subcriticalConstant_nonneg (k : ℕ) (p : ℝ) :
    0 ≤ subcriticalConstant k d p :=
  TowerStep.subcriticalConstant_nonneg k d p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.WithBoundary.EuclideanTowerStep.subcriticalConstant_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.WithBoundary.EuclideanTowerStep.subcriticalConstant_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.WithBoundary.EuclideanTowerStep.subcriticalConstant_nonneg ``Submission.DifferentialGeometry.Analysis.Sobolev.WithBoundary.EuclideanTowerStep.subcriticalConstant_nonneg

theorem MemWkpHalfSpace_subcritical_iterated
    (k : ℕ) {p : ℝ} (hp_one : 1 ≤ p) (hp_dim : p < (d : ℝ))
    {Ω : Set EuN} (hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    {f : EuN → ℝ}
    (hf_compact : HasCompactSupport f)
    (hf_support : tsupport f ⊆ interiorHalfSpace Ω)
    (hf : MemWkpHalfSpace (d := d) (k + 1) (ENNReal.ofReal p) f Ω) :
    MemWkpHalfSpace (d := d) k (ENNReal.ofReal (pOne d p)) f Ω ∧
      wkpNormHalfSpace (d := d) k (ENNReal.ofReal (pOne d p)) f Ω ≤
        ENNReal.ofReal (subcriticalConstant k d p) *
          wkpNormHalfSpace (d := d) (k + 1) (ENNReal.ofReal p) f Ω := by
  have hΩ_int_open : IsOpen (interiorHalfSpace (d := d) Ω) :=
    interiorHalfSpace_isOpen hΩ
  have hf' : MemWkp (d := d) (k + 1) (ENNReal.ofReal p) f
      (interiorHalfSpace Ω) := hf
  exact TowerStep.MemWkp_subcritical_iterated (d := d) k hp_one hp_dim
    hΩ_int_open hf_compact hf_support hf'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.WithBoundary.EuclideanTowerStep.MemWkpHalfSpace_subcritical_iterated then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.WithBoundary.EuclideanTowerStep.MemWkpHalfSpace_subcritical_iterated"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.WithBoundary.EuclideanTowerStep.MemWkpHalfSpace_subcritical_iterated ``Submission.DifferentialGeometry.Analysis.Sobolev.WithBoundary.EuclideanTowerStep.MemWkpHalfSpace_subcritical_iterated

theorem MemWkpHalfSpace_succ_subcritical_step
    {k : ℕ} {p : ℝ} (hp_one : 1 ≤ p) (hp_dim : p < (d : ℝ))
    {Ω : Set EuN} (hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    {f : EuN → ℝ}
    (hf_compact : HasCompactSupport f)
    (hf_support : tsupport f ⊆ interiorHalfSpace Ω)
    (hf : MemWkpHalfSpace (d := d) (k + 1) (ENNReal.ofReal p) f Ω) :
    MemWkpHalfSpace (d := d) k
        (ENNReal.ofReal ((d : ℝ) * p / ((d : ℝ) - p))) f Ω ∧
      ∃ C : ℝ, 0 ≤ C ∧
        wkpNormHalfSpace (d := d) k
            (ENNReal.ofReal ((d : ℝ) * p / ((d : ℝ) - p))) f Ω ≤
          ENNReal.ofReal C *
            wkpNormHalfSpace (d := d) (k + 1) (ENNReal.ofReal p) f Ω := by
  obtain ⟨h_mem, h_norm⟩ :=
    MemWkpHalfSpace_subcritical_iterated (d := d) k hp_one hp_dim hΩ
      hf_compact hf_support hf
  have hpOne_eq : pOne d p = (d : ℝ) * p / ((d : ℝ) - p) := rfl
  refine ⟨?_, ?_⟩
  · rw [show (ENNReal.ofReal ((d : ℝ) * p / ((d : ℝ) - p))) =
      ENNReal.ofReal (pOne d p) from by rw [hpOne_eq]]
    exact h_mem
  · refine ⟨subcriticalConstant k d p, subcriticalConstant_nonneg k p, ?_⟩
    rw [show (ENNReal.ofReal ((d : ℝ) * p / ((d : ℝ) - p))) =
      ENNReal.ofReal (pOne d p) from by rw [hpOne_eq]]
    exact h_norm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.WithBoundary.EuclideanTowerStep.MemWkpHalfSpace_succ_subcritical_step then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.WithBoundary.EuclideanTowerStep.MemWkpHalfSpace_succ_subcritical_step"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.WithBoundary.EuclideanTowerStep.MemWkpHalfSpace_succ_subcritical_step ``Submission.DifferentialGeometry.Analysis.Sobolev.WithBoundary.EuclideanTowerStep.MemWkpHalfSpace_succ_subcritical_step

end EuclideanTowerStep

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]

theorem wkpNormChart_succ_subcritical_step_withBoundary_perChart
    [T2Space M] [SigmaCompactSpace M]
    {k : ℕ} {p : ℝ} (hp_one : 1 ≤ p) (hp_dim : p < (n : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u : M → ℝ},
        (∀ α : M,
          HasCompactSupport
            (chartPushed (n := n) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU
                (modelWithCornersEuclideanHalfSpace n) M) α u)) →
        (∀ α : M,
          tsupport
            (chartPushed (n := n) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU
                (modelWithCornersEuclideanHalfSpace n) M) α u) ⊆
          DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
            (chartTargetEuclid (n := n) (M := M) α)) →
        MemWkpChart (n := n) (M := M) (k + 1) (ENNReal.ofReal p) u →
          MemWkpChart (n := n) (M := M) k
              (ENNReal.ofReal ((n : ℝ) * p / ((n : ℝ) - p))) u ∧
            wkpNormChart (n := n) (M := M) k
                (ENNReal.ofReal ((n : ℝ) * p / ((n : ℝ) - p))) u ≤
              ENNReal.ofReal C *
                wkpNormChart (n := n) (M := M) (k + 1) (ENNReal.ofReal p) u := by
  classical
  set C : ℝ := EuclideanTowerStep.subcriticalConstant k n p with hC_def
  have hC_nn : 0 ≤ C :=
    EuclideanTowerStep.subcriticalConstant_nonneg (d := n) k p
  refine ⟨C, hC_nn, ?_⟩
  intro u h_compact h_support hu
  have h_per_chart : ∀ α : M,
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace
          (d := n) k (ENNReal.ofReal ((n : ℝ) * p / ((n : ℝ) - p)))
          (chartPushed (n := n) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU
              (modelWithCornersEuclideanHalfSpace n) M) α u)
          (chartTargetEuclid (n := n) (M := M) α) ∧
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
          (d := n) k (ENNReal.ofReal ((n : ℝ) * p / ((n : ℝ) - p)))
          (chartPushed (n := n) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU
              (modelWithCornersEuclideanHalfSpace n) M) α u)
          (chartTargetEuclid (n := n) (M := M) α) ≤
        ENNReal.ofReal C *
          DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
            (d := n) (k + 1) (ENNReal.ofReal p)
            (chartPushed (n := n) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU
                (modelWithCornersEuclideanHalfSpace n) M) α u)
            (chartTargetEuclid (n := n) (M := M) α) := by
    intro α
    have h_iter :=
      EuclideanTowerStep.MemWkpHalfSpace_subcritical_iterated (d := n) k
        hp_one hp_dim
        (chartTargetEuclid_isHalfSpaceRelOpen (n := n) (M := M) α)
        (h_compact α) (h_support α) (hu α)
    obtain ⟨h_mem_p1, h_norm_p1⟩ := h_iter
    have h_pOne_eq : EuclideanTowerStep.pOne n p =
        (n : ℝ) * p / ((n : ℝ) - p) := rfl
    refine ⟨?_, ?_⟩
    · rw [show ENNReal.ofReal ((n : ℝ) * p / ((n : ℝ) - p)) =
        ENNReal.ofReal (EuclideanTowerStep.pOne n p) from by rw [h_pOne_eq]]
      exact h_mem_p1
    · rw [show ENNReal.ofReal ((n : ℝ) * p / ((n : ℝ) - p)) =
        ENNReal.ofReal (EuclideanTowerStep.pOne n p) from by rw [h_pOne_eq]]
      exact h_norm_p1
  refine ⟨fun α => (h_per_chart α).1, ?_⟩
  unfold wkpNormChart
  rw [show ENNReal.ofReal C * ∑' α : M,
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
          (d := n) (k + 1) (ENNReal.ofReal p)
          (chartPushed (n := n) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU
              (modelWithCornersEuclideanHalfSpace n) M) α u)
          (chartTargetEuclid (n := n) (M := M) α) =
      ∑' α : M, ENNReal.ofReal C *
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
          (d := n) (k + 1) (ENNReal.ofReal p)
          (chartPushed (n := n) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU
              (modelWithCornersEuclideanHalfSpace n) M) α u)
          (chartTargetEuclid (n := n) (M := M) α) from
    (ENNReal.tsum_mul_left).symm]
  exact ENNReal.tsum_le_tsum (fun α => (h_per_chart α).2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpNormChart_succ_subcritical_step_withBoundary_perChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpNormChart_succ_subcritical_step_withBoundary_perChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpNormChart_succ_subcritical_step_withBoundary_perChart ``Submission.DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpNormChart_succ_subcritical_step_withBoundary_perChart

theorem wkpNormChart_succ_subcritical_step_withBoundary_perChart_smooth
    [T2Space M] [SigmaCompactSpace M]
    {k : ℕ} {p : ℝ} (hp_one : 1 ≤ p) (hp_dim : p < (n : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u : M → ℝ},
        (∀ α : M,
          ContDiff ℝ (⊤ : ℕ∞)
            (chartPushed (n := n) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU
                (modelWithCornersEuclideanHalfSpace n) M) α u)) →
        (∀ α : M,
          HasCompactSupport
            (chartPushed (n := n) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU
                (modelWithCornersEuclideanHalfSpace n) M) α u)) →
        (∀ α : M,
          tsupport
            (chartPushed (n := n) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU
                (modelWithCornersEuclideanHalfSpace n) M) α u) ⊆
          DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
            (chartTargetEuclid (n := n) (M := M) α)) →
        MemWkpChart (n := n) (M := M) (k + 1) (ENNReal.ofReal p) u →
          MemWkpChart (n := n) (M := M) k
              (ENNReal.ofReal ((n : ℝ) * p / ((n : ℝ) - p))) u ∧
            wkpNormChart (n := n) (M := M) k
                (ENNReal.ofReal ((n : ℝ) * p / ((n : ℝ) - p))) u ≤
              ENNReal.ofReal C *
                wkpNormChart (n := n) (M := M) (k + 1) (ENNReal.ofReal p) u := by
  obtain ⟨C, hC_nn, h⟩ :=
    wkpNormChart_succ_subcritical_step_withBoundary_perChart (n := n) (M := M)
      (k := k) hp_one hp_dim
  refine ⟨C, hC_nn, ?_⟩
  intro u _hu_smooth h_compact h_support hu
  exact h h_compact h_support hu

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpNormChart_succ_subcritical_step_withBoundary_perChart_smooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpNormChart_succ_subcritical_step_withBoundary_perChart_smooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpNormChart_succ_subcritical_step_withBoundary_perChart_smooth ``Submission.DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpNormChart_succ_subcritical_step_withBoundary_perChart_smooth

theorem dim_lt_mul_sobolevConjugate_of_dim_lt_succ_mul
    (d : ℕ) (k : ℕ) (p : ℝ) (hp_pos : 0 < p) (hp_dim : p < (d : ℝ))
    (hkp : (d : ℝ) < (k + 1 : ℝ) * p) :
    (d : ℝ) < (k : ℝ) * ((d : ℝ) * p / ((d : ℝ) - p)) :=
  DifferentialGeometry.Analysis.Sobolev.Chart.IterationCalc.kp1_real_gt_d_of_kp1p_gt_d
    d k p hp_pos hp_dim hkp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.WithBoundary.dim_lt_mul_sobolevConjugate_of_dim_lt_succ_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.WithBoundary.dim_lt_mul_sobolevConjugate_of_dim_lt_succ_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.WithBoundary.dim_lt_mul_sobolevConjugate_of_dim_lt_succ_mul ``Submission.DifferentialGeometry.Analysis.Sobolev.WithBoundary.dim_lt_mul_sobolevConjugate_of_dim_lt_succ_mul

end WithBoundary
end Sobolev
end Analysis
end DifferentialGeometry
