import Submission.DifferentialGeometry.Analysis.Sobolev.Manifold.Embedding.Subcritical
import Submission.DifferentialGeometry.Analysis.Sobolev.WithBoundary.Chart.Defs
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.SupportAndDomain.IteratedSobolevHalfSpace
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Family.Basic

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

variable {n : ℕ} [NeZero n]

local notation "EuN" => EuclideanSpace ℝ (Fin n)

theorem wkpNormHalfSpace_eq_wkpNorm_interiorHalfSpace
    (k : ℕ) (p : ℝ≥0∞) (u : EuN → ℝ) (Ω : Set EuN) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
      (d := n) k p u Ω =
    DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
      (d := n) k p u
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace Ω) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpNormHalfSpace_eq_wkpNorm_interiorHalfSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpNormHalfSpace_eq_wkpNorm_interiorHalfSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpNormHalfSpace_eq_wkpNorm_interiorHalfSpace ``Submission.DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpNormHalfSpace_eq_wkpNorm_interiorHalfSpace

theorem memWkpHalfSpace_iff_memWkp_interiorHalfSpace
    (k : ℕ) (p : ℝ≥0∞) (u : EuN → ℝ) (Ω : Set EuN) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace
        (d := n) k p u Ω ↔
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := n) k p u
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace Ω) :=
  Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.WithBoundary.memWkpHalfSpace_iff_memWkp_interiorHalfSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.WithBoundary.memWkpHalfSpace_iff_memWkp_interiorHalfSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.WithBoundary.memWkpHalfSpace_iff_memWkp_interiorHalfSpace ``Submission.DifferentialGeometry.Analysis.Sobolev.WithBoundary.memWkpHalfSpace_iff_memWkp_interiorHalfSpace

theorem eLpNorm_p_star_le_const_mul_wkpNormHalfSpace_of_memWkpHalfSpace
    {p : ℝ} (hp_one : 1 ≤ p) (hp_dim : p < (n : ℝ)) {Ω : Set EuN}
    (hΩ : DifferentialGeometry.Analysis.Sobolev.Euclidean.IsHalfSpaceRelOpen
      (d := n) Ω)
    {f : EuN → ℝ}
    (hf : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace
      (d := n) 1 (ENNReal.ofReal p) f Ω)
    (hf_compact : HasCompactSupport f)
    (hf_support : tsupport f ⊆
      DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace Ω) :
    _root_.MeasureTheory.eLpNorm f
        (ENNReal.ofReal ((n : ℝ) * p / ((n : ℝ) - p)))
        (volume.restrict
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace Ω)) ≤
      ENNReal.ofReal (DeGiorgi.CGns n p) * (n : ℝ≥0∞) *
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
          (d := n) 1 (ENNReal.ofReal p) f Ω := by
  have hΩ_int_open :
      IsOpen (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
        (d := n) Ω) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace_isOpen hΩ
  have h_main :=
    Analysis.Sobolev.Chart.EuclideanSubcritical.eLpNorm_p_star_le_const_mul_wkpNorm_of_memWkp
      (d := n) hp_one hp_dim hΩ_int_open hf hf_compact hf_support
  exact h_main

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.WithBoundary.eLpNorm_p_star_le_const_mul_wkpNormHalfSpace_of_memWkpHalfSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.WithBoundary.eLpNorm_p_star_le_const_mul_wkpNormHalfSpace_of_memWkpHalfSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.WithBoundary.eLpNorm_p_star_le_const_mul_wkpNormHalfSpace_of_memWkpHalfSpace ``Submission.DifferentialGeometry.Analysis.Sobolev.WithBoundary.eLpNorm_p_star_le_const_mul_wkpNormHalfSpace_of_memWkpHalfSpace

theorem eLpNorm_p_star_smooth_le_const_mul_wkpNormHalfSpace
    {p : ℝ} (hp_one : 1 ≤ p) (hp_dim : p < (n : ℝ)) {Ω : Set EuN}
    (hΩ : DifferentialGeometry.Analysis.Sobolev.Euclidean.IsHalfSpaceRelOpen
      (d := n) Ω)
    {f : EuN → ℝ} (hf_smooth : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf_compact : HasCompactSupport f)
    (hf_support : tsupport f ⊆
      DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace Ω) :
    _root_.MeasureTheory.eLpNorm f
        (ENNReal.ofReal ((n : ℝ) * p / ((n : ℝ) - p)))
        (volume.restrict
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace Ω)) ≤
      ENNReal.ofReal (DeGiorgi.CGns n p) * (n : ℝ≥0∞) *
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
          (d := n) 1 (ENNReal.ofReal p) f Ω := by
  have hΩ_int_open :
      IsOpen (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
        (d := n) Ω) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace_isOpen hΩ
  have hp_pos : 0 < p := by linarith
  have hp_enn_one : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp]
    exact ENNReal.ofReal_le_ofReal hp_one
  have hf_mem :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace
        (d := n) 1 (ENNReal.ofReal p) f Ω :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_of_smooth_compactSupport
      (d := n) hΩ_int_open hf_smooth hf_compact hf_support hp_enn_one 1
  exact eLpNorm_p_star_le_const_mul_wkpNormHalfSpace_of_memWkpHalfSpace
    (n := n) hp_one hp_dim hΩ hf_mem hf_compact hf_support

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.WithBoundary.eLpNorm_p_star_smooth_le_const_mul_wkpNormHalfSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.WithBoundary.eLpNorm_p_star_smooth_le_const_mul_wkpNormHalfSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.WithBoundary.eLpNorm_p_star_smooth_le_const_mul_wkpNormHalfSpace ``Submission.DifferentialGeometry.Analysis.Sobolev.WithBoundary.eLpNorm_p_star_smooth_le_const_mul_wkpNormHalfSpace

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]

omit [IsManifold (𝓡∂ n) ∞ M] in
theorem interiorHalfSpace_chartTargetEuclid_eq (α : M) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
        (chartTargetEuclid (n := n) (M := M) α) =
      (extChartAt (modelWithCornersEuclideanHalfSpace n) α).target ∩
        DifferentialGeometry.Analysis.Sobolev.Euclidean.openHalfSpace := by
  unfold DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
  unfold chartTargetEuclid
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.WithBoundary.interiorHalfSpace_chartTargetEuclid_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.WithBoundary.interiorHalfSpace_chartTargetEuclid_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.WithBoundary.interiorHalfSpace_chartTargetEuclid_eq ``Submission.DifferentialGeometry.Analysis.Sobolev.WithBoundary.interiorHalfSpace_chartTargetEuclid_eq

omit [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M] in
theorem interiorHalfSpace_chartTargetEuclid_isOpen (α : M) :
    IsOpen (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
      (chartTargetEuclid (n := n) (M := M) α)) :=
  DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace_isOpen
    (chartTargetEuclid_isHalfSpaceRelOpen (n := n) (M := M) α)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.WithBoundary.interiorHalfSpace_chartTargetEuclid_isOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.WithBoundary.interiorHalfSpace_chartTargetEuclid_isOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.WithBoundary.interiorHalfSpace_chartTargetEuclid_isOpen ``Submission.DifferentialGeometry.Analysis.Sobolev.WithBoundary.interiorHalfSpace_chartTargetEuclid_isOpen

omit [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M] in
theorem chartTargetEuclid_eLpNorm_p_star_smooth_le_const_mul_wkpNormHalfSpace
    {p : ℝ} (hp_one : 1 ≤ p) (hp_dim : p < (n : ℝ)) (α : M)
    {f : EuN → ℝ} (hf_smooth : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf_compact : HasCompactSupport f)
    (hf_support : tsupport f ⊆
      DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
        (chartTargetEuclid (n := n) (M := M) α)) :
    _root_.MeasureTheory.eLpNorm f
        (ENNReal.ofReal ((n : ℝ) * p / ((n : ℝ) - p)))
        (volume.restrict
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
            (chartTargetEuclid (n := n) (M := M) α))) ≤
      ENNReal.ofReal (DeGiorgi.CGns n p) * (n : ℝ≥0∞) *
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
          (d := n) 1 (ENNReal.ofReal p) f
          (chartTargetEuclid (n := n) (M := M) α) :=
  eLpNorm_p_star_smooth_le_const_mul_wkpNormHalfSpace
    (n := n) hp_one hp_dim
    (chartTargetEuclid_isHalfSpaceRelOpen (n := n) (M := M) α)
    hf_smooth hf_compact hf_support

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartTargetEuclid_eLpNorm_p_star_smooth_le_const_mul_wkpNormHalfSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartTargetEuclid_eLpNorm_p_star_smooth_le_const_mul_wkpNormHalfSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartTargetEuclid_eLpNorm_p_star_smooth_le_const_mul_wkpNormHalfSpace ``Submission.DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartTargetEuclid_eLpNorm_p_star_smooth_le_const_mul_wkpNormHalfSpace

omit [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M] in
theorem chartTargetEuclid_eLpNorm_p_star_le_const_mul_wkpNormHalfSpace_of_memWkpHalfSpace
    {p : ℝ} (hp_one : 1 ≤ p) (hp_dim : p < (n : ℝ)) (α : M)
    {f : EuN → ℝ}
    (hf : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace
      (d := n) 1 (ENNReal.ofReal p) f
      (chartTargetEuclid (n := n) (M := M) α))
    (hf_compact : HasCompactSupport f)
    (hf_support : tsupport f ⊆
      DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
        (chartTargetEuclid (n := n) (M := M) α)) :
    _root_.MeasureTheory.eLpNorm f
        (ENNReal.ofReal ((n : ℝ) * p / ((n : ℝ) - p)))
        (volume.restrict
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
            (chartTargetEuclid (n := n) (M := M) α))) ≤
      ENNReal.ofReal (DeGiorgi.CGns n p) * (n : ℝ≥0∞) *
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
          (d := n) 1 (ENNReal.ofReal p) f
          (chartTargetEuclid (n := n) (M := M) α) :=
  eLpNorm_p_star_le_const_mul_wkpNormHalfSpace_of_memWkpHalfSpace
    (n := n) hp_one hp_dim
    (chartTargetEuclid_isHalfSpaceRelOpen (n := n) (M := M) α)
    hf hf_compact hf_support

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartTargetEuclid_eLpNorm_p_star_le_const_mul_wkpNormHalfSpace_of_memWkpHalfSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartTargetEuclid_eLpNorm_p_star_le_const_mul_wkpNormHalfSpace_of_memWkpHalfSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartTargetEuclid_eLpNorm_p_star_le_const_mul_wkpNormHalfSpace_of_memWkpHalfSpace ``Submission.DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartTargetEuclid_eLpNorm_p_star_le_const_mul_wkpNormHalfSpace_of_memWkpHalfSpace

theorem chartPushed_eLpNorm_p_star_smooth_le_const_mul_wkpNormHalfSpace
    [T2Space M] [SigmaCompactSpace M]
    {p : ℝ} (hp_one : 1 ≤ p) (hp_dim : p < (n : ℝ)) (α : M)
    {u : M → ℝ}
    (hf_smooth : ContDiff ℝ (⊤ : ℕ∞)
      (chartPushed (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU
          (modelWithCornersEuclideanHalfSpace n) M) α u))
    (hf_compact : HasCompactSupport
      (chartPushed (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU
          (modelWithCornersEuclideanHalfSpace n) M) α u))
    (hf_support : tsupport
      (chartPushed (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU
          (modelWithCornersEuclideanHalfSpace n) M) α u) ⊆
      DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
        (chartTargetEuclid (n := n) (M := M) α)) :
    _root_.MeasureTheory.eLpNorm
        (chartPushed (n := n) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU
            (modelWithCornersEuclideanHalfSpace n) M) α u)
        (ENNReal.ofReal ((n : ℝ) * p / ((n : ℝ) - p)))
        (volume.restrict
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
            (chartTargetEuclid (n := n) (M := M) α))) ≤
      ENNReal.ofReal (DeGiorgi.CGns n p) * (n : ℝ≥0∞) *
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
          (d := n) 1 (ENNReal.ofReal p)
          (chartPushed (n := n) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU
              (modelWithCornersEuclideanHalfSpace n) M) α u)
          (chartTargetEuclid (n := n) (M := M) α) := by
  exact chartTargetEuclid_eLpNorm_p_star_smooth_le_const_mul_wkpNormHalfSpace
    (n := n) (M := M) hp_one hp_dim α hf_smooth hf_compact hf_support

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartPushed_eLpNorm_p_star_smooth_le_const_mul_wkpNormHalfSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartPushed_eLpNorm_p_star_smooth_le_const_mul_wkpNormHalfSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartPushed_eLpNorm_p_star_smooth_le_const_mul_wkpNormHalfSpace ``Submission.DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartPushed_eLpNorm_p_star_smooth_le_const_mul_wkpNormHalfSpace

theorem chartPushed_eLpNorm_p_star_le_const_mul_wkpNormHalfSpace_of_memWkpChart
    [T2Space M] [SigmaCompactSpace M]
    {p : ℝ} (hp_one : 1 ≤ p) (hp_dim : p < (n : ℝ)) (α : M)
    {u : M → ℝ}
    (hu : MemWkpChart (n := n) (M := M) 1 (ENNReal.ofReal p) u)
    (hf_compact : HasCompactSupport
      (chartPushed (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU
          (modelWithCornersEuclideanHalfSpace n) M) α u))
    (hf_support : tsupport
      (chartPushed (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU
          (modelWithCornersEuclideanHalfSpace n) M) α u) ⊆
      DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
        (chartTargetEuclid (n := n) (M := M) α)) :
    _root_.MeasureTheory.eLpNorm
        (chartPushed (n := n) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU
            (modelWithCornersEuclideanHalfSpace n) M) α u)
        (ENNReal.ofReal ((n : ℝ) * p / ((n : ℝ) - p)))
        (volume.restrict
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
            (chartTargetEuclid (n := n) (M := M) α))) ≤
      ENNReal.ofReal (DeGiorgi.CGns n p) * (n : ℝ≥0∞) *
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
          (d := n) 1 (ENNReal.ofReal p)
          (chartPushed (n := n) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU
              (modelWithCornersEuclideanHalfSpace n) M) α u)
          (chartTargetEuclid (n := n) (M := M) α) :=
  chartTargetEuclid_eLpNorm_p_star_le_const_mul_wkpNormHalfSpace_of_memWkpHalfSpace
    (n := n) (M := M) hp_one hp_dim α (hu α) hf_compact hf_support

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartPushed_eLpNorm_p_star_le_const_mul_wkpNormHalfSpace_of_memWkpChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartPushed_eLpNorm_p_star_le_const_mul_wkpNormHalfSpace_of_memWkpChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartPushed_eLpNorm_p_star_le_const_mul_wkpNormHalfSpace_of_memWkpChart ``Submission.DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartPushed_eLpNorm_p_star_le_const_mul_wkpNormHalfSpace_of_memWkpChart

theorem chartPushed_sum_eLpNorm_p_star_smooth_le_const_mul_wkpNormChart
    [T2Space M] [SigmaCompactSpace M]
    {p : ℝ} (hp_one : 1 ≤ p) (hp_dim : p < (n : ℝ))
    {u : M → ℝ}
    (h_smooth : ∀ α : M,
      ContDiff ℝ (⊤ : ℕ∞)
        (chartPushed (n := n) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU
            (modelWithCornersEuclideanHalfSpace n) M) α u))
    (h_compact : ∀ α : M,
      HasCompactSupport
        (chartPushed (n := n) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU
            (modelWithCornersEuclideanHalfSpace n) M) α u))
    (h_support : ∀ α : M,
      tsupport
        (chartPushed (n := n) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU
            (modelWithCornersEuclideanHalfSpace n) M) α u) ⊆
      DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
        (chartTargetEuclid (n := n) (M := M) α)) :
    ∑' α : M,
      _root_.MeasureTheory.eLpNorm
          (chartPushed (n := n) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU
              (modelWithCornersEuclideanHalfSpace n) M) α u)
          (ENNReal.ofReal ((n : ℝ) * p / ((n : ℝ) - p)))
          (volume.restrict
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
              (chartTargetEuclid (n := n) (M := M) α))) ≤
      ENNReal.ofReal (DeGiorgi.CGns n p) * (n : ℝ≥0∞) *
        wkpNormChart (n := n) (M := M) 1 (ENNReal.ofReal p) u := by
  classical
  set C : ℝ≥0∞ := ENNReal.ofReal (DeGiorgi.CGns n p) * (n : ℝ≥0∞) with hC_def
  have h_per : ∀ α : M,
      _root_.MeasureTheory.eLpNorm
          (chartPushed (n := n) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU
              (modelWithCornersEuclideanHalfSpace n) M) α u)
          (ENNReal.ofReal ((n : ℝ) * p / ((n : ℝ) - p)))
          (volume.restrict
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
              (chartTargetEuclid (n := n) (M := M) α))) ≤
        C *
          DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
            (d := n) 1 (ENNReal.ofReal p)
            (chartPushed (n := n) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU
                (modelWithCornersEuclideanHalfSpace n) M) α u)
            (chartTargetEuclid (n := n) (M := M) α) := fun α =>
    chartPushed_eLpNorm_p_star_smooth_le_const_mul_wkpNormHalfSpace
      (n := n) (M := M) hp_one hp_dim α (h_smooth α) (h_compact α) (h_support α)
  have h_sum := ENNReal.tsum_le_tsum h_per
  have h_factor : ∑' α : M, C *
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
          (d := n) 1 (ENNReal.ofReal p)
          (chartPushed (n := n) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU
              (modelWithCornersEuclideanHalfSpace n) M) α u)
          (chartTargetEuclid (n := n) (M := M) α) =
      C * wkpNormChart (n := n) (M := M) 1 (ENNReal.ofReal p) u := by
    rw [ENNReal.tsum_mul_left]
    rfl
  rw [h_factor] at h_sum
  exact h_sum

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartPushed_sum_eLpNorm_p_star_smooth_le_const_mul_wkpNormChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartPushed_sum_eLpNorm_p_star_smooth_le_const_mul_wkpNormChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartPushed_sum_eLpNorm_p_star_smooth_le_const_mul_wkpNormChart ``Submission.DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartPushed_sum_eLpNorm_p_star_smooth_le_const_mul_wkpNormChart

end WithBoundary
end Sobolev
end Analysis
end DifferentialGeometry
