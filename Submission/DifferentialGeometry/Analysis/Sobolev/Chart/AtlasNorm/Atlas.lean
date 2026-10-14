import Submission.DifferentialGeometry.Analysis.Sobolev.Chart.Defs
import Submission.DifferentialGeometry.Analysis.Sobolev.Chart.BanachCompleteness.Banach

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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def MemWkpChartWithPartition
    (k : ℕ) (p : ℝ≥0∞)
    (ρ : SmoothPartitionOfUnity M I M Set.univ)
    (u : M → ℝ) : Prop :=
  ∀ α : M,
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E)
      k p
      (chartPushed (I := I) (M := M) ρ α u)
      (chartTargetEuclid (I := I) (M := M) α)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChartWithPartition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChartWithPartition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChartWithPartition ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChartWithPartition

def wkpNormChartWithPartition
    (k : ℕ) (p : ℝ≥0∞)
    (ρ : SmoothPartitionOfUnity M I M Set.univ)
    (u : M → ℝ) : ℝ≥0∞ :=
  ∑' α : M,
    DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
      (d := Module.finrank ℝ E)
      k p
      (chartPushed (I := I) (M := M) ρ α u)
      (chartTargetEuclid (I := I) (M := M) α)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartWithPartition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartWithPartition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartWithPartition ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartWithPartition

theorem MemWkpChartWithPartition_chartAtlasPOU
    [T2Space M] [SigmaCompactSpace M] (k : ℕ) (p : ℝ≥0∞) (u : M → ℝ) :
    MemWkpChartWithPartition (I := I) (M := M) k p
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) u ↔
      MemWkpChart (I := I) (M := M) k p u := Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChartWithPartition_chartAtlasPOU then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChartWithPartition_chartAtlasPOU"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChartWithPartition_chartAtlasPOU ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChartWithPartition_chartAtlasPOU

theorem wkpNormChartWithPartition_chartAtlasPOU
    [T2Space M] [SigmaCompactSpace M] (k : ℕ) (p : ℝ≥0∞) (u : M → ℝ) :
    wkpNormChartWithPartition (I := I) (M := M) k p
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) u =
      wkpNormChart (I := I) (M := M) k p u := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartWithPartition_chartAtlasPOU then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartWithPartition_chartAtlasPOU"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartWithPartition_chartAtlasPOU ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartWithPartition_chartAtlasPOU

omit [IsManifold I ∞ M] in
theorem chartPushed_congr_of_pointwise_eq
    (ρ ρ' : SmoothPartitionOfUnity M I M Set.univ)
    (h : ∀ α : M, ∀ x : M, (ρ α : C^∞⟮I, M; ℝ⟯) x = (ρ' α : C^∞⟮I, M; ℝ⟯) x)
    (α : M) (u : M → ℝ) :
    chartPushed (I := I) (M := M) ρ α u =
      chartPushed (I := I) (M := M) ρ' α u := by
  funext y
  unfold chartPushed
  rw [h α]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed_congr_of_pointwise_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed_congr_of_pointwise_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed_congr_of_pointwise_eq ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed_congr_of_pointwise_eq

omit [IsManifold I ∞ M] in
theorem wkpNormChartWithPartition_congr_of_pointwise_eq
    (k : ℕ) (p : ℝ≥0∞)
    (ρ ρ' : SmoothPartitionOfUnity M I M Set.univ)
    (h : ∀ α : M, ∀ x : M, (ρ α : C^∞⟮I, M; ℝ⟯) x = (ρ' α : C^∞⟮I, M; ℝ⟯) x)
    (u : M → ℝ) :
    wkpNormChartWithPartition (I := I) (M := M) k p ρ u =
      wkpNormChartWithPartition (I := I) (M := M) k p ρ' u := by
  unfold wkpNormChartWithPartition
  refine tsum_congr (fun α => ?_)
  rw [chartPushed_congr_of_pointwise_eq (I := I) (M := M) ρ ρ' h α u]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartWithPartition_congr_of_pointwise_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartWithPartition_congr_of_pointwise_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartWithPartition_congr_of_pointwise_eq ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartWithPartition_congr_of_pointwise_eq

omit [IsManifold I ∞ M] in
theorem MemWkpChartWithPartition_congr_of_pointwise_eq
    {k : ℕ} {p : ℝ≥0∞}
    (ρ ρ' : SmoothPartitionOfUnity M I M Set.univ)
    (h : ∀ α : M, ∀ x : M, (ρ α : C^∞⟮I, M; ℝ⟯) x = (ρ' α : C^∞⟮I, M; ℝ⟯) x)
    (u : M → ℝ) :
    MemWkpChartWithPartition (I := I) (M := M) k p ρ u ↔
      MemWkpChartWithPartition (I := I) (M := M) k p ρ' u := by
  refine ⟨fun H α => ?_, fun H α => ?_⟩
  · have hcp := chartPushed_congr_of_pointwise_eq (I := I) (M := M) ρ ρ' h α u
    rw [← hcp]
    exact H α
  · have hcp := chartPushed_congr_of_pointwise_eq (I := I) (M := M) ρ ρ'
      h α u
    rw [hcp]
    exact H α

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChartWithPartition_congr_of_pointwise_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChartWithPartition_congr_of_pointwise_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChartWithPartition_congr_of_pointwise_eq ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChartWithPartition_congr_of_pointwise_eq

omit [IsManifold I ∞ M] in
theorem MemWkpChartWithPartition_zero_fun
    [I.Boundaryless]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (ρ : SmoothPartitionOfUnity M I M Set.univ) :
    MemWkpChartWithPartition (I := I) (M := M) k p ρ (fun _ : M => (0 : ℝ)) := by
  intro α
  rw [chartPushed_zero]
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_zero_fun
    (d := Module.finrank ℝ E) hp (chartTargetEuclid_isOpen (I := I) (M := M) α)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChartWithPartition_zero_fun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChartWithPartition_zero_fun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChartWithPartition_zero_fun ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChartWithPartition_zero_fun

omit [IsManifold I ∞ M] in
theorem wkpNormChartWithPartition_zero_fun
    [I.Boundaryless]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (ρ : SmoothPartitionOfUnity M I M Set.univ) :
    wkpNormChartWithPartition (I := I) (M := M) k p ρ (fun _ : M => (0 : ℝ)) = 0 := by
  unfold wkpNormChartWithPartition
  have hpt : ∀ α : M,
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) k p
        (chartPushed (I := I) (M := M) ρ α (fun _ : M => (0 : ℝ)))
        (chartTargetEuclid (I := I) (M := M) α) = 0 := by
    intro α
    rw [chartPushed_zero]
    exact DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_zero_fun_zero
      (d := Module.finrank ℝ E) hp
      (chartTargetEuclid_isOpen (I := I) (M := M) α)
  rw [tsum_congr hpt]
  exact tsum_zero

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartWithPartition_zero_fun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartWithPartition_zero_fun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartWithPartition_zero_fun ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartWithPartition_zero_fun

omit [IsManifold I ∞ M] in
theorem MemWkpChartWithPartition_add
    [I.Boundaryless]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (ρ : SmoothPartitionOfUnity M I M Set.univ)
    {u v : M → ℝ}
    (hu : MemWkpChartWithPartition (I := I) (M := M) k p ρ u)
    (hv : MemWkpChartWithPartition (I := I) (M := M) k p ρ v) :
    MemWkpChartWithPartition (I := I) (M := M) k p ρ (fun x => u x + v x) := by
  intro α
  rw [chartPushed_add]
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.add
    (d := Module.finrank ℝ E) hp
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    (hu α) (hv α)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChartWithPartition_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChartWithPartition_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChartWithPartition_add ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChartWithPartition_add

omit [IsManifold I ∞ M] in
theorem MemWkpChartWithPartition_const_smul
    [I.Boundaryless]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (ρ : SmoothPartitionOfUnity M I M Set.univ)
    (c : ℝ) {u : M → ℝ}
    (hu : MemWkpChartWithPartition (I := I) (M := M) k p ρ u) :
    MemWkpChartWithPartition (I := I) (M := M) k p ρ (fun x => c * u x) := by
  intro α
  rw [chartPushed_const_smul]
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.const_smul
    (d := Module.finrank ℝ E) hp
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    (hu α) c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChartWithPartition_const_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChartWithPartition_const_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChartWithPartition_const_smul ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChartWithPartition_const_smul

omit [IsManifold I ∞ M] in
theorem MemWkpChartWithPartition_neg
    [I.Boundaryless]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (ρ : SmoothPartitionOfUnity M I M Set.univ)
    {u : M → ℝ}
    (hu : MemWkpChartWithPartition (I := I) (M := M) k p ρ u) :
    MemWkpChartWithPartition (I := I) (M := M) k p ρ (fun x => -u x) := by
  have h := MemWkpChartWithPartition_const_smul (I := I) (M := M) hp ρ (-1) hu
  have hEq : (fun x : M => (-1 : ℝ) * u x) = (fun x : M => -u x) := by
    funext x; ring
  rw [hEq] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChartWithPartition_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChartWithPartition_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChartWithPartition_neg ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChartWithPartition_neg

omit [IsManifold I ∞ M] in
theorem MemWkpChartWithPartition_sub
    [I.Boundaryless]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (ρ : SmoothPartitionOfUnity M I M Set.univ)
    {u v : M → ℝ}
    (hu : MemWkpChartWithPartition (I := I) (M := M) k p ρ u)
    (hv : MemWkpChartWithPartition (I := I) (M := M) k p ρ v) :
    MemWkpChartWithPartition (I := I) (M := M) k p ρ (fun x => u x - v x) := by
  have hneg := MemWkpChartWithPartition_neg (I := I) (M := M) hp ρ hv
  have h := MemWkpChartWithPartition_add (I := I) (M := M) hp ρ hu hneg
  have hEq : (fun x : M => u x + -v x) = (fun x : M => u x - v x) := by
    funext x; ring
  rw [hEq] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChartWithPartition_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChartWithPartition_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChartWithPartition_sub ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChartWithPartition_sub

omit [IsManifold I ∞ M] in
theorem wkpNormChartWithPartition_add_le
    [I.Boundaryless]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (ρ : SmoothPartitionOfUnity M I M Set.univ)
    {u v : M → ℝ}
    (hu : MemWkpChartWithPartition (I := I) (M := M) k p ρ u)
    (hv : MemWkpChartWithPartition (I := I) (M := M) k p ρ v) :
    wkpNormChartWithPartition (I := I) (M := M) k p ρ (fun x => u x + v x) ≤
      wkpNormChartWithPartition (I := I) (M := M) k p ρ u +
        wkpNormChartWithPartition (I := I) (M := M) k p ρ v := by
  unfold wkpNormChartWithPartition
  rw [← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum ?_
  intro α
  rw [chartPushed_add]
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_add_le
    (d := Module.finrank ℝ E) hp
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    (hu α) (hv α)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartWithPartition_add_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartWithPartition_add_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartWithPartition_add_le ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartWithPartition_add_le

omit [IsManifold I ∞ M] in
theorem wkpNormChartWithPartition_const_smul
    [I.Boundaryless]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (ρ : SmoothPartitionOfUnity M I M Set.univ)
    (c : ℝ) {u : M → ℝ}
    (hu : MemWkpChartWithPartition (I := I) (M := M) k p ρ u) :
    wkpNormChartWithPartition (I := I) (M := M) k p ρ (fun x => c * u x) =
      ‖c‖ₑ * wkpNormChartWithPartition (I := I) (M := M) k p ρ u := by
  unfold wkpNormChartWithPartition
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr ?_
  intro α
  rw [chartPushed_const_smul]
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_const_smul
    (d := Module.finrank ℝ E) hp
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    (hu α) c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartWithPartition_const_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartWithPartition_const_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartWithPartition_const_smul ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartWithPartition_const_smul

omit [IsManifold I ∞ M] in
theorem MemWkpChartWithPartition.le_succ
    {k : ℕ} {p : ℝ≥0∞}
    {ρ : SmoothPartitionOfUnity M I M Set.univ}
    {u : M → ℝ}
    (h : MemWkpChartWithPartition (I := I) (M := M) (k + 1) p ρ u) :
    MemWkpChartWithPartition (I := I) (M := M) k p ρ u := by
  intro α
  exact (h α).le_succ

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChartWithPartition
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChartWithPartition.le_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChartWithPartition.le_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChartWithPartition.le_succ ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChartWithPartition.le_succ

omit [IsManifold I ∞ M] in
theorem MemWkpChartWithPartition.le_of_le
    {k k' : ℕ} {p : ℝ≥0∞}
    {ρ : SmoothPartitionOfUnity M I M Set.univ}
    {u : M → ℝ}
    (hk : k ≤ k') (h : MemWkpChartWithPartition (I := I) (M := M) k' p ρ u) :
    MemWkpChartWithPartition (I := I) (M := M) k p ρ u := by
  intro α
  exact (h α).le_of_le hk

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChartWithPartition.le_of_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChartWithPartition.le_of_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChartWithPartition.le_of_le ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChartWithPartition.le_of_le

omit [IsManifold I ∞ M] in
theorem wkpNormChartWithPartition_lt_top_of_memWkpChartWithPartition
    [CompactSpace M] [I.Boundaryless]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (ρ : SmoothPartitionOfUnity M I M Set.univ)
    {u : M → ℝ} (hu : MemWkpChartWithPartition (I := I) (M := M) k p ρ u) :
    wkpNormChartWithPartition (I := I) (M := M) k p ρ u < ⊤ := by
  classical
  unfold wkpNormChartWithPartition
  set f : M → ℝ≥0∞ := fun α =>
    DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
      (d := Module.finrank ℝ E) k p
      (chartPushed (I := I) (M := M) ρ α u)
      (chartTargetEuclid (I := I) (M := M) α) with hf_def
  have hPOU_localFin : LocallyFinite
      (fun α : M => Function.support (ρ α : M → ℝ)) :=
    ρ.locallyFinite
  have hSupport_finite : {α : M | (Function.support (ρ α : M → ℝ)).Nonempty}.Finite :=
    hPOU_localFin.finite_nonempty_of_compact
  have hf_zero_off : ∀ α : M, (Function.support (ρ α : M → ℝ)) = ∅ →
        f α = 0 := by
    intro α hα
    have hρ_empty : ∀ x : M, (ρ α : M → ℝ) x = 0 := by
      intro x
      have : x ∉ Function.support (ρ α : M → ℝ) := by
        rw [hα]
        exact Set.notMem_empty x
      simpa [Function.mem_support] using this
    have hChartPushed_zero : chartPushed (I := I) (M := M) ρ α u =
        (fun _ => (0 : ℝ)) := by
      funext y
      unfold chartPushed
      rw [hρ_empty]
      ring
    change DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
      (d := Module.finrank ℝ E) k p
      (chartPushed (I := I) (M := M) ρ α u)
      (chartTargetEuclid (I := I) (M := M) α) = 0
    rw [hChartPushed_zero]
    exact DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_zero_fun_zero
      (d := Module.finrank ℝ E) hp
      (chartTargetEuclid_isOpen (I := I) (M := M) α)
  set S : Set M := {α : M | (Function.support (ρ α : M → ℝ)).Nonempty}
      with hS_def
  have hS_finite : S.Finite := hSupport_finite
  have htsum_eq : ∑' α : M, f α = ∑ α ∈ hS_finite.toFinset, f α := by
    rw [tsum_eq_sum]
    intro α hα
    have hαS : α ∉ S := by
      intro hαS
      apply hα
      exact (Set.Finite.mem_toFinset _).mpr hαS
    have hempty : (Function.support (ρ α : M → ℝ)) = ∅ := by
      have h_not_nonempty : ¬ (Function.support (ρ α : M → ℝ)).Nonempty := by
        intro hne
        exact hαS hne
      exact Set.not_nonempty_iff_eq_empty.mp h_not_nonempty
    exact hf_zero_off α hempty
  rw [htsum_eq]
  apply ENNReal.sum_lt_top.mpr
  intro α _
  rw [hf_def]
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_lt_top_of_memWkp
    (d := Module.finrank ℝ E) (hu α)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartWithPartition_lt_top_of_memWkpChartWithPartition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartWithPartition_lt_top_of_memWkpChartWithPartition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartWithPartition_lt_top_of_memWkpChartWithPartition ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartWithPartition_lt_top_of_memWkpChartWithPartition

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem support_set_finite_of_compactSpace
    [CompactSpace M]
    (ρ : SmoothPartitionOfUnity M I M Set.univ) :
    {α : M | (Function.support (ρ α : M → ℝ)).Nonempty}.Finite :=
  ρ.locallyFinite.finite_nonempty_of_compact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.support_set_finite_of_compactSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.support_set_finite_of_compactSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.support_set_finite_of_compactSpace ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.support_set_finite_of_compactSpace

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem fintsupport_finite
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (x₀ : M) :
    {α : M | x₀ ∈ tsupport (ρ α : M → ℝ)}.Finite :=
  ρ.finite_tsupport x₀

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.fintsupport_finite then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.fintsupport_finite"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.fintsupport_finite ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.fintsupport_finite

omit [IsManifold I ∞ M] in
omit [FiniteDimensional ℝ E] in
theorem support_pou_mul_subset
    (ρ ρ' : SmoothPartitionOfUnity M I M Set.univ) (α β : M) :
    Function.support (fun x : M => (ρ α : M → ℝ) x * (ρ' β : M → ℝ) x) ⊆
      Function.support (ρ α : M → ℝ) ∩ Function.support (ρ' β : M → ℝ) := by
  intro x hx
  simp only [Function.mem_support] at hx
  refine ⟨?_, ?_⟩ <;> simp only [Function.mem_support] <;> intro h <;>
    apply hx <;> rw [h] <;> ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.support_pou_mul_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.support_pou_mul_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.support_pou_mul_subset ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.support_pou_mul_subset

omit [IsManifold I ∞ M] in
omit [FiniteDimensional ℝ E] in
theorem tsupport_pou_mul_subset
    (ρ ρ' : SmoothPartitionOfUnity M I M Set.univ) (α β : M) :
    tsupport (fun x : M => (ρ α : M → ℝ) x * (ρ' β : M → ℝ) x) ⊆
      tsupport (ρ α : M → ℝ) ∩ tsupport (ρ' β : M → ℝ) := by
  refine _root_.Set.subset_inter ?_ ?_
  · refine closure_mono ?_
    intro x hx
    simp only [Function.mem_support] at hx
    simp only [Function.mem_support]
    intro h; exact hx (by rw [h]; ring)
  · refine closure_mono ?_
    intro x hx
    simp only [Function.mem_support] at hx
    simp only [Function.mem_support]
    intro h; exact hx (by rw [h]; ring)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.tsupport_pou_mul_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.tsupport_pou_mul_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.tsupport_pou_mul_subset ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.tsupport_pou_mul_subset

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem tsupport_subset_chartAt_source
    (ρ : SmoothPartitionOfUnity M I M Set.univ)
    (hρ : ρ.IsSubordinate (fun α : M => (chartAt H α).source))
    (α : M) :
    tsupport (ρ α : M → ℝ) ⊆ (chartAt H α).source := hρ α

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.tsupport_subset_chartAt_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.tsupport_subset_chartAt_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.tsupport_subset_chartAt_source ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.tsupport_subset_chartAt_source

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem support_subset_chartAt_source
    (ρ : SmoothPartitionOfUnity M I M Set.univ)
    (hρ : ρ.IsSubordinate (fun α : M => (chartAt H α).source))
    (α : M) :
    Function.support (ρ α : M → ℝ) ⊆ (chartAt H α).source :=
  (subset_tsupport _).trans (tsupport_subset_chartAt_source ρ hρ α)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.support_subset_chartAt_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.support_subset_chartAt_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.support_subset_chartAt_source ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.support_subset_chartAt_source

omit [IsManifold I ∞ M] in
theorem chartPushed_pointwise_bound
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M) (u : M → ℝ)
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    |chartPushed (I := I) (M := M) ρ α u y| ≤
      |u ((extChartAt I α).symm (toEuclidean.symm y))| := by
  unfold chartPushed
  rw [abs_mul]
  have hbound : |(ρ α : C^∞⟮I, M; ℝ⟯) ((extChartAt I α).symm (toEuclidean.symm y))| ≤ 1 := by
    rw [abs_of_nonneg (ρ.nonneg α _)]
    exact ρ.le_one α _
  have hu_nonneg : 0 ≤ |u ((extChartAt I α).symm (toEuclidean.symm y))| := abs_nonneg _
  calc
    |(ρ α : C^∞⟮I, M; ℝ⟯) ((extChartAt I α).symm (toEuclidean.symm y))| *
        |u ((extChartAt I α).symm (toEuclidean.symm y))|
      ≤ 1 * |u ((extChartAt I α).symm (toEuclidean.symm y))| :=
        mul_le_mul_of_nonneg_right hbound hu_nonneg
    _ = |u ((extChartAt I α).symm (toEuclidean.symm y))| := one_mul _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed_pointwise_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed_pointwise_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed_pointwise_bound ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed_pointwise_bound

def wkpNormChartFin
    [CompactSpace M]
    (k : ℕ) (p : ℝ≥0∞)
    (ρ : SmoothPartitionOfUnity M I M Set.univ)
    (u : M → ℝ) : ℝ≥0∞ :=
  ∑ α ∈ (support_set_finite_of_compactSpace (I := I) (M := M) ρ).toFinset,
    DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
      (d := Module.finrank ℝ E)
      k p
      (chartPushed (I := I) (M := M) ρ α u)
      (chartTargetEuclid (I := I) (M := M) α)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartFin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartFin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartFin ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartFin

omit [IsManifold I ∞ M] in
theorem wkpNormChartWithPartition_eq_wkpNormChartFin
    [CompactSpace M] [I.Boundaryless]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (ρ : SmoothPartitionOfUnity M I M Set.univ)
    (u : M → ℝ) :
    wkpNormChartWithPartition (I := I) (M := M) k p ρ u =
      wkpNormChartFin (I := I) (M := M) k p ρ u := by
  classical
  let f : M → ℝ≥0∞ := fun α =>
    DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
      (d := Module.finrank ℝ E) k p
      (chartPushed (I := I) (M := M) ρ α u)
      (chartTargetEuclid (I := I) (M := M) α)
  have hLHS : wkpNormChartWithPartition (I := I) (M := M) k p ρ u = ∑' α : M, f α := rfl
  have hRHS : wkpNormChartFin (I := I) (M := M) k p ρ u =
      ∑ α ∈ (support_set_finite_of_compactSpace (I := I) (M := M) ρ).toFinset,
        f α := rfl
  rw [hLHS, hRHS]
  have hf_zero_off : ∀ α : M, (Function.support (ρ α : M → ℝ)) = ∅ →
        f α = 0 := by
    intro α hα
    have hρ_empty : ∀ x : M, (ρ α : M → ℝ) x = 0 := by
      intro x
      have : x ∉ Function.support (ρ α : M → ℝ) := by
        rw [hα]
        exact Set.notMem_empty x
      simpa [Function.mem_support] using this
    have hChartPushed_zero : chartPushed (I := I) (M := M) ρ α u =
        (fun _ => (0 : ℝ)) := by
      funext y
      unfold chartPushed
      rw [hρ_empty]
      ring
    change DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
      (d := Module.finrank ℝ E) k p
      (chartPushed (I := I) (M := M) ρ α u)
      (chartTargetEuclid (I := I) (M := M) α) = 0
    rw [hChartPushed_zero]
    exact DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_zero_fun_zero
      (d := Module.finrank ℝ E) hp
      (chartTargetEuclid_isOpen (I := I) (M := M) α)
  rw [tsum_eq_sum]
  intro α hα
  have hαS : α ∉ {α : M | (Function.support (ρ α : M → ℝ)).Nonempty} := by
    intro hαS
    apply hα
    exact (Set.Finite.mem_toFinset _).mpr hαS
  have hempty : (Function.support (ρ α : M → ℝ)) = ∅ := by
    have h_not_nonempty : ¬ (Function.support (ρ α : M → ℝ)).Nonempty := by
      intro hne
      exact hαS hne
    exact Set.not_nonempty_iff_eq_empty.mp h_not_nonempty
  exact hf_zero_off α hempty

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartWithPartition_eq_wkpNormChartFin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartWithPartition_eq_wkpNormChartFin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartWithPartition_eq_wkpNormChartFin ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartWithPartition_eq_wkpNormChartFin

def chartTransitionFinset
    [CompactSpace M]
    (ρ : SmoothPartitionOfUnity M I M Set.univ) : Finset M :=
  (support_set_finite_of_compactSpace (I := I) (M := M) ρ).toFinset

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionFinset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionFinset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionFinset ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.chartTransitionFinset

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem mem_chartTransitionFinset_iff
    [CompactSpace M] (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M) :
    α ∈ chartTransitionFinset (I := I) (M := M) ρ ↔
      (Function.support (ρ α : M → ℝ)).Nonempty := by
  unfold chartTransitionFinset
  rw [Set.Finite.mem_toFinset]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.mem_chartTransitionFinset_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.mem_chartTransitionFinset_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.mem_chartTransitionFinset_iff ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.mem_chartTransitionFinset_iff

omit [FiniteDimensional ℝ E] in
theorem chartAt_transition_hasFDerivWithinAt_overlap
    (α β : M) :
    ∀ y ∈ (extChartAt I α) ''
      ((chartAt H α).source ∩ (chartAt H β).source),
        HasFDerivWithinAt (extChartAt I β ∘ (extChartAt I α).symm)
          (tangentCoordChange I α β ((extChartAt I α).symm y))
          ((extChartAt I α) ''
            ((chartAt H α).source ∩ (chartAt H β).source)) y :=
  DifferentialGeometry.Integral.Measure.extChartAt_transition_hasFDerivWithinAt_on_overlap_image
    (I := I) α β Set.inter_subset_left Set.inter_subset_right

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.chartAt_transition_hasFDerivWithinAt_overlap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.chartAt_transition_hasFDerivWithinAt_overlap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.chartAt_transition_hasFDerivWithinAt_overlap ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.chartAt_transition_hasFDerivWithinAt_overlap

end Chart
end Sobolev
end Analysis
end DifferentialGeometry
