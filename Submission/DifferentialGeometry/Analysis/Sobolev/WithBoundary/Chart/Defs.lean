import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.SupportAndDomain.IteratedSobolevHalfSpace
import Submission.DifferentialGeometry.Analysis.Sobolev.Chart.Defs
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties
import Submission.DifferentialGeometry.Analysis.Integration.L2.CompactSupport
import Submission.DifferentialGeometry.Geometry.Boundary.Model.EuclideanHalfSpace

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory _root_.Set _root_.Filter _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.Manifold
open scoped _root_.Manifold _root_.ContDiff _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace WithBoundary

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]

def chartPushed
    (ρ : SmoothPartitionOfUnity M (modelWithCornersEuclideanHalfSpace n) M Set.univ)
    (α : M) (u : M → ℝ) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  fun y =>
    (ρ α : C^∞⟮modelWithCornersEuclideanHalfSpace n, M; ℝ⟯)
        ((extChartAt (modelWithCornersEuclideanHalfSpace n) α).symm y) *
      u ((extChartAt (modelWithCornersEuclideanHalfSpace n) α).symm y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartPushed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartPushed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartPushed ``Submission.DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartPushed

def chartTargetEuclid (α : M) : Set (EuclideanSpace ℝ (Fin n)) :=
  (extChartAt (modelWithCornersEuclideanHalfSpace n) α).target

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartTargetEuclid then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartTargetEuclid"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartTargetEuclid ``Submission.DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartTargetEuclid

omit [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M] in
theorem chartTargetEuclid_isHalfSpaceRelOpen (α : M) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.IsHalfSpaceRelOpen (d := n)
      (chartTargetEuclid (n := n) (M := M) α) :=
  DifferentialGeometry.Analysis.Sobolev.Euclidean.extChartAt_target_isHalfSpaceRelOpen
    (n := n) (M := M) α

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartTargetEuclid_isHalfSpaceRelOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartTargetEuclid_isHalfSpaceRelOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartTargetEuclid_isHalfSpaceRelOpen ``Submission.DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartTargetEuclid_isHalfSpaceRelOpen

def MemWkpChart [T2Space M] [SigmaCompactSpace M]
    (k : ℕ) (p : ℝ≥0∞) (u : M → ℝ) : Prop :=
  ∀ α : M,
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace
      (d := n) k p
      (chartPushed (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU
          (modelWithCornersEuclideanHalfSpace n) M) α u)
      (chartTargetEuclid (n := n) (M := M) α)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.WithBoundary.MemWkpChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.WithBoundary.MemWkpChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.WithBoundary.MemWkpChart ``Submission.DifferentialGeometry.Analysis.Sobolev.WithBoundary.MemWkpChart

def wkpNormChart [T2Space M] [SigmaCompactSpace M]
    (k : ℕ) (p : ℝ≥0∞) (u : M → ℝ) : ℝ≥0∞ :=
  ∑' α : M,
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
      (d := n) k p
      (chartPushed (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU
          (modelWithCornersEuclideanHalfSpace n) M) α u)
      (chartTargetEuclid (n := n) (M := M) α)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpNormChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpNormChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpNormChart ``Submission.DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpNormChart

theorem wkpNormChart_eq_tsum
    [T2Space M] [SigmaCompactSpace M]
    (k : ℕ) (p : ℝ≥0∞) (u : M → ℝ) :
    wkpNormChart (n := n) (M := M) k p u =
      ∑' α : M,
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
          (d := n) k p
          (chartPushed (n := n) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU
              (modelWithCornersEuclideanHalfSpace n) M) α u)
          (chartTargetEuclid (n := n) (M := M) α) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpNormChart_eq_tsum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpNormChart_eq_tsum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpNormChart_eq_tsum ``Submission.DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpNormChart_eq_tsum

theorem MemWkpChart_iff
    [T2Space M] [SigmaCompactSpace M]
    (k : ℕ) (p : ℝ≥0∞) (u : M → ℝ) :
    MemWkpChart (n := n) (M := M) k p u ↔
      ∀ α : M,
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace
          (d := n) k p
          (chartPushed (n := n) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU
              (modelWithCornersEuclideanHalfSpace n) M) α u)
          (chartTargetEuclid (n := n) (M := M) α) := Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.WithBoundary.MemWkpChart_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.WithBoundary.MemWkpChart_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.WithBoundary.MemWkpChart_iff ``Submission.DifferentialGeometry.Analysis.Sobolev.WithBoundary.MemWkpChart_iff

omit [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M] in
theorem chartPushed_zero
    (ρ : SmoothPartitionOfUnity M (modelWithCornersEuclideanHalfSpace n) M Set.univ)
    (α : M) :
    chartPushed (n := n) (M := M) ρ α (fun _ => (0 : ℝ)) =
      (fun _ => (0 : ℝ)) := by
  funext y
  unfold chartPushed
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartPushed_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartPushed_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartPushed_zero ``Submission.DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartPushed_zero

theorem MemWkpChart_zero_fun
    [T2Space M] [SigmaCompactSpace M]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) :
    MemWkpChart (n := n) (M := M) k p (fun _ : M => (0 : ℝ)) := by
  intro α
  rw [chartPushed_zero]
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace_zero_fun
    (d := n) hp (chartTargetEuclid_isHalfSpaceRelOpen (n := n) (M := M) α)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.WithBoundary.MemWkpChart_zero_fun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.WithBoundary.MemWkpChart_zero_fun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.WithBoundary.MemWkpChart_zero_fun ``Submission.DifferentialGeometry.Analysis.Sobolev.WithBoundary.MemWkpChart_zero_fun

theorem wkpNormChart_zero_fun
    [T2Space M] [SigmaCompactSpace M]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) :
    wkpNormChart (n := n) (M := M) k p (fun _ : M => (0 : ℝ)) = 0 := by
  unfold wkpNormChart
  have hpt : ∀ α : M,
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
        (d := n) k p
        (chartPushed (n := n) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU
            (modelWithCornersEuclideanHalfSpace n) M) α
          (fun _ : M => (0 : ℝ)))
        (chartTargetEuclid (n := n) (M := M) α) = 0 := by
    intro α
    rw [chartPushed_zero]
    exact DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace_zero_fun_zero
      (d := n) hp
      (chartTargetEuclid_isHalfSpaceRelOpen (n := n) (M := M) α)
  rw [tsum_congr hpt]
  exact tsum_zero

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpNormChart_zero_fun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpNormChart_zero_fun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpNormChart_zero_fun ``Submission.DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpNormChart_zero_fun

omit [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M] in
theorem chartPushed_add
    (ρ : SmoothPartitionOfUnity M (modelWithCornersEuclideanHalfSpace n) M Set.univ)
    (α : M) (u v : M → ℝ) :
    chartPushed (n := n) (M := M) ρ α (fun x => u x + v x) =
      (fun y =>
        chartPushed (n := n) (M := M) ρ α u y +
          chartPushed (n := n) (M := M) ρ α v y) := by
  funext y
  unfold chartPushed
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartPushed_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartPushed_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartPushed_add ``Submission.DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartPushed_add

omit [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M] in
theorem chartPushed_const_smul
    (ρ : SmoothPartitionOfUnity M (modelWithCornersEuclideanHalfSpace n) M Set.univ)
    (α : M) (c : ℝ) (u : M → ℝ) :
    chartPushed (n := n) (M := M) ρ α (fun x => c * u x) =
      (fun y => c * chartPushed (n := n) (M := M) ρ α u y) := by
  funext y
  unfold chartPushed
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartPushed_const_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartPushed_const_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartPushed_const_smul ``Submission.DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartPushed_const_smul

theorem MemWkpChart_add
    [T2Space M] [SigmaCompactSpace M]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u v : M → ℝ}
    (hu : MemWkpChart (n := n) (M := M) k p u)
    (hv : MemWkpChart (n := n) (M := M) k p v) :
    MemWkpChart (n := n) (M := M) k p (fun x => u x + v x) := by
  intro α
  rw [chartPushed_add]
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace.add
    (d := n) hp
    (chartTargetEuclid_isHalfSpaceRelOpen (n := n) (M := M) α)
    (hu α) (hv α)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.WithBoundary.MemWkpChart_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.WithBoundary.MemWkpChart_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.WithBoundary.MemWkpChart_add ``Submission.DifferentialGeometry.Analysis.Sobolev.WithBoundary.MemWkpChart_add

theorem MemWkpChart_const_smul
    [T2Space M] [SigmaCompactSpace M]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (c : ℝ) {u : M → ℝ}
    (hu : MemWkpChart (n := n) (M := M) k p u) :
    MemWkpChart (n := n) (M := M) k p (fun x => c * u x) := by
  intro α
  rw [chartPushed_const_smul]
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace.const_smul
    (d := n) hp
    (chartTargetEuclid_isHalfSpaceRelOpen (n := n) (M := M) α)
    (hu α) c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.WithBoundary.MemWkpChart_const_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.WithBoundary.MemWkpChart_const_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.WithBoundary.MemWkpChart_const_smul ``Submission.DifferentialGeometry.Analysis.Sobolev.WithBoundary.MemWkpChart_const_smul

theorem MemWkpChart_neg
    [T2Space M] [SigmaCompactSpace M]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u : M → ℝ}
    (hu : MemWkpChart (n := n) (M := M) k p u) :
    MemWkpChart (n := n) (M := M) k p (fun x => -u x) := by
  have h := MemWkpChart_const_smul (n := n) (M := M) hp (-1) hu
  have hEq : (fun x : M => (-1 : ℝ) * u x) = (fun x : M => -u x) := by
    funext x; ring
  rw [hEq] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.WithBoundary.MemWkpChart_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.WithBoundary.MemWkpChart_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.WithBoundary.MemWkpChart_neg ``Submission.DifferentialGeometry.Analysis.Sobolev.WithBoundary.MemWkpChart_neg

theorem MemWkpChart_sub
    [T2Space M] [SigmaCompactSpace M]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u v : M → ℝ}
    (hu : MemWkpChart (n := n) (M := M) k p u)
    (hv : MemWkpChart (n := n) (M := M) k p v) :
    MemWkpChart (n := n) (M := M) k p (fun x => u x - v x) := by
  have hneg := MemWkpChart_neg (n := n) (M := M) hp hv
  have h := MemWkpChart_add (n := n) (M := M) hp hu hneg
  have hEq : (fun x : M => u x + -v x) = (fun x : M => u x - v x) := by
    funext x; ring
  rw [hEq] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.WithBoundary.MemWkpChart_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.WithBoundary.MemWkpChart_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.WithBoundary.MemWkpChart_sub ``Submission.DifferentialGeometry.Analysis.Sobolev.WithBoundary.MemWkpChart_sub

def wkpChartAddSubgroup
    [T2Space M] [SigmaCompactSpace M]
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) : AddSubgroup (M → ℝ) where
  carrier := { u | MemWkpChart (n := n) (M := M) k p u }
  zero_mem' := MemWkpChart_zero_fun (n := n) (M := M) hp
  add_mem' := fun hu hv => MemWkpChart_add (n := n) (M := M) hp hu hv
  neg_mem' := fun hu => MemWkpChart_neg (n := n) (M := M) hp hu

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpChartAddSubgroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpChartAddSubgroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpChartAddSubgroup ``Submission.DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpChartAddSubgroup

def wkpChartSubmodule
    [T2Space M] [SigmaCompactSpace M]
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) : Submodule ℝ (M → ℝ) where
  carrier := { u | MemWkpChart (n := n) (M := M) k p u }
  zero_mem' := MemWkpChart_zero_fun (n := n) (M := M) hp
  add_mem' := fun hu hv => MemWkpChart_add (n := n) (M := M) hp hu hv
  smul_mem' := fun c u hu => by
    have h := MemWkpChart_const_smul (n := n) (M := M) hp c hu
    have hEq : (c • u : M → ℝ) = fun x => c * u x := by
      funext x
      simp [Pi.smul_apply, smul_eq_mul]
    rw [hEq]
    exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpChartSubmodule then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpChartSubmodule"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpChartSubmodule ``Submission.DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpChartSubmodule

def WkpChart
    [T2Space M] [SigmaCompactSpace M]
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) : Type _ :=
  ↥(wkpChartSubmodule (n := n) (M := M) k p hp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.WithBoundary.WkpChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.WithBoundary.WkpChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.WithBoundary.WkpChart ``Submission.DifferentialGeometry.Analysis.Sobolev.WithBoundary.WkpChart

instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.WithBoundary.instAddCommGroupWkpChart
    [T2Space M] [SigmaCompactSpace M]
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    AddCommGroup (WkpChart (n := n) (M := M) k p hp) :=
  inferInstanceAs (AddCommGroup ↥(wkpChartSubmodule (n := n) (M := M) k p hp))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.WithBoundary.instAddCommGroupWkpChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.WithBoundary.instAddCommGroupWkpChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.WithBoundary.instAddCommGroupWkpChart ``Submission.DifferentialGeometry.Analysis.Sobolev.WithBoundary.instAddCommGroupWkpChart

instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.WithBoundary.instModuleRealWkpChart
    [T2Space M] [SigmaCompactSpace M]
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    Module ℝ (WkpChart (n := n) (M := M) k p hp) :=
  inferInstanceAs (Module ℝ ↥(wkpChartSubmodule (n := n) (M := M) k p hp))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.WithBoundary.instModuleRealWkpChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.WithBoundary.instModuleRealWkpChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.WithBoundary.instModuleRealWkpChart ``Submission.DifferentialGeometry.Analysis.Sobolev.WithBoundary.instModuleRealWkpChart

theorem MemWkpChart.le_succ
    [T2Space M] [SigmaCompactSpace M]
    {k : ℕ} {p : ℝ≥0∞} {u : M → ℝ}
    (h : MemWkpChart (n := n) (M := M) (k + 1) p u) :
    MemWkpChart (n := n) (M := M) k p u := by
  intro α
  exact (h α).le_succ

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Analysis.Sobolev.WithBoundary.MemWkpChart
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.WithBoundary.MemWkpChart.le_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.WithBoundary.MemWkpChart.le_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.WithBoundary.MemWkpChart.le_succ ``Submission.DifferentialGeometry.Analysis.Sobolev.WithBoundary.MemWkpChart.le_succ

theorem MemWkpChart.le_of_le
    [T2Space M] [SigmaCompactSpace M]
    {k k' : ℕ} {p : ℝ≥0∞} {u : M → ℝ}
    (hk : k ≤ k') (h : MemWkpChart (n := n) (M := M) k' p u) :
    MemWkpChart (n := n) (M := M) k p u := by
  intro α
  exact (h α).le_of_le hk

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.WithBoundary.MemWkpChart.le_of_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.WithBoundary.MemWkpChart.le_of_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.WithBoundary.MemWkpChart.le_of_le ``Submission.DifferentialGeometry.Analysis.Sobolev.WithBoundary.MemWkpChart.le_of_le

def ChartPushedAEEq
    [T2Space M] [SigmaCompactSpace M]
    (u v : M → ℝ) : Prop :=
  ∀ α : M,
    chartPushed (n := n) (M := M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU
        (modelWithCornersEuclideanHalfSpace n) M) α u
        =ᵐ[MeasureTheory.volume.restrict
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
              (chartTargetEuclid (n := n) (M := M) α))]
      chartPushed (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU
          (modelWithCornersEuclideanHalfSpace n) M) α v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.WithBoundary.ChartPushedAEEq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.WithBoundary.ChartPushedAEEq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.WithBoundary.ChartPushedAEEq ``Submission.DifferentialGeometry.Analysis.Sobolev.WithBoundary.ChartPushedAEEq

theorem ChartPushedAEEq.rfl
    [T2Space M] [SigmaCompactSpace M]
    (u : M → ℝ) :
    ChartPushedAEEq (n := n) (M := M) u u := by
  intro α
  exact Filter.EventuallyEq.rfl

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Analysis.Sobolev.WithBoundary.ChartPushedAEEq
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.WithBoundary.ChartPushedAEEq.rfl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.WithBoundary.ChartPushedAEEq.rfl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.WithBoundary.ChartPushedAEEq.rfl ``Submission.DifferentialGeometry.Analysis.Sobolev.WithBoundary.ChartPushedAEEq.rfl

theorem ChartPushedAEEq.symm
    [T2Space M] [SigmaCompactSpace M]
    {u v : M → ℝ} (h : ChartPushedAEEq (n := n) (M := M) u v) :
    ChartPushedAEEq (n := n) (M := M) v u := by
  intro α
  exact (h α).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.WithBoundary.ChartPushedAEEq.symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.WithBoundary.ChartPushedAEEq.symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.WithBoundary.ChartPushedAEEq.symm ``Submission.DifferentialGeometry.Analysis.Sobolev.WithBoundary.ChartPushedAEEq.symm

theorem ChartPushedAEEq.trans
    [T2Space M] [SigmaCompactSpace M]
    {u v w : M → ℝ}
    (huv : ChartPushedAEEq (n := n) (M := M) u v)
    (hvw : ChartPushedAEEq (n := n) (M := M) v w) :
    ChartPushedAEEq (n := n) (M := M) u w := by
  intro α
  exact (huv α).trans (hvw α)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.WithBoundary.ChartPushedAEEq.trans then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.WithBoundary.ChartPushedAEEq.trans"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.WithBoundary.ChartPushedAEEq.trans ``Submission.DifferentialGeometry.Analysis.Sobolev.WithBoundary.ChartPushedAEEq.trans

theorem MemWkpChart_congr_chartPushed_ae
    [T2Space M] [SigmaCompactSpace M]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u v : M → ℝ} (huv : ChartPushedAEEq (n := n) (M := M) u v) :
    MemWkpChart (n := n) (M := M) k p u ↔
      MemWkpChart (n := n) (M := M) k p v := by
  refine ⟨fun h α => ?_, fun h α => ?_⟩
  · exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace_congr_ae
      (d := n) hp
      (chartTargetEuclid_isHalfSpaceRelOpen (n := n) (M := M) α)
      (huv α)).mp (h α)
  · exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace_congr_ae
      (d := n) hp
      (chartTargetEuclid_isHalfSpaceRelOpen (n := n) (M := M) α)
      (huv α).symm).mp (h α)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.WithBoundary.MemWkpChart_congr_chartPushed_ae then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.WithBoundary.MemWkpChart_congr_chartPushed_ae"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.WithBoundary.MemWkpChart_congr_chartPushed_ae ``Submission.DifferentialGeometry.Analysis.Sobolev.WithBoundary.MemWkpChart_congr_chartPushed_ae

theorem wkpNormChart_congr_chartPushed_ae
    [T2Space M] [SigmaCompactSpace M]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u v : M → ℝ} (huv : ChartPushedAEEq (n := n) (M := M) u v) :
    wkpNormChart (n := n) (M := M) k p u =
      wkpNormChart (n := n) (M := M) k p v := by
  unfold wkpNormChart
  refine tsum_congr ?_
  intro α
  unfold DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_congr_ae
    (d := n) hp
    (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace_isOpen
      (chartTargetEuclid_isHalfSpaceRelOpen (n := n) (M := M) α))
    (huv α)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpNormChart_congr_chartPushed_ae then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpNormChart_congr_chartPushed_ae"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpNormChart_congr_chartPushed_ae ``Submission.DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpNormChart_congr_chartPushed_ae

theorem wkpNormChart_add_le
    [T2Space M] [SigmaCompactSpace M]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u v : M → ℝ}
    (hu : MemWkpChart (n := n) (M := M) k p u)
    (hv : MemWkpChart (n := n) (M := M) k p v) :
    wkpNormChart (n := n) (M := M) k p (fun x => u x + v x) ≤
      wkpNormChart (n := n) (M := M) k p u +
        wkpNormChart (n := n) (M := M) k p v := by
  unfold wkpNormChart
  rw [← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum ?_
  intro α
  rw [chartPushed_add]
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace_add_le
    (d := n) hp
    (chartTargetEuclid_isHalfSpaceRelOpen (n := n) (M := M) α)
    (hu α) (hv α)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpNormChart_add_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpNormChart_add_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpNormChart_add_le ``Submission.DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpNormChart_add_le

theorem wkpNormChart_const_smul
    [T2Space M] [SigmaCompactSpace M]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (c : ℝ) {u : M → ℝ}
    (hu : MemWkpChart (n := n) (M := M) k p u) :
    wkpNormChart (n := n) (M := M) k p (fun x => c * u x) =
      ‖c‖ₑ * wkpNormChart (n := n) (M := M) k p u := by
  unfold wkpNormChart
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr ?_
  intro α
  rw [chartPushed_const_smul]
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace_const_smul
    (d := n) hp
    (chartTargetEuclid_isHalfSpaceRelOpen (n := n) (M := M) α)
    (hu α) c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpNormChart_const_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpNormChart_const_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpNormChart_const_smul ``Submission.DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpNormChart_const_smul

theorem wkpNormChart_lt_top_of_memWkpChart
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u : M → ℝ} (hu : MemWkpChart (n := n) (M := M) k p u) :
    wkpNormChart (n := n) (M := M) k p u < ⊤ := by
  classical
  unfold wkpNormChart
  set f : M → ℝ≥0∞ := fun α =>
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
      (d := n) k p
      (chartPushed (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU
          (modelWithCornersEuclideanHalfSpace n) M) α u)
      (chartTargetEuclid (n := n) (M := M) α) with hf_def
  have hPOU_localFin : LocallyFinite
      (fun α : M => Function.support
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU
          (modelWithCornersEuclideanHalfSpace n) M α : M → ℝ)) :=
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU
      (modelWithCornersEuclideanHalfSpace n) M).locallyFinite
  have hSupport_finite : {α : M | (Function.support
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU
        (modelWithCornersEuclideanHalfSpace n) M α : M → ℝ)).Nonempty}.Finite :=
    hPOU_localFin.finite_nonempty_of_compact
  have hf_zero_off : ∀ α : M, (Function.support
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU
        (modelWithCornersEuclideanHalfSpace n) M α : M → ℝ)) = ∅ →
        f α = 0 := by
    intro α hα
    have hρ_empty : ∀ x : M, (DifferentialGeometry.Integral.Measure.chartAtlasPOU
        (modelWithCornersEuclideanHalfSpace n) M α : M → ℝ) x = 0 := by
      intro x
      have : x ∉ Function.support
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU
            (modelWithCornersEuclideanHalfSpace n) M α : M → ℝ) := by
        rw [hα]
        exact Set.notMem_empty x
      simpa [Function.mem_support] using this
    have hChartPushed_zero : chartPushed (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU
          (modelWithCornersEuclideanHalfSpace n) M) α u =
        (fun _ => (0 : ℝ)) := by
      funext y
      unfold chartPushed
      rw [hρ_empty]
      ring
    change DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
      (d := n) k p
      (chartPushed (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU
          (modelWithCornersEuclideanHalfSpace n) M) α u)
      (chartTargetEuclid (n := n) (M := M) α) = 0
    rw [hChartPushed_zero]
    exact DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace_zero_fun_zero
      (d := n) hp
      (chartTargetEuclid_isHalfSpaceRelOpen (n := n) (M := M) α)
  set S : Set M := {α : M | (Function.support
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU
        (modelWithCornersEuclideanHalfSpace n) M α : M → ℝ)).Nonempty}
      with hS_def
  have hS_finite : S.Finite := hSupport_finite
  have hf_support_S : Function.support f ⊆ S := by
    intro α hα
    by_contra hαS
    apply hα
    have h_not_in_S : (Function.support
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU
          (modelWithCornersEuclideanHalfSpace n) M α : M → ℝ)) = ∅ := by
      have h_not_nonempty : ¬ (Function.support
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU
            (modelWithCornersEuclideanHalfSpace n) M α : M → ℝ)).Nonempty := by
        intro hne
        exact hαS hne
      exact Set.not_nonempty_iff_eq_empty.mp h_not_nonempty
    exact hf_zero_off α h_not_in_S
  have htsum_eq : ∑' α : M, f α = ∑ α ∈ hS_finite.toFinset, f α := by
    rw [tsum_eq_sum]
    intro α hα
    have hαS : α ∉ S := by
      intro hαS
      apply hα
      exact (Set.Finite.mem_toFinset _).mpr hαS
    have hempty : (Function.support
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU
          (modelWithCornersEuclideanHalfSpace n) M α : M → ℝ)) = ∅ := by
      have h_not_nonempty : ¬ (Function.support
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU
            (modelWithCornersEuclideanHalfSpace n) M α : M → ℝ)).Nonempty := by
        intro hne
        exact hαS hne
      exact Set.not_nonempty_iff_eq_empty.mp h_not_nonempty
    exact hf_zero_off α hempty
  rw [htsum_eq]
  apply ENNReal.sum_lt_top.mpr
  intro α _
  rw [hf_def]
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace_lt_top_of_memWkpHalfSpace
    (hu α)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpNormChart_lt_top_of_memWkpChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpNormChart_lt_top_of_memWkpChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpNormChart_lt_top_of_memWkpChart ``Submission.DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpNormChart_lt_top_of_memWkpChart

end WithBoundary
end Sobolev
end Analysis
end DifferentialGeometry
