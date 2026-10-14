import Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.Chart.Components

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Tensor

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

def MemWtwokTwo
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) : Prop :=
  ∀ (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)),
    MemWkp (d := Module.finrank ℝ E) (2 * k) 2
      (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.MemWtwokTwo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.MemWtwokTwo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.MemWtwokTwo ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.MemWtwokTwo

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem MemWtwokTwo_def
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) :
    MemWtwokTwo (I := I) (M := M) g k T ↔
      ∀ (α : M)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        MemWkp (d := Module.finrank ℝ E) (2 * k) 2
          (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
          (chartTargetEuclid (I := I) (M := M) α) := Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.MemWtwokTwo_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.MemWtwokTwo_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.MemWtwokTwo_def ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.MemWtwokTwo_def

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem MemWtwokTwo_iff
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) :
    MemWtwokTwo (I := I) (M := M) g k T ↔
      ∀ (α : M)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        MemWkp (d := Module.finrank ℝ E) (2 * k) 2
          (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
          (chartTargetEuclid (I := I) (M := M) α) := Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.MemWtwokTwo_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.MemWtwokTwo_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.MemWtwokTwo_iff ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.MemWtwokTwo_iff

omit [NeZero (Module.finrank ℝ E)] in
theorem MemWtwokTwo_zero
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (T : SmoothCcTensor g r s) :
    MemWtwokTwo (I := I) (M := M) g 0 T := by
  intro α Idx Jdx
  have hmul : (2 * 0 : ℕ) = 0 := by norm_num
  rw [hmul, MemWkp_zero]
  have hcont : Continuous
      (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx) :=
    tensorChartComp_continuous (I := I) (M := M) g r s T α Idx Jdx
  have hcs : HasCompactSupport
      (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx) :=
    tensorChartComp_hasCompactSupport (I := I) (M := M) g r s T α Idx Jdx
  exact (hcont.memLp_of_hasCompactSupport (μ := volume.restrict
    (chartTargetEuclid (I := I) (M := M) α)) hcs)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.MemWtwokTwo_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.MemWtwokTwo_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.MemWtwokTwo_zero ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.MemWtwokTwo_zero

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem MemWtwokTwo_zero_section
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (k : ℕ) :
    MemWtwokTwo (I := I) (M := M) g k (0 : SmoothCcTensor g r s) := by
  intro α Idx Jdx
  rw [tensorChartComp_zero (I := I) (M := M) g r s α Idx Jdx]
  exact MemWkp_zero_fun (d := Module.finrank ℝ E) (by norm_num)
    (chartTargetEuclid_isOpen (I := I) (M := M) α)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.MemWtwokTwo_zero_section then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.MemWtwokTwo_zero_section"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.MemWtwokTwo_zero_section ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.MemWtwokTwo_zero_section

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem MemWtwokTwo_add
    (g : SmoothRiemannianMetric I M) {r s : ℕ} {k : ℕ}
    {T₁ T₂ : SmoothCcTensor g r s}
    (h₁ : MemWtwokTwo (I := I) (M := M) g k T₁)
    (h₂ : MemWtwokTwo (I := I) (M := M) g k T₂) :
    MemWtwokTwo (I := I) (M := M) g k (T₁ + T₂) := by
  intro α Idx Jdx
  rw [tensorChartComp_add (I := I) (M := M) g r s T₁ T₂ α Idx Jdx]
  have hfun :
      (tensorChartComp (I := I) (M := M) g r s T₁ α Idx Jdx +
        tensorChartComp (I := I) (M := M) g r s T₂ α Idx Jdx) =
      (fun y => tensorChartComp (I := I) (M := M) g r s T₁ α Idx Jdx y +
        tensorChartComp (I := I) (M := M) g r s T₂ α Idx Jdx y) := rfl
  rw [hfun]
  exact MemWkp.add (d := Module.finrank ℝ E) (by norm_num)
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    (h₁ α Idx Jdx) (h₂ α Idx Jdx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.MemWtwokTwo_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.MemWtwokTwo_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.MemWtwokTwo_add ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.MemWtwokTwo_add

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem MemWtwokTwo_smul
    (g : SmoothRiemannianMetric I M) {r s : ℕ} {k : ℕ}
    (c : ℝ) {T : SmoothCcTensor g r s}
    (h : MemWtwokTwo (I := I) (M := M) g k T) :
    MemWtwokTwo (I := I) (M := M) g k (c • T) := by
  intro α Idx Jdx
  rw [tensorChartComp_smul (I := I) (M := M) g r s c T α Idx Jdx]
  have hfun :
      (c • tensorChartComp (I := I) (M := M) g r s T α Idx Jdx) =
      (fun y => c * tensorChartComp (I := I) (M := M) g r s T α Idx Jdx y) := by
    funext y
    simp [Pi.smul_apply, smul_eq_mul]
  rw [hfun]
  exact MemWkp.const_smul (d := Module.finrank ℝ E) (by norm_num)
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    (h α Idx Jdx) c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.MemWtwokTwo_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.MemWtwokTwo_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.MemWtwokTwo_smul ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.MemWtwokTwo_smul

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem MemWtwokTwo_neg
    (g : SmoothRiemannianMetric I M) {r s : ℕ} {k : ℕ}
    {T : SmoothCcTensor g r s}
    (h : MemWtwokTwo (I := I) (M := M) g k T) :
    MemWtwokTwo (I := I) (M := M) g k (-T) := by
  have hsmul := MemWtwokTwo_smul (I := I) (M := M) g (-1 : ℝ) h
  rwa [neg_one_smul] at hsmul

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.MemWtwokTwo_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.MemWtwokTwo_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.MemWtwokTwo_neg ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.MemWtwokTwo_neg

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem MemWtwokTwo_sub
    (g : SmoothRiemannianMetric I M) {r s : ℕ} {k : ℕ}
    {T₁ T₂ : SmoothCcTensor g r s}
    (h₁ : MemWtwokTwo (I := I) (M := M) g k T₁)
    (h₂ : MemWtwokTwo (I := I) (M := M) g k T₂) :
    MemWtwokTwo (I := I) (M := M) g k (T₁ - T₂) := by
  rw [sub_eq_add_neg]
  exact MemWtwokTwo_add (I := I) (M := M) g h₁ (MemWtwokTwo_neg (I := I) (M := M) g h₂)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.MemWtwokTwo_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.MemWtwokTwo_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.MemWtwokTwo_sub ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.MemWtwokTwo_sub

def wtwokTwoSubmodule
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (k : ℕ) :
    Submodule ℝ (SmoothCcTensor g r s) where
  carrier := { T | MemWtwokTwo (I := I) (M := M) g k T }
  zero_mem' := MemWtwokTwo_zero_section (I := I) (M := M) g k
  add_mem' := fun h₁ h₂ => MemWtwokTwo_add (I := I) (M := M) g h₁ h₂
  smul_mem' := fun c _ h => MemWtwokTwo_smul (I := I) (M := M) g c h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoSubmodule then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoSubmodule"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoSubmodule ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoSubmodule

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
@[simp] lemma mem_wtwokTwoSubmodule
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (k : ℕ)
    (T : SmoothCcTensor g r s) :
    T ∈ wtwokTwoSubmodule (I := I) (M := M) g r s k ↔
      MemWtwokTwo (I := I) (M := M) g k T := Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.mem_wtwokTwoSubmodule then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.mem_wtwokTwoSubmodule"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.mem_wtwokTwoSubmodule ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.mem_wtwokTwoSubmodule

def WtwokTwo
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (k : ℕ) : Type _ :=
  ↥(wtwokTwoSubmodule (I := I) (M := M) g r s k)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.WtwokTwo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.WtwokTwo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.WtwokTwo ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.WtwokTwo

instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.instAddCommGroupWtwokTwo
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (k : ℕ) :
    AddCommGroup (WtwokTwo (I := I) (M := M) g r s k) :=
  inferInstanceAs (AddCommGroup ↥(wtwokTwoSubmodule (I := I) (M := M) g r s k))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.instAddCommGroupWtwokTwo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.instAddCommGroupWtwokTwo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.instAddCommGroupWtwokTwo ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.instAddCommGroupWtwokTwo

instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.instModuleRealWtwokTwo
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (k : ℕ) :
    Module ℝ (WtwokTwo (I := I) (M := M) g r s k) :=
  inferInstanceAs (Module ℝ ↥(wtwokTwoSubmodule (I := I) (M := M) g r s k))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.instModuleRealWtwokTwo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.instModuleRealWtwokTwo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.instModuleRealWtwokTwo ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.instModuleRealWtwokTwo

def wtwokTwoNorm
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) : ℝ≥0∞ :=
  ∑' α : M,
    ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
      ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 * k) 2
          (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
          (chartTargetEuclid (I := I) (M := M) α)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoNorm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoNorm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoNorm ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoNorm

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem wtwokTwoNorm_eq_tsum
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) :
    wtwokTwoNorm (I := I) (M := M) g k T =
      ∑' α : M,
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 * k) 2
              (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
              (chartTargetEuclid (I := I) (M := M) α) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoNorm_eq_tsum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoNorm_eq_tsum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoNorm_eq_tsum ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoNorm_eq_tsum

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem wtwokTwoNorm_nonneg
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) :
    0 ≤ wtwokTwoNorm (I := I) (M := M) g k T :=
  zero_le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoNorm_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoNorm_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoNorm_nonneg ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoNorm_nonneg

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem wtwokTwoNorm_zero_section
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (k : ℕ) :
    wtwokTwoNorm (I := I) (M := M) g k (0 : SmoothCcTensor g r s) = 0 := by
  unfold wtwokTwoNorm
  have hpt : ∀ α : M,
      (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 * k) 2
            (tensorChartComp (I := I) (M := M) g r s
              (0 : SmoothCcTensor g r s) α Idx Jdx)
            (chartTargetEuclid (I := I) (M := M) α)) = 0 := by
    intro α
    refine Finset.sum_eq_zero ?_
    intro Idx _
    refine Finset.sum_eq_zero ?_
    intro Jdx _
    rw [tensorChartComp_zero (I := I) (M := M) g r s α Idx Jdx]
    exact wkpNorm_zero_fun_zero (d := Module.finrank ℝ E) (by norm_num)
      (chartTargetEuclid_isOpen (I := I) (M := M) α)
  rw [tsum_congr hpt]
  exact tsum_zero

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoNorm_zero_section then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoNorm_zero_section"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoNorm_zero_section ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoNorm_zero_section

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem wtwokTwoNorm_add_le
    (g : SmoothRiemannianMetric I M) {r s : ℕ} {k : ℕ}
    {T₁ T₂ : SmoothCcTensor g r s}
    (h₁ : MemWtwokTwo (I := I) (M := M) g k T₁)
    (h₂ : MemWtwokTwo (I := I) (M := M) g k T₂) :
    wtwokTwoNorm (I := I) (M := M) g k (T₁ + T₂) ≤
      wtwokTwoNorm (I := I) (M := M) g k T₁ +
        wtwokTwoNorm (I := I) (M := M) g k T₂ := by
  unfold wtwokTwoNorm
  rw [← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum ?_
  intro α
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum ?_
  intro Idx _
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum ?_
  intro Jdx _
  rw [tensorChartComp_add (I := I) (M := M) g r s T₁ T₂ α Idx Jdx]
  have hfun :
      (tensorChartComp (I := I) (M := M) g r s T₁ α Idx Jdx +
        tensorChartComp (I := I) (M := M) g r s T₂ α Idx Jdx) =
      (fun y => tensorChartComp (I := I) (M := M) g r s T₁ α Idx Jdx y +
        tensorChartComp (I := I) (M := M) g r s T₂ α Idx Jdx y) := rfl
  rw [hfun]
  exact wkpNorm_add_le (d := Module.finrank ℝ E) (by norm_num)
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    (h₁ α Idx Jdx) (h₂ α Idx Jdx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoNorm_add_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoNorm_add_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoNorm_add_le ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoNorm_add_le

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem wtwokTwoNorm_smul
    (g : SmoothRiemannianMetric I M) {r s : ℕ} {k : ℕ}
    (c : ℝ) {T : SmoothCcTensor g r s}
    (h : MemWtwokTwo (I := I) (M := M) g k T) :
    wtwokTwoNorm (I := I) (M := M) g k (c • T) =
      ‖c‖ₑ * wtwokTwoNorm (I := I) (M := M) g k T := by
  unfold wtwokTwoNorm
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr ?_
  intro α
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro Idx _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro Jdx _
  rw [tensorChartComp_smul (I := I) (M := M) g r s c T α Idx Jdx]
  have hfun :
      (c • tensorChartComp (I := I) (M := M) g r s T α Idx Jdx) =
      (fun y => c * tensorChartComp (I := I) (M := M) g r s T α Idx Jdx y) := by
    funext y
    simp [Pi.smul_apply, smul_eq_mul]
  rw [hfun]
  exact wkpNorm_const_smul (d := Module.finrank ℝ E) (by norm_num)
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    (h α Idx Jdx) c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoNorm_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoNorm_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoNorm_smul ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoNorm_smul

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem MemWtwokTwo.le_succ
    {g : SmoothRiemannianMetric I M} {r s : ℕ} {k : ℕ}
    {T : SmoothCcTensor g r s}
    (h : MemWtwokTwo (I := I) (M := M) g (k + 1) T) :
    MemWtwokTwo (I := I) (M := M) g k T := by
  intro α Idx Jdx
  have hle : 2 * k ≤ 2 * (k + 1) := by omega
  exact MemWkp.le_of_le (d := Module.finrank ℝ E) hle (h α Idx Jdx)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.MemWtwokTwo
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.MemWtwokTwo.le_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.MemWtwokTwo.le_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.MemWtwokTwo.le_succ ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.MemWtwokTwo.le_succ

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem MemWtwokTwo.le_of_le
    {g : SmoothRiemannianMetric I M} {r s : ℕ} {k k' : ℕ}
    {T : SmoothCcTensor g r s}
    (hk : k ≤ k') (h : MemWtwokTwo (I := I) (M := M) g k' T) :
    MemWtwokTwo (I := I) (M := M) g k T := by
  intro α Idx Jdx
  have hle : 2 * k ≤ 2 * k' := by omega
  exact MemWkp.le_of_le (d := Module.finrank ℝ E) hle (h α Idx Jdx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.MemWtwokTwo.le_of_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.MemWtwokTwo.le_of_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.MemWtwokTwo.le_of_le ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.MemWtwokTwo.le_of_le

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem wtwokTwoSubmodule_le_succ
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (k : ℕ) :
    wtwokTwoSubmodule (I := I) (M := M) g r s (k + 1) ≤
      wtwokTwoSubmodule (I := I) (M := M) g r s k := by
  intro T hT
  exact MemWtwokTwo.le_succ (I := I) (M := M) hT

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoSubmodule_le_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoSubmodule_le_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoSubmodule_le_succ ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoSubmodule_le_succ

end Tensor
end Sobolev
end Analysis
end DifferentialGeometry
