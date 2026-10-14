import Submission.DifferentialGeometry.Analysis.Sobolev.Chart.Defs
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Group.NullSubmodule
import Mathlib.Analysis.Normed.Group.Uniform

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
namespace Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def wkpNormChartReal
    [T2Space M] [SigmaCompactSpace M] (k : ℕ) (p : ℝ≥0∞) (u : M → ℝ) : ℝ :=
  (wkpNormChart (I := I) (M := M) k p u).toReal

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartReal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartReal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartReal ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartReal

@[simp]
lemma wkpNormChartReal_def
    [T2Space M] [SigmaCompactSpace M] (k : ℕ) (p : ℝ≥0∞) (u : M → ℝ) :
    wkpNormChartReal (I := I) (M := M) k p u =
      (wkpNormChart (I := I) (M := M) k p u).toReal := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartReal_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartReal_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartReal_def ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartReal_def

lemma wkpNormChartReal_nonneg
    [T2Space M] [SigmaCompactSpace M] (k : ℕ) (p : ℝ≥0∞) (u : M → ℝ) :
    0 ≤ wkpNormChartReal (I := I) (M := M) k p u :=
  ENNReal.toReal_nonneg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartReal_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartReal_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartReal_nonneg ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartReal_nonneg

lemma wkpNormChartReal_zero
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) :
    wkpNormChartReal (I := I) (M := M) k p (fun _ : M => (0 : ℝ)) = 0 := by
  unfold wkpNormChartReal
  rw [wkpNormChart_zero_fun (I := I) (M := M) hp]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartReal_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartReal_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartReal_zero ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartReal_zero

lemma wkpNormChartReal_add_le
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u v : M → ℝ}
    (hu : MemWkpChart (I := I) (M := M) k p u)
    (hv : MemWkpChart (I := I) (M := M) k p v) :
    wkpNormChartReal (I := I) (M := M) k p (fun x => u x + v x) ≤
      wkpNormChartReal (I := I) (M := M) k p u +
        wkpNormChartReal (I := I) (M := M) k p v := by
  unfold wkpNormChartReal
  have hu_lt : wkpNormChart (I := I) (M := M) k p u < ⊤ :=
    wkpNormChart_lt_top_of_memWkpChart (I := I) (M := M) hp hu
  have hv_lt : wkpNormChart (I := I) (M := M) k p v < ⊤ :=
    wkpNormChart_lt_top_of_memWkpChart (I := I) (M := M) hp hv
  have hu_ne : wkpNormChart (I := I) (M := M) k p u ≠ ⊤ := hu_lt.ne
  have hv_ne : wkpNormChart (I := I) (M := M) k p v ≠ ⊤ := hv_lt.ne
  have hSum_le := wkpNormChart_add_le (I := I) (M := M) hp hu hv
  have hRHS_ne : wkpNormChart (I := I) (M := M) k p u +
      wkpNormChart (I := I) (M := M) k p v ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hu_ne, hv_ne⟩
  have hToReal := ENNReal.toReal_mono hRHS_ne hSum_le
  rw [ENNReal.toReal_add hu_ne hv_ne] at hToReal
  exact hToReal

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartReal_add_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartReal_add_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartReal_add_le ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartReal_add_le

lemma wkpNormChartReal_const_smul
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (c : ℝ) {u : M → ℝ} (hu : MemWkpChart (I := I) (M := M) k p u) :
    wkpNormChartReal (I := I) (M := M) k p (fun x => c * u x) =
      ‖c‖ * wkpNormChartReal (I := I) (M := M) k p u := by
  unfold wkpNormChartReal
  rw [wkpNormChart_const_smul (I := I) (M := M) hp c hu]
  rw [ENNReal.toReal_mul, toReal_enorm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartReal_const_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartReal_const_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartReal_const_smul ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChartReal_const_smul

def wkpChartFun
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {k : ℕ} {p : ℝ≥0∞} {hp : 1 ≤ p}
    (u : WkpChart (I := I) (M := M) k p hp) : M → ℝ :=
  Subtype.val (α := (M → ℝ))
    (p := fun u => u ∈ wkpChartSubmodule (I := I) (M := M) k p hp) u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.wkpChartFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.wkpChartFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.wkpChartFun ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.wkpChartFun

lemma wkpChartFun_memWkpChart
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {k : ℕ} {p : ℝ≥0∞} {hp : 1 ≤ p}
    (u : WkpChart (I := I) (M := M) k p hp) :
    MemWkpChart (I := I) (M := M) k p (wkpChartFun u) :=
  Subtype.property
    (α := (M → ℝ))
    (p := fun u => u ∈ wkpChartSubmodule (I := I) (M := M) k p hp) u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.wkpChartFun_memWkpChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.wkpChartFun_memWkpChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.wkpChartFun_memWkpChart ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.wkpChartFun_memWkpChart

@[simp]
lemma wkpChartFun_add
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {k : ℕ} {p : ℝ≥0∞} {hp : 1 ≤ p}
    (u v : WkpChart (I := I) (M := M) k p hp) :
    wkpChartFun (u + v) = fun x => wkpChartFun u x + wkpChartFun v x := by
  ext x
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.wkpChartFun_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.wkpChartFun_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.wkpChartFun_add ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.wkpChartFun_add

@[simp]
lemma wkpChartFun_smul
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {k : ℕ} {p : ℝ≥0∞} {hp : 1 ≤ p}
    (c : ℝ) (u : WkpChart (I := I) (M := M) k p hp) :
    wkpChartFun (c • u) = fun x => c * wkpChartFun u x := by
  ext x
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.wkpChartFun_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.wkpChartFun_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.wkpChartFun_smul ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.wkpChartFun_smul

instance instNormWkpChart
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    Norm (WkpChart (I := I) (M := M) k p hp) where
  norm u := (wkpNormChart (I := I) (M := M) k p (wkpChartFun u)).toReal

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.instNormWkpChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.instNormWkpChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.instNormWkpChart ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.instNormWkpChart

@[simp]
lemma norm_wkpChart_def
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {k : ℕ} {p : ℝ≥0∞} {hp : 1 ≤ p}
    (u : WkpChart (I := I) (M := M) k p hp) :
    ‖u‖ = (wkpNormChart (I := I) (M := M) k p (wkpChartFun u)).toReal := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.norm_wkpChart_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.norm_wkpChart_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.norm_wkpChart_def ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.norm_wkpChart_def

private lemma wkpChart_seminormedSpace_core
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    SeminormedSpace.Core ℝ (WkpChart (I := I) (M := M) k p hp) where
  norm_nonneg u := ENNReal.toReal_nonneg
  norm_smul c u := by
    have hu_mem := wkpChartFun_memWkpChart u
    change (wkpNormChart (I := I) (M := M) k p (wkpChartFun (c • u))).toReal =
      ‖c‖ * (wkpNormChart (I := I) (M := M) k p (wkpChartFun u)).toReal
    rw [wkpChartFun_smul]
    rw [wkpNormChart_const_smul (I := I) (M := M) hp c hu_mem]
    rw [ENNReal.toReal_mul, toReal_enorm]
  norm_triangle u v := by
    have hu_mem := wkpChartFun_memWkpChart u
    have hv_mem := wkpChartFun_memWkpChart v
    change (wkpNormChart (I := I) (M := M) k p (wkpChartFun (u + v))).toReal ≤
      (wkpNormChart (I := I) (M := M) k p (wkpChartFun u)).toReal +
        (wkpNormChart (I := I) (M := M) k p (wkpChartFun v)).toReal
    rw [wkpChartFun_add]
    have h_add_le := wkpNormChart_add_le (I := I) (M := M) hp hu_mem hv_mem
    have hu_lt : wkpNormChart (I := I) (M := M) k p (wkpChartFun u) < ⊤ :=
      wkpNormChart_lt_top_of_memWkpChart (I := I) (M := M) hp hu_mem
    have hv_lt : wkpNormChart (I := I) (M := M) k p (wkpChartFun v) < ⊤ :=
      wkpNormChart_lt_top_of_memWkpChart (I := I) (M := M) hp hv_mem
    have hu_ne : wkpNormChart (I := I) (M := M) k p (wkpChartFun u) ≠ ⊤ := hu_lt.ne
    have hv_ne : wkpNormChart (I := I) (M := M) k p (wkpChartFun v) ≠ ⊤ := hv_lt.ne
    have hRHS_ne : wkpNormChart (I := I) (M := M) k p (wkpChartFun u) +
        wkpNormChart (I := I) (M := M) k p (wkpChartFun v) ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨hu_ne, hv_ne⟩
    have hToReal := ENNReal.toReal_mono hRHS_ne h_add_le
    rw [ENNReal.toReal_add hu_ne hv_ne] at hToReal
    exact hToReal

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.wkpChart_seminormedSpace_core
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Chart.wkpChart_seminormedSpace_core target :: scope.openDecls } }

instance instSeminormedAddCommGroupWkpChart
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    SeminormedAddCommGroup (WkpChart (I := I) (M := M) k p hp) :=
  SeminormedAddCommGroup.ofCore (wkpChart_seminormedSpace_core (I := I) (M := M) k p hp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.instSeminormedAddCommGroupWkpChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.instSeminormedAddCommGroupWkpChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.instSeminormedAddCommGroupWkpChart ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.instSeminormedAddCommGroupWkpChart

instance instNormedSpaceRealWkpChart
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    NormedSpace ℝ (WkpChart (I := I) (M := M) k p hp) where
  norm_smul_le c u := by
    have hu_mem := wkpChartFun_memWkpChart u
    change (wkpNormChart (I := I) (M := M) k p (wkpChartFun (c • u))).toReal ≤
      ‖c‖ * (wkpNormChart (I := I) (M := M) k p (wkpChartFun u)).toReal
    rw [wkpChartFun_smul]
    rw [wkpNormChart_const_smul (I := I) (M := M) hp c hu_mem]
    rw [ENNReal.toReal_mul, toReal_enorm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.instNormedSpaceRealWkpChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.instNormedSpaceRealWkpChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.instNormedSpaceRealWkpChart ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.instNormedSpaceRealWkpChart

def WkpChartQuot
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) : Type _ :=
  SeparationQuotient (WkpChart (I := I) (M := M) k p hp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.WkpChartQuot then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.WkpChartQuot"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.WkpChartQuot ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.WkpChartQuot

instance instAddCommGroupWkpChartQuot
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    AddCommGroup (WkpChartQuot (I := I) (M := M) k p hp) :=
  inferInstanceAs (AddCommGroup (SeparationQuotient (WkpChart (I := I) (M := M) k p hp)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.instAddCommGroupWkpChartQuot then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.instAddCommGroupWkpChartQuot"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.instAddCommGroupWkpChartQuot ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.instAddCommGroupWkpChartQuot

instance instNormedAddCommGroupWkpChartQuot
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    NormedAddCommGroup (WkpChartQuot (I := I) (M := M) k p hp) :=
  inferInstanceAs (NormedAddCommGroup
    (SeparationQuotient (WkpChart (I := I) (M := M) k p hp)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.instNormedAddCommGroupWkpChartQuot then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.instNormedAddCommGroupWkpChartQuot"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.instNormedAddCommGroupWkpChartQuot ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.instNormedAddCommGroupWkpChartQuot

instance instModuleWkpChartQuot
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    Module ℝ (WkpChartQuot (I := I) (M := M) k p hp) :=
  inferInstanceAs (Module ℝ (SeparationQuotient (WkpChart (I := I) (M := M) k p hp)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.instModuleWkpChartQuot then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.instModuleWkpChartQuot"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.instModuleWkpChartQuot ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.instModuleWkpChartQuot

instance instNormedSpaceRealWkpChartQuot
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    NormedSpace ℝ (WkpChartQuot (I := I) (M := M) k p hp) :=
  inferInstanceAs (NormedSpace ℝ (SeparationQuotient (WkpChart (I := I) (M := M) k p hp)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.instNormedSpaceRealWkpChartQuot then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.instNormedSpaceRealWkpChartQuot"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.instNormedSpaceRealWkpChartQuot ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.instNormedSpaceRealWkpChartQuot

end Chart
end Sobolev
end Analysis
end DifferentialGeometry
