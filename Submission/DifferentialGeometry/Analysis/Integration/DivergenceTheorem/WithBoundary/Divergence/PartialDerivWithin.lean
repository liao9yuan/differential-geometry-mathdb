import Submission.DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Local.Formula
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.TangentCone.Basic
import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Set
open scoped _root_.Topology _root_.ContDiff

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem
namespace WithBoundary

open _root_.Submission.DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]

def partialDerivWithin (s : Set E) (i : Fin (Module.finrank ℝ E))
    (u : E → ℝ) (y : E) : ℝ :=
  fderivWithin ℝ u s y ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.partialDerivWithin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.partialDerivWithin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.partialDerivWithin ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.partialDerivWithin

@[simp] lemma partialDerivWithin_def (s : Set E)
    (i : Fin (Module.finrank ℝ E)) (u : E → ℝ) (y : E) :
    partialDerivWithin (E := E) s i u y =
      fderivWithin ℝ u s y ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.partialDerivWithin_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.partialDerivWithin_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.partialDerivWithin_def ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.partialDerivWithin_def

section ComparisonWithFDeriv

variable {s : Set E} {i : Fin (Module.finrank ℝ E)} {u : E → ℝ} {y : E}

lemma partialDerivWithin_eq_partialDeriv_of_isOpen
    (hs : IsOpen s) (hy : y ∈ s) :
    partialDerivWithin (E := E) s i u y = DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i u y := by
  unfold partialDerivWithin DifferentialGeometry.Tensor.Coordinates.partialDeriv
  rw [fderivWithin_of_isOpen hs hy]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.partialDerivWithin_eq_partialDeriv_of_isOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.partialDerivWithin_eq_partialDeriv_of_isOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.partialDerivWithin_eq_partialDeriv_of_isOpen ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.partialDerivWithin_eq_partialDeriv_of_isOpen

lemma partialDerivWithin_eq_partialDeriv_of_mem_interior
    (hy : y ∈ interior s) :
    partialDerivWithin (E := E) s i u y = DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i u y := by
  have hnhds : s ∈ 𝓝 y :=
    Filter.mem_of_superset (isOpen_interior.mem_nhds hy) interior_subset
  unfold partialDerivWithin DifferentialGeometry.Tensor.Coordinates.partialDeriv
  rw [fderivWithin_of_mem_nhds hnhds]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.partialDerivWithin_eq_partialDeriv_of_mem_interior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.partialDerivWithin_eq_partialDeriv_of_mem_interior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.partialDerivWithin_eq_partialDeriv_of_mem_interior ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.partialDerivWithin_eq_partialDeriv_of_mem_interior

lemma partialDerivWithin_congr {u v : E → ℝ}
    (huv : _root_.Set.EqOn u v s) (hy : u y = v y) :
    partialDerivWithin (E := E) s i u y =
      partialDerivWithin (E := E) s i v y := by
  unfold partialDerivWithin
  rw [fderivWithin_congr huv hy]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.partialDerivWithin_congr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.partialDerivWithin_congr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.partialDerivWithin_congr ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.partialDerivWithin_congr

lemma partialDerivWithin_congr_of_eqOn_of_mem {u v : E → ℝ}
    (huv : _root_.Set.EqOn u v s) (hy : y ∈ s) :
    partialDerivWithin (E := E) s i u y =
      partialDerivWithin (E := E) s i v y :=
  partialDerivWithin_congr huv (huv hy)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.partialDerivWithin_congr_of_eqOn_of_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.partialDerivWithin_congr_of_eqOn_of_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.partialDerivWithin_congr_of_eqOn_of_mem ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.partialDerivWithin_congr_of_eqOn_of_mem

end ComparisonWithFDeriv

section Smoothness

variable {m n : WithTop ℕ∞} {s : Set E} {u : E → ℝ}
  {i : Fin (Module.finrank ℝ E)}

lemma partialDerivWithin_contDiffOn_of_uniqueDiffOn
    (hu : ContDiffOn ℝ n u s) (hs : UniqueDiffOn ℝ s) (hmn : m + 1 ≤ n) :
    ContDiffOn ℝ m (partialDerivWithin (E := E) s i u) s := by
  have hfderiv : ContDiffOn ℝ m (fderivWithin ℝ u s) s :=
    hu.fderivWithin hs hmn
  have hconst : ContDiffOn ℝ m
      (fun _ : E => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) s := contDiffOn_const
  exact hfderiv.clm_apply hconst

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.partialDerivWithin_contDiffOn_of_uniqueDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.partialDerivWithin_contDiffOn_of_uniqueDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.partialDerivWithin_contDiffOn_of_uniqueDiffOn ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.partialDerivWithin_contDiffOn_of_uniqueDiffOn

lemma partialDerivWithin_contDiffOn_top_of_uniqueDiffOn
    (hu : ContDiffOn ℝ ∞ u s) (hs : UniqueDiffOn ℝ s) :
    ContDiffOn ℝ ∞ (partialDerivWithin (E := E) s i u) s :=
  partialDerivWithin_contDiffOn_of_uniqueDiffOn (n := ∞) (m := ∞) hu hs
    (by rw [ENat.coe_top_add_one])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.partialDerivWithin_contDiffOn_top_of_uniqueDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.partialDerivWithin_contDiffOn_top_of_uniqueDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.partialDerivWithin_contDiffOn_top_of_uniqueDiffOn ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.partialDerivWithin_contDiffOn_top_of_uniqueDiffOn

lemma partialDerivWithin_contDiffOn_of_isOpen
    (hu : ContDiffOn ℝ n u s) (hs : IsOpen s) (hmn : m + 1 ≤ n) :
    ContDiffOn ℝ m (partialDerivWithin (E := E) s i u) s :=
  partialDerivWithin_contDiffOn_of_uniqueDiffOn hu hs.uniqueDiffOn hmn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.partialDerivWithin_contDiffOn_of_isOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.partialDerivWithin_contDiffOn_of_isOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.partialDerivWithin_contDiffOn_of_isOpen ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.partialDerivWithin_contDiffOn_of_isOpen

lemma partialDerivWithin_contDiffOn_top_of_isOpen
    (hu : ContDiffOn ℝ ∞ u s) (hs : IsOpen s) :
    ContDiffOn ℝ ∞ (partialDerivWithin (E := E) s i u) s :=
  partialDerivWithin_contDiffOn_of_isOpen (n := ∞) (m := ∞) hu hs
    (by rw [ENat.coe_top_add_one])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.partialDerivWithin_contDiffOn_top_of_isOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.partialDerivWithin_contDiffOn_top_of_isOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.partialDerivWithin_contDiffOn_top_of_isOpen ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.partialDerivWithin_contDiffOn_top_of_isOpen

end Smoothness

section LeibnizIdentities

variable {s : Set E} {y : E} {i : Fin (Module.finrank ℝ E)}

lemma partialDerivWithin_add (u v : E → ℝ)
    (hs : UniqueDiffWithinAt ℝ s y)
    (hu : DifferentiableWithinAt ℝ u s y)
    (hv : DifferentiableWithinAt ℝ v s y) :
    partialDerivWithin (E := E) s i (fun y => u y + v y) y =
      partialDerivWithin (E := E) s i u y +
        partialDerivWithin (E := E) s i v y := by
  unfold partialDerivWithin
  rw [fderivWithin_fun_add hs hu hv]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.partialDerivWithin_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.partialDerivWithin_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.partialDerivWithin_add ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.partialDerivWithin_add

lemma partialDerivWithin_smul (c : E → ℝ) (u : E → ℝ)
    (hs : UniqueDiffWithinAt ℝ s y)
    (hc : DifferentiableWithinAt ℝ c s y)
    (hu : DifferentiableWithinAt ℝ u s y) :
    partialDerivWithin (E := E) s i (fun y => c y • u y) y =
      c y • partialDerivWithin (E := E) s i u y +
        partialDerivWithin (E := E) s i c y • u y := by
  unfold partialDerivWithin
  rw [fderivWithin_fun_smul hs hc hu]
  simp [ContinuousLinearMap.smulRight_apply, smul_eq_mul, mul_comm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.partialDerivWithin_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.partialDerivWithin_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.partialDerivWithin_smul ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.partialDerivWithin_smul

lemma partialDerivWithin_mul (u v : E → ℝ)
    (hs : UniqueDiffWithinAt ℝ s y)
    (hu : DifferentiableWithinAt ℝ u s y)
    (hv : DifferentiableWithinAt ℝ v s y) :
    partialDerivWithin (E := E) s i (fun y => u y * v y) y =
      u y * partialDerivWithin (E := E) s i v y +
        v y * partialDerivWithin (E := E) s i u y := by
  unfold partialDerivWithin
  rw [fderivWithin_fun_mul hs hu hv]
  simp [add_apply, smul_apply,
    smul_eq_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.partialDerivWithin_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.partialDerivWithin_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.partialDerivWithin_mul ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.partialDerivWithin_mul

end LeibnizIdentities

section ChartTarget

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [Module.Finite ℝ E] [IsManifold I ∞ M] in
lemma uniqueDiffOn_extChartAt_target_apply (α : M) {y : E}
    (hy : y ∈ (extChartAt I α).target) :
    UniqueDiffWithinAt ℝ (extChartAt I α).target y :=
  uniqueDiffOn_extChartAt_target α y hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.uniqueDiffOn_extChartAt_target_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.uniqueDiffOn_extChartAt_target_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.uniqueDiffOn_extChartAt_target_apply ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.uniqueDiffOn_extChartAt_target_apply

omit [IsManifold I ∞ M] in
theorem partialDerivWithin_extChartAt_target_eq_partialDeriv
    (α : M) (i : Fin (Module.finrank ℝ E)) (u : E → ℝ)
    {y : E} (hy : y ∈ interior (extChartAt I α).target) :
    partialDerivWithin (E := E) (extChartAt I α).target i u y =
      DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i u y :=
  partialDerivWithin_eq_partialDeriv_of_mem_interior hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.partialDerivWithin_extChartAt_target_eq_partialDeriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.partialDerivWithin_extChartAt_target_eq_partialDeriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.partialDerivWithin_extChartAt_target_eq_partialDeriv ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.partialDerivWithin_extChartAt_target_eq_partialDeriv

end ChartTarget

end WithBoundary
end DivergenceTheorem
end Integral
end DifferentialGeometry
