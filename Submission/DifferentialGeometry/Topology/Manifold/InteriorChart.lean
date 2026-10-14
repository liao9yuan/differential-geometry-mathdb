import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
open _root_.Set
open scoped _root_.Manifold _root_.ContDiff
noncomputable section
namespace DifferentialGeometry.Manifold
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H M : Type*} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) [IsManifold I n M]

def interiorChart (x : M) : PartialDiffeomorph I 𝓘(𝕜, E) M E n where
  toFun := extChartAt I x
  invFun := (extChartAt I x).symm
  source := (chartAt H x).source ∩ (extChartAt I x) ⁻¹' interior (extChartAt I x).target
  target := interior (extChartAt I x).target
  map_source' _ hy := hy.2
  map_target' y hy := by
    refine ⟨?_, ?_⟩
    · simpa only [extChartAt_source] using (extChartAt I x).map_target (interior_subset hy)
    · change extChartAt I x ((extChartAt I x).symm y) ∈ interior (extChartAt I x).target
      rw [(extChartAt I x).right_inv (interior_subset hy)]
      exact hy
  left_inv' y hy := (extChartAt I x).left_inv (by simpa only [extChartAt_source] using hy.1)
  right_inv' _ hy := (extChartAt I x).right_inv (interior_subset hy)
  open_source := isOpen_extChartAt_preimage x isOpen_interior
  open_target := isOpen_interior
  contMDiffOn_toFun := contMDiffOn_extChartAt.mono _root_.Set.inter_subset_left
  contMDiffOn_invFun := (contMDiffOn_extChartAt_symm x).mono interior_subset

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.interiorChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.interiorChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.interiorChart ``Submission.DifferentialGeometry.Manifold.interiorChart


@[simp]
theorem interiorChart_apply (x y : M) : interiorChart I n x y = extChartAt I x y := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.interiorChart_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.interiorChart_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.interiorChart_apply ``Submission.DifferentialGeometry.Manifold.interiorChart_apply


@[simp]
theorem interiorChart_symm_apply (x : M) (y : E) :
    (interiorChart I n x).symm y = (extChartAt I x).symm y := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.interiorChart_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.interiorChart_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.interiorChart_symm_apply ``Submission.DifferentialGeometry.Manifold.interiorChart_symm_apply


@[simp]
theorem interiorChart_source (x : M) :
    (interiorChart I n x).source =
      (chartAt H x).source ∩ (extChartAt I x) ⁻¹' interior (extChartAt I x).target := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.interiorChart_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.interiorChart_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.interiorChart_source ``Submission.DifferentialGeometry.Manifold.interiorChart_source


@[simp]
theorem interiorChart_target (x : M) :
    (interiorChart I n x).target = interior (extChartAt I x).target := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.interiorChart_target then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.interiorChart_target"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.interiorChart_target ``Submission.DifferentialGeometry.Manifold.interiorChart_target

theorem mem_interiorChart_source_iff (x : M) :
    x ∈ (interiorChart I n x).source ↔ I.IsInteriorPoint x := by
  simp only [interiorChart_source, _root_.Set.mem_inter_iff, mem_chart_source, true_and, _root_.Set.mem_preimage]
  exact I.isInteriorPoint_iff.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.mem_interiorChart_source_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.mem_interiorChart_source_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.mem_interiorChart_source_iff ``Submission.DifferentialGeometry.Manifold.mem_interiorChart_source_iff


theorem isInteriorPoint_of_mem_interiorChart_source (hn : n ≠ 0) {x y : M}
    (hy : y ∈ (interiorChart I n x).source) : I.IsInteriorPoint y :=
  (I.isInteriorPoint_iff_of_mem_atlas hn (chart_mem_atlas H x) hy.1).mpr hy.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.isInteriorPoint_of_mem_interiorChart_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.isInteriorPoint_of_mem_interiorChart_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.isInteriorPoint_of_mem_interiorChart_source ``Submission.DifferentialGeometry.Manifold.isInteriorPoint_of_mem_interiorChart_source

omit [IsManifold I n M] in
theorem isInteriorPoint_of_model_partialDiffeomorph
    (f : PartialDiffeomorph 𝓘(𝕜, E) I E M n) (hn : n ≠ 0)
    {x : E} (hx : x ∈ f.source) : I.IsInteriorPoint (f x) := by
  have hf : IsLocalDiffeomorphAt 𝓘(𝕜, E) I n f x := ⟨f, hx, fun _ _ => rfl⟩
  exact (hf.isInteriorPoint_iff hn).mp BoundarylessManifold.isInteriorPoint

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.isInteriorPoint_of_model_partialDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.isInteriorPoint_of_model_partialDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.isInteriorPoint_of_model_partialDiffeomorph ``Submission.DifferentialGeometry.Manifold.isInteriorPoint_of_model_partialDiffeomorph

end DifferentialGeometry.Manifold
