import Submission.DifferentialGeometry.Topology.Manifold.InteriorChart
import Mathlib.Geometry.Manifold.Diffeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
open _root_.Set
open scoped _root_.Manifold _root_.ContDiff _root_.Topology
noncomputable section
namespace DifferentialGeometry.Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H M : Type*} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) [IsManifold I n M]
  [BoundarylessManifold I M]

@[reducible]
def interiorChartedSpace : ChartedSpace E M where
  atlas := _root_.Set.range (fun x : M => (interiorChart I n x).toOpenPartialHomeomorph)
  chartAt x := (interiorChart I n x).toOpenPartialHomeomorph
  mem_chart_source x :=
    (mem_interiorChart_source_iff I n x).mpr BoundarylessManifold.isInteriorPoint
  chart_mem_atlas x := ⟨x, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.interiorChartedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.interiorChartedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.interiorChartedSpace ``Submission.DifferentialGeometry.Manifold.interiorChartedSpace


theorem extChartAt_interiorAtlas_apply (x y : M) :
    let _ := interiorChartedSpace I n (M := M)
    extChartAt 𝓘(𝕜, E) x y = extChartAt I x y := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.extChartAt_interiorAtlas_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.extChartAt_interiorAtlas_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.extChartAt_interiorAtlas_apply ``Submission.DifferentialGeometry.Manifold.extChartAt_interiorAtlas_apply

theorem extChartAt_interiorAtlas_symm_apply (x : M) (y : E) :
    let _ := interiorChartedSpace I n (M := M)
    (extChartAt 𝓘(𝕜, E) x).symm y = (extChartAt I x).symm y := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.extChartAt_interiorAtlas_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.extChartAt_interiorAtlas_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.extChartAt_interiorAtlas_symm_apply ``Submission.DifferentialGeometry.Manifold.extChartAt_interiorAtlas_symm_apply

theorem interiorIsManifold :
    let _ := interiorChartedSpace I n (M := M)
    IsManifold 𝓘(𝕜, E) n M := by
  let _ := interiorChartedSpace I n (M := M)
  apply isManifold_of_contDiffOn
  rintro e e' ⟨x, rfl⟩ ⟨y, rfl⟩
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, _root_.Set.preimage_id, _root_.Set.range_id, _root_.Set.inter_univ]
  convert! contMDiffOn_iff_contDiffOn.mp
    ((interiorChart I n x).symm.trans (interiorChart I n y)).contMDiffOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.interiorIsManifold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.interiorIsManifold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.interiorIsManifold ``Submission.DifferentialGeometry.Manifold.interiorIsManifold


theorem contMDiff_interiorAtlas_id :
    let _ := interiorChartedSpace I n (M := M)
    ContMDiff 𝓘(𝕜, E) I n (id : M → M) := by
  let _ := interiorChartedSpace I n (M := M)
  change ContMDiff 𝓘(𝕜, E) I n (id : M → M)
  intro x
  rw [contMDiffAt_iff_source]
  have hx := (mem_interiorChart_source_iff I n x).mpr
    BoundarylessManifold.isInteriorPoint
  have h := (interiorChart I n x).symm.contMDiffOn.contMDiffAt
    ((interiorChart I n x).open_target.mem_nhds ((interiorChart I n x).map_source hx))
  simp only [modelWithCornersSelf_coe, _root_.Set.range_id, contMDiffWithinAt_univ,
    Function.id_comp]
  change ContMDiffAt 𝓘(𝕜, E) I n (fun y => (extChartAt I x).symm y)
    (extChartAt I x x)
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.contMDiff_interiorAtlas_id then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.contMDiff_interiorAtlas_id"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.contMDiff_interiorAtlas_id ``Submission.DifferentialGeometry.Manifold.contMDiff_interiorAtlas_id


theorem contMDiff_id_interiorAtlas :
    let _ := interiorChartedSpace I n (M := M)
    ContMDiff I 𝓘(𝕜, E) n (id : M → M) := by
  let _ := interiorChartedSpace I n (M := M)
  change ContMDiff I 𝓘(𝕜, E) n (id : M → M)
  intro x
  rw [contMDiffAt_iff_target]
  refine ⟨continuousAt_id, ?_⟩
  change ContMDiffAt I 𝓘(𝕜, E) n (extChartAt I x) x
  exact contMDiffAt_extChartAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.contMDiff_id_interiorAtlas then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.contMDiff_id_interiorAtlas"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.contMDiff_id_interiorAtlas ``Submission.DifferentialGeometry.Manifold.contMDiff_id_interiorAtlas

def interiorAtlasDiffeomorph :
    let _ := interiorChartedSpace I n (M := M)
    M ≃ₘ^n⟮I, 𝓘(𝕜, E)⟯ M := by
  let _ := interiorChartedSpace I n (M := M)
  exact { toEquiv := Equiv.refl M
          contMDiff_toFun := contMDiff_id_interiorAtlas I n
          contMDiff_invFun := contMDiff_interiorAtlas_id I n }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.interiorAtlasDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.interiorAtlasDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.interiorAtlasDiffeomorph ``Submission.DifferentialGeometry.Manifold.interiorAtlasDiffeomorph


@[simp]
theorem interiorAtlasDiffeomorph_apply (x : M) :
    interiorAtlasDiffeomorph I n x = x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.interiorAtlasDiffeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.interiorAtlasDiffeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.interiorAtlasDiffeomorph_apply ``Submission.DifferentialGeometry.Manifold.interiorAtlasDiffeomorph_apply


theorem interiorAtlasDiffeomorph_symm_apply (x : M) :
    let _ := interiorChartedSpace I n (M := M)
    (interiorAtlasDiffeomorph I n).symm x = x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.interiorAtlasDiffeomorph_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.interiorAtlasDiffeomorph_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.interiorAtlasDiffeomorph_symm_apply ``Submission.DifferentialGeometry.Manifold.interiorAtlasDiffeomorph_symm_apply

omit [BoundarylessManifold I M] in
def intrinsicInterior (hn : n ≠ 0) : TopologicalSpace.Opens M :=
  ⟨I.interior M, I.isOpen_interior hn⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.intrinsicInterior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.intrinsicInterior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.intrinsicInterior ``Submission.DifferentialGeometry.Manifold.intrinsicInterior

omit [BoundarylessManifold I M] in
instance boundarylessManifold_intrinsicInterior (hn : n ≠ 0) :
    BoundarylessManifold I (intrinsicInterior I n hn (M := M)) where
  isInteriorPoint' x := I.isInteriorPoint_iff_isInteriorPoint_val.mpr x.property

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.boundarylessManifold_intrinsicInterior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.boundarylessManifold_intrinsicInterior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.boundarylessManifold_intrinsicInterior ``Submission.DifferentialGeometry.Manifold.boundarylessManifold_intrinsicInterior

omit [BoundarylessManifold I M] in
theorem contMDiff_intrinsicInterior_val (hn : n ≠ 0) :
    let _ := interiorChartedSpace I n (M := intrinsicInterior I n hn (M := M))
    ContMDiff 𝓘(𝕜, E) I n
      (Subtype.val : intrinsicInterior I n hn (M := M) → M) := by
  let U := intrinsicInterior I n hn (M := M)
  let _ := interiorChartedSpace I n (M := U)
  exact (contMDiff_subtype_val (I := I) (U := U)).comp
    (contMDiff_interiorAtlas_id I n (M := U))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.contMDiff_intrinsicInterior_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.contMDiff_intrinsicInterior_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.contMDiff_intrinsicInterior_val ``Submission.DifferentialGeometry.Manifold.contMDiff_intrinsicInterior_val

end DifferentialGeometry.Manifold
