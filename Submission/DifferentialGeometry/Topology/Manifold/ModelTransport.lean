import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.HasGroupoid

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set
namespace DifferentialGeometry.Manifold

variable {H H' M : Type*} [TopologicalSpace H] [TopologicalSpace H']
  [TopologicalSpace M] [ChartedSpace H M]


@[instance_reducible]
def chartedSpaceTransHomeomorph (e : H ≃ₜ H') : ChartedSpace H' M :=
  let _ : ChartedSpace H' H := e.toOpenPartialHomeomorph.singletonChartedSpace (by simp)
  ChartedSpace.comp H' H M

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.chartedSpaceTransHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.chartedSpaceTransHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.chartedSpaceTransHomeomorph ``Submission.DifferentialGeometry.Manifold.chartedSpaceTransHomeomorph


theorem chartAt_transHomeomorph (e : H ≃ₜ H') (x : M) :
    let _ := chartedSpaceTransHomeomorph (M := M) e
    chartAt H' x = (chartAt H x).trans e.toOpenPartialHomeomorph := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.chartAt_transHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.chartAt_transHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.chartAt_transHomeomorph ``Submission.DifferentialGeometry.Manifold.chartAt_transHomeomorph

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  (I : ModelWithCorners 𝕜 E H) (J : ModelWithCorners 𝕜 F H')
  (e : H ≃ₜ H') (L : E ≃ₜ F)
  (hcompat : ∀ y, J (e y) = L (I y))

include hcompat in
theorem range_model_transHomeomorph : _root_.Set.range J = L '' _root_.Set.range I := by
  ext y
  constructor
  · rintro ⟨z,rfl⟩
    refine ⟨I (e.symm z), _root_.Set.mem_range_self _, ?_⟩
    rw [← hcompat, e.apply_symm_apply]
  · rintro ⟨z,⟨w,rfl⟩,rfl⟩
    rw [← hcompat]
    exact _root_.Set.mem_range_self _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.range_model_transHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.range_model_transHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.range_model_transHomeomorph ``Submission.DifferentialGeometry.Manifold.range_model_transHomeomorph

include hcompat in
theorem isInteriorPoint_transHomeomorph_iff (x : M) :
    @ModelWithCorners.IsInteriorPoint 𝕜 _ F _ _ H' _ J M _
      (chartedSpaceTransHomeomorph (M := M) e) x ↔ I.IsInteriorPoint x := by
  change J (e (chartAt H x x)) ∈ interior (_root_.Set.range J) ↔ I (chartAt H x x) ∈ interior (_root_.Set.range I)
  rw [hcompat, range_model_transHomeomorph I J e L hcompat, ← L.image_interior]
  exact L.injective.mem_set_image

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.isInteriorPoint_transHomeomorph_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.isInteriorPoint_transHomeomorph_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.isInteriorPoint_transHomeomorph_iff ``Submission.DifferentialGeometry.Manifold.isInteriorPoint_transHomeomorph_iff

include hcompat in
theorem boundary_transHomeomorph :
    @ModelWithCorners.boundary 𝕜 _ F _ _ H' _ J M _
      (chartedSpaceTransHomeomorph (M := M) e) = I.boundary M := by
  let _ := chartedSpaceTransHomeomorph (M := M) e
  ext x
  simp only [ModelWithCorners.boundary, _root_.Set.mem_ofPred_eq]
  rw [ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint,
    ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint,
    isInteriorPoint_transHomeomorph_iff I J e L hcompat]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.boundary_transHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.boundary_transHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.boundary_transHomeomorph ``Submission.DifferentialGeometry.Manifold.boundary_transHomeomorph

end DifferentialGeometry.Manifold
