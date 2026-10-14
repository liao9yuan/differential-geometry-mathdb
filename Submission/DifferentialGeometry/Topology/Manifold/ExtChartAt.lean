import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set
open scoped _root_.Manifold _root_.Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

open _root_.OpenPartialHomeomorph in
theorem OpenPartialHomeomorph.isOpen_extend_target_of_isInteriorPoint
    {e : OpenPartialHomeomorph M H} (he : e ∈ atlas H M)
    (hint : ∀ x ∈ e.source, I.IsInteriorPoint x) : IsOpen (e.extend I).target := by
  apply isOpen_iff_mem_nhds.mpr
  intro y hy
  have hx : (e.extend I).symm y ∈ e.source := by
    simpa only [OpenPartialHomeomorph.extend_source] using (e.extend I).map_target hy
  have hi := (I.isInteriorPoint_iff_of_mem_atlas (n := 1) (by simp) he hx).mp
    (hint _ hx)
  rw [(e.extend I).right_inv hy] at hi
  exact mem_interior_iff_mem_nhds.mp hi

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.OpenPartialHomeomorph
  let env ← Lean.getEnv
  if env.contains `OpenPartialHomeomorph.isOpen_extend_target_of_isInteriorPoint then
    throwError "Refusing to shadow existing declaration OpenPartialHomeomorph.isOpen_extend_target_of_isInteriorPoint"
  Lean.modifyEnv fun env => Lean.addAlias env `OpenPartialHomeomorph.isOpen_extend_target_of_isInteriorPoint ``Submission.OpenPartialHomeomorph.isOpen_extend_target_of_isInteriorPoint

theorem isOpen_extChartAt_target_of_boundarylessManifold [BoundarylessManifold I M] (x : M) :
    IsOpen (extChartAt I x).target :=
  OpenPartialHomeomorph.isOpen_extend_target_of_isInteriorPoint (chart_mem_atlas H x)
    (fun _ _ => BoundarylessManifold.isInteriorPoint)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `isOpen_extChartAt_target_of_boundarylessManifold then
    throwError "Refusing to shadow existing declaration isOpen_extChartAt_target_of_boundarylessManifold"
  Lean.modifyEnv fun env => Lean.addAlias env `isOpen_extChartAt_target_of_boundarylessManifold ``Submission.isOpen_extChartAt_target_of_boundarylessManifold
