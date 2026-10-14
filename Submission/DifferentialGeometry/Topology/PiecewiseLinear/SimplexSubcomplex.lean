/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SubcomplexComplementLink

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem restrict_eq_of_subcomplex (K A : Geometry.SimplicialComplex ℝ E)
    (hAK : A.faces ⊆ K.faces) : restrict K A.space = A := by
  ext s
  rw [mem_restrict_faces_iff_of_faces_subset K K A subset_rfl hAK]
  exact ⟨And.right, fun h => ⟨hAK h, h⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.restrict_eq_of_subcomplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.restrict_eq_of_subcomplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.restrict_eq_of_subcomplex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.restrict_eq_of_subcomplex

theorem restrict_convexHull_eq_simplexComplex (K : Geometry.SimplicialComplex ℝ E)
    {s : Finset E} (hs : s ∈ K.faces) :
    restrict K (convexHull ℝ (s : Set E)) = simplexComplex s (K.indep hs) := by
  rw [← simplexComplex_space s (K.indep hs) (K.nonempty_of_mem_faces hs)]
  exact restrict_eq_of_subcomplex K _ (fun t ht => K.down_closed hs ht.2 ht.1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.restrict_convexHull_eq_simplexComplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.restrict_convexHull_eq_simplexComplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.restrict_convexHull_eq_simplexComplex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.restrict_convexHull_eq_simplexComplex

theorem mem_restrict_convexHull_faces_iff (K : Geometry.SimplicialComplex ℝ E)
    {s e : Finset E} (hs : s ∈ K.faces) :
    e ∈ (restrict K (convexHull ℝ (s : Set E))).faces ↔ e.Nonempty ∧ e ⊆ s := by
  rw [restrict_convexHull_eq_simplexComplex K hs]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mem_restrict_convexHull_faces_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mem_restrict_convexHull_faces_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mem_restrict_convexHull_faces_iff ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mem_restrict_convexHull_faces_iff

end DifferentialGeometry.Topology.PiecewiseLinear
