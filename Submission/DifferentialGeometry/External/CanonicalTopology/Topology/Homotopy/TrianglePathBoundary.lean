import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homotopy.TriangleBoundaryQuotient
import Mathlib.Topology.Path

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-! # Gluing the same three prescribed paths on the actual triangle frontier -/

noncomputable section

open _root_.Set _root_.Function _root_.ContinuousMap
open scoped _root_.Topology

namespace DifferentialGeometry.Topology

variable {Q : Type*} [TopologicalSpace Q] {a b c : Q}

/-- The original three paths on the ordered disjoint union of intervals. -/
def triangleBoundaryPaths (p : Path a b) (q : Path b c) (r : Path a c) :
    C(Fin 3 × unitInterval, Q) :=
  (⟨![q.toContinuousMap, r.toContinuousMap, p.toContinuousMap], continuous_of_discreteTopology⟩ :
    C(Fin 3, C(unitInterval, Q))).uncurry

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.triangleBoundaryPaths then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.triangleBoundaryPaths"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.triangleBoundaryPaths ``Submission.DifferentialGeometry.Topology.triangleBoundaryPaths

/-- The same paths agree whenever two original edge parameters represent
the same actual boundary point. All nine edge pairs are checked. -/
theorem triangleBoundaryPaths_fiber (p : Path a b) (q : Path b c) (r : Path a c)
    {z w : Fin 3 × unitInterval} (h : triangleBoundaryProjection z = triangleBoundaryProjection w) :
    triangleBoundaryPaths p q r z = triangleBoundaryPaths p q r w := by
  rcases z with ⟨i, s⟩
  rcases w with ⟨j, t⟩
  have he : planeTriangleEdgeValue i s = planeTriangleEdgeValue j t := congrArg Subtype.val h
  have hre := congrArg Complex.re he
  have him := congrArg Complex.im he
  fin_cases i <;> fin_cases j <;> norm_num [planeTriangleEdgeValue] at hre him
  · change q s = q t
    exact congrArg q (Subtype.ext him)
  · change q s = r t
    have hs : s = 1 := Subtype.ext (by change (s : ℝ) = 1; linarith only [hre, him])
    have ht : t = 1 := Subtype.ext (by change (t : ℝ) = 1; simp only [hs] at hre him; linarith only [hre, him])
    simp [hs, ht]
  · change q s = p t
    have hs : s = 0 := him
    have hsR : (s : ℝ) = 0 := congrArg Subtype.val hs
    have ht : t = 1 := Subtype.ext (by change (t : ℝ) = 1; linarith only [hre, hsR])
    simp [hs, ht]
  · change r s = q t
    have hs : s = 1 := Subtype.ext (by change (s : ℝ) = 1; linarith only [hre, him])
    have ht : t = 1 := Subtype.ext (by change (t : ℝ) = 1; simp only [hs] at hre him; linarith only [hre, him])
    simp [hs, ht]
  · change r s = r t
    exact congrArg r (Subtype.ext him)
  · change r s = p t
    have hs : s = 0 := by assumption
    have ht : t = 0 := Subtype.ext (by change (t : ℝ) = 0; linarith)
    simp [hs, ht]
  · change p s = q t
    have hs : s = 1 := Subtype.ext (by change (s : ℝ) = 1; linarith only [hre, him])
    have ht : t = 0 := Subtype.ext (by change (t : ℝ) = 0; linarith)
    simp [hs, ht]
  · change p s = r t
    have hs : s = 0 := by assumption
    have ht : t = 0 := Subtype.ext (by change (t : ℝ) = 0; linarith)
    simp [hs, ht]
  · change p s = p t
    exact congrArg p (Subtype.ext hre)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.triangleBoundaryPaths_fiber then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.triangleBoundaryPaths_fiber"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.triangleBoundaryPaths_fiber ``Submission.DifferentialGeometry.Topology.triangleBoundaryPaths_fiber

/-- The single boundary map obtained from those original paths. -/
def triangleBoundaryMap (p : Path a b) (q : Path b c) (r : Path a c) :
    C(frontier planeTriangle, Q) := by
  let j := Function.surjInv triangleBoundaryProjection_surjective
  let F : frontier planeTriangle → Q := fun z => triangleBoundaryPaths p q r (j z)
  have he : F ∘ triangleBoundaryProjection = triangleBoundaryPaths p q r := by
    funext z
    exact triangleBoundaryPaths_fiber p q r
      (Function.surjInv_eq triangleBoundaryProjection_surjective (triangleBoundaryProjection z))
  exact ⟨F, triangleBoundaryProjection_isQuotientMap.continuous_iff.mpr
    (he.symm ▸ (triangleBoundaryPaths p q r).continuous)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.triangleBoundaryMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.triangleBoundaryMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.triangleBoundaryMap ``Submission.DifferentialGeometry.Topology.triangleBoundaryMap

/-- Descent preserves all the original edge values exactly. -/
theorem triangleBoundaryMap_edge (p : Path a b) (q : Path b c) (r : Path a c)
    (i : Fin 3) (s : unitInterval) :
    triangleBoundaryMap p q r (planeTriangleEdge i s) = triangleBoundaryPaths p q r (i, s) :=
  triangleBoundaryPaths_fiber p q r
    (Function.surjInv_eq triangleBoundaryProjection_surjective (triangleBoundaryProjection (i, s)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.triangleBoundaryMap_edge then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.triangleBoundaryMap_edge"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.triangleBoundaryMap_edge ``Submission.DifferentialGeometry.Topology.triangleBoundaryMap_edge

end DifferentialGeometry.Topology
