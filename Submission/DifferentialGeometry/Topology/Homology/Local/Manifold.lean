import Submission.DifferentialGeometry.Topology.Homology.Local.HalfSpace
import Submission.DifferentialGeometry.Topology.Manifold.InteriorChart

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Set
open scoped _root_.Manifold _root_.ContDiff
namespace DifferentialGeometry.Homology
variable (k : Type) [Field k]

section Interior
variable {n : ℕ} {H M : Type} [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] [T1Space M] (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) H)
  (x : M) (hx : I.IsInteriorPoint x)
include hx


theorem finiteHomologyType_localManifold_interior :
    DifferentialGeometry.HomologicalComplex.finiteHomologyType
      (relativeChainComplex (TopCat.of M) ({x}ᶜ : Set M) (ModuleCat.of k k)) := by
  let e := (DifferentialGeometry.Manifold.interiorChart I 0 x).toOpenPartialHomeomorph
  have he : x ∈ e.source := (DifferentialGeometry.Manifold.mem_interiorChart_source_iff I 0 x).mpr hx
  exact (finiteHomologyType_chart_iff (X := TopCat.of M)
    (Y := TopCat.of (EuclideanSpace ℝ (Fin n))) e x he k).mpr
      (finiteHomologyType_localEuclidean_at k n (e x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.finiteHomologyType_localManifold_interior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.finiteHomologyType_localManifold_interior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.finiteHomologyType_localManifold_interior ``Submission.DifferentialGeometry.Homology.finiteHomologyType_localManifold_interior


theorem relativeEulerChar_localManifold_interior :
    relativeEulerChar (TopCat.of M) ({x}ᶜ : Set M) k = (-1 : ℤ) ^ n := by
  let e := (DifferentialGeometry.Manifold.interiorChart I 0 x).toOpenPartialHomeomorph
  have he : x ∈ e.source := (DifferentialGeometry.Manifold.mem_interiorChart_source_iff I 0 x).mpr hx
  exact (relativeEulerChar_chart (X := TopCat.of M)
    (Y := TopCat.of (EuclideanSpace ℝ (Fin n))) e x he k).trans
      (relativeEulerChar_localEuclidean_at k n (e x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.relativeEulerChar_localManifold_interior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.relativeEulerChar_localManifold_interior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.relativeEulerChar_localManifold_interior ``Submission.DifferentialGeometry.Homology.relativeEulerChar_localManifold_interior

end Interior
section Boundary
variable {n : ℕ} [NeZero n] {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M] [T1Space M]
  (x : M) (hx : (𝓡∂ n).IsBoundaryPoint x)
include hx

omit [T1Space M] in
theorem chartAt_boundary_normal_eq_zero :
    ((chartAt (EuclideanHalfSpace n) x) x).val 0 = 0 := by
  rw [ModelWithCorners.isBoundaryPoint_iff,
    frontier_range_modelWithCornersEuclideanHalfSpace] at hx
  exact hx.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.chartAt_boundary_normal_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.chartAt_boundary_normal_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.chartAt_boundary_normal_eq_zero ``Submission.DifferentialGeometry.Homology.chartAt_boundary_normal_eq_zero


theorem finiteHomologyType_localManifold_boundary :
    DifferentialGeometry.HomologicalComplex.finiteHomologyType
      (relativeChainComplex (TopCat.of M) ({x}ᶜ : Set M) (ModuleCat.of k k)) := by
  let : T1Space (EuclideanHalfSpace n) := inferInstanceAs
    (T1Space {v : EuclideanSpace ℝ (Fin n) // 0 ≤ v 0})
  exact (finiteHomologyType_chart_iff (X := TopCat.of M)
    (Y := TopCat.of (EuclideanHalfSpace n)) (chartAt (EuclideanHalfSpace n) x) x
      (mem_chart_source _ x) k).mpr
    (finiteHomologyType_localHalfSpace _ k (chartAt_boundary_normal_eq_zero x hx))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.finiteHomologyType_localManifold_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.finiteHomologyType_localManifold_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.finiteHomologyType_localManifold_boundary ``Submission.DifferentialGeometry.Homology.finiteHomologyType_localManifold_boundary


theorem relativeEulerChar_localManifold_boundary :
    relativeEulerChar (TopCat.of M) ({x}ᶜ : Set M) k = 0 := by
  let : T1Space (EuclideanHalfSpace n) := inferInstanceAs
    (T1Space {v : EuclideanSpace ℝ (Fin n) // 0 ≤ v 0})
  exact (relativeEulerChar_chart (X := TopCat.of M)
    (Y := TopCat.of (EuclideanHalfSpace n)) (chartAt (EuclideanHalfSpace n) x) x
      (mem_chart_source _ x) k).trans
    (relativeEulerChar_localHalfSpace _ k (chartAt_boundary_normal_eq_zero x hx))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.relativeEulerChar_localManifold_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.relativeEulerChar_localManifold_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.relativeEulerChar_localManifold_boundary ``Submission.DifferentialGeometry.Homology.relativeEulerChar_localManifold_boundary

end Boundary
end DifferentialGeometry.Homology
