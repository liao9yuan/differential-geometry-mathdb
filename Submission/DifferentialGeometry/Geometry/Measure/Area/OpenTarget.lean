import Submission.DifferentialGeometry.Geometry.Measure.Area.Manifold
import Submission.DifferentialGeometry.Topology.Manifold.OpenTarget
import Submission.DifferentialGeometry.Geometry.Metric.Basic
import Submission.DifferentialGeometry.Geometry.Metric.Pullback.PartialDiffeomorph.OpenSubtype

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission








open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry
open scoped _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]



theorem riemannianAreaDensity_restrictOpen
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M) [T2Space U]
    (u : ℂ → U) (z : ℂ) :
    riemannianAreaDensity (g.restrictOpen U) u z =
      riemannianAreaDensity g (Subtype.val ∘ u) z := by
  unfold riemannianAreaDensity
  rw [DifferentialGeometry.Topology.mfderiv_subtypeVal_comp]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianAreaDensity_restrictOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianAreaDensity_restrictOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianAreaDensity_restrictOpen ``Submission.DifferentialGeometry.Geometry.riemannianAreaDensity_restrictOpen



theorem riemannianArea_restrictOpen
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M) [T2Space U]
    (u : ℂ → U) (s : Set ℂ) :
    riemannianArea (g.restrictOpen U) u s = riemannianArea g (Subtype.val ∘ u) s := by
  unfold riemannianArea
  congr 1
  funext z
  exact riemannianAreaDensity_restrictOpen g U u z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianArea_restrictOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianArea_restrictOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianArea_restrictOpen ``Submission.DifferentialGeometry.Geometry.riemannianArea_restrictOpen



theorem riemannianDiskArea_restrictOpen
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M) [T2Space U]
    (u : DifferentialGeometry.Topology.closedDisk → U) :
    riemannianDiskArea (g.restrictOpen U) u = riemannianDiskArea g (Subtype.val ∘ u) :=
  riemannianArea_restrictOpen g U (diskExtension u) _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianDiskArea_restrictOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianDiskArea_restrictOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianDiskArea_restrictOpen ``Submission.DifferentialGeometry.Geometry.riemannianDiskArea_restrictOpen

end DifferentialGeometry.Geometry
