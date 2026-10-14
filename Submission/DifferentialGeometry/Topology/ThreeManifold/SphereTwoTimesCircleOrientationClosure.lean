import Submission.DifferentialGeometry.Topology.Manifold.ProductOrientationCongruence
import Submission.DifferentialGeometry.Topology.Manifold.StereographicAntipodal
import Submission.DifferentialGeometry.Topology.ThreeManifold.PoincareStandardFactorOrientation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Manifold _root_.Submission.Manifold _root_.Metric _root_.Submission.Metric
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology

theorem sphereTwoTimesCircleOrientationClosure_holds : sphereTwoTimesCircleOrientationClosure := by
  let A := Manifold.sphereAntipodalDiffeomorph (E := EuclideanSpace ℝ (Fin 3)) (n := 2)
  let B := Diffeomorph.refl (𝓡 1) (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) ∞
  have hA : A.preservesOrientation (sphereOrientation 2 (by decide)).opposite
      (sphereOrientation 2 (by decide)) := by
    simpa only [ManifoldOrientation.opposite_opposite] using
      Diffeomorph.preservesOrientation_opposite
        sphereAntipodalDiffeomorph_preservesOrientation_opposite
  have hB : B.preservesOrientation (sphereOrientation 1 (by decide))
      (sphereOrientation 1 (by decide)) := Diffeomorph.preservesOrientation_refl _
  have hρ := Diffeomorph.prodCongr_preservesOrientation (I := 𝓡 2) (J := 𝓡 1)
    (I' := 𝓡 2) (J' := 𝓡 1) (m := 2) (n := 1)
    (oM := (sphereOrientation 2 (by decide)).opposite) (oN := sphereOrientation 1 (by decide))
    (oM' := sphereOrientation 2 (by decide)) (oN' := sphereOrientation 1 (by decide))
    (by decide) (by decide) A B hA hB
  rw [← productOrientation_opposite (I := 𝓡 2) (J := 𝓡 1) (by decide) (by decide)
    (sphereOrientation 2 (by decide)) (sphereOrientation 1 (by decide))] at hρ
  exact ⟨A.prodCongr B, hρ⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereTwoTimesCircleOrientationClosure_holds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereTwoTimesCircleOrientationClosure_holds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereTwoTimesCircleOrientationClosure_holds ``Submission.DifferentialGeometry.Topology.sphereTwoTimesCircleOrientationClosure_holds

end DifferentialGeometry.Topology
