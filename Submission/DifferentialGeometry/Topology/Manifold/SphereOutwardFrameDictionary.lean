import Submission.DifferentialGeometry.Topology.Manifold.SphereOrientation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Manifold _root_.Metric _root_.Module
open scoped _root_.Manifold _root_.ContDiff _root_.InnerProductSpace

namespace DifferentialGeometry

theorem sphereOutwardDeterminant_eq_basisDet_frame (n : ℕ)
    (x : _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    (b : _root_.Module.Basis (Fin n) ℝ (TangentSpace (𝓡 n) x)) :
    sphereOutwardDeterminant n x b =
      ((EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis).det
        (fun j => Fin.cases x (fun k => mfderiv (𝓡 n) (𝓡 (n + 1))
          (fun y : _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 =>
            (y : EuclideanSpace ℝ (Fin (n + 1)))) x (b k)) j) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.sphereOutwardDeterminant_eq_basisDet_frame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.sphereOutwardDeterminant_eq_basisDet_frame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.sphereOutwardDeterminant_eq_basisDet_frame ``Submission.DifferentialGeometry.sphereOutwardDeterminant_eq_basisDet_frame

theorem sphereOutwardFrame_pos_iff_sphereOrientation (n : ℕ) (hn : 1 ≤ n)
    (x : _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    (b : _root_.Module.Basis (Fin n) ℝ (TangentSpace (𝓡 n) x)) :
    0 < ((EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis).det
        (fun j => Fin.cases x (fun k => mfderiv (𝓡 n) (𝓡 (n + 1))
          (fun y : _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 =>
            (y : EuclideanSpace ℝ (Fin (n + 1)))) x (b k)) j) ↔
      b.orientation = (sphereOrientation n hn).orientation x := by
  rw [← sphereOutwardDeterminant_eq_basisDet_frame n x b]
  exact (sphereOrientation_characterization n hn x b).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.sphereOutwardFrame_pos_iff_sphereOrientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.sphereOutwardFrame_pos_iff_sphereOrientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.sphereOutwardFrame_pos_iff_sphereOrientation ``Submission.DifferentialGeometry.sphereOutwardFrame_pos_iff_sphereOrientation

end DifferentialGeometry
