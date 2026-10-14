import Submission.DifferentialGeometry.Topology.ThreeManifold.SphereTwoTimesCircleOrientationClosure
import Submission.DifferentialGeometry.Topology.Manifold.DiffeomorphOrientationDichotomy
import Submission.DifferentialGeometry.Topology.ThreeManifold.SphereTwoTimesCircleLift

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology

universe u

theorem isSphereTwoTimesCircleFactor_of_diffeomorph
    (M : ConnectedClosedOrientedManifold.{u} 3)
    (f : M.Carrier ≃ₘ⟮𝓡 3, (𝓡 2).prod (𝓡 1)⟯ SphereTwoTimesCircle) :
    isSphereTwoTimesCircleFactor M := by
  let F : M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ sphereTwoTimesCircleLift.Carrier :=
    f.trans sphereTwoTimesCircleModelCopy.equiv
  rcases Diffeomorph.preservesOrientation_or_preservesOrientation_opposite F M.orientation
    sphereTwoTimesCircleLiftOrientation with hf | hf
  · exact ⟨F.trans sphereTwoTimesCircleModelCopy.equiv.symm,
      Diffeomorph.preservesOrientation_trans hf sphereTwoTimesCircleLift_preservesOrientation⟩
  · obtain ⟨ρ, hρ⟩ := sphereTwoTimesCircleOrientationClosure_holds
    have hG := Diffeomorph.preservesOrientation_trans hf
      (Diffeomorph.preservesOrientation_opposite sphereTwoTimesCircleLift_preservesOrientation)
    exact ⟨(F.trans sphereTwoTimesCircleModelCopy.equiv.symm).trans ρ,
      Diffeomorph.preservesOrientation_trans hG hρ⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isSphereTwoTimesCircleFactor_of_diffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isSphereTwoTimesCircleFactor_of_diffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isSphereTwoTimesCircleFactor_of_diffeomorph ``Submission.DifferentialGeometry.Topology.isSphereTwoTimesCircleFactor_of_diffeomorph

theorem isStandardFactor_of_diffeomorph_sphereTwoTimesCircle
    (M : ConnectedClosedOrientedManifold.{u} 3)
    (f : M.Carrier ≃ₘ⟮𝓡 3, (𝓡 2).prod (𝓡 1)⟯ SphereTwoTimesCircle) :
    isStandardFactor M :=
  isStandardFactor_of_isSphereTwoTimesCircleFactor
    (isSphereTwoTimesCircleFactor_of_diffeomorph M f)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isStandardFactor_of_diffeomorph_sphereTwoTimesCircle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isStandardFactor_of_diffeomorph_sphereTwoTimesCircle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isStandardFactor_of_diffeomorph_sphereTwoTimesCircle ``Submission.DifferentialGeometry.Topology.isStandardFactor_of_diffeomorph_sphereTwoTimesCircle

end DifferentialGeometry.Topology
