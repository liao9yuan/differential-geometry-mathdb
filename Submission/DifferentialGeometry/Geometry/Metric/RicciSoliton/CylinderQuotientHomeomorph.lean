import Submission.DifferentialGeometry.Topology.ProjectiveSpace.CylinderQuotientSmoothModels
import Submission.DifferentialGeometry.Geometry.Metric.RicciSoliton.CylinderQuotients

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient

theorem exists_homeomorph_orbitQuotient :
    ∃ e : CylinderDiagonalQuotient ≃ₜ DifferentialGeometry.Geometry.CylinderDiagonalQuotient,
      ∀ p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ,
        e (proj p) = DifferentialGeometry.Geometry.cylinderDiagonalQuotientMap p := by
  apply exists_homeomorph DifferentialGeometry.Geometry.cylinderDiagonalQuotientMap
    DifferentialGeometry.Geometry.cylinderDiagonalQuotientMap_isLocalDiffeomorph.contMDiff.continuous
    DifferentialGeometry.Geometry.cylinderDiagonalQuotientMap_isLocalDiffeomorph.isOpenMap
    DifferentialGeometry.Geometry.cylinderDiagonalQuotientMap_surjective
  intro p q
  rw [eq_comm, DifferentialGeometry.Geometry.cylinderDiagonalQuotientMap_eq_iff]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.exists_homeomorph_orbitQuotient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.exists_homeomorph_orbitQuotient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.exists_homeomorph_orbitQuotient ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.exists_homeomorph_orbitQuotient

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient
