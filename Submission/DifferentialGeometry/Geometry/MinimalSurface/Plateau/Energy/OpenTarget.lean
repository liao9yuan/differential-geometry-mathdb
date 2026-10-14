import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.OpenTargetDifferential
import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.MinimizingSequence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section

open _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

theorem riemannianDiskEnergy_restrictOpen
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (N : TopologicalSpace.Opens M) [T2Space N] (q : closedDisk → N) :
    riemannianDiskEnergy (g.restrictOpen N) q =
      riemannianDiskEnergy g (Subtype.val ∘ q) := by
  unfold riemannianDiskEnergy
  apply _root_.MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall fun z => diskMapEnergyDensity_restrictOpen g N _ z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianDiskEnergy_restrictOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianDiskEnergy_restrictOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianDiskEnergy_restrictOpen ``Submission.DifferentialGeometry.Geometry.riemannianDiskEnergy_restrictOpen

end DifferentialGeometry.Geometry

end

end
