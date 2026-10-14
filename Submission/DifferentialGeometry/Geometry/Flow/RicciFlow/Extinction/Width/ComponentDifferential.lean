import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.ComponentDisk

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology
open _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
    [T2Space Q]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ Q] [T2Space Q] in
theorem differential_subtypeVal (U : TopologicalSpace.Opens Q)
    (v : SmoothDisk (I := I) (Q := U)) (u : SmoothDisk (I := I) (Q := Q))
    (hmap : ∀ z, u.map z = (v.map z : Q)) (z : Disk) (X : ℂ) :
    (v.differential z X : E) = (u.differential z X : E) := by
  have hext : diskExtension u.map = Subtype.val ∘ diskExtension v.map := by
    rw [show (u.map : Disk → Q) = (fun z => (v.map z : Q)) from funext hmap]
    exact diskExtension_subtypeVal U v.map
  have hv : MDifferentiableWithinAt 𝓘(ℝ, ℂ) I (diskExtension v.map)
      (Metric.closedBall (0 : ℂ) 1) (z : ℂ) :=
    (v.contMDiffOn_extension z z.2).mdifferentiableWithinAt (by simp)
  have hd := mfderivWithin_subtypeVal U (diskExtension v.map)
    (Metric.closedBall (0 : ℂ) 1) (z : ℂ) hv
    (disk_uniqueDiffWithinAt z).uniqueMDiffWithinAt
  change mfderivWithin 𝓘(ℝ, ℂ) I (diskExtension v.map)
      (Metric.closedBall (0 : ℂ) 1) (z : ℂ) X =
    mfderivWithin 𝓘(ℝ, ℂ) I (diskExtension u.map)
      (Metric.closedBall (0 : ℂ) 1) (z : ℂ) X
  rw [hext, hd]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.differential_subtypeVal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.differential_subtypeVal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.differential_subtypeVal ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.differential_subtypeVal


theorem conformal_subtypeVal (g : SmoothRiemannianMetric I Q)
    (U : TopologicalSpace.Opens Q)
    (v : SmoothDisk (I := I) (Q := U)) (u : SmoothDisk (I := I) (Q := Q))
    (hmap : ∀ z, u.map z = (v.map z : Q)) :
    letI : IsManifold I ∞ U := { U.instHasGroupoid (contDiffGroupoid ∞ I) with }
    v.IsConformal (g.restrictOpen U) ↔ u.IsConformal g := by
  let : IsManifold I ∞ U := { U.instHasGroupoid (contDiffGroupoid ∞ I) with }
  have hd := differential_subtypeVal U v u hmap
  unfold SmoothDisk.IsConformal
  have hi (z : Disk) (X Y : ℂ) :
      (g.restrictOpen U).inner (v.map z) (v.differential z X) (v.differential z Y) =
      g.inner (u.map z) (u.differential z X) (u.differential z Y) := by
    change g.inner (v.map z : Q) (v.differential z X) (v.differential z Y) = _
    rw [hd z X, hd z Y, hmap z]
  simp only [hi]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.conformal_subtypeVal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.conformal_subtypeVal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.conformal_subtypeVal ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.conformal_subtypeVal

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width
