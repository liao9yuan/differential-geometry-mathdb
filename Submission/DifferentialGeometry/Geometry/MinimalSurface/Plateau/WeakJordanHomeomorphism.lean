import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.MorreyDisk
import Submission.DifferentialGeometry.Topology.LoopSpace.HomeomorphismOrientation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section

open _root_.Submission.DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry

theorem isWeaklyMonotoneOnce_homeomorph (e : loopCircle ≃ₜ loopCircle) :
    IsWeaklyMonotoneOnce (⟨e, e.continuous⟩ : C(loopCircle, loopCircle)) := by
  rcases circleHomeomorph_affineLift_or_neg e with ⟨F, hp, hm, he⟩ | ⟨F, hp, hm, he⟩
  · refine ⟨F, F.continuous, ?_, Or.inl ⟨hm.monotone, hp⟩⟩
    intro t
    exact (he (t : loopCircle)).symm
  · refine ⟨fun t => -F t, F.continuous.neg, ?_, Or.inr ⟨hm.monotone.neg, ?_⟩⟩
    · intro t
      change ((-F t : ℝ) : loopCircle) = e (t : loopCircle)
      rw [QuotientAddGroup.mk_neg, he, affineCircleMap_coe]
    · intro t
      change -F (t + 1) = -F t - 1
      rw [hp]
      ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.isWeaklyMonotoneOnce_homeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.isWeaklyMonotoneOnce_homeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.isWeaklyMonotoneOnce_homeomorph ``Submission.DifferentialGeometry.Geometry.isWeaklyMonotoneOnce_homeomorph

end DifferentialGeometry.Geometry

end

end
