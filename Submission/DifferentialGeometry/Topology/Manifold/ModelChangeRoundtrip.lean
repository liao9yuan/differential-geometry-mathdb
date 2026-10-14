import Submission.DifferentialGeometry.Topology.Manifold.ModelWithCorners
import Mathlib.Geometry.Manifold.Diffeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.ContDiff

namespace ContinuousLinearEquiv
open _root_.ContinuousLinearEquiv

variable {𝕜 E F H M : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}

open _root_.ContinuousLinearEquiv in
theorem isManifold_transContinuousLinearEquiv_iff (e : E ≃L[𝕜] F) :
    IsManifold (I.transContinuousLinearEquiv e) n M ↔ IsManifold I n M := by
  constructor
  · intro h
    let _ := h
    have hback : IsManifold
        ((I.transContinuousLinearEquiv e).transContinuousLinearEquiv e.symm) n M :=
      inferInstance
    simpa only [ModelWithCorners.transContinuousLinearEquiv_symm] using hback
  · intro h
    let _ := h
    infer_instance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousLinearEquiv.isManifold_transContinuousLinearEquiv_iff then
    throwError "Refusing to shadow existing declaration ContinuousLinearEquiv.isManifold_transContinuousLinearEquiv_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousLinearEquiv.isManifold_transContinuousLinearEquiv_iff ``Submission.ContinuousLinearEquiv.isManifold_transContinuousLinearEquiv_iff

end ContinuousLinearEquiv
