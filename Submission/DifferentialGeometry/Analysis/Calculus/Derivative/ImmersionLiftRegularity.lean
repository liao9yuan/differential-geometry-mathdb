import Submission.DifferentialGeometry.Analysis.Calculus.Inverse.SmoothLocalInverse

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Filter _root_.Function
open scoped _root_.Topology _root_.ContDiff

namespace DifferentialGeometry.Analysis

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]




theorem contDiffAt_lift_of_immersion {f : E → F} {s : Set E} {ψ : G → E} {x : G}
    (hs : IsOpen s) (hf : ContDiffOn ℝ ∞ f s) (hx : ψ x ∈ s)
    (hi : _root_.Function.Injective (fderiv ℝ f (ψ x))) (hψ : ContinuousAt ψ x)
    (hc : ContDiffAt ℝ ∞ (f ∘ ψ) x) : ContDiffAt ℝ ∞ ψ x := by
  obtain ⟨r, U, V, hU, hxU, hV, hxV, _, hr, hleft, _⟩ :=
    exists_smooth_local_leftInverse hs hf hx hi
  have hrx : ContDiffAt ℝ ∞ r (f (ψ x)) :=
    (hr _ hxU).contDiffAt (hU.mem_nhds hxU)
  apply (hrx.comp x hc).congr_of_eventuallyEq
  filter_upwards [hψ (hV.mem_nhds hxV)] with y hy
  exact (hleft (ψ y) hy).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.contDiffAt_lift_of_immersion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.contDiffAt_lift_of_immersion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.contDiffAt_lift_of_immersion ``Submission.DifferentialGeometry.Analysis.contDiffAt_lift_of_immersion

end DifferentialGeometry.Analysis
