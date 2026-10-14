import Submission.DifferentialGeometry.Geometry.Connection.ParallelTransport.Derivative.CovariantDerivativeAlong
import Mathlib.Geometry.Manifold.VectorBundle.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Function _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Filter
open scoped _root_.Topology _root_.ContDiff _root_.Bundle _root_.Submission.Bundle _root_.Manifold

namespace DifferentialGeometry.Geometry

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

set_option backward.isDefEq.respectTransparency false in



theorem contDiffAt_chartRepAt_of_section
    {γ : ℝ → M} {V : ∀ t, TangentSpace 𝓘(ℝ, E) (γ t)} {t : ℝ} {n : WithTop ℕ∞}
    (hV : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) n
      (fun s => TotalSpace.mk' E (γ s) (V s)) t) :
    ContDiffAt ℝ n (chartRepAt γ V t) t := by
  have hs := contMDiffAt_totalSpace.mp hV
  have hb : γ t ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace 𝓘(ℝ, E)) (γ t)).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace 𝓘(ℝ, E)) (γ t)
  have heq : chartRepAt γ V t =ᶠ[𝓝 t]
      (fun s => (_root_.FiberBundle.trivializationAt E (TangentSpace 𝓘(ℝ, E)) (γ t)
        (TotalSpace.mk' E (γ s) (V s))).2) := by
    filter_upwards [hs.1.continuousAt
      ((_root_.FiberBundle.trivializationAt E (TangentSpace 𝓘(ℝ, E)) (γ t)).open_baseSet.mem_nhds hb)] with s hmem
    rw [chartRepAt_apply,
      (_root_.FiberBundle.trivializationAt E (TangentSpace 𝓘(ℝ, E)) (γ t)).continuousLinearMapAt_apply (R := ℝ),
      (_root_.FiberBundle.trivializationAt E (TangentSpace 𝓘(ℝ, E)) (γ t)).coe_linearMapAt_of_mem hmem]
  exact hs.2.contDiffAt.congr_of_eventuallyEq heq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.contDiffAt_chartRepAt_of_section then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.contDiffAt_chartRepAt_of_section"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.contDiffAt_chartRepAt_of_section ``Submission.DifferentialGeometry.Geometry.contDiffAt_chartRepAt_of_section

end DifferentialGeometry.Geometry
