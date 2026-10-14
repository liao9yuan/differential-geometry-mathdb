import Mathlib.Analysis.Calculus.ContDiff.Operations

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

namespace DifferentialGeometry

variable {𝕜 E F : Type*}
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem iteratedFDeriv_pi
    {ι : Type*} [Fintype ι] {n : WithTop ℕ∞} {f : ι → E → F} {x : E}
    (hf : ∀ i, ContDiffAt 𝕜 n (f i) x) {r : ℕ} (hr : (r : WithTop ℕ∞) ≤ n) :
    iteratedFDeriv 𝕜 r (fun y i => f i y) x =
      ContinuousMultilinearMap.pi (fun i => iteratedFDeriv 𝕜 r (f i) x) := by
  have hpi : ContDiffAt 𝕜 n (fun y i => f i y) x :=
    contDiffAt_pi' (fun i => hf i)
  ext m i
  rw [ContinuousMultilinearMap.pi_apply]
  have hcomp := ContinuousLinearMap.iteratedFDeriv_comp_left
    (ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : ι => F) i) hpi hr
  have hfun :
      (ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : ι => F) i ∘
        fun y (j : ι) => f j y) = f i := rfl
  rw [hfun] at hcomp
  rw [hcomp]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.iteratedFDeriv_pi then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.iteratedFDeriv_pi"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.iteratedFDeriv_pi ``Submission.DifferentialGeometry.iteratedFDeriv_pi

end DifferentialGeometry
