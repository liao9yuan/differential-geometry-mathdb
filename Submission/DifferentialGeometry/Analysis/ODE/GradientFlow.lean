import Submission.DifferentialGeometry.Analysis.ODE.Flow.IntegralCurveTransport
import Submission.DifferentialGeometry.Geometry.Operator.Scalar.Calculus

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Analysis.ODE

open _root_.Submission.DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

theorem hasDerivAt_comp_integralCurve_gradientFun
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (f : M → Real)
    (hf : ContMDiff I (modelWithCornersSelf Real Real) ∞ f)
    {γ : Real → M}
    (hγ : IsMIntegralCurve γ (fun x ↦ gradientFun (I := I) g f x))
    (t : Real) :
    HasDerivAt (f ∘ γ)
      (g.inner (γ t) (gradientFun (I := I) g f (γ t))
        (gradientFun (I := I) g f (γ t))) t := by
  have h := hasDerivAt_df_comp_integralCurve
    (I := I) f hf (fun x ↦ gradientFun (I := I) g f x) hγ t
  change HasDerivAt (f ∘ γ)
    (mvfderiv (I := I) f (γ t) (gradientFun (I := I) g f (γ t))) t at h
  convert h using 1
  exact inner_gradientFun (I := I) g f (γ t)
    (gradientFun (I := I) g f (γ t))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.hasDerivAt_comp_integralCurve_gradientFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.hasDerivAt_comp_integralCurve_gradientFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.hasDerivAt_comp_integralCurve_gradientFun ``Submission.DifferentialGeometry.Analysis.ODE.hasDerivAt_comp_integralCurve_gradientFun

end DifferentialGeometry.Analysis.ODE
