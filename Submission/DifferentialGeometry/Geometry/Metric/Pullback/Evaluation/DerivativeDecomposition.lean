import Submission.DifferentialGeometry.Geometry.Metric.Pullback.Evaluation.Derivative
import Submission.DifferentialGeometry.Tensor.RSTensor.Defs
import Mathlib.Geometry.Manifold.MFDeriv.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.PDE.RicciFlow.Pullback

open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [SigmaCompactSpace M]
    [T2Space M] [BoundarylessManifold I M] in
theorem mfderiv_time_derivative_along_flow
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v : TangentSpace I x)
    {V : ℝ → TangentSpace I (Φ_fam t x)}
    {V' : TangentSpace I (Φ_fam t x)}
    (h_eq : V =ᶠ[nhds t] fun s => mfderiv I I (Φ_fam s : M → M) x v)
    (h_deriv : HasDerivAt V V' t) :
    HasDerivAt (fun s => mfderiv I I (Φ_fam s : M → M) x v) V' t :=
  h_deriv.congr_of_eventuallyEq h_eq.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Pullback.mfderiv_time_derivative_along_flow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Pullback.mfderiv_time_derivative_along_flow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Pullback.mfderiv_time_derivative_along_flow ``Submission.DifferentialGeometry.PDE.RicciFlow.Pullback.mfderiv_time_derivative_along_flow

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] in
theorem pullback_metric_derivative_decomposition
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v w : TangentSpace I x)
    (G' : ℝ)
    (h_G : HasDerivAt
      (fun s : ℝ => (g_fam s).inner (Φ_fam t x)
        (mfderiv I I (Φ_fam t : M → M) x v) (mfderiv I I (Φ_fam t : M → M) x w))
      G' t)
    (A' : ℝ)
    (h_A : HasDerivAt
      (fun s : ℝ => (g_fam t).inner (Φ_fam t x)
        (mfderiv I I (Φ_fam s : M → M) x v) (mfderiv I I (Φ_fam t : M → M) x w))
      A' t)
    (B' : ℝ)
    (h_B : HasDerivAt
      (fun s : ℝ => (g_fam t).inner (Φ_fam t x)
        (mfderiv I I (Φ_fam t : M → M) x v) (mfderiv I I (Φ_fam s : M → M) x w))
      B' t)
    (h_total_eval : HasDerivAt
      (fun s : ℝ => (g_fam s).inner (Φ_fam s x)
        (mfderiv I I (Φ_fam s : M → M) x v)
        (mfderiv I I (Φ_fam s : M → M) x w))
      (G' + A' + B') t) :
    HasDerivAt
      (fun s : ℝ => (Diffeomorph.pullbackMetric (g_fam s) (Φ_fam s)).inner x v w)
      (G' + A' + B') t := by
  let _ := h_G; let _ := h_A; let _ := h_B
  exact pullbackMetric_inner_hasDerivAt_of_eval g_fam Φ_fam x v w h_total_eval

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Pullback.pullback_metric_derivative_decomposition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Pullback.pullback_metric_derivative_decomposition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Pullback.pullback_metric_derivative_decomposition ``Submission.DifferentialGeometry.PDE.RicciFlow.Pullback.pullback_metric_derivative_decomposition

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] in
theorem combine_pullback_derivative_pieces
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v w : TangentSpace I x)
    (G' L' : ℝ)
    (h_chain_eval : HasDerivAt
      (fun s : ℝ => (g_fam s).inner (Φ_fam s x)
        (mfderiv I I (Φ_fam s : M → M) x v)
        (mfderiv I I (Φ_fam s : M → M) x w))
      (G' + L') t) :
    HasDerivAt
      (fun s : ℝ => (Diffeomorph.pullbackMetric (g_fam s) (Φ_fam s)).inner x v w)
      (G' + L') t :=
  pullbackMetric_inner_hasDerivAt_of_eval g_fam Φ_fam x v w h_chain_eval

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Pullback.combine_pullback_derivative_pieces then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Pullback.combine_pullback_derivative_pieces"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Pullback.combine_pullback_derivative_pieces ``Submission.DifferentialGeometry.PDE.RicciFlow.Pullback.combine_pullback_derivative_pieces

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] in
theorem pullback_time_derivative_chain_rule
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v w : TangentSpace I x)
    (G' L' : ℝ)
    (h_chain_eval : HasDerivAt
      (fun s : ℝ => (g_fam s).inner (Φ_fam s x)
        (mfderiv I I (Φ_fam s : M → M) x v)
        (mfderiv I I (Φ_fam s : M → M) x w))
      (G' + L') t) :
    HasDerivAt
      (fun s : ℝ => (Diffeomorph.pullbackMetric (g_fam s) (Φ_fam s)).inner x v w)
      (G' + L') t :=
  combine_pullback_derivative_pieces g_fam Φ_fam t x v w G' L' h_chain_eval

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Pullback.pullback_time_derivative_chain_rule then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Pullback.pullback_time_derivative_chain_rule"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Pullback.pullback_time_derivative_chain_rule ``Submission.DifferentialGeometry.PDE.RicciFlow.Pullback.pullback_time_derivative_chain_rule

end DifferentialGeometry.PDE.RicciFlow.Pullback
