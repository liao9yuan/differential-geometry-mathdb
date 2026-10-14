import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.ConformalChart
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.ConformalEstimates
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.PositiveCurvature

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.DifferentialGeometry.Geometry.Riemannian _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Analysis
open scoped _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.E3 target :: scope.openDecls } }
private abbrev S2 := Metric.sphere (0 : E3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.S2 target :: scope.openDecls } }

theorem sectionalCurvature_conformalChart_pos (q : S2 × ℝ) (hq : q.2 < 0)
    (u v : E3)
    (hplane : metric.inner (conformalChart q : E3) u u *
      metric.inner (conformalChart q : E3) v v -
      (metric.inner (conformalChart q : E3) u v) ^ 2 ≠ 0) :
    0 < sectionalCurvature metric (conformalChart q : E3) u v := by
  apply sectionalCurvature_pos _ u v hplane
  rw [conformalChart_norm]
  exact conformalRadius_lt_transitionEnd hq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.sectionalCurvature_conformalChart_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.sectionalCurvature_conformalChart_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.sectionalCurvature_conformalChart_pos ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.sectionalCurvature_conformalChart_pos

theorem exists_compatible_end_collar {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧ 2 * A < 1 / 2 ∧
      (∀ q : S2 × ℝ, q.2 ∈ _root_.Set.Ico (-2 * A) 0 → ∀ u v : E3,
        metric.inner (conformalChart q : E3) u u *
          metric.inner (conformalChart q : E3) v v -
          (metric.inner (conformalChart q : E3) u v) ^ 2 ≠ 0 →
        0 < sectionalCurvature metric (conformalChart q : E3) u v) ∧
      (∀ z ∈ _root_.Set.Ioo (-A) 0,
        conformalFactor z < 0 ∧ 0 < deriv conformalFactor z ∧
          deriv (deriv conformalFactor) z < 0 ∧
          max |conformalFactor z| |deriv conformalFactor z| ≤
            ε * (-deriv (deriv conformalFactor) z)) ∧
      intervalDerivativeNorm contDiff_conformalFactor 2 (-A) 0 < ε := by
  obtain ⟨A, hA, hsmall, _, hsigns, hnorm⟩ := exists_conformal_collar hε
  exact ⟨A, hA, hsmall, fun q hq u v hp =>
    sectionalCurvature_conformalChart_pos q hq.2 u v hp, hsigns, hnorm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_compatible_end_collar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_compatible_end_collar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_compatible_end_collar ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_compatible_end_collar

end DifferentialGeometry.PDE.RicciFlow.StandardCap
