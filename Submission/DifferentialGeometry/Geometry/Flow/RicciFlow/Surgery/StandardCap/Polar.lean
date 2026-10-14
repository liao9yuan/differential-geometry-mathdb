import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.Metric
import Submission.DifferentialGeometry.Geometry.Metric.PolarCoordinates
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticCap
import Submission.DifferentialGeometry.Geometry.Metric.RoundCylinder

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Geometry
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian _root_.Submission.DifferentialGeometry.Geometry.Metric
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.E3 target :: scope.openDecls } }
private abbrev Sphere2 := Metric.sphere (0 : E3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.Sphere2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.Sphere2 target :: scope.openDecls } }

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }

theorem metric_polar_pullback (q : Sphere2 × ℝ) (hq : 0 < q.2)
    (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ)) q) :
    metric.inner (euclideanPolarMap q)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ)) (𝓡 3) euclideanPolarMap q v)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ)) (𝓡 3) euclideanPolarMap q w) =
      warpingFunction q.2 ^ 2 * (roundMetric (E := E3) (n := 2)).inner q.1 v.1 w.1 +
        v.2 * w.2 := by
  rw [euclideanPolarMap_mfderiv, euclideanPolarMap_mfderiv]
  change metric.inner (q.2 • (q.1 : E3))
    (v.2 • (q.1 : E3) + q.2 • dIncl q.1 v.1)
    (w.2 • (q.1 : E3) + q.2 • dIncl q.1 w.1) = _
  rw [metric_inner_polar (norm_eq_of_mem_sphere q.1)
    (dIncl_orth q.1 v.1) (dIncl_orth q.1 w.1) hq, add_comm]
  exact congrArg (fun t : ℝ => warpingFunction q.2 ^ 2 * t + v.2 * w.2)
    (roundMetric_inner q.1 v.1 w.1).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.metric_polar_pullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.metric_polar_pullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.metric_polar_pullback ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.metric_polar_pullback

theorem metric_polar_pullback_cylindrical (q : Sphere2 × ℝ)
    (hq : transitionEnd ≤ q.2) (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ)) q) :
    metric.inner (euclideanPolarMap q)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ)) (𝓡 3) euclideanPolarMap q v)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ)) (𝓡 3) euclideanPolarMap q w) =
      (roundCylinderMetric (E := E3) (n := 2)).inner q v w := by
  rw [metric_polar_pullback q (transitionEnd_pos.trans_le hq),
    warpingFunction_eq_sqrt_two hq, Real.sq_sqrt (by norm_num),
    roundCylinderMetric_inner]
  exact congrArg (fun t : ℝ => 2 * t + v.2 * w.2) (roundMetric_inner q.1 v.1 w.1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.metric_polar_pullback_cylindrical then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.metric_polar_pullback_cylindrical"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.metric_polar_pullback_cylindrical ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.metric_polar_pullback_cylindrical

end DifferentialGeometry.PDE.RicciFlow.StandardCap
