import Submission.DifferentialGeometry.Geometry.Curvature.DerivativeIsometry
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CompactDouble
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.DerivativeBounds

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian _root_.Submission.DifferentialGeometry.Topology.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.E3 target :: scope.openDecls } }
private abbrev E4 := EuclideanSpace ℝ (Fin 4)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.E4
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.E4 target :: scope.openDecls } }
private abbrev S3 := Metric.sphere (0 : E4) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.S3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.S3 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE4HAddOfNat : Fact (Module.finrank ℝ E4 = 3 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE4HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE4HAddOfNat target :: scope.openDecls } }

theorem normSq_iterCov_compactDoubleMetric_capMap (north : S3) (R : ℝ)
    (hR : _root_.Max.max transitionEnd 2 + 2 ≤ R) (k : ℕ) (x : E3) (hx : x ∈ Metric.ball 0 (R + 1)) :
    normSq0S (compactDoubleMetric north R hR) (compactDoubleCapMap north R x) (4 + k)
      (iterCov (compactDoubleMetric north R hR) 4 (metricRm04 (compactDoubleMetric north R hR))
        k (compactDoubleCapMap north R x)) =
      normSq0S metric x (4 + k) (iterCov metric 4 (metricRm04 metric) k x) := by
  let U : TopologicalSpace.Opens E3 := ⟨Metric.ball 0 (R + 1), Metric.isOpen_ball⟩
  exact (normSq_iterCov_metricRm04_of_metric_isometry_on_open metric
    (compactDoubleMetric north R hR) U (compactDoubleCapMap north R)
    (contMDiff_compactDoubleCapMap north R).contMDiffOn
    (fun y hy v w => (compactDoubleMetric_cap_pullback north R hR y hy v w).symm) k ⟨x, hx⟩).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.normSq_iterCov_compactDoubleMetric_capMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.normSq_iterCov_compactDoubleMetric_capMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.normSq_iterCov_compactDoubleMetric_capMap ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.normSq_iterCov_compactDoubleMetric_capMap

theorem normSq_iterCov_compactDoubleMetric_antipodal_capMap (north : S3) (R : ℝ)
    (hR : _root_.Max.max transitionEnd 2 + 2 ≤ R) (k : ℕ) (x : E3) (hx : x ∈ Metric.ball 0 (R + 1)) :
    let p := sphereAntipodalDiffeomorph (n := 3) (compactDoubleCapMap north R x)
    normSq0S (compactDoubleMetric north R hR) p (4 + k)
      (iterCov (compactDoubleMetric north R hR) 4 (metricRm04 (compactDoubleMetric north R hR)) k p) =
      normSq0S metric x (4 + k) (iterCov metric 4 (metricRm04 metric) k x) := by
  let U : TopologicalSpace.Opens E3 := ⟨Metric.ball 0 (R + 1), Metric.isOpen_ball⟩
  let F := (sphereAntipodalDiffeomorph (n := 3) : S3 → S3) ∘ compactDoubleCapMap north R
  have hF : ContMDiff (𝓡 3) (𝓡 3) ∞ F :=
    (sphereAntipodalDiffeomorph (n := 3)).contMDiff.comp (contMDiff_compactDoubleCapMap north R)
  exact (normSq_iterCov_metricRm04_of_metric_isometry_on_open metric
    (compactDoubleMetric north R hR) U F hF.contMDiffOn
    (fun y hy v w => (compactDoubleMetric_antipodal_cap_pullback north R hR y hy v w).symm)
    k ⟨x, hx⟩).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.normSq_iterCov_compactDoubleMetric_antipodal_capMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.normSq_iterCov_compactDoubleMetric_antipodal_capMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.normSq_iterCov_compactDoubleMetric_antipodal_capMap ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.normSq_iterCov_compactDoubleMetric_antipodal_capMap

theorem exists_pos_bounds_iterCov_compactDoubleMetric :
    ∃ A : ℕ → ℝ, (∀ k, 0 < A k) ∧
      ∀ (north : S3) (R : ℝ) (hR : _root_.Max.max transitionEnd 2 + 2 ≤ R) (k : ℕ) (p : S3),
        Real.sqrt (normSq0S (compactDoubleMetric north R hR) p (4 + k)
          (iterCov (compactDoubleMetric north R hR) 4
            (metricRm04 (compactDoubleMetric north R hR)) k p)) ≤ A k := by
  choose A hA hbound using exists_pos_bound_iterCov_metricRm04
  refine ⟨A, hA, ?_⟩
  intro north R hR k p
  obtain ⟨x, hx, he | he⟩ := compactDoubleCapMap_cover north R
    (by linarith [le_max_right transitionEnd 2]) p
  · have hh := congrArg Real.sqrt (normSq_iterCov_compactDoubleMetric_capMap north R hR k x hx)
    rw [he] at hh
    exact hh.le.trans (hbound k x)
  · have hh := congrArg Real.sqrt (normSq_iterCov_compactDoubleMetric_antipodal_capMap north R hR k x hx)
    rw [he] at hh
    exact hh.le.trans (hbound k x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_pos_bounds_iterCov_compactDoubleMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_pos_bounds_iterCov_compactDoubleMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_pos_bounds_iterCov_compactDoubleMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_pos_bounds_iterCov_compactDoubleMetric
end DifferentialGeometry.PDE.RicciFlow.StandardCap
