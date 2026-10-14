import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.EndTranslations
import Submission.DifferentialGeometry.Geometry.Curvature.LocalIsometry
import Submission.DifferentialGeometry.Tensor.Metric.IsometryNorm
import Submission.DifferentialGeometry.Tensor.Metric.CompactBounds
import Submission.DifferentialGeometry.Topology.SigmaCompactOpen

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian _root_.Submission.DifferentialGeometry.Geometry.Tensor
open _root_.TopologicalSpace
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.E3 target :: scope.openDecls } }

theorem metricRm04_endTranslation (s : ℝ) (x : endTranslationDomain s)
    (v : Fin 4 → TangentSpace (𝓡 3) x) :
    metricRm04 metric (x : E3) v =
      metricRm04 metric (endTranslation s x : E3)
        (fun i => mfderiv (𝓡 3) (𝓡 3) (endTranslation s) x (v i)) := by
  let : SigmaCompactSpace (endTranslationDomain s) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen (𝓡 3) (endTranslationDomain s).isOpen)
  let : SigmaCompactSpace (endTranslationImage s) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen (𝓡 3) (endTranslationImage s).isOpen)
  have h := metricRm04StdAt_of_pullback_on_opens metric metric
    (endTranslationDomain s) (endTranslationImage s) (endTranslation s)
    (endTranslation_metric_inner s) x (v 0) (v 1) (v 2) (v 3)
  have hv : vec4 (I := 𝓡 3) (x := (x : E3)) (v 0) (v 1) (v 2) (v 3) = v := by
    funext i
    fin_cases i <;> rfl
  have hdv : vec4 (I := 𝓡 3) (x := (endTranslation s x : E3))
      (mfderiv (𝓡 3) (𝓡 3) (endTranslation s) x (v 0))
      (mfderiv (𝓡 3) (𝓡 3) (endTranslation s) x (v 1))
      (mfderiv (𝓡 3) (𝓡 3) (endTranslation s) x (v 2))
      (mfderiv (𝓡 3) (𝓡 3) (endTranslation s) x (v 3)) =
      (fun i => mfderiv (𝓡 3) (𝓡 3) (endTranslation s) x (v i)) := by
    funext i
    fin_cases i <;> rfl
  change metricRm04At metric (x : E3) (vec4 (v 0) (v 1) (v 2) (v 3)) =
    metricRm04At metric (endTranslation s x : E3) (vec4
      (mfderiv (𝓡 3) (𝓡 3) (endTranslation s) x (v 0))
      (mfderiv (𝓡 3) (𝓡 3) (endTranslation s) x (v 1))
      (mfderiv (𝓡 3) (𝓡 3) (endTranslation s) x (v 2))
      (mfderiv (𝓡 3) (𝓡 3) (endTranslation s) x (v 3))) at h
  simpa only [metricRm04_apply, hv, hdv] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.metricRm04_endTranslation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.metricRm04_endTranslation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.metricRm04_endTranslation ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.metricRm04_endTranslation

theorem normSq_iterCov_metricRm04_endTranslation (s : ℝ) (k : ℕ)
    (x : endTranslationDomain s) :
    normSq0S metric (x : E3) (4 + k) (iterCov metric 4 (metricRm04 metric) k (x : E3)) =
      normSq0S metric (endTranslation s x : E3) (4 + k)
        (iterCov metric 4 (metricRm04 metric) k (endTranslation s x : E3)) :=
  normSq0S_iterCov_of_metric_isometry_on_opens metric metric
    (endTranslationDomain s) (endTranslationImage s) (endTranslation s)
    (endTranslation_metric_inner s) (metricRm04 metric) (metricRm04 metric)
    (metricRm04_endTranslation s) k x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.normSq_iterCov_metricRm04_endTranslation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.normSq_iterCov_metricRm04_endTranslation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.normSq_iterCov_metricRm04_endTranslation ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.normSq_iterCov_metricRm04_endTranslation

theorem exists_pos_bound_iterCov_metricRm04 (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : E3,
      Real.sqrt (normSq0S metric x (4 + k) (iterCov metric 4 (metricRm04 metric) k x)) ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_pos_bound_iterCov_on_compact metric
    (metricRm04 metric) k (_root_.ProperSpace.isCompact_closedBall (0 : E3) (transitionEnd + 2))
  refine ⟨C, hC, fun x => ?_⟩
  by_cases hx : ‖x‖ ≤ transitionEnd + 2
  · exact hbound x (by simpa only [Metric.mem_closedBall, dist_zero_right] using hx)
  · have hxe : transitionEnd < ‖x‖ := by linarith [lt_of_not_ge hx]
    let s := transitionEnd + 2 - ‖x‖
    let p : endTranslationDomain s := ⟨x, mem_endTranslationDomain_to_fixed_radius hxe⟩
    have heq := normSq_iterCov_metricRm04_endTranslation s k p
    have href : ‖(endTranslation s p : E3)‖ = transitionEnd + 2 :=
      endTranslationDiffeomorph_norm_to_fixed_radius hxe
    have hb := hbound (endTranslation s p : E3)
      (by simpa only [Metric.mem_closedBall, dist_zero_right, href] using (le_refl (transitionEnd + 2)))
    exact (congrArg Real.sqrt heq).le.trans hb

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_pos_bound_iterCov_metricRm04 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_pos_bound_iterCov_metricRm04"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_pos_bound_iterCov_metricRm04 ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_pos_bound_iterCov_metricRm04

end DifferentialGeometry.PDE.RicciFlow.StandardCap
