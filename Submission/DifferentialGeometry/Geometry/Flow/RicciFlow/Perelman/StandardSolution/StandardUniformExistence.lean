import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardUniformRestart
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardMaximalExtension
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.UniformLifetime

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.ENNReal
namespace DifferentialGeometry.PDE.RicciFlow
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.E3 target :: scope.openDecls } }
private abbrev E4 := EuclideanSpace ℝ (Fin 4)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.E4
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.E4 target :: scope.openDecls } }
private abbrev S3 := Metric.sphere (0 : E4) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.S3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.S3 target :: scope.openDecls } }

theorem standard_solution_nonempty : Nonempty StandardSolution := by
  obtain ⟨τ, hτ, K, hK, hseeds⟩ := exists_uniform_partial_standard_solution
  let north : S3 := ⟨EuclideanSpace.single 0 1, by simp⟩
  obtain ⟨S, _⟩ := hseeds north
  obtain ⟨U, _⟩ := S.exists_maximal_extension
  exact ⟨U⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.standard_solution_nonempty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.standard_solution_nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.standard_solution_nonempty ``Submission.DifferentialGeometry.PDE.RicciFlow.standard_solution_nonempty

theorem standard_uniform_initial_window :
    ∃ α : ℝ, 0 < α ∧ ∃ K : ℝ, 0 < K ∧
      (∀ S : StandardSolution, ENNReal.ofReal α < S.val.lifetime) ∧
      ∀ S : StandardSolution, ∀ t ∈ _root_.Set.Icc 0 α, ∀ x : E3,
        Real.sqrt (normSq0S (S.val.metric t) x 4 (metricRm04 (S.val.metric t) x)) ≤ K := by
  obtain ⟨a, ha, τ, hτ, KR, hKR, hrestart⟩ := standard_uniform_closed_restart_extension
  obtain ⟨b, hb, K, hK, hcurv⟩ := standard_uniform_initial_curvature_control
  let α := _root_.Min.min a b
  have hα : 0 < α := lt_min ha hb
  have hlife (S : StandardSolution) : ENNReal.ofReal α < S.val.lifetime := by
    by_contra hn
    have hle : S.val.lifetime ≤ ENNReal.ofReal α := le_of_not_gt hn
    have htop : S.val.lifetime ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
    let T := S.val.lifetime.toReal
    have hT : 0 < T := ENNReal.toReal_pos S.val.lifetime_pos.ne' htop
    have htime : S.val.lifetime = ENNReal.ofReal T := (ENNReal.ofReal_toReal htop).symm
    have hTa : T ≤ a := by
      rw [htime] at hle
      exact ((ENNReal.ofReal_le_ofReal_iff hα.le).mp hle).trans (min_le_left a b)
    obtain ⟨G, H, Q, _, _, _, _, hext, hstrict, _, _⟩ := hrestart S.val T hT hTa htime
    exact (not_le_of_gt hstrict) (S.property Q hext).1
  refine ⟨α, hα, K, hK, hlife, ?_⟩
  intro S t ht x
  exact hcurv S.val α hα.le (min_le_right a b) (hlife S) t ht x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.standard_uniform_initial_window then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.standard_uniform_initial_window"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.standard_uniform_initial_window ``Submission.DifferentialGeometry.PDE.RicciFlow.standard_uniform_initial_window

theorem exists_uniform_standard_lifetime : ∃ α : ℝ, IsUniformStandardLifetime α := by
  obtain ⟨α, hα, K, hK, hlife, hcurv⟩ := standard_uniform_initial_window
  refine ⟨α, hα, ?_⟩
  intro θ hθ hθα
  refine ⟨fun S => (ENNReal.ofReal_le_ofReal hθα.le).trans_lt (hlife S), K, hK.le, ?_⟩
  intro S t ht x
  exact hcurv S t ⟨ht.1, ht.2.trans hθα.le⟩ x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.exists_uniform_standard_lifetime then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.exists_uniform_standard_lifetime"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.exists_uniform_standard_lifetime ``Submission.DifferentialGeometry.PDE.RicciFlow.exists_uniform_standard_lifetime

theorem uniformStandardLifetime_pos : 0 < uniformStandardLifetime :=
  uniformStandardLifetime_pos_iff.mpr exists_uniform_standard_lifetime

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.uniformStandardLifetime_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.uniformStandardLifetime_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.uniformStandardLifetime_pos ``Submission.DifferentialGeometry.PDE.RicciFlow.uniformStandardLifetime_pos

theorem standard_solution_existence :
    Nonempty StandardSolution ∧ 0 < uniformStandardLifetime :=
  ⟨standard_solution_nonempty, uniformStandardLifetime_pos⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.standard_solution_existence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.standard_solution_existence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.standard_solution_existence ``Submission.DifferentialGeometry.PDE.RicciFlow.standard_solution_existence
end DifferentialGeometry.PDE.RicciFlow
