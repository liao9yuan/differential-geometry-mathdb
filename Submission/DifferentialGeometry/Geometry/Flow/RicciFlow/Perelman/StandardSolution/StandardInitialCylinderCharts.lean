import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.GrowingInitialCylinderCharts
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardSolution
import Submission.DifferentialGeometry.Geometry.Metric.RoundCylinder

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Filter _root_.Function _root_.TopologicalSpace _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Geometry
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian _root_.Submission.DifferentialGeometry.Geometry.Metric _root_.Submission.DifferentialGeometry.Geometry.Neck
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ENNReal
namespace DifferentialGeometry.PDE.RicciFlow
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.E3 target :: scope.openDecls } }
private abbrev S2 := Metric.sphere (0 : E3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.S2 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }

theorem standard_uniform_initial_cylinder_charts (A : ℝ) (hA : 0 < A) :
    ∃ D : ℝ, 0 < D ∧ ∀ S : DifferentialGeometry.PDE.RicciFlow.StandardSolution, ∀ x : E3,
      D ≤ (riemannianEDistOf (S.val.metric 0) 0 x).toReal →
      ∃ hfit : transitionEnd + (A + 1) ≤ ‖x‖,
        (initialCylinderChart (pointedInitialRotation x) ‖x‖ (A + 1) hfit
          ⟨(spherePoint, 0), by constructor <;> linarith⟩ : E3) = x ∧
        Diffeomorph.pullbackMetricCross
          ((S.val.metric 0).restrictOpen
            (initialCylinderImage (pointedInitialRotation x) ‖x‖ (A + 1) hfit))
          (initialCylinderChart (pointedInitialRotation x) ‖x‖ (A + 1) hfit) =
          (roundCylinderMetric (E := E3) (n := 2)).restrictOpen (openCylinder (A + 1)) := by
  refine ⟨transitionEnd + A + 2, by linarith [transitionEnd_pos], ?_⟩
  intro S x hx
  rw [S.val.initial, distance_zero] at hx
  have hfit : transitionEnd + (A + 1) ≤ ‖x‖ := by linarith
  refine ⟨hfit, initialCylinderChart_center x (A + 1) (by linarith) hfit, ?_⟩
  rw [S.val.initial]
  exact initialCylinderChart_pullback _ _ _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.standard_uniform_initial_cylinder_charts then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.standard_uniform_initial_cylinder_charts"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.standard_uniform_initial_cylinder_charts ``Submission.DifferentialGeometry.PDE.RicciFlow.standard_uniform_initial_cylinder_charts

theorem escaping_initial_centers_exhaust
    (S : ℕ → DifferentialGeometry.PDE.RicciFlow.StandardSolution) (x : ℕ → E3)
    (hescape : _root_.Filter.Tendsto (fun i => (riemannianEDistOf ((S i).val.metric 0) 0 (x i)).toReal)
      _root_.Filter.atTop _root_.Filter.atTop) {K : Set (S2 × ℝ)} (hK : IsCompact K) :
    ∃ L : ℝ, 0 < L ∧ K ⊆ (openCylinder L : Set (S2 × ℝ)) ∧
      ∀ᶠ i in _root_.Filter.atTop, ∃ hfit : transitionEnd + L ≤ ‖x i‖,
        Diffeomorph.pullbackMetricCross
          (((S i).val.metric 0).restrictOpen
            (initialCylinderImage (pointedInitialRotation (x i)) ‖x i‖ L hfit))
          (initialCylinderChart (pointedInitialRotation (x i)) ‖x i‖ L hfit) =
          (roundCylinderMetric (E := E3) (n := 2)).restrictOpen (openCylinder L) := by
  obtain ⟨L, hL, hKL⟩ := compact_subset_openCylinder hK
  refine ⟨L, hL, hKL, ?_⟩
  filter_upwards [hescape.eventually_ge_atTop (transitionEnd + L)] with i hi
  rw [(S i).val.initial, distance_zero] at hi
  refine ⟨hi, ?_⟩
  rw [(S i).val.initial]
  exact initialCylinderChart_pullback _ _ _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.escaping_initial_centers_exhaust then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.escaping_initial_centers_exhaust"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.escaping_initial_centers_exhaust ``Submission.DifferentialGeometry.PDE.RicciFlow.escaping_initial_centers_exhaust

theorem escaping_initial_centers_growing_subsequence
    (S : ℕ → DifferentialGeometry.PDE.RicciFlow.StandardSolution) (x : ℕ → E3)
    (hescape : _root_.Filter.Tendsto (fun i => (riemannianEDistOf ((S i).val.metric 0) 0 (x i)).toReal)
      _root_.Filter.atTop _root_.Filter.atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ k : ℕ,
      ∃ hfit : transitionEnd + ((k : ℝ) + 1) ≤ ‖x (φ k)‖,
        (initialCylinderChart (pointedInitialRotation (x (φ k))) ‖x (φ k)‖
          ((k : ℝ) + 1) hfit
          ⟨(spherePoint, 0), by
            change -((k : ℝ) + 1) < 0 ∧ (0 : ℝ) < (k : ℝ) + 1
            have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
            exact ⟨neg_neg_of_pos hk, hk⟩⟩ : E3) = x (φ k) ∧
        Diffeomorph.pullbackMetricCross
          (((S (φ k)).val.metric 0).restrictOpen
            (initialCylinderImage (pointedInitialRotation (x (φ k))) ‖x (φ k)‖
              ((k : ℝ) + 1) hfit))
          (initialCylinderChart (pointedInitialRotation (x (φ k))) ‖x (φ k)‖
            ((k : ℝ) + 1) hfit) =
          (roundCylinderMetric (E := E3) (n := 2)).restrictOpen
            (openCylinder ((k : ℝ) + 1)) := by
  classical
  have hN : ∀ k : ℕ, ∃ N : ℕ, ∀ i ≥ N,
      transitionEnd + ((k : ℝ) + 1) ≤ ‖x i‖ := by
    intro k
    obtain ⟨N, hN⟩ := eventually_atTop.mp
      (hescape.eventually_ge_atTop (transitionEnd + ((k : ℝ) + 1)))
    refine ⟨N, fun i hi => ?_⟩
    have h := hN i hi
    rwa [(S i).val.initial, distance_zero] at h
  choose N hN using hN
  let φ : ℕ → ℕ := Nat.rec (N 0) (fun k prev => _root_.Max.max (prev + 1) (N (k + 1)))
  have hstep (k : ℕ) : φ k < φ (k + 1) := by
    change φ k < _root_.Max.max (φ k + 1) (N (k + 1))
    exact (Nat.lt_succ_self (φ k)).trans_le (le_max_left _ _)
  have hNφ (k : ℕ) : N k ≤ φ k := by
    cases k with
    | zero => exact le_rfl
    | succ k => exact le_max_right _ _
  refine ⟨φ, strictMono_nat_of_lt_succ hstep, ?_⟩
  intro k
  have hfit := hN k (φ k) (hNφ k)
  refine ⟨hfit, initialCylinderChart_center _ _ (by positivity) hfit, ?_⟩
  rw [(S (φ k)).val.initial]
  exact initialCylinderChart_pullback _ _ _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.escaping_initial_centers_growing_subsequence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.escaping_initial_centers_growing_subsequence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.escaping_initial_centers_growing_subsequence ``Submission.DifferentialGeometry.PDE.RicciFlow.escaping_initial_centers_growing_subsequence

end DifferentialGeometry.PDE.RicciFlow

end
