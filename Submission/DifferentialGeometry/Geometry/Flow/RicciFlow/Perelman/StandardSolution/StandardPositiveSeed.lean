import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.RicciRayleigh
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardRayleigh

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.ENNReal
namespace DifferentialGeometry.PDE.RicciFlow
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.E3 target :: scope.openDecls } }

theorem PartialStandardSolution.leastUpperRicciAt_initial_tip
    (S : PartialStandardSolution) :
    leastUpperRicciAt (S.metric 0) (0 : E3) = 1 / 2 := by
  rw [S.initial]
  exact StandardCap.leastUpperRicciAt_zero

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.leastUpperRicciAt_initial_tip then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.leastUpperRicciAt_initial_tip"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.leastUpperRicciAt_initial_tip ``Submission.DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.leastUpperRicciAt_initial_tip

theorem PartialStandardSolution.exists_positive_upperRicci_seed_before
    (S : PartialStandardSolution) (t0 : ℝ)
    (ht0pos : 0 < t0) (ht0 : t0 ∈ S.domain) :
    ∃ a : ℝ, 0 < a ∧ a < t0 ∧ a ∈ S.domain ∧
      ∃ r : ℝ, 0 < r ∧
        ∃ eta : ℝ, 0 < eta ∧
          ∀ x ∈ Metric.closedBall (0 : E3) r,
            eta ≤ leastUpperRicciAt (S.metric a) x := by
  have hzero : (0 : ℝ) ∈ S.domain :=
    (mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos 0).mpr
      ⟨le_rfl, by simpa using S.lifetime_pos⟩
  have hc :=
    S.leastUpperRicciAt_continuousOn
      (0, (0 : E3)) ⟨hzero, _root_.Set.mem_univ _⟩
  obtain ⟨delta, hdelta, hnear⟩ :=
    (Metric.continuousWithinAt_iff.mp hc)
      (1 / 4 : ℝ) (by norm_num)
  let a : ℝ := _root_.Min.min (t0 / 2) (delta / 4)
  have ha : 0 < a := lt_min (half_pos ht0pos) (by positivity)
  have hat0 : a < t0 :=
    (min_le_left (t0 / 2) (delta / 4)).trans_lt
      (half_lt_self ht0pos)
  have hadelta : a ≤ delta / 4 :=
    min_le_right (t0 / 2) (delta / 4)
  have hquarter : delta / 4 < delta := by
    linarith only [hdelta]
  have ht0life :=
    (mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos t0).mp ht0
  have haD : a ∈ S.domain :=
    (mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos a).mpr
      ⟨ha.le,
        (ENNReal.ofReal_le_ofReal hat0.le).trans_lt ht0life.2⟩
  refine ⟨a, ha, hat0, haD, delta / 4, by positivity,
    1 / 4, by norm_num, ?_⟩
  intro x hx
  have hdist : _root_.Dist.dist (a, x) (0, (0 : E3)) < delta := by
    rw [Prod.dist_eq]
    change _root_.Max.max (_root_.Dist.dist a 0) (_root_.Dist.dist x 0) < delta
    refine max_lt_iff.mpr ⟨?_, ?_⟩
    · rw [Real.dist_eq, sub_zero, abs_of_pos ha]
      exact hadelta.trans_lt hquarter
    · exact (Metric.mem_closedBall.mp hx).trans_lt hquarter
  have hclose := hnear (x := (a, x)) ⟨haD, _root_.Set.mem_univ x⟩ hdist
  change _root_.Dist.dist (leastUpperRicciAt (S.metric a) x)
    (leastUpperRicciAt (S.metric 0) (0 : E3)) < (1 / 4 : ℝ) at hclose
  rw [S.leastUpperRicciAt_initial_tip, Real.dist_eq] at hclose
  have hlower := (abs_lt.mp hclose).1
  linarith only [hlower]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.exists_positive_upperRicci_seed_before then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.exists_positive_upperRicci_seed_before"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.exists_positive_upperRicci_seed_before ``Submission.DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.exists_positive_upperRicci_seed_before

end DifferentialGeometry.PDE.RicciFlow
