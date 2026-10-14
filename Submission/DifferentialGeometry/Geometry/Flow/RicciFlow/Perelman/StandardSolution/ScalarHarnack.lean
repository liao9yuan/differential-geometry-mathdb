import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.TraceCorollaries
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardCurvatureOperator
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardSolutionRealization

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Submission.Set _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.ENNReal
namespace DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Tensor0SBundle

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.E3 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instNeZeroNatFinrankRealE3 : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instNeZeroNatFinrankRealE3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instNeZeroNatFinrankRealE3 target :: scope.openDecls } }

private theorem PartialStandardSolution.harnack_curvature_bound
    (S : PartialStandardSolution) :
    ∀ a b : ℝ, _root_.Set.Icc a b ⊆ (lifetimeInterval S.lifetime S.lifetime_pos).regular →
      ∃ C : ℝ, ∀ t ∈ _root_.Set.Icc a b, ∀ x : E3,
        normSq0S (S.metric t) x 4 (metricRm04 (S.metric t) x) ≤ C := by
  intro a b hab
  by_cases h : a ≤ b
  · have hb := (mem_lifetimeInterval_regular S.lifetime S.lifetime_pos b).mp (hab ⟨h, le_rfl⟩)
    obtain ⟨K, _, hK⟩ := S.curvature_bound b hb.1.le hb.2
    refine ⟨K ^ 2, ?_⟩
    intro t ht x
    exact (Real.sqrt_le_iff.mp (hK t
      ⟨((mem_lifetimeInterval_regular S.lifetime S.lifetime_pos t).mp (hab ht)).1.le, ht.2⟩ x)).2
  · refine ⟨0, ?_⟩
    intro t ht
    exact (h (ht.1.trans ht.2)).elim

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.harnack_curvature_bound
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.harnack_curvature_bound target :: scope.openDecls } }

private theorem PartialStandardSolution.scalar_time_mul_le_of_pos
    (S : PartialStandardSolution) {s t : ℝ}
    (hs : 0 < s) (hst : s ≤ t) (ht : t ∈ S.domain) (x : E3) :
    s * metricScalarAt (S.metric s) x ≤ t * metricScalarAt (S.metric t) x := by
  have htime := (mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos t).mp ht
  have hregular : ∀ a : ℝ, 0 < a → a < s →
      Icc a t ⊆ (lifetimeInterval S.lifetime S.lifetime_pos).regular := by
    intro a ha has r hr
    exact (mem_lifetimeInterval_regular S.lifetime S.lifetime_pos r).mpr
      ⟨ha.trans_le hr.1, (ENNReal.ofReal_le_ofReal hr.2).trans_lt htime.2⟩
  have hshift (a : ℝ) (ha : 0 < a) (has : a < s) :
      (s - a) * metricScalarAt (S.metric s) x ≤
        (t - a) * metricScalarAt (S.metric t) x := by
    have hmono := hamilton_scalar_clock_monotoneOn S.toSolutionOn S.isSolutionOn
      (fun r hr => S.complete r ((lifetimeInterval S.lifetime S.lifetime_pos).regular_subset hr))
      S.harnack_curvature_bound
      (fun r hr y => S.curvatureOperator_nonnegative r
        ((lifetimeInterval S.lifetime S.lifetime_pos).regular_subset hr) y)
      has (hregular a ha has) x
    exact hmono ⟨le_rfl, hst⟩ ⟨hst, le_rfl⟩ hst
  have hleft : _root_.Filter.Tendsto
      (fun a : ℝ => (s - a) * metricScalarAt (S.metric s) x)
      (𝓝[>] (0 : ℝ)) (𝓝 (s * metricScalarAt (S.metric s) x)) := by
    have hc : Continuous (fun a : ℝ => (s - a) * metricScalarAt (S.metric s) x) :=
      (continuous_const.sub continuous_id).mul continuous_const
    simpa only [sub_zero] using (hc.continuousAt (x := 0)).continuousWithinAt.tendsto
  have hright : _root_.Filter.Tendsto
      (fun a : ℝ => (t - a) * metricScalarAt (S.metric t) x)
      (𝓝[>] (0 : ℝ)) (𝓝 (t * metricScalarAt (S.metric t) x)) := by
    have hc : Continuous (fun a : ℝ => (t - a) * metricScalarAt (S.metric t) x) :=
      (continuous_const.sub continuous_id).mul continuous_const
    simpa only [sub_zero] using (hc.continuousAt (x := 0)).continuousWithinAt.tendsto
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hs)] with a ha has
  exact hshift a ha has

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.scalar_time_mul_le_of_pos
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.scalar_time_mul_le_of_pos target :: scope.openDecls } }


theorem PartialStandardSolution.scalar_time_mul_le
    (S : PartialStandardSolution) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ∈ S.domain) (x : E3) :
    s * metricScalarAt (S.metric s) x ≤ t * metricScalarAt (S.metric t) x := by
  rcases hs.eq_or_lt with rfl | hs
  · rw [_root_.MulZeroClass.zero_mul]
    exact mul_nonneg hst (metricScalarAt_nonnegative_of_curvatureOperator_nonnegative
      (S.metric t) x (S.curvatureOperator_nonnegative t ht x))
  · exact S.scalar_time_mul_le_of_pos hs hst ht x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.scalar_time_mul_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.scalar_time_mul_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.scalar_time_mul_le ``Submission.DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.scalar_time_mul_le

theorem PartialStandardSolution.scalar_time_mul_monotoneOn
    (S : PartialStandardSolution) (x : E3) :
    MonotoneOn (fun t : ℝ => t * metricScalarAt (S.metric t) x) S.domain := by
  intro s hs t ht hst
  exact S.scalar_time_mul_le
    ((mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos s).mp hs).1 hst ht x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.scalar_time_mul_monotoneOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.scalar_time_mul_monotoneOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.scalar_time_mul_monotoneOn ``Submission.DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.scalar_time_mul_monotoneOn

end DifferentialGeometry.PDE.RicciFlow
