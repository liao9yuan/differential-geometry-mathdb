import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CostEndpoint
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.NoAdmissibleCurve
import Mathlib.Topology.Compactness.Compact
import Mathlib.Algebra.Order.BigOperators.Group.Finset

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.Set
open _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.Submission.Topology _root_.Submission.DifferentialGeometry.Topology _root_.BigOperators

namespace DifferentialGeometry.PDE.RicciFlow

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

theorem lCost_locally_bddAbove_of_rm
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (K T tau : ℝ) (htau : 0 < tau)
    (hreg : _root_.Set.Icc (T - tau) T ⊆ D.regular)
    (hRm : ∀ t ∈ _root_.Set.Icc (T - tau) T, ∀ q : M,
      normSq0S (I := I) (S.base.metric t) q 4
        (S.base.rm04 t q) ≤ K)
    (x y : M) :
    ∃ A : ℝ, ∀ᶠ q in 𝓝 y, lCost S T x q tau < A := by
  classical
  let b : ℝ := Real.sqrt tau
  have hb : 0 < b := Real.sqrt_pos.2 htau
  have hb2 : b ^ 2 = tau := Real.sq_sqrt htau.le
  have hregSq : _root_.Set.Icc (T - b ^ 2) T ⊆ D.regular := by
    simpa only [hb2] using hreg
  have hclock : ∀ s ∈ _root_.Set.Icc (0 : ℝ) b,
      T - s ^ 2 ∈ D.regular := by
    intro s hs
    apply hregSq
    have hs2 : s ^ 2 ≤ b ^ 2 :=
      (sq_le_sq₀ hs.1 hb.le).2 hs.2
    exact ⟨sub_le_sub_left hs2 T, sub_le_self T (sq_nonneg s)⟩
  by_cases hreach : ∃ alpha : ℝ → M,
      ContMDiff (modelWithCornersSelf ℝ ℝ) I 1 alpha ∧
        alpha 0 = x ∧ alpha b = y
  · obtain ⟨alpha, halpha, hstart, hend⟩ := hreach
    refine ⟨lRegularizedAction S T alpha 0 b + 1, ?_⟩
    exact lCost_lt_event_of_rm (I := I) S hS K T tau htau
      hreg hRm x y alpha halpha hstart hend
      (lRegularizedAction S T alpha 0 b + 1)
      (lt_add_one (lRegularizedAction S T alpha 0 b))
  · have hnoChart : ¬ ∃ alpha : ℝ → M,
        ContMDiff (modelWithCornersSelf ℝ ℝ) I 1 alpha ∧
          alpha 0 = x ∧
          alpha b = (extChartAt I y).symm (extChartAt I y y) := by
      simpa only [(extChartAt I y).left_inv
        (mem_extChartAt_source (I := I) y)] using hreach
    obtain ⟨ε, hε, hnoBall⟩ :=
      lNoCurve_nhds (I := I) S hS T x b hb hclock y
        (q0 := extChartAt I y y)
        (mem_extChartAt_target (I := I) y) hnoChart
    have hball : ∀ᶠ q in 𝓝 y,
        extChartAt I y q ∈ Metric.ball (extChartAt I y y) ε :=
      (continuousAt_extChartAt (I := I) y).preimage_mem_nhds
        (Metric.ball_mem_nhds _ hε)
    refine ⟨1, ?_⟩
    filter_upwards [extChartAt_source_mem_nhds (I := I) y, hball]
      with q hqsource hqball
    have hnoq : ¬ ∃ alpha : ℝ → M,
        ContMDiff (modelWithCornersSelf ℝ ℝ) I 1 alpha ∧
          alpha 0 = x ∧ alpha b = q := by
      simpa only [(extChartAt I y).left_inv hqsource] using
        hnoBall (extChartAt I y q) hqball
    have hzero : lCost S T x q tau = 0 := by
      simpa only [hb2] using
        lCost_zero_no_curve (I := I) S T x q b hb hnoq
    rw [hzero]
    norm_num

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.lCost_locally_bddAbove_of_rm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.lCost_locally_bddAbove_of_rm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.lCost_locally_bddAbove_of_rm ``Submission.DifferentialGeometry.PDE.RicciFlow.lCost_locally_bddAbove_of_rm

theorem lCost_bddAbove_on_compact_of_rm
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (K T tau : ℝ) (htau : 0 < tau)
    (hreg : _root_.Set.Icc (T - tau) T ⊆ D.regular)
    (hRm : ∀ t ∈ _root_.Set.Icc (T - tau) T, ∀ q : M,
      normSq0S (I := I) (S.base.metric t) q 4
        (S.base.rm04 t q) ≤ K)
    (x : M) {Cpt : Set M} (hCpt : IsCompact Cpt) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ y ∈ Cpt, lCost S T x y tau ≤ A := by
  classical
  have hlocal (y : M) : ∃ U : Set M,
      IsOpen U ∧ y ∈ U ∧
        ∃ B : ℝ, ∀ q ∈ U, lCost S T x q tau < B := by
    obtain ⟨B, hB⟩ :=
      lCost_locally_bddAbove_of_rm (I := I) S hS K T tau htau
        hreg hRm x y
    obtain ⟨U, hUsub, hUopen, hyU⟩ := mem_nhds_iff.mp hB
    exact ⟨U, hUopen, hyU, B, fun q hq => hUsub hq⟩
  choose U hUopen hUself B hUbound using hlocal
  obtain ⟨s, hcover⟩ := hCpt.elim_finite_subcover U hUopen
    (fun y _hy => mem_iUnion.mpr ⟨y, hUself y⟩)
  refine ⟨∑ a ∈ s, _root_.Max.max 0 (B a), ?_, ?_⟩
  · exact Finset.sum_nonneg (fun a _ha => le_max_left 0 (B a))
  · intro y hy
    rcases mem_iUnion.mp (hcover hy) with ⟨a, ha⟩
    rcases mem_iUnion.mp ha with ⟨has, hya⟩
    calc
      lCost S T x y tau ≤ B a := (hUbound a y hya).le
      _ ≤ _root_.Max.max 0 (B a) := le_max_right _ _
      _ ≤ ∑ a ∈ s, _root_.Max.max 0 (B a) :=
        Finset.single_le_sum (fun a _ha => le_max_left 0 (B a)) has

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.lCost_bddAbove_on_compact_of_rm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.lCost_bddAbove_on_compact_of_rm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.lCost_bddAbove_on_compact_of_rm ``Submission.DifferentialGeometry.PDE.RicciFlow.lCost_bddAbove_on_compact_of_rm

end DifferentialGeometry.PDE.RicciFlow

end
