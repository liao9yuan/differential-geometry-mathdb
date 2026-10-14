import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.ChartRamp

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.Submission.Topology _root_.NNReal
namespace DifferentialGeometry.PDE.RicciFlow
variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

theorem lRampAct_slab_of_compact_chart
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : ℝ) (p : M) {A B : ℝ}
    (hreg : ∀ s ∈ _root_.Set.Icc A B, T - s ^ 2 ∈ D.regular)
    {K : Set E} (hKc : IsCompact K)
    (hKchart : K ⊆ interior (extChartAt I p).target) :
    ∃ Cg Cs : ℝ, 0 ≤ Cg ∧ 0 ≤ Cs ∧
      ∀ {a L : ℝ} {y z : E} (hL : 0 < L),
        (∀ r ∈ _root_.Set.Icc (0 : ℝ) L, a + r ∈ _root_.Set.Icc A B) →
        _root_.Set.MapsTo (lChartRamp y z hL.le).toFun (_root_.Set.Icc (0 : ℝ) L) K →
        lChartAction S T a p (lChartRamp y z hL.le) ≤
          (Cg / 2) * (‖z - y‖ ^ 2 / L) + Cs * L := by
  let τ : ℝ → ℝ := fun s => T - s ^ 2
  let J : Set ℝ := τ '' _root_.Set.Icc A B
  have hτc : ContinuousOn τ (_root_.Set.Icc A B) :=
    (continuous_const.sub (continuous_id.pow 2)).continuousOn
  have hJc : IsCompact J := isCompact_Icc.image_of_continuousOn hτc
  have hJreg : J ⊆ D.regular := by
    rintro _ ⟨s, hs, rfl⟩
    exact hreg s hs
  obtain ⟨Cg, hCg⟩ :=
    chartGramOp_bound (I := I) hS.smoothMetric hJreg hJc p hKchart hKc
  let Kman : Set M := (extChartAt I p).symm '' K
  have hKman : IsCompact Kman :=
    hKc.image_of_continuousOn
      ((continuousOn_extChartAt_symm p).mono (hKchart.trans interior_subset))
  let P : ℝ → M → ℝ := fun s x => 2 * s ^ 2 * S.scalar (T - s ^ 2) x
  have hpair : ContinuousOn
      (fun q : ℝ × M => (T - q.1 ^ 2, q.2)) (_root_.Set.Icc A B ×ˢ Kman) :=
    (continuous_const.sub (continuous_fst.pow 2)).continuousOn.prodMk
      continuous_snd.continuousOn
  have hmaps : _root_.Set.MapsTo (fun q : ℝ × M => (T - q.1 ^ 2, q.2))
      (_root_.Set.Icc A B ×ˢ Kman) (D.carrier ×ˢ (_root_.Set.univ : Set M)) := by
    intro q hq
    exact ⟨D.regular_subset (hreg q.1 hq.1), _root_.Set.mem_univ _⟩
  let hSc : ScalarSTContOn (I := I) (M := M) S := ⟨hS.scalarCont⟩
  have hscalar : ContinuousOn
      (fun q : ℝ × M => S.scalar (T - q.1 ^ 2) q.2) (_root_.Set.Icc A B ×ˢ Kman) := by
    simpa only [Function.comp_def] using hSc.scalar_continuousOn.comp hpair hmaps
  have hP : ContinuousOn (fun q : ℝ × M => P q.1 q.2) (_root_.Set.Icc A B ×ˢ Kman) :=
    (continuous_const.mul (continuous_fst.pow 2)).continuousOn.mul hscalar
  obtain ⟨Cs0, hCs0⟩ :=
    (isCompact_Icc.prod hKman).exists_bound_of_continuousOn hP
  let Cs : ℝ := _root_.Max.max Cs0 0
  refine ⟨Cg, Cs, NNReal.coe_nonneg Cg, le_max_right _ _, ?_⟩
  intro a L y z hL htime hrange
  apply lRampAct_bound (I := I) S hS T a p hL
  · intro r hr
    exact hreg (a + r) (htime r hr)
  · intro r hr
    exact hKchart (hrange hr)
  · intro r hr
    exact hCg (T - (a + r) ^ 2, (lChartRamp y z hL.le).toFun r)
      ⟨⟨a + r, htime r hr, rfl⟩, hrange hr⟩
  · intro r hr
    have hpoint : (extChartAt I p).symm ((lChartRamp y z hL.le).toFun r) ∈ Kman :=
      ⟨(lChartRamp y z hL.le).toFun r, hrange hr, rfl⟩
    have hb := hCs0
      (a + r, (extChartAt I p).symm ((lChartRamp y z hL.le).toFun r))
      ⟨htime r hr, hpoint⟩
    rw [Real.norm_eq_abs] at hb
    exact hb.trans (le_max_left Cs0 0)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.lRampAct_slab_of_compact_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.lRampAct_slab_of_compact_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.lRampAct_slab_of_compact_chart ``Submission.DifferentialGeometry.PDE.RicciFlow.lRampAct_slab_of_compact_chart
end DifferentialGeometry.PDE.RicciFlow
