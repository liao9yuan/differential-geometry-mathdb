import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ScalarDecayCompactControl
import Submission.DifferentialGeometry.Geometry.Curvature.Bounds.RicciUpper
import Mathlib.Analysis.Calculus.Deriv.MeanValue

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology _root_.ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance ancientScalarDecayIsManifoldOne : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientScalarDecayIsManifoldOne
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientScalarDecayIsManifoldOne target :: scope.openDecls } }

variable (S : SolutionOn (I := I) (M := M) ancientTimeInterval)

omit [SigmaCompactSpace M] in
private theorem ancientScalarDecay_derivWithin_nonneg
    (htrace : ∀ t ∈ ancientTimeInterval.carrier, ∀ (x : M) (V : TangentSpace I x),
      0 ≤ derivWithin (fun s : ℝ => S.scalar s x) ancientTimeInterval.carrier t +
        2 * (S.base.metric t).inner x
          (gradientAt (I := I) (flowG (I := I) S) t (S.scalar t) x) V +
        2 * metricRicci (I := I) (M := M) (S.base.metric t) x (vec2 V V))
    {t : ℝ} (ht : t ∈ ancientTimeInterval.carrier) (x : M) :
    0 ≤ derivWithin (fun s : ℝ => S.scalar s x) ancientTimeInterval.carrier t := by
  have h := htrace t ht x (0 : TangentSpace I x)
  have hRicZero : metricRicci (I := I) (M := M) (S.base.metric t) x
      (vec2 (0 : TangentSpace I x) 0) = 0 := by
    exact (metricRicci (I := I) (M := M) (S.base.metric t) x).map_coord_zero
      (i := 0) (by simp [vec2])
  rw [hRicZero] at h
  simpa using h

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientScalarDecay_derivWithin_nonneg
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientScalarDecay_derivWithin_nonneg target :: scope.openDecls } }

omit [SigmaCompactSpace M] in
theorem ancient_scalar_monotoneOn_of_traceHarnack (hS : IsSolutionOn S)
    (htrace : ∀ t ∈ ancientTimeInterval.carrier, ∀ (x : M) (V : TangentSpace I x),
      0 ≤ derivWithin (fun s : ℝ => S.scalar s x) ancientTimeInterval.carrier t +
        2 * (S.base.metric t).inner x
          (gradientAt (I := I) (flowG (I := I) S) t (S.scalar t) x) V +
        2 * metricRicci (I := I) (M := M) (S.base.metric t) x (vec2 V V))
    (x : M) :
    MonotoneOn (fun t : ℝ => S.scalar t x) (Set.Iic 0) := by
  have hmap : Continuous (fun t : ℝ => (t, x)) := continuous_id.prodMk continuous_const
  have hcont : ContinuousOn (fun t : ℝ => S.scalar t x) (Set.Iic 0) := by
    have h := hS.scalarCont.comp hmap.continuousOn
      (fun t (ht : t ∈ Set.Iic (0 : ℝ)) => ⟨ht, Set.mem_univ x⟩)
    simpa only [Function.comp_def] using h
  apply monotoneOn_of_deriv_nonneg (convex_Iic 0) hcont
  · intro t ht
    have htreg : t ∈ ancientTimeInterval.regular := by
      simpa only [ancientTimeInterval_regular, interior_Iic, Set.mem_Iio] using ht
    exact ((hS.scalarTime (K := ancientTimeInterval.carrier)
      (ancientTimeInterval.regular_subset htreg) (fun _ hs => hs) x).differentiableAt
        (ancientTimeInterval.regular_mem_nhds htreg)).differentiableWithinAt
  · intro t ht
    have htreg : t ∈ ancientTimeInterval.regular := by
      simpa only [ancientTimeInterval_regular, interior_Iic, Set.mem_Iio] using ht
    have h := ancientScalarDecay_derivWithin_nonneg S htrace
      (ancientTimeInterval.regular_subset htreg) x
    rw [derivWithin_of_mem_nhds (ancientTimeInterval.regular_mem_nhds htreg)] at h
    exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_scalar_monotoneOn_of_traceHarnack then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_scalar_monotoneOn_of_traceHarnack"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_scalar_monotoneOn_of_traceHarnack ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_scalar_monotoneOn_of_traceHarnack

omit [SigmaCompactSpace M] in
theorem ancient_scalar_slab_le_later_of_traceHarnack (hS : IsSolutionOn S)
    (htrace : ∀ t ∈ ancientTimeInterval.carrier, ∀ (x : M) (V : TangentSpace I x),
      0 ≤ derivWithin (fun s : ℝ => S.scalar s x) ancientTimeInterval.carrier t +
        2 * (S.base.metric t).inner x
          (gradientAt (I := I) (flowG (I := I) S) t (S.scalar t) x) V +
        2 * metricRicci (I := I) (M := M) (S.base.metric t) x (vec2 V V))
    (hcurvature : ∀ t ≤ (0 : ℝ), ∀ x : M,
      metricAlgebraicCurvatureTensorAt (I := I) (M := M) (S.base.metric t) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    {t₁ t₂ : ℝ} (ht₂ : t₂ ≤ 0) {t : ℝ} (ht : t ∈ Set.Icc t₁ t₂) (x : M) :
    0 ≤ S.scalar t x ∧ S.scalar t x ≤ S.scalar t₂ x := by
  have ht0 : t ≤ 0 := ht.2.trans ht₂
  constructor
  · exact metricScalarAt_nonnegative_of_curvatureOperator_nonnegative
      (I := I) (M := M) (S.base.metric t) x (hcurvature t ht0 x)
  · exact ancient_scalar_monotoneOn_of_traceHarnack S hS htrace x ht0 ht₂ ht.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_scalar_slab_le_later_of_traceHarnack then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_scalar_slab_le_later_of_traceHarnack"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_scalar_slab_le_later_of_traceHarnack ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_scalar_slab_le_later_of_traceHarnack

variable [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space (TangentBundle I M)] [ConnectedSpace M]

theorem ancient_scalar_decay_compact_control (hS : IsSolutionOn S)
    (htrace : ∀ t ∈ ancientTimeInterval.carrier, ∀ (x : M) (V : TangentSpace I x),
      0 ≤ derivWithin (fun s : ℝ => S.scalar s x) ancientTimeInterval.carrier t +
        2 * (S.base.metric t).inner x
          (gradientAt (I := I) (flowG (I := I) S) t (S.scalar t) x) V +
        2 * metricRicci (I := I) (M := M) (S.base.metric t) x (vec2 V V))
    (hcurvature : ∀ t ≤ (0 : ℝ), ∀ x : M,
      metricAlgebraicCurvatureTensorAt (I := I) (M := M) (S.base.metric t) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    {t₁ t₂ : ℝ} (ht₂ : t₂ ≤ 0)
    (hcomplete : RiemannianMetricComplete (I := I) (M := M) (S.base.metric t₂))
    (p : M)
    (hdecay : ∀ eps : ℝ, 0 < eps → ∃ D : ℝ, 0 < D ∧
      ∀ x : M, D ≤ (riemannianEDistOf (I := I) (M := M) (S.base.metric t₂) p x).toReal →
        S.scalar t₂ x ≤ eps) :
    ∃ C : ℝ, C = _root_.SupSet.sSup (Set.range (S.scalar t₂)) ∧ 0 ≤ C ∧
      (∀ t ∈ Set.Icc t₁ t₂, ∀ x : M, 0 ≤ S.scalar t x ∧ S.scalar t x ≤ C) ∧
      (∀ eps : ℝ, 0 < eps → ∃ D : ℝ, 0 < D ∧
        IsCompact (riemannianClosedBallOf (I := I) (M := M) (S.base.metric t₂) p D) ∧
        ∀ t ∈ Set.Icc t₁ t₂, ∀ x : M,
          x ∉ riemannianClosedBallOf (I := I) (M := M) (S.base.metric t₂) p D →
            S.scalar t x ≤ eps) := by
  have hdecayMetric : ∀ eps : ℝ, 0 < eps → ∃ D : ℝ, 0 < D ∧
      ∀ x : M, D ≤ (riemannianEDistOf (I := I) (M := M) (S.base.metric t₂) p x).toReal →
        metricScalarAt (I := I) (M := M) (S.base.metric t₂) x ≤ eps := hdecay
  have hscalar : ∀ x : M, 0 ≤ metricScalarAt (I := I) (M := M) (S.base.metric t₂) x := by
    intro x
    exact metricScalarAt_nonnegative_of_curvatureOperator_nonnegative
      (I := I) (M := M) (S.base.metric t₂) x (hcurvature t₂ ht₂ x)
  have hsup := metricScalar_sSup_bounds_of_decay
    (I := I) (M := M) (S.base.metric t₂) hcomplete p hscalar hdecayMetric
  change 0 ≤ _root_.SupSet.sSup (Set.range (S.scalar t₂)) ∧
    ∀ x : M, S.scalar t₂ x ≤ _root_.SupSet.sSup (Set.range (S.scalar t₂)) at hsup
  refine ⟨sSup (Set.range (S.scalar t₂)), rfl, hsup.1, ?_, ?_⟩
  · intro t ht x
    have hslab := ancient_scalar_slab_le_later_of_traceHarnack S hS htrace hcurvature ht₂ ht x
    exact ⟨hslab.1, hslab.2.trans (hsup.2 x)⟩
  · intro eps heps
    obtain ⟨D, hD, hcompact, houtside⟩ := exists_compact_exceptional_ball_of_scalar_decay
      (I := I) (M := M) (S.base.metric t₂) hcomplete p hdecayMetric heps
    refine ⟨D, hD, hcompact, ?_⟩
    intro t ht x hx
    have hslab := ancient_scalar_slab_le_later_of_traceHarnack S hS htrace hcurvature ht₂ ht x
    exact hslab.2.trans (houtside x hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_scalar_decay_compact_control then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_scalar_decay_compact_control"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_scalar_decay_compact_control ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_scalar_decay_compact_control

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
