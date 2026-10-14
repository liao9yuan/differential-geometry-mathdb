import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelWitness
import Submission.DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper
import Submission.DifferentialGeometry.Geometry.Curvature.Metric.Defs
import Mathlib.Topology.Order.Compact

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem scalarDecay_edist_ne_top [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M) (p x : M) :
    riemannianEDistOf (I := I) g p x ≠ ⊤ := by
  let _ : _root_.Bundle.RiemannianBundle (fun y : M => TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro y v w; rfl⟩⟩
  exact riemannianEDist_ne_top (I := I) p x

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarDecay_edist_ne_top
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarDecay_edist_ne_top target :: scope.openDecls } }

variable [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M] [ConnectedSpace M]

private local instance scalarDecayIsManifoldOne : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarDecayIsManifoldOne
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarDecayIsManifoldOne target :: scope.openDecls } }

theorem exists_compact_exceptional_ball_of_scalar_decay
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete g) (p : M)
    (hdecay : ∀ eps : ℝ, 0 < eps → ∃ D : ℝ, 0 < D ∧
      ∀ x : M, D ≤ (riemannianEDistOf (I := I) g p x).toReal →
        metricScalarAt (I := I) g x ≤ eps)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ D : ℝ, 0 < D ∧ IsCompact (riemannianClosedBallOf (I := I) g p D) ∧
      ∀ x : M, x ∉ riemannianClosedBallOf (I := I) g p D →
        metricScalarAt (I := I) g x ≤ eps := by
  obtain ⟨D, hD, hfar⟩ := hdecay eps heps
  refine ⟨D, hD, hcomplete.closedEBall_isCompact p D, ?_⟩
  intro x hx
  apply hfar x
  by_contra hdist
  apply hx
  change riemannianEDistOf (I := I) g p x ≤ ENNReal.ofReal D
  calc
    riemannianEDistOf (I := I) g p x =
        ENNReal.ofReal ((riemannianEDistOf (I := I) g p x).toReal) :=
      (ENNReal.ofReal_toReal (scalarDecay_edist_ne_top g p x)).symm
    _ ≤ ENNReal.ofReal D := ENNReal.ofReal_le_ofReal (lt_of_not_ge hdist).le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_compact_exceptional_ball_of_scalar_decay then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_compact_exceptional_ball_of_scalar_decay"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_compact_exceptional_ball_of_scalar_decay ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_compact_exceptional_ball_of_scalar_decay

theorem exists_scalar_decay_compact_and_global_bound
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete g) (p : M)
    (hdecay : ∀ eps : ℝ, 0 < eps → ∃ D : ℝ, 0 < D ∧
      ∀ x : M, D ≤ (riemannianEDistOf (I := I) g p x).toReal →
        metricScalarAt (I := I) g x ≤ eps) :
    ∃ D : ℝ, 0 < D ∧ ∃ B : ℝ,
      IsCompact (riemannianClosedBallOf (I := I) g p D) ∧
      (∀ x : M, x ∈ riemannianClosedBallOf (I := I) g p D →
        metricScalarAt (I := I) g x ≤ B) ∧
      (∀ x : M, x ∉ riemannianClosedBallOf (I := I) g p D →
        metricScalarAt (I := I) g x ≤ 1) ∧
      (∀ x : M, metricScalarAt (I := I) g x ≤ _root_.Max.max 1 B) := by
  classical
  obtain ⟨D, hD, hcompact, houtside⟩ :=
    exists_compact_exceptional_ball_of_scalar_decay g hcomplete p hdecay (eps := 1) one_pos
  have hcontinuous : Continuous (fun x : M => metricScalarAt (I := I) g x) :=
    (metricScalar_smooth (I := I) g).continuous
  obtain ⟨B, hB⟩ := hcompact.bddAbove_image hcontinuous.continuousOn
  have hinside (x : M) (hx : x ∈ riemannianClosedBallOf (I := I) g p D) :
      metricScalarAt (I := I) g x ≤ B := hB ⟨x, hx, rfl⟩
  refine ⟨D, hD, B, hcompact, hinside, houtside, ?_⟩
  intro x
  by_cases hx : x ∈ riemannianClosedBallOf (I := I) g p D
  · exact (hinside x hx).trans (le_max_right 1 B)
  · exact (houtside x hx).trans (le_max_left 1 B)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_scalar_decay_compact_and_global_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_scalar_decay_compact_and_global_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_scalar_decay_compact_and_global_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_scalar_decay_compact_and_global_bound

theorem metricScalar_bddAbove_of_decay
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete g) (p : M)
    (hdecay : ∀ eps : ℝ, 0 < eps → ∃ D : ℝ, 0 < D ∧
      ∀ x : M, D ≤ (riemannianEDistOf (I := I) g p x).toReal →
        metricScalarAt (I := I) g x ≤ eps) :
    BddAbove (Set.range (fun x : M => metricScalarAt (I := I) g x)) := by
  obtain ⟨_D, _hD, B, _hcompact, _hinside, _houtside, hglobal⟩ :=
    exists_scalar_decay_compact_and_global_bound g hcomplete p hdecay
  refine ⟨max 1 B, ?_⟩
  rintro y ⟨x, rfl⟩
  exact hglobal x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metricScalar_bddAbove_of_decay then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metricScalar_bddAbove_of_decay"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metricScalar_bddAbove_of_decay ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metricScalar_bddAbove_of_decay

theorem metricScalar_sSup_bounds_of_decay
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete g) (p : M)
    (hscalar : ∀ x : M, 0 ≤ metricScalarAt (I := I) g x)
    (hdecay : ∀ eps : ℝ, 0 < eps → ∃ D : ℝ, 0 < D ∧
      ∀ x : M, D ≤ (riemannianEDistOf (I := I) g p x).toReal →
        metricScalarAt (I := I) g x ≤ eps) :
    0 ≤ _root_.SupSet.sSup (Set.range (fun x : M => metricScalarAt (I := I) g x)) ∧
      ∀ x : M, metricScalarAt (I := I) g x ≤
        sSup (Set.range (fun y : M => metricScalarAt (I := I) g y)) := by
  have hbounded := metricScalar_bddAbove_of_decay g hcomplete p hdecay
  have hupper (x : M) : metricScalarAt (I := I) g x ≤
      sSup (Set.range (fun y : M => metricScalarAt (I := I) g y)) :=
    le_csSup hbounded ⟨x, rfl⟩
  exact ⟨(hscalar p).trans (hupper p), hupper⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metricScalar_sSup_bounds_of_decay then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metricScalar_sSup_bounds_of_decay"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metricScalar_sSup_bounds_of_decay ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metricScalar_sSup_bounds_of_decay

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
