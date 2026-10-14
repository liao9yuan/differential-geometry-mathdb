import Submission.DifferentialGeometry.Geometry.Exponential.ChartFlow.Orbit.Basic
import Submission.DifferentialGeometry.Geometry.Exponential.ChartFlow.Coordinates.Chart
import Submission.DifferentialGeometry.Geometry.Exponential.ChartFlow.Coordinates.VectorField
import Submission.DifferentialGeometry.Geometry.Exponential.Defs
import Submission.DifferentialGeometry.Geometry.Exponential.Smoothness.AtZero.VelocitySlice
import Submission.DifferentialGeometry.Geometry.Exponential.Smoothness.AtZero.Representation
import Submission.DifferentialGeometry.Geometry.Exponential.Smoothness.AtZero.ZeroSectionConstancy
import Submission.DifferentialGeometry.Geometry.Geodesic.Flow.ChartPhase

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Function _root_.Filter _root_.Metric _root_.Bundle _root_.Submission.Bundle _root_.Manifold
open scoped _root_.Topology _root_.NNReal _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem

section ChartTargetInterior

variable [I.Boundaryless]

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
private lemma extChartAt_self_mem_interior_target (p : M) :
    extChartAt I p p ∈ interior (extChartAt I p).target := by
  have hsrc : p ∈ (extChartAt I p).source :=
    mem_extChartAt_source (I := I) p
  have htgt : extChartAt I p p ∈ (extChartAt I p).target :=
    (extChartAt I p).map_source hsrc
  exact extChartAt_target_subset_interior_of_boundaryless (I := I) p htgt

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.Exponential.extChartAt_self_mem_interior_target
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.Exponential.extChartAt_self_mem_interior_target target :: scope.openDecls } }

end ChartTargetInterior

section ZeroSectionWitness

variable [I.Boundaryless] [CompleteSpace E]

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_chartFlow_fixed_zero_section_near_zero
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ (Φ : (E × E) × ℝ → E × E) (ρ T T_match : ℝ),
      0 < ρ ∧ 0 < T ∧ 0 < T_match ∧ T_match ≤ T ∧
      ContDiffOn ℝ 1 Φ
        ((Metric.ball ((extChartAt I p p, (0 : E)) : E × E) ρ) ×ˢ
          Set.Ioo (-T) T) ∧
      Φ (((extChartAt I p p, (0 : E)) : E × E), 0) =
        (extChartAt I p p, (0 : E)) ∧
      (∀ t' : ℝ, t' ∈ Set.Ioo (-T_match) T_match →
        Φ (((extChartAt I p p, (0 : E)) : E × E), t') =
          ((extChartAt I p p, (0 : E)) : E × E)) := by
  classical
  set x₀ : E := extChartAt I p p with hx₀_def
  have hx₀_interior : x₀ ∈ interior (extChartAt I p).target :=
    extChartAt_self_mem_interior_target (I := I) p
  obtain ⟨b, r, ε, ρ, T, Φ, hr, hε, hρ_pos, hT_pos, hb_sub, hΦ_local, hcd, hinit⟩ :=
    exists_chartPhase_contDiffOn_isLocalFlow_combined
      (I := I) (M := M) (g := g) (α := p)
      (x₀ := x₀) (v₀ := (0 : E)) hx₀_interior
  have hconst :=
    chartFlow_zero_section_eventually_const (I := I) (g := g) (p := p)
      (Φ := Φ) (b := b) (r := r) (ε := ε) hΦ_local hb_sub hr hε
  rcases Filter.eventually_iff_exists_mem.mp hconst with ⟨U, hU_nhds, hU⟩
  rcases _root_.mem_nhds_iff.mp hU_nhds with ⟨V, hVU, hV_open, hV_mem_zero⟩
  rcases (Metric.isOpen_iff.mp hV_open) (0 : ℝ) hV_mem_zero with ⟨δ_match, hδ_match_pos, hδ_sub⟩
  set T_match : ℝ := _root_.Min.min δ_match T with hT_match_def
  have hT_match_pos : 0 < T_match := by
    exact lt_min hδ_match_pos hT_pos
  have hT_match_le : T_match ≤ T := min_le_right _ _
  refine ⟨Φ, ρ, T, T_match, hρ_pos, hT_pos, hT_match_pos, hT_match_le,
    hcd, hinit, ?_⟩
  intro t' ht'
  have hT_match_le_δ : T_match ≤ δ_match := min_le_left _ _
  have ht'_in_V : t' ∈ V := by
    apply hδ_sub
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    refine ⟨?_, ?_⟩
    · have h1 : -T_match < t' := ht'.1
      linarith
    · have h2 : t' < T_match := ht'.2
      linarith
  exact hU _ (hVU ht'_in_V)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Exponential.exists_chartFlow_fixed_zero_section_near_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Exponential.exists_chartFlow_fixed_zero_section_near_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Exponential.exists_chartFlow_fixed_zero_section_near_zero ``Submission.DifferentialGeometry.Geometry.Riemannian.Exponential.exists_chartFlow_fixed_zero_section_near_zero

end ZeroSectionWitness

section HasMatchData

variable [I.Boundaryless] [CompleteSpace E]
  [T2Space (TangentBundle I M)]

def HasChartFlowGeodesicMatchAtZero (g : SmoothRiemannianMetric I M) (p : M) : Prop :=
  ∃ (Φ : (E × E) × ℝ → E × E) (ρ T t' ρ' : ℝ),
    0 < ρ ∧ 0 < T ∧ 0 < t' ∧ t' ∈ Set.Ioo (-T) T ∧ 0 < ρ' ∧
    ContDiffOn ℝ 1 Φ
      ((Metric.ball ((extChartAt I p p, (0 : E)) : E × E) ρ) ×ˢ
        Set.Ioo (-T) T) ∧
    (Φ (((extChartAt I p p, (0 : E)) : E × E), t')).1 ∈
      (extChartAt I p).target ∧
    (extChartAt I p).symm
      (Φ (((extChartAt I p p, (0 : E)) : E × E), t')).1 = p ∧
    ChartFlowGeodesicMatchAt (I := I) g p Φ t' ρ'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Exponential.HasChartFlowGeodesicMatchAtZero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Exponential.HasChartFlowGeodesicMatchAtZero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Exponential.HasChartFlowGeodesicMatchAtZero ``Submission.DifferentialGeometry.Geometry.Riemannian.Exponential.HasChartFlowGeodesicMatchAtZero

end HasMatchData

section ReductionToMatch

variable [I.Boundaryless] [CompleteSpace E]
  [T2Space (TangentBundle I M)]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E]
    [T2Space (TangentBundle I M)] in
theorem hasChartFlowGeodesicMatchAtZero_of_eventually_fixed
    (g : SmoothRiemannianMetric I M) (p : M)
    (h : ∃ (Φ : (E × E) × ℝ → E × E) (ρ T T_match t' ρ' : ℝ),
      0 < ρ ∧ 0 < T ∧ 0 < T_match ∧ T_match ≤ T ∧
      0 < t' ∧ 0 < ρ' ∧ t' < T_match ∧
      ContDiffOn ℝ 1 Φ
        ((Metric.ball ((extChartAt I p p, (0 : E)) : E × E) ρ) ×ˢ
          Set.Ioo (-T) T) ∧
      Φ (((extChartAt I p p, (0 : E)) : E × E), 0) =
        (extChartAt I p p, (0 : E)) ∧
      (∀ s : ℝ, s ∈ Set.Ioo (-T_match) T_match →
        Φ (((extChartAt I p p, (0 : E)) : E × E), s) =
          ((extChartAt I p p, (0 : E)) : E × E)) ∧
      ChartFlowGeodesicMatchAt (I := I) g p Φ t' ρ') :
    HasChartFlowGeodesicMatchAtZero (I := I) g p := by
  classical
  obtain ⟨Φ, ρ, T, T_match, t', ρ', hρ, hT, hT_match, hT_match_le, ht'_pos, hρ'_pos,
    ht'_lt, hcd, _hinit, hconst, hmatch⟩ := h
  have ht'_in_match : t' ∈ Set.Ioo (-T_match) T_match := by
    refine ⟨?_, ht'_lt⟩
    linarith
  have hval0 : Φ (((extChartAt I p p, (0 : E)) : E × E), t') =
      ((extChartAt I p p, (0 : E)) : E × E) := hconst t' ht'_in_match
  have hval0_fst : (Φ (((extChartAt I p p, (0 : E)) : E × E), t')).1 =
      extChartAt I p p := by
    rw [hval0]
  have hx₀_source : p ∈ (extChartAt I p).source :=
    mem_extChartAt_source (I := I) p
  have hx₀_target : extChartAt I p p ∈ (extChartAt I p).target :=
    (extChartAt I p).map_source hx₀_source
  have hval_target : (Φ (((extChartAt I p p, (0 : E)) : E × E), t')).1 ∈
      (extChartAt I p).target := by
    rw [hval0_fst]; exact hx₀_target
  have hval_symm : (extChartAt I p).symm
      (Φ (((extChartAt I p p, (0 : E)) : E × E), t')).1 = p := by
    rw [hval0_fst]
    exact (extChartAt I p).left_inv hx₀_source
  have ht'_in : t' ∈ Set.Ioo (-T) T := by
    refine ⟨?_, ?_⟩
    · linarith
    · linarith [ht'_lt]
  exact ⟨Φ, ρ, T, t', ρ', hρ, hT, ht'_pos, ht'_in, hρ'_pos,
    hcd, hval_target, hval_symm, hmatch⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Exponential.hasChartFlowGeodesicMatchAtZero_of_eventually_fixed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Exponential.hasChartFlowGeodesicMatchAtZero_of_eventually_fixed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Exponential.hasChartFlowGeodesicMatchAtZero_of_eventually_fixed ``Submission.DifferentialGeometry.Geometry.Riemannian.Exponential.hasChartFlowGeodesicMatchAtZero_of_eventually_fixed

end ReductionToMatch

section Headline

variable [I.Boundaryless] [CompleteSpace E]
  [T2Space (TangentBundle I M)]

omit [T2Space (TangentBundle I M)] in
omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
theorem expMap_contMDiffAt_zero_of_match_at_zero
    (g : SmoothRiemannianMetric I M) (p : M)
    (h : HasChartFlowGeodesicMatchAtZero (I := I) g p) :
    ContMDiffAt 𝓘(ℝ, E) I 1
      (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M))
      (0 : E) :=
  expMap_contMDiffAt_zero_of_chartFlowGeodesicMatch
    (I := I) (g := g) (p := p) h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Exponential.expMap_contMDiffAt_zero_of_match_at_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Exponential.expMap_contMDiffAt_zero_of_match_at_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Exponential.expMap_contMDiffAt_zero_of_match_at_zero ``Submission.DifferentialGeometry.Geometry.Riemannian.Exponential.expMap_contMDiffAt_zero_of_match_at_zero

end Headline

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry

end
