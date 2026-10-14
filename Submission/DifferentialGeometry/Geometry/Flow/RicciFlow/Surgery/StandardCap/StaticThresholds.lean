import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.NormalizedInsertionPinching
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.NormalizedInsertionDerivativeBounds
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.ModelWindow
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CollapseProfile

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.TopologicalSpace _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Topology
open _root_.Submission.DifferentialGeometry.Tensor0SBundle _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Curvature.DimensionThree
open _root_.Submission.DifferentialGeometry.Geometry.Neck _root_.Submission.DifferentialGeometry.Geometry.Metric _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Topology.Manifold.Attachment
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Topology.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.E3 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instNeZeroNatFinrankRealE3 : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instNeZeroNatFinrankRealE3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instNeZeroNatFinrankRealE3 target :: scope.openDecls } }
private local instance quotientChartedSpace {B : ℝ} {hB : 0 < B} :
    ChartedSpace E3 (InsertionQuotient hB) := radialCapAttachmentChartedSpace transitionEnd_pos hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.quotientChartedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.quotientChartedSpace target :: scope.openDecls } }
private local instance quotientIsManifold {B : ℝ} {hB : 0 < B} :
    IsManifold (𝓡 3) ∞ (InsertionQuotient hB) := radialCapAttachment_isManifold transitionEnd_pos hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.quotientIsManifold
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.quotientIsManifold target :: scope.openDecls } }
private local instance quotientT2Space {B : ℝ} {hB : 0 < B} :
    T2Space (InsertionQuotient hB) := radialCapAttachment_t2Space transitionEnd_pos hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.quotientT2Space
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.quotientT2Space target :: scope.openDecls } }

theorem exists_uniform_positiveCoordinate_static_estimates :
    ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧ ∃ (A : ℝ) (hA : 0 < A), 2 * A < 1 / 2 ∧
      ∀ (D : ℝ), 0 < D → ∀ (m : ℕ) (ε : ℝ), 0 < ε →
      ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < 1 / 2 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        ∃ (hAB : 2 * A < δ⁻¹) (hfit : D + 1 ≤ transitionEnd + δ⁻¹),
          collapseTip A ∈ _root_.Set.Ioo (-δ⁻¹) (-2 * A - transitionEnd) ∧
          ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
            [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
            [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
            [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M],
            ∀ (g : SmoothRiemannianMetric I M) (x₀ : M) (d : normalizedDatum g x₀ δ (m + 4)),
              let out := d.positiveSideInsertionMetric hA hAB
              metricDerivENormSupOn
                {x : modelWindow (D + 1) | (riemannianEDistOf metric 0 x.val).toReal < D} m
                (modelWindowPullback (inv_pos.mpr d.precision_pos) hfit
                  (scaleMetric (metricScalarAt g x₀) d.scalar_pos out))
                (metric.restrictOpen (modelWindow (D + 1))) (metric.restrictOpen (modelWindow (D + 1))) <
                ENNReal.ofReal ε ∧
              (∀ x, 0 < metricScalarAt out x) ∧
              (∀ a : ℝ, 0 < a →
                (∀ q : openCylinder δ⁻¹,
                  (metricScalarAt g (d.controlledMap q),
                    2 * leastCurvatureOperatorEigenvalueAt g (d.controlledMap q)
                      (metricAlgebraicCurvatureTensorAt g (d.controlledMap q))) ∈ fixedHamiltonIveyRegion a) →
                ∀ x, (metricScalarAt out x,
                  2 * leastCurvatureOperatorEigenvalueAt out x (metricAlgebraicCurvatureTensorAt out x)) ∈
                  fixedHamiltonIveyRegion a) ∧
              ∀ q : InsertionQuotient (inv_pos.mpr d.precision_pos),
                q ∈ _root_.Set.range (adjunctionCell (radialCapBoundary transitionEnd_pos)
                  (retainedBoundary (inv_pos.mpr d.precision_pos))) →
                (∀ j ≤ m, Real.sqrt (normSq0S out q (4 + j) (iterCov out 4 (metricRm04 out) j q)) ≤
                  C j * (metricScalarAt g x₀) ^ (1 + (j : ℝ) / 2)) ∧
                  |metricScalarAt out q| ≤ C 0 * metricScalarAt g x₀ := by
  obtain ⟨C, hC, hder⟩ := exists_normalizedDatum_positiveSideInsertionMetric_cap_derivative_bounds
  obtain ⟨A, hA, hAsmall, δp, hδp, hδphalf, hpin⟩ :=
    exists_normalizedDatum_positiveSideInsertionMetric_pinching
  refine ⟨C, hC, A, hA, hAsmall, ?_⟩
  intro D hD m ε hε
  obtain ⟨δw, hδw, _, hwin⟩ := exists_normalizedDatum_modelWindow_error_lt A hA D hD m ε hε
  obtain ⟨δc, hδc, _, hcurv⟩ := hder A hA m
  let δt := (2 * A + 5 * transitionEnd / 2 + 3)⁻¹
  have hδt : 0 < δt := inv_pos.mpr (by linarith [transitionEnd_pos])
  let δ₀ := _root_.Min.min δp (_root_.Min.min δw (_root_.Min.min δc δt))
  have hδ₀ : 0 < δ₀ := lt_min hδp (lt_min hδw (lt_min hδc hδt))
  refine ⟨δ₀, hδ₀, (min_le_left _ _).trans_lt hδphalf, ?_⟩
  intro δ hδ hle
  have hp : δ ≤ δp := hle.trans (min_le_left _ _)
  have hw : δ ≤ δw := hle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hc : δ ≤ δc := hle.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have ht : δ ≤ δt := hle.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨hAB, hb⟩ := hpin δ hδ hp
  obtain ⟨_, hfit, hwbound⟩ := hwin δ hδ hw
  obtain ⟨_, hcbound⟩ := hcurv δ hδ hc
  refine ⟨hAB, hfit, collapseTip_mem_buffer hA hδ ht, ?_⟩
  intro E H M _ _ _ _ _ I _ _ _ _ _ g x₀ d
  obtain ⟨hR, hHI⟩ := hb (m + 4) (by omega) g x₀ d
  exact ⟨hwbound (m + 4) (by omega) g x₀ d, hR, hHI,
    hcbound (m + 4) (by omega) g x₀ d⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_uniform_positiveCoordinate_static_estimates then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_uniform_positiveCoordinate_static_estimates"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_uniform_positiveCoordinate_static_estimates ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_uniform_positiveCoordinate_static_estimates
end DifferentialGeometry.PDE.RicciFlow.StandardCap
