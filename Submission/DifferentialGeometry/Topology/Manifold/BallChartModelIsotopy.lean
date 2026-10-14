import Submission.DifferentialGeometry.Topology.Manifold.BallChartScale
import Submission.DifferentialGeometry.Topology.Manifold.AffineBallIsotopy

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Metric _root_.Submission.Metric _root_.Filter _root_.Topology _root_.Manifold _root_.Submission.Manifold
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.Topology.Manifold

private abbrev E₃ := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.E₃
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.E₃ target :: scope.openDecls } }

theorem ballChartIsotopic_of_modelIsotopy {M : Type*} [TopologicalSpace M]
    [ChartedSpace E₃ M] [IsManifold (𝓡 3) ∞ M] [T2Space M]
    (c c' : BallChart 3 (𝓡 3) M)
    (hover : ∀ x ∈ Metric.closedBall (0 : E₃) 2, c.chart x ∈ c'.chart.target)
    (D : ℝ → Diffeomorph 𝓘(ℝ, E₃) 𝓘(ℝ, E₃) E₃ E₃ ∞)
    (hDc : ContDiff ℝ ∞ (fun q : ℝ × E₃ => D q.1 q.2))
    (hDi : ContDiff ℝ ∞ (fun q : ℝ × E₃ => (D q.1).symm q.2))
    (hD0 : D 0 = Diffeomorph.refl 𝓘(ℝ, E₃) E₃ ∞)
    {K : Set E₃} (hK : IsCompact K) (hKt : K ⊆ c'.chart.source)
    (hfix : ∀ t z, z ∉ K → D t z = z ∧ (D t).symm z = z)
    (hact : ∀ x ∈ Metric.closedBall (0 : E₃) 2, D 1 (c'.chart.symm (c.chart x)) = x) :
    BallChartIsotopic c c' := by
  obtain ⟨J, hJ, hJi, hJe, -, -, -⟩ :=
    exists_diffeomorph_extension_of_partial_chart_family (P := ℝ)
      c'.chart.symm.toOpenPartialHomeomorph c'.chart.contMDiffOn_invFun
      c'.chart.contMDiffOn_toFun D hDc hDi hK hKt hfix
  refine ⟨J, hJ, hJi, ?_, ?_⟩
  · apply Diffeomorph.ext
    intro y
    rw [(hJe 0 y).1]
    by_cases hy : y ∈ c'.chart.symm.toOpenPartialHomeomorph.source
    · have h1 : extendChartById c'.chart.symm.toOpenPartialHomeomorph (D 0) y
          = c'.chart.symm.toOpenPartialHomeomorph.symm
            (c'.chart.symm.toOpenPartialHomeomorph y) := by
        rw [extendChartById, if_pos hy, hD0]
        rfl
      rw [h1, OpenPartialHomeomorph.left_inv _ hy]
      simp only [Diffeomorph.coe_refl, id_eq]
    · rw [extendChartById, if_neg hy]
      simp only [Diffeomorph.coe_refl, id_eq]
  · intro x hx
    rw [(hJe 1 (c.chart x)).1, extendChartById_chartSymm_of_target c' (D 1) (hover x hx),
      hact x hx]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.ballChartIsotopic_of_modelIsotopy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.ballChartIsotopic_of_modelIsotopy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.ballChartIsotopic_of_modelIsotopy ``Submission.DifferentialGeometry.Topology.Manifold.ballChartIsotopic_of_modelIsotopy

end DifferentialGeometry.Topology.Manifold
