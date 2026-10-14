import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.BallEmbeddingFamilyStraightening
import Submission.DifferentialGeometry.Topology.Manifold.BallChartPalaisTransport

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Metric _root_.Submission.Metric _root_.Filter _root_.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology
open _root_.Submission.DifferentialGeometry.Topology (BallChart)

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem ballChartIsotopicAwayFromCompact_of_modelIsotopy {U : Type u} [TopologicalSpace U]
    [ChartedSpace ThreeSpace U] [IsManifold ThreeModel ∞ U] [T2Space U]
    (b b' : BallChart 3 (𝓡 3) U) (C : Set U)
    (D : ℝ → Diffeomorph ThreeModel ThreeModel ThreeSpace ThreeSpace ∞)
    (hDc : ContDiff ℝ ∞ (fun q : ℝ × ThreeSpace => D q.1 q.2))
    (hDi : ContDiff ℝ ∞ (fun q : ℝ × ThreeSpace => (D q.1).symm q.2))
    (hD0 : D 0 = Diffeomorph.refl ThreeModel ThreeSpace ∞)
    {K : Set ThreeSpace} (hK : IsCompact K) (hKt : K ⊆ b'.chart.source)
    (hKfix : ∀ t z, z ∉ K → D t z = z ∧ (D t).symm z = z)
    (havoid : Disjoint (b'.chart '' K) C)
    (hover : b.chart '' Metric.closedBall (0 : ThreeSpace) 1 ⊆ b'.chart.target)
    (hact : ∀ x ∈ Metric.closedBall (0 : ThreeSpace) 1,
      D 1 (b'.chart.symm (b.chart x)) = x) :
    ballChartIsotopicAwayFromCompact b b' C := by
  obtain ⟨J, hJc, hJi, hJe, hKc, -, hKfixU⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_diffeomorph_extension_of_partial_chart_family
      (P := ℝ) b'.chart.symm.toOpenPartialHomeomorph b'.chart.contMDiffOn_invFun
      b'.chart.contMDiffOn_toFun D hDc hDi hK hKt hKfix
  have hset : (b'.chart.symm.toOpenPartialHomeomorph.symm : OpenPartialHomeomorph ThreeSpace U) '' K
      = b'.chart '' K := rfl
  have hJ0 : J 0 = Diffeomorph.refl ThreeModel U ∞ := by
    apply Diffeomorph.ext
    intro y
    rw [(hJe 0 y).1]
    by_cases hy : y ∈ b'.chart.symm.toOpenPartialHomeomorph.source
    · have h1 : DifferentialGeometry.Topology.Manifold.extendChartById
            b'.chart.symm.toOpenPartialHomeomorph (D 0) y
          = b'.chart.symm.toOpenPartialHomeomorph.symm
            (b'.chart.symm.toOpenPartialHomeomorph y) := by
        rw [hD0]
        exact if_pos hy
      rw [h1, OpenPartialHomeomorph.left_inv _ hy]
      simp only [Diffeomorph.coe_refl, id_eq]
    · have h2 : DifferentialGeometry.Topology.Manifold.extendChartById
            b'.chart.symm.toOpenPartialHomeomorph (D 0) y = y := by
        rw [hD0]
        exact if_neg hy
      rw [h2]
      rfl
  refine ⟨J, b'.chart.symm.toOpenPartialHomeomorph.symm '' K, hKc, ?_, hJ0, hJc, hJi, ?_, ?_,
    ?_⟩
  · rw [hset]
    exact havoid
  · intro t x hx
    exact (hKfixU t x hx).1
  · intro t x hx
    exact (hKfixU t x hx).2
  · intro x hx
    rw [(hJe 1 (b.chart x)).1,
      DifferentialGeometry.Topology.extendChartById_chartSymm_of_target b' (D 1)
        (hover ⟨x, hx, rfl⟩),
      hact x hx]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ballChartIsotopicAwayFromCompact_of_modelIsotopy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ballChartIsotopicAwayFromCompact_of_modelIsotopy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ballChartIsotopicAwayFromCompact_of_modelIsotopy ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ballChartIsotopicAwayFromCompact_of_modelIsotopy

theorem ballChartIsotopicAwayFromCompact_of_matching_refl {U : Type u} [TopologicalSpace U]
    [ChartedSpace ThreeSpace U] [IsManifold ThreeModel ∞ U] [T2Space U]
    (b b' : BallChart 3 (𝓡 3) U) (C : Set U)
    (hover : b.chart '' Metric.closedBall (0 : ThreeSpace) 1 ⊆ b'.chart.target)
    (hpoint : ∀ x ∈ Metric.closedBall (0 : ThreeSpace) 1, b'.chart.symm (b.chart x) = x) :
    ballChartIsotopicAwayFromCompact b b' C := by
  refine ballChartIsotopicAwayFromCompact_of_modelIsotopy b b' C
    (fun _ => Diffeomorph.refl ThreeModel ThreeSpace ∞) contDiff_snd contDiff_snd rfl
    isCompact_empty (by simp) (fun _ _ _ => ⟨rfl, rfl⟩) (by simp) hover ?_
  intro x hx
  simpa only [Diffeomorph.coe_refl, id_eq] using hpoint x hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ballChartIsotopicAwayFromCompact_of_matching_refl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ballChartIsotopicAwayFromCompact_of_matching_refl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ballChartIsotopicAwayFromCompact_of_matching_refl ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ballChartIsotopicAwayFromCompact_of_matching_refl

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
