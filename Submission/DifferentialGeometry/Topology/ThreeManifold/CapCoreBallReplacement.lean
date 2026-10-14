import Submission.DifferentialGeometry.Topology.ThreeManifold.RelativeBallReplacement
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapRegionStructure

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Submission.Set _root_.Metric _root_.Submission.Metric _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u

variable {Z M : Type u} [TopologicalSpace Z] [ChartedSpace ThreeSpace Z] [T3Space Z]
  [TopologicalSpace M] [ChartedSpace ThreeSpace M] [T2Space M]

theorem CapCore.nonempty_ball_replacement
    {Ω : Set Z} (cap : CapCore Ω)
    (b : PartialDiffeomorph I3 I3 ThreeSpace Z ∞)
    (P : PartialDiffeomorph I3 I3 Z M ∞)
    (G : PartialDiffeomorph I3 I3 ThreeSpace M ∞)
    (hb : _root_.Metric.closedBall (0 : ThreeSpace) 1 ⊆ b.source)
    (hG : _root_.Metric.closedBall (0 : ThreeSpace) 1 ⊆ G.source)
    (hbΩ : b '' _root_.Metric.closedBall (0 : ThreeSpace) 1 ⊆ interior Ω)
    (hP : Ω \ b '' Metric.ball (0 : ThreeSpace) 1 ⊆ P.source)
    (hboundary : P '' (b '' _root_.Metric.sphere (0 : ThreeSpace) 1) = G '' _root_.Metric.sphere (0 : ThreeSpace) 1)
    (hinter : P '' (Ω \ b '' Metric.ball (0 : ThreeSpace) 1) ∩ G '' _root_.Metric.closedBall (0 : ThreeSpace) 1 ⊆
      G '' _root_.Metric.sphere (0 : ThreeSpace) 1) :
    Nonempty (CapCore (P '' (Ω \ b '' Metric.ball (0 : ThreeSpace) 1) ∪
      G '' _root_.Metric.closedBall (0 : ThreeSpace) 1)) ∧
      ∃ (J : PartialDiffeomorph I3 I3 Z M ∞)
        (D : Diffeomorph I3 I3 ThreeSpace ThreeSpace ∞),
        Ω ⊆ J.source ∧
        J '' Ω = P '' (Ω \ b '' Metric.ball (0 : ThreeSpace) 1) ∪ G '' _root_.Metric.closedBall (0 : ThreeSpace) 1 ∧
        D '' _root_.Metric.closedBall (0 : ThreeSpace) 1 = _root_.Metric.closedBall (0 : ThreeSpace) 1 ∧
        (∀ z ∈ _root_.Metric.closedBall (0 : ThreeSpace) 1, J (b z) = G (D z)) ∧
        ∃ O : Set Z, IsOpen O ∧ Ω \ b '' Metric.ball (0 : ThreeSpace) 1 ⊆ O ∧
          O ⊆ P.source ∧ _root_.Set.EqOn J P O := by
  obtain ⟨J, D, hJ, hJimage, hD, hcap, O, hO, hKO, hOP, hJP⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_partialDiffeomorph_ball_replacement_eqOn_complement
      b P G hb hG cap.isCompact_carrier hbΩ hP hboundary hinter
  refine ⟨?_, J, D, hJ, hJimage, hD, hcap, O, hO, hKO, hOP, hJP⟩
  rw [← hJimage]
  exact cap.image_of_partialDiffeomorph J hJ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CapCore.nonempty_ball_replacement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CapCore.nonempty_ball_replacement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CapCore.nonempty_ball_replacement ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CapCore.nonempty_ball_replacement

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

section

open _root_.Set _root_.Submission.Set _root_.Metric _root_.Submission.Metric _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u
variable {Z M : Type u} {ι : Type*}
  [TopologicalSpace Z] [ChartedSpace ThreeSpace Z] [T3Space Z]
  [TopologicalSpace M] [ChartedSpace ThreeSpace M] [T2Space M]

theorem CapCore.nonempty_finite_ball_replacement
    {Ω : Set Z} (cap : CapCore Ω) (s : Finset ι)
    (b : ι → PartialDiffeomorph I3 I3 ThreeSpace Z ∞)
    (G : ι → PartialDiffeomorph I3 I3 ThreeSpace M ∞)
    (hb : ∀ i ∈ s, _root_.Metric.closedBall (0 : ThreeSpace) 1 ⊆ (b i).source)
    (hG : ∀ i ∈ s, _root_.Metric.closedBall (0 : ThreeSpace) 1 ⊆ (G i).source)
    (hbΩ : ∀ i ∈ s, b i '' _root_.Metric.closedBall (0 : ThreeSpace) 1 ⊆ interior Ω)
    (hdisb : (s : Set ι).Pairwise (fun i j => Disjoint
      (b i '' _root_.Metric.closedBall (0 : ThreeSpace) 1) (b j '' _root_.Metric.closedBall (0 : ThreeSpace) 1)))
    (hdisG : (s : Set ι).Pairwise (fun i j => Disjoint
      (G i '' _root_.Metric.closedBall (0 : ThreeSpace) 1) (G j '' _root_.Metric.closedBall (0 : ThreeSpace) 1)))
    (P : PartialDiffeomorph I3 I3 Z M ∞)
    (hP : Ω \ ⋃ i ∈ s, b i '' Metric.ball (0 : ThreeSpace) 1 ⊆ P.source)
    (hboundary : ∀ i ∈ s,
      P '' (b i '' _root_.Metric.sphere (0 : ThreeSpace) 1) = G i '' _root_.Metric.sphere (0 : ThreeSpace) 1)
    (hinter : ∀ i ∈ s, P '' (Ω \ ⋃ j ∈ s, b j '' Metric.ball (0 : ThreeSpace) 1) ∩
      G i '' _root_.Metric.closedBall (0 : ThreeSpace) 1 ⊆ G i '' _root_.Metric.sphere (0 : ThreeSpace) 1) :
    Nonempty (CapCore (P '' (Ω \ ⋃ i ∈ s, b i '' Metric.ball (0 : ThreeSpace) 1) ∪
      ⋃ i ∈ s, G i '' _root_.Metric.closedBall (0 : ThreeSpace) 1)) ∧
      ∃ J : PartialDiffeomorph I3 I3 Z M ∞,
        Ω ⊆ J.source ∧
        J '' Ω = P '' (Ω \ ⋃ i ∈ s, b i '' Metric.ball (0 : ThreeSpace) 1) ∪
          ⋃ i ∈ s, G i '' _root_.Metric.closedBall (0 : ThreeSpace) 1 ∧
        (∀ i ∈ s, ∃ D : ThreeSpace ≃ₘ[ℝ] ThreeSpace,
          D '' _root_.Metric.closedBall (0 : ThreeSpace) 1 = _root_.Metric.closedBall (0 : ThreeSpace) 1 ∧
          ∀ z ∈ _root_.Metric.closedBall (0 : ThreeSpace) 1, J (b i z) = G i (D z)) ∧
        ∃ O : Set Z, IsOpen O ∧ (Ω \ ⋃ i ∈ s, b i '' Metric.ball (0 : ThreeSpace) 1) ⊆ O ∧
          O ⊆ P.source ∧ _root_.Set.EqOn J P O := by
  obtain ⟨J,hJ,himage,hballs,O,hO,hKO,hOP,hJP⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_partialDiffeomorph_finite_ball_replacement_eqOn_complement
      s b G hb hG cap.isCompact_carrier hbΩ hdisb hdisG P hP hboundary hinter
  refine ⟨?_,J,hJ,himage,hballs,O,hO,hKO,hOP,hJP⟩
  rw [← himage]
  exact cap.image_of_partialDiffeomorph J hJ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CapCore.nonempty_finite_ball_replacement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CapCore.nonempty_finite_ball_replacement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CapCore.nonempty_finite_ball_replacement ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CapCore.nonempty_finite_ball_replacement

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
