import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CostLocalBound
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.MinVectorCompact
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Length

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Set
open _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.Submission.Topology _root_.Submission.DifferentialGeometry.Topology

namespace DifferentialGeometry.PDE.RicciFlow

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  {D : RealTimeInterval}

theorem lMinVec_compact_over_of_rm
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (K T : ℝ)
    (hg : RiemannianMetricComplete (I := I) (S.base.metric T))
    (x : M) (tau : ℝ) (htau : 0 < tau)
    (hreg : _root_.Set.Icc (T - tau) T ⊆ D.regular)
    (hRm : ∀ t ∈ _root_.Set.Icc (T - tau) T, ∀ y : M,
      normSq0S (I := I) (S.base.metric t) y 4
        (S.base.rm04 t y) ≤ K)
    {Cpt : Set M} (hCpt : IsCompact Cpt) :
    ∃ A : ℝ, 0 ≤ A ∧
      (∀ y ∈ Cpt, lCost S T x y tau ≤ A) ∧
      (∀ Z : TangentSpace I x,
        (Z, tau) ∈ lMinDomain S T x →
        lExp S T x Z tau ∈ Cpt →
        lRegularizedAction S T (lRegularizedCurve S T x Z) 0 (Real.sqrt tau) ≤ A) ∧
      IsCompact {Z : TangentSpace I x |
        (Z, tau) ∈ lMinDomain S T x ∧ lExp S T x Z tau ∈ Cpt} := by
  obtain ⟨A, hA, hcost⟩ :=
    lCost_bddAbove_on_compact_of_rm (I := I) S hS K T tau htau
      hreg hRm x hCpt
  have hact : ∀ Z : TangentSpace I x,
      (Z, tau) ∈ lMinDomain S T x →
      lExp S T x Z tau ∈ Cpt →
      lRegularizedAction S T (lRegularizedCurve S T x Z) 0 (Real.sqrt tau) ≤ A := by
    intro Z hmin hend
    calc
      lRegularizedAction S T (lRegularizedCurve S T x Z) 0 (Real.sqrt tau) =
          lLength S T (fun r : ℝ ↦ lExp S T x Z r) 0 tau := by
        change lRegularizedAction S T (lRegularizedCurve S T x Z) 0 (Real.sqrt tau) =
          lLength S T (squareRootReparametrization (lRegularizedCurve S T x Z)) 0 tau
        exact (lLength_squareRootReparametrization_eq_lRegularizedAction (I := I) S T
          (lRegularizedCurve S T x Z) tau htau.le).symm
      _ = lCost S T x (lExp S T x Z tau) tau :=
        ((mem_lMinDomain S T x Z tau).mp hmin).2
      _ ≤ A := hcost (lExp S T x Z tau) hend
  exact ⟨A, hA, hcost, hact,
    isCompact_lMinVec_over_of_rm (I := I) S hS K T hg x tau htau
      hreg hRm hCpt A hact⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.lMinVec_compact_over_of_rm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.lMinVec_compact_over_of_rm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.lMinVec_compact_over_of_rm ``Submission.DifferentialGeometry.PDE.RicciFlow.lMinVec_compact_over_of_rm

end DifferentialGeometry.PDE.RicciFlow

end
