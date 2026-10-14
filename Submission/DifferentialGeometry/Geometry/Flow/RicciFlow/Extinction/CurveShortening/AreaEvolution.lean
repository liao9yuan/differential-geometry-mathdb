import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.AreaEvolution.Basic
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.GenericCurves

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [hBoundary : I.Boundaryless] [hT2 : T2Space M]
    [hCompact : CompactSpace M] [hNonempty : Nonempty M]

variable [SigmaCompactSpace M]
variable {D : RealTimeInterval} {a b : ℝ}

include hBoundary hT2 hCompact hNonempty


omit hNonempty [SigmaCompactSpace M] in
theorem rfs_csf_generic_curves (B : RicciBackground (I := I) (M := M) D a b)
    (hdim : Module.finrank ℝ E = 3) {N : ℕ}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (γ : ℝ → ContinuousFreeLoop M)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (_root_.Set.Icc a b))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := I) (_root_.Set.Icc a b)) :
    ∃ approximants : ℕ → ℝ → ContinuousFreeLoop M,
      (∀ j, (curveOfLoopFamily (approximants j)).SmoothOn (I := I) (_root_.Set.Icc a b) ∧
        (curveOfLoopFamily (approximants j)).ImmersedOn (I := I) (_root_.Set.Icc a b) ∧
        ∃ exceptional : Finset ℝ, ∀ t ∈ _root_.Set.Icc a b,
          t ∉ exceptional → Topology.IsEmbedding (approximants j t)) ∧
      (∀ ε > 0, ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ m : ℕ, m ≤ 2 →
        ∀ p ∈ _root_.Set.Icc (0 : ℝ) 1 ×ˢ _root_.Set.Icc a b,
          ‖iteratedFDerivWithin ℝ m
              (fun q : ℝ × ℝ => e.map (approximants j q.2 (q.1 : Surgery.Topology.Circle)))
              (_root_.Set.univ ×ˢ _root_.Set.Icc a b) p -
            iteratedFDerivWithin ℝ m
              (fun q : ℝ × ℝ => e.map (γ q.2 (q.1 : Surgery.Topology.Circle)))
              (_root_.Set.univ ×ˢ _root_.Set.Icc a b) p‖ < ε) ∧
      (∀ ε > 0, ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ t ∈ _root_.Set.Icc a b,
        |(curveOfLoopFamily (approximants j)).areaError B.family.metric (_root_.Set.Icc a b) t -
          (curveOfLoopFamily γ).areaError B.family.metric (_root_.Set.Icc a b) t| < ε) ∧
      ((∀ t ∈ _root_.Set.Icc a b, IsContractibleLoop (γ t)) →
        (∀ j t, t ∈ _root_.Set.Icc a b → IsContractibleLoop (approximants j t)) ∧
        ∀ ε > 0, ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ t ∈ _root_.Set.Icc a b,
          |loopFamilyLeastArea B.family.metric (approximants j) t -
            loopFamilyLeastArea B.family.metric γ t| < ε) := by
  exact exists_generic_loopFamily_approximation_sequence hdim e B.family.metric
    B.smooth B.lt B.regular γ hγ hi

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.rfs_csf_generic_curves then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.rfs_csf_generic_curves"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.rfs_csf_generic_curves ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.rfs_csf_generic_curves



end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
