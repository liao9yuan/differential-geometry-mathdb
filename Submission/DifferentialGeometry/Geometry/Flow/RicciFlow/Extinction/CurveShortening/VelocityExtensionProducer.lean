import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.BoundaryIsotopyFrontier
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.VelocityExtensionManifoldFrontier

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory _root_.Filter
open scoped _root_.Manifold _root_.ContDiff _root_.Topology
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [hBoundary : I.Boundaryless] [hT2 : T2Space M] [hCompact : CompactSpace M]
  [hNonempty : Nonempty M] [SigmaCompactSpace M]
  {a b : ℝ}

omit [FiniteDimensional ℝ E] [CompleteSpace E] hBoundary hT2 hCompact hNonempty
  [SigmaCompactSpace M] in
theorem hasBoundaryIsotopyVelocityExtension_iff_loopFamilyVelocityExtensionProducer :
    HasBoundaryIsotopyVelocityExtension (I := I) (M := M) a b ↔
      LoopFamilyVelocityExtensionProducer (I := I) (M := M) a b :=
  ⟨fun h => h, fun h => h⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.hasBoundaryIsotopyVelocityExtension_iff_loopFamilyVelocityExtensionProducer then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.hasBoundaryIsotopyVelocityExtension_iff_loopFamilyVelocityExtensionProducer"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.hasBoundaryIsotopyVelocityExtension_iff_loopFamilyVelocityExtensionProducer ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.hasBoundaryIsotopyVelocityExtension_iff_loopFamilyVelocityExtensionProducer

omit [FiniteDimensional ℝ E] [CompleteSpace E] hBoundary hT2 hCompact hNonempty
  [SigmaCompactSpace M] in
theorem loopFamilyVelocityExtensionProducer_iff_allWindows :
    (∀ a b : ℝ, LoopFamilyVelocityExtensionProducer (I := I) (M := M) a b) ↔
      ∀ (a' b' : ℝ) (γ : ℝ → ContinuousFreeLoop M),
        (curveOfLoopFamily γ).SmoothOn (I := I) (_root_.Set.Icc a' b') →
        (curveOfLoopFamily γ).ImmersedOn (I := I) (_root_.Set.Icc a' b') →
        (∀ t ∈ _root_.Set.Icc a' b', Topology.IsEmbedding (γ t)) →
        LoopFamilyVelocityExtension (I := I) a' b' γ :=
  ⟨fun h a' b' => h a' b', fun h a b => h a b⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.loopFamilyVelocityExtensionProducer_iff_allWindows then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.loopFamilyVelocityExtensionProducer_iff_allWindows"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.loopFamilyVelocityExtensionProducer_iff_allWindows ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.loopFamilyVelocityExtensionProducer_iff_allWindows

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
