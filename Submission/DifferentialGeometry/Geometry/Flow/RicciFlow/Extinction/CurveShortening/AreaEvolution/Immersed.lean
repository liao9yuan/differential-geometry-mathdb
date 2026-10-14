import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.AreaEvolution.Embedded
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ImmersedAreaFrontier

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.Set _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Filter _root_.Submission.Filter
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


theorem rfs_csf_immersed_area (B : RicciBackground (I := I) (M := M) D a b)
    (hdim : Module.finrank ℝ E = 3) (γ : ℝ → ContinuousFreeLoop M)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (_root_.Set.Icc a b))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := I) (_root_.Set.Icc a b))
    (hctr : ∀ t ∈ _root_.Set.Icc a b, IsContractibleLoop (γ t)) :
    ContinuousOn (loopFamilyLeastArea B.family.metric γ) (_root_.Set.Icc a b) ∧
      (∀ s ∈ _root_.Set.Icc a b, ∀ t ∈ _root_.Set.Icc s b,
        areaIntegratingFactor B.family s t * loopFamilyLeastArea B.family.metric γ t ≤
          loopFamilyLeastArea B.family.metric γ s +
            ∫ v in s..t, areaIntegratingFactor B.family s v *
              (-2 * Real.pi + (curveOfLoopFamily γ).areaError B.family.metric (_root_.Set.Icc a b) v)) ∧
      (∀ t ∈ _root_.Set.Ico a b, ∀ ε > 0, ∃ δ > 0, ∀ h ∈ _root_.Set.Ioo (0 : ℝ) δ, t + h ≤ b →
        (loopFamilyLeastArea B.family.metric γ (t + h) -
            loopFamilyLeastArea B.family.metric γ t) / h ≤
          -2 * Real.pi - scalarMinimum B.family t * loopFamilyLeastArea B.family.metric γ t / 2 +
            (curveOfLoopFamily γ).areaError B.family.metric (_root_.Set.Icc a b) t + ε) := by
  obtain ⟨N, ⟨e⟩⟩ := Width.smoothLoopEmbedding_exists (I := I) (Q := M)
  refine rfs_csf_immersed_area_of_embedded_area_of_generic_curves
    (I := I) (M := M) B hdim e γ hγ hi hctr ?_
    (rfs_csf_generic_curves (I := I) (M := M) B hdim e γ hγ hi)
  intro a' b' B' hdim' γ' hγ' hi' hctr' hemb'
  exact rfs_csf_embedded_area (I := I) (M := M)
    B' hdim' γ' hγ' hi' hctr' hemb'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.rfs_csf_immersed_area then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.rfs_csf_immersed_area"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.rfs_csf_immersed_area ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.rfs_csf_immersed_area


end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
