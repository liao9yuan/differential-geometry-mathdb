import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductLengthEvolution
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.RampLengthEvolution

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.Set _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
    [SigmaCompactSpace Q] [T2Space Q] [I.Boundaryless]
    {D : RealTimeInterval} {a b : ℝ}

theorem ramp_length_evolution (B : RicciBackground (I := I) (M := Q) D a b) :
    RampLengthEvolution (I := I) (Q := Q) (D := D) (a := a) (b := b) B := by
  intro lambda hlambda _ c hsol s t has hst htb
  have h := c.length_energy_bounds B lambda hlambda (uniqueDiffOn_Icc B.lt) hsol
    B.lt Subset.rfl Subset.rfl
  have hsub : _root_.Set.Icc s t ⊆ _root_.Set.Icc a b := _root_.Set.Icc_subset_Icc has htb
  have hs : s ∈ _root_.Set.Icc a b := ⟨has, hst.trans htb⟩
  refine ⟨h.1.continuousOn.mono hsub, (h.2.1.mono hsub).intervalIntegrable_of_Icc hst,
    fun v _ => productCurve_energy_nonneg c B.family.metric lambda v,
    (h.2.2 s hs t ⟨hst, htb⟩).2, ?_⟩
  intro v hv
  exact (h.2.2 s hs v ⟨hv.1, hv.2.trans htb⟩).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.ramp_length_evolution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Families.ramp_length_evolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.ramp_length_evolution ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.ramp_length_evolution

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families
