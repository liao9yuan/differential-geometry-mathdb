import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.VolumeGrowth
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.VolumeContinuity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventData
import Mathlib.Analysis.Calculus.Deriv.MeanValue

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Filter _root_.MeasureTheory _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Integral.Measure
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal _root_.Topology _root_.Submission.DifferentialGeometry.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow

universe u

variable {P : OrientedThreeStage.{u}} {a b : ℝ}

theorem OrientedThreeStage.ClosedSlab.antitoneOn_exp_mul_volume
    (G : P.ClosedSlab a b) (K : ℝ)
    (hscalar : ∀ t ∈ _root_.Set.Icc a b, ∀ x : P.Carrier,
      -K ≤ metricScalarAt (G.flow.base.metric t) x) :
    AntitoneOn
      (fun t : ℝ => Real.exp (-K * t) *
        (riemannianVolumeMeasure (𝓡 3) P.Carrier (G.flow.base.metric t) _root_.Set.univ).toReal)
      (_root_.Set.Icc a b) := by
  let F : ℝ → ℝ := fun t => Real.exp (-K * t) *
    (riemannianVolumeMeasure (𝓡 3) P.Carrier (G.flow.base.metric t) _root_.Set.univ).toReal
  have hcontV := SolutionOn.continuousOn_volume G.flow G.equation
  have hcont : ContinuousOn F (_root_.Set.Icc a b) := by
    exact ContinuousOn.mul (Real.continuous_exp.comp_continuousOn
      ((continuous_const.mul continuous_id).continuousOn)) hcontV
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b) hcont
  · intro t ht
    have hti : t ∈ _root_.Set.Ioo a b := by simpa only [interior_Icc] using ht
    have hreg : t ∈ (RealTimeInterval.closed a b G.lt.le).regular :=
      ⟨hti.1, hti.2⟩
    exact (G.flow.hasDerivAt_exp_mul_volume G.equation K hreg).hasDerivWithinAt
  · intro t ht
    have hti : t ∈ _root_.Set.Ioo a b := by simpa only [interior_Icc] using ht
    apply _root_.MeasureTheory.integral_nonpos
    intro x
    have hbound := hscalar t (by exact ⟨hti.1.le, hti.2.le⟩) x
    have hmul := mul_le_mul_of_nonneg_left hbound (Real.exp_pos (-K * t)).le
    change Real.exp (-K * t) * (-K) -
      metricScalarAt (G.flow.base.metric t) x * Real.exp (-K * t) ≤ 0
    nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.antitoneOn_exp_mul_volume then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.antitoneOn_exp_mul_volume"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.antitoneOn_exp_mul_volume ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.antitoneOn_exp_mul_volume

theorem OrientedThreeStage.ClosedSlab.exp_mul_volume_le_endpoint
    (G : P.ClosedSlab a b) (K : ℝ)
    (hscalar : ∀ t ∈ _root_.Set.Icc a b, ∀ x : P.Carrier,
      -K ≤ metricScalarAt (G.flow.base.metric t) x) :
    ∀ t ∈ _root_.Set.Icc a b,
      Real.exp (-K * t) *
          (riemannianVolumeMeasure (𝓡 3) P.Carrier (G.flow.base.metric t) _root_.Set.univ).toReal ≤
        Real.exp (-K * a) *
          (riemannianVolumeMeasure (𝓡 3) P.Carrier (G.flow.base.metric a) _root_.Set.univ).toReal := by
  intro t ht
  exact G.antitoneOn_exp_mul_volume K hscalar ⟨le_rfl, G.lt.le⟩ ⟨ht.1, ht.2⟩ ht.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.exp_mul_volume_le_endpoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.exp_mul_volume_le_endpoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.exp_mul_volume_le_endpoint ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.exp_mul_volume_le_endpoint

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
