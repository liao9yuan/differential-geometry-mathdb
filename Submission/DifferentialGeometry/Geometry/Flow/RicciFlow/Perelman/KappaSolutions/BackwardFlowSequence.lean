import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardSliceSequence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.ContDiff
universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

def backwardFlowSequence (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M) :
    PointedFlowSeq.{u, uE, uH} (I := I) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact { D := ancientTimeInterval
          term := fun i => curvatureNormalizedFlow F rfl rfl (-tau i) (tau i)⁻¹
            (inv_pos.mpr (htau i)) (neg_nonpos.mpr (htau i).le) (q i) }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardFlowSequence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardFlowSequence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardFlowSequence ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardFlowSequence

theorem backwardFlowSequence_metric
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M) (i : ℕ) (t : ℝ) :
    ((backwardFlowSequence F tau htau q).term i).S.base.metric t =
      scaleMetric (tau i)⁻¹ (inv_pos.mpr (htau i))
        (F.S.base.metric (tau i * (t - 1))) := by
  change scaleMetric (tau i)⁻¹ (inv_pos.mpr (htau i)) (F.S.base.metric (-tau i + t / (tau i)⁻¹)) = _
  congr 2
  rw [div_inv_eq_mul]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardFlowSequence_metric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardFlowSequence_metric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardFlowSequence_metric ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardFlowSequence_metric

theorem backwardFlowSequence_atZero
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M) :
    (backwardFlowSequence F tau htau q).atZero = backwardSliceSequence F tau htau q := by
  simp only [backwardFlowSequence, PointedFlowSeq.atZero, PointedFlowSeq.atTime,
    PointedFlowData.atTime, curvatureNormalizedFlow, curvatureNormalizedSolution,
    SolutionOn.timeRestrict, parabolicSolution, parabolicFamily, SolutionOn.family, backwardSliceSequence,
    parabolicTime_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardFlowSequence_atZero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardFlowSequence_atZero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardFlowSequence_atZero ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardFlowSequence_atZero

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
