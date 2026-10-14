import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BlowupConvergence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Scaling.Parabolic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.CheegerGromovCompactness

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

namespace FlowSequence

def terminalCurvatureRescale (X : FlowSequence.{u})
    (x : ∀ i, (X.term i).M)
    (hQ : ∀ i, 0 < (X.term i).S.scalar 0 (x i))
    (hzero : ∀ i, (0 : ℝ) ∈ (X.interval i).carrier) : FlowSequence.{u} where
  interval i := parabolicInterval (X.interval i) 0 ((X.term i).S.scalar 0 (x i)) (hzero i)
  term i := {
    M := (X.term i).M
    topology := (X.term i).topology
    charted := (X.term i).charted
    smooth := (X.term i).smooth
    sigmaCompact := (X.term i).sigmaCompact
    t2 := (X.term i).t2
    t2TangentBundle := (X.term i).t2TangentBundle
    basepoint := x i
    S := parabolicSolution (X.term i).S 0 ((X.term i).S.scalar 0 (x i)) (hQ i) (hzero i)
    isSolution := parabolicSolution_isSolutionOn (X.term i).S (X.term i).isSolution _ _ _ _ }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.terminalCurvatureRescale then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.terminalCurvatureRescale"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.terminalCurvatureRescale ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.terminalCurvatureRescale

@[simp] theorem terminalCurvatureRescale_metric (X : FlowSequence.{u})
    (x : ∀ i, (X.term i).M) (hQ : ∀ i, 0 < (X.term i).S.scalar 0 (x i))
    (hzero : ∀ i, (0 : ℝ) ∈ (X.interval i).carrier) (i : ℕ) (t : ℝ) :
    ((X.terminalCurvatureRescale x hQ hzero).term i).S.base.metric t =
      scaleMetric ((X.term i).S.scalar 0 (x i)) (hQ i)
        ((X.term i).S.base.metric (t / (X.term i).S.scalar 0 (x i))) := by
  simp only [terminalCurvatureRescale, parabolicSolution, parabolicFamily, parabolicTime, zero_add]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.terminalCurvatureRescale_metric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.terminalCurvatureRescale_metric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.terminalCurvatureRescale_metric ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.terminalCurvatureRescale_metric

@[simp] theorem terminalCurvatureRescale_basepoint (X : FlowSequence.{u})
    (x : ∀ i, (X.term i).M) (hQ : ∀ i, 0 < (X.term i).S.scalar 0 (x i))
    (hzero : ∀ i, (0 : ℝ) ∈ (X.interval i).carrier) (i : ℕ) :
    ((X.terminalCurvatureRescale x hQ hzero).term i).basepoint = x i := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.terminalCurvatureRescale_basepoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.terminalCurvatureRescale_basepoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.terminalCurvatureRescale_basepoint ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.terminalCurvatureRescale_basepoint

end FlowSequence

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
