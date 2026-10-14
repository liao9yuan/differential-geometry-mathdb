import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BlowupConvergence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SlabRicciCoefficientLimit
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Inner

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open scoped _root_.Topology _root_.Submission.Topology
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open _root_.Filter _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal
universe u
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

def FlowSequence.timeShift (X : FlowSequence.{u}) (s : ℝ) : FlowSequence.{u} where
  interval i := (X.interval i).timeShift s
  term i := {
    M := (X.term i).M
    topology := (X.term i).topology
    charted := (X.term i).charted
    smooth := (X.term i).smooth
    sigmaCompact := (X.term i).sigmaCompact
    t2 := (X.term i).t2
    t2TangentBundle := (X.term i).t2TangentBundle
    basepoint := (X.term i).basepoint
    S := (X.term i).S.timeShift s
    isSolution := isSolutionOn_timeShift (X.term i).isSolution s }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.timeShift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.timeShift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.timeShift ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.timeShift

theorem FlowSequence.timeShift_atTime (X : FlowSequence.{u}) (s t : ℝ) :
    (X.timeShift s).atTime t = X.atTime (t + s) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.timeShift_atTime then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.timeShift_atTime"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.timeShift_atTime ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.timeShift_atTime


end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

set_option autoImplicit false
noncomputable section
open scoped _root_.Topology _root_.Submission.Topology
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open _root_.Filter _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal
universe u
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem ConvergesOn.tendsto_metric_inner
    {X : FlowSequence.{u}} {P : PointedRiemannianManifold.{u, 0, 0} I3} {f : ℕ → ℕ}
    {F : PointedRiemannianConvergenceMaps (X.atTime 0) P f}
    {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := P.M) D}
    (hconv : ConvergesOn F S) {t : ℝ} (ht : t ∈ D.carrier)
    (x : P.M) (v w : TangentSpace I3 x) :
    _root_.Filter.Tendsto (fun i => ((X.term (f i)).S.base.metric t).inner
      (F.partialDiffeomorph i x) (mfderiv I3 I3 (F.partialDiffeomorph i) x v)
      (mfderiv I3 I3 (F.partialDiffeomorph i) x w))
      atTop (𝓝 ((S.base.metric t).inner x v w)) := by
  obtain ⟨C, hcanonical⟩ := hconv.exists_canonical_metric_convergence ht
  exact pointed_metric_inner_tendsto (Phi := X.sliceMaps F S.base.metric t)
    (fun K hK => by
      have h := C.converges K hK 0
      rwa [show C.domain = _ from funext hcanonical] at h) x v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ConvergesOn.tendsto_metric_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ConvergesOn.tendsto_metric_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ConvergesOn.tendsto_metric_inner ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ConvergesOn.tendsto_metric_inner

theorem ConvergesOn.metric_eq_on_overlap
    {X : FlowSequence.{u}} {P : PointedRiemannianManifold.{u, 0, 0} I3} {f : ℕ → ℕ}
    {F : PointedRiemannianConvergenceMaps (X.atTime 0) P f}
    {D₁ D₂ : RealTimeInterval} {S₁ : SolutionOn (I := I3) (M := P.M) D₁}
    {S₂ : SolutionOn (I := I3) (M := P.M) D₂}
    (h₁ : ConvergesOn F S₁) (h₂ : ConvergesOn F S₂)
    {t : ℝ} (ht₁ : t ∈ D₁.carrier) (ht₂ : t ∈ D₂.carrier) :
    S₁.base.metric t = S₂.base.metric t := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  exact tendsto_nhds_unique (h₁.tendsto_metric_inner ht₁ x v w)
    (h₂.tendsto_metric_inner ht₂ x v w)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ConvergesOn.metric_eq_on_overlap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ConvergesOn.metric_eq_on_overlap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ConvergesOn.metric_eq_on_overlap ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ConvergesOn.metric_eq_on_overlap



end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
