import Submission.DifferentialGeometry.Geometry.Exponential.DiagonalExponential.LocalInverse

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.Set
open scoped _root_.Topology _root_.ContDiff _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic

namespace DifferentialGeometry.Geometry.Topology

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

section FrameLaunch

variable {U V E : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hasFDerivAt_frameLaunch_zero {σ : U → E} {σ' : U →L[ℝ] E}
    {A : U → V →L[ℝ] E} {u : U}
    (hσ : HasFDerivAt σ σ' u) (hA : DifferentiableAt ℝ A u) :
    HasFDerivAt (fun z : U × V => (σ z.1, A z.1 z.2))
      ((σ'.comp (ContinuousLinearMap.fst ℝ U V)).prod
        ((A u).comp (ContinuousLinearMap.snd ℝ U V))) (u, 0) := by
  have hfst : HasFDerivAt (Prod.fst : U × V → U)
      (ContinuousLinearMap.fst ℝ U V) (u, 0) := hasFDerivAt_fst
  have hAcomp := hA.hasFDerivAt.comp (u, (0 : V)) hfst
  have heval := hAcomp.clm_apply
    (hasFDerivAt_snd : HasFDerivAt (Prod.snd : U × V → V)
      (ContinuousLinearMap.snd ℝ U V) (u, 0))
  have heval' : HasFDerivAt (fun z : U × V => A z.1 z.2)
      ((A u).comp (ContinuousLinearMap.snd ℝ U V)) (u, 0) := by
    simpa only [Function.comp_apply, ContinuousLinearMap.flip_apply, map_zero, add_zero] using heval
  exact (hσ.comp (u, (0 : V)) hfst).prodMk heval'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.hasFDerivAt_frameLaunch_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.hasFDerivAt_frameLaunch_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.hasFDerivAt_frameLaunch_zero ``Submission.DifferentialGeometry.Geometry.Topology.hasFDerivAt_frameLaunch_zero

end FrameLaunch

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)]

def tangentChartExp (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) g) (p : M) : E × E → E :=
  fun z => (writtenInExtChartAt I.tangent (I.prod I)
    (⟨p, (0 : E)⟩ : TangentBundle I M) (diagExp (I := I) g hEnorm) z).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.tangentChartExp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.tangentChartExp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.tangentChartExp ``Submission.DifferentialGeometry.Geometry.Topology.tangentChartExp

omit [T2Space (TangentBundle I M)] in
theorem tangentChartExp_apply (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) g) (p : M) (z : E × E) :
    tangentChartExp (I := I) g hEnorm p z =
      extChartAt I p (expMapIntrinsic (I := I) g hEnorm
        ((extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).symm z).proj
        ((extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).symm z).snd) := by
  have hzero : diagExp (I := I) g hEnorm
      (⟨p, (0 : E)⟩ : TangentBundle I M) = (p, p) := by
    rw [diagExp_apply]
    exact Prod.ext rfl (expMapIntrinsic_zero (I := I) g hEnorm p)
  simp only [tangentChartExp, writtenInExtChartAt, Function.comp_apply,
    hzero, extChartAt_prod, PartialEquiv.prod_coe, diagExp_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.tangentChartExp_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.tangentChartExp_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.tangentChartExp_apply ``Submission.DifferentialGeometry.Geometry.Topology.tangentChartExp_apply

theorem tangentChartExp_hasFDerivAt_zero (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) g) (p : M) :
    HasFDerivAt (tangentChartExp (I := I) g hEnorm p)
      (ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E)
      (extChartAt I p p, 0) := by
  have h := (diagExp_hasFDerivAt_zero_linearEquiv (I := I) g hEnorm p 1 le_rfl).snd
  change HasFDerivAt (tangentChartExp (I := I) g hEnorm p)
    ((ContinuousLinearMap.snd ℝ E E).comp
      (DifferentialGeometry.PhaseFlow.freeDiagCLE (E := E) : (E × E) →L[ℝ] (E × E)))
    (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)
      (⟨p, (0 : E)⟩ : TangentBundle I M)) at h
  have hpt : extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)
      (⟨p, (0 : E)⟩ : TangentBundle I M) = (extChartAt I p p, 0) := by
    rw [extChartAt_tangent_zero_apply_chartFiber (I := I) p
      (p := (⟨p, (0 : E)⟩ : TangentBundle I M)) (mem_chart_source H p)]
    exact Prod.ext rfl (chartFiberCoord_self_zero (I := I) p)
  have hsum : (ContinuousLinearMap.snd ℝ E E).comp
      (DifferentialGeometry.PhaseFlow.freeDiagCLE (E := E) : (E × E) →L[ℝ] (E × E)) =
      ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E := by
    apply ContinuousLinearMap.ext
    intro z
    rfl
  rwa [hpt, hsum] at h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.tangentChartExp_hasFDerivAt_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.tangentChartExp_hasFDerivAt_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.tangentChartExp_hasFDerivAt_zero ``Submission.DifferentialGeometry.Geometry.Topology.tangentChartExp_hasFDerivAt_zero

theorem tangentChartExp_frameLaunch_hasFDerivAt_zero
    {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g) (p : M)
    {σ : U → E} {σ' : U →L[ℝ] E} {A : U → V →L[ℝ] E} {u : U}
    (hσ : HasFDerivAt σ σ' u) (hA : DifferentiableAt ℝ A u)
    (hσp : σ u = extChartAt I p p) :
    HasFDerivAt (fun z : U × V =>
        tangentChartExp (I := I) g hEnorm p (σ z.1, A z.1 z.2))
      (σ'.comp (ContinuousLinearMap.fst ℝ U V) +
        (A u).comp (ContinuousLinearMap.snd ℝ U V)) (u, 0) := by
  have he : HasFDerivAt (tangentChartExp (I := I) g hEnorm p)
      (ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E)
      (σ u, A u 0) := by
    simpa only [hσp, map_zero] using tangentChartExp_hasFDerivAt_zero (I := I) g hEnorm p
  have h := he.comp (u, (0 : V)) (hasFDerivAt_frameLaunch_zero hσ hA)
  apply h.congr_fderiv
  apply ContinuousLinearMap.ext
  intro z
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.tangentChartExp_frameLaunch_hasFDerivAt_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.tangentChartExp_frameLaunch_hasFDerivAt_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.tangentChartExp_frameLaunch_hasFDerivAt_zero ``Submission.DifferentialGeometry.Geometry.Topology.tangentChartExp_frameLaunch_hasFDerivAt_zero

end DifferentialGeometry.Geometry.Topology

end
