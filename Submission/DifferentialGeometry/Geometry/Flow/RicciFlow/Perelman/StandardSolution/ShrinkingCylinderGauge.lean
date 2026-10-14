import Submission.DifferentialGeometry.Geometry.Curvature.LocalPullbackRicci
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ShrinkingCylinder
import Submission.DifferentialGeometry.Geometry.Curvature.RicciRestriction
import Submission.DifferentialGeometry.Geometry.Metric.CylinderRotation
import Submission.DifferentialGeometry.Geometry.Metric.RoundCylinder

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.TopologicalSpace _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Submission.DifferentialGeometry.Geometry.Metric _root_.Submission.DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2 + 1)]

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instFiniteDimensionalReal_differentialGeometry : FiniteDimensional ℝ E :=
  FiniteDimensional.of_fact_finrank_eq_succ 2

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instFiniteDimensionalReal_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instFiniteDimensionalReal_differentialGeometry target :: scope.openDecls } }

private theorem shrinkingCylinderMetric_affine_eval {t : ℝ} (ht : t < 1)
    (x : Metric.sphere (0 : E) 1 × ℝ)
    (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ)) x) :
    (shrinkingCylinderMetric (E := E) t).inner x v w =
      (shrinkingCylinderMetric (E := E) 0).inner x v w -
        (2 * t) * ricciTensor (shrinkingCylinderMetric (E := E) 0) x v w := by
  have h := congrFun (shrinkingCylinderMetric_affine (E := E) ht) x
  exact congrArg (fun b => b v w) h

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric_affine_eval
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric_affine_eval target :: scope.openDecls } }

theorem localPullMetric_shrinkingCylinderMetric_of_initial
    (U V : _root_.TopologicalSpace.Opens (Metric.sphere (0 : E) 1 × ℝ)) (f : U → V)
    (hf : IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ)) ((𝓡 2).prod 𝓘(ℝ)) ∞ f)
    (hzero : localPullMetric ((shrinkingCylinderMetric (E := E) 0).restrictOpen V) f hf =
      (shrinkingCylinderMetric (E := E) 0).restrictOpen U)
    {t : ℝ} (ht : t < 1) :
    localPullMetric ((shrinkingCylinderMetric (E := E) t).restrictOpen V) f hf =
      (shrinkingCylinderMetric (E := E) t).restrictOpen U := by
  let : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (isSigmaCompact_of_isOpen ((𝓡 2).prod 𝓘(ℝ)) U.isOpen)
  let : SigmaCompactSpace V := isSigmaCompact_iff_sigmaCompactSpace.mp
    (isSigmaCompact_of_isOpen ((𝓡 2).prod 𝓘(ℝ)) V.isOpen)
  have hric (x : U) (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ)) x) :
      ricciTensor (shrinkingCylinderMetric (E := E) 0)
          (f x : Metric.sphere (0 : E) 1 × ℝ)
          (mfderiv ((𝓡 2).prod 𝓘(ℝ)) ((𝓡 2).prod 𝓘(ℝ)) f x v)
          (mfderiv ((𝓡 2).prod 𝓘(ℝ)) ((𝓡 2).prod 𝓘(ℝ)) f x w) =
        ricciTensor (shrinkingCylinderMetric (E := E) 0)
          (x : Metric.sphere (0 : E) 1 × ℝ) v w := by
    have h := ricciTensor_localPullMetric
      ((shrinkingCylinderMetric (E := E) 0).restrictOpen V) f hf x v w
    rw [hzero, DifferentialGeometry.Geometry.Curvature.ricciTensor_restrictOpen, DifferentialGeometry.Geometry.Curvature.ricciTensor_restrictOpen] at h
    simpa only [mfderiv_subtype_val_apply] using h.symm
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  have hz := congrArg
    (fun g : SmoothRiemannianMetric ((𝓡 2).prod 𝓘(ℝ)) U => g.inner x v w) hzero
  rw [localPullMetric_inner, SmoothRiemannianMetric.restrictOpen_inner,
    SmoothRiemannianMetric.restrictOpen_inner] at hz
  have ha := shrinkingCylinderMetric_affine_eval ht
    (f x : Metric.sphere (0 : E) 1 × ℝ)
    (mfderiv ((𝓡 2).prod 𝓘(ℝ)) ((𝓡 2).prod 𝓘(ℝ)) f x v)
    (mfderiv ((𝓡 2).prod 𝓘(ℝ)) ((𝓡 2).prod 𝓘(ℝ)) f x w)
  have hb := shrinkingCylinderMetric_affine_eval ht
    (x : Metric.sphere (0 : E) 1 × ℝ) v w
  have hc := congrArg₂ (fun a b : ℝ => a - (2 * t) * b) hz (hric x v w)
  rw [localPullMetric_inner, SmoothRiemannianMetric.restrictOpen_inner,
    SmoothRiemannianMetric.restrictOpen_inner]
  exact ha.trans (hc.trans hb.symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.localPullMetric_shrinkingCylinderMetric_of_initial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.localPullMetric_shrinkingCylinderMetric_of_initial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.localPullMetric_shrinkingCylinderMetric_of_initial ``Submission.DifferentialGeometry.PDE.RicciFlow.localPullMetric_shrinkingCylinderMetric_of_initial

theorem pullback_shrinkingCylinderMetric_of_initial
    (U V : _root_.TopologicalSpace.Opens (Metric.sphere (0 : E) 1 × ℝ))
    (Φ : U ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ), (𝓡 2).prod 𝓘(ℝ)⟯ V)
    (hzero : Diffeomorph.pullbackMetric
      ((shrinkingCylinderMetric (E := E) 0).restrictOpen V) Φ =
        (shrinkingCylinderMetric (E := E) 0).restrictOpen U)
    {t : ℝ} (ht : t < 1) :
    Diffeomorph.pullbackMetric ((shrinkingCylinderMetric (E := E) t).restrictOpen V) Φ =
      (shrinkingCylinderMetric (E := E) t).restrictOpen U := by
  have hlocal (s : ℝ) :
      localPullMetric ((shrinkingCylinderMetric (E := E) s).restrictOpen V)
          Φ Φ.isLocalDiffeomorph =
        Diffeomorph.pullbackMetric ((shrinkingCylinderMetric (E := E) s).restrictOpen V) Φ := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rw [localPullMetric_inner, Diffeomorph.pullbackMetric_inner]
  have h := localPullMetric_shrinkingCylinderMetric_of_initial U V Φ
    Φ.isLocalDiffeomorph ((hlocal 0).trans hzero) ht
  rw [hlocal t] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.pullback_shrinkingCylinderMetric_of_initial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.pullback_shrinkingCylinderMetric_of_initial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.pullback_shrinkingCylinderMetric_of_initial ``Submission.DifferentialGeometry.PDE.RicciFlow.pullback_shrinkingCylinderMetric_of_initial

theorem pullback_shrinkingCylinderMetric_roundCylinderRestrict
    (e : E ≃ₗᵢ[ℝ] E) (a : ℝ) (U : _root_.TopologicalSpace.Opens (Metric.sphere (0 : E) 1 × ℝ))
    {t : ℝ} (ht : t < 1) :
    Diffeomorph.pullbackMetric
      ((shrinkingCylinderMetric (E := E) t).restrictOpen
        (roundCylinderImage (n := 2) e a U))
      (roundCylinderRestrict (n := 2) e a U) =
        (shrinkingCylinderMetric (E := E) t).restrictOpen U := by
  apply pullback_shrinkingCylinderMetric_of_initial U
    (roundCylinderImage (n := 2) e a U) (roundCylinderRestrict (n := 2) e a U) _ ht
  simpa only [shrinkingCylinderMetric_zero] using
    pullback_roundCylinderMetric_roundCylinderRestrict (n := 2) e a U

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.pullback_shrinkingCylinderMetric_roundCylinderRestrict then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.pullback_shrinkingCylinderMetric_roundCylinderRestrict"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.pullback_shrinkingCylinderMetric_roundCylinderRestrict ``Submission.DifferentialGeometry.PDE.RicciFlow.pullback_shrinkingCylinderMetric_roundCylinderRestrict

end DifferentialGeometry.PDE.RicciFlow

end
