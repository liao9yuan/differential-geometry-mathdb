import Submission.DifferentialGeometry.Geometry.Metric.Basic
import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Ricci.Basic
import Submission.DifferentialGeometry.Geometry.Metric.DeTurck.VectorField
import Submission.DifferentialGeometry.Geometry.Metric.LieDerivative.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Submission.DifferentialGeometry.Geometry.Curvature

open _root_.Submission.DifferentialGeometry.Geometry.Connection

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow

open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.ContDiff

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.PDE.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

noncomputable def smoothRiemannianMetricToInfty
    (g : SmoothRiemannianMetric I M) :
    SmoothRiemannianMetric I M := g

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.smoothRiemannianMetricToInfty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.smoothRiemannianMetricToInfty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.smoothRiemannianMetricToInfty ``Submission.DifferentialGeometry.PDE.RicciFlow.smoothRiemannianMetricToInfty

private noncomputable def lieDerivMetricLinearMap
    (g : SmoothRiemannianMetric I M)
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    TangentSpace I x →ₗ[ℝ] (TangentSpace I x →L[ℝ] ℝ) :=
  haveI : T2Space (TangentSpace I x) := inferInstanceAs (T2Space E)
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  { toFun := fun v =>
      LinearMap.toContinuousLinearMap (lieDerivMetric (I := I) g W x v)
    map_add' := fun v v' => by
      ext w
      have := (lieDerivMetric (I := I) g W x).map_add v v'
      have happ := congrArg
        (fun (φ : TangentSpace I x →ₗ[ℝ] ℝ) => φ w) this
      simp [add_apply,
             LinearMap.coe_toContinuousLinearMap']
    map_smul' := fun c v => by
      ext w
      have := (lieDerivMetric (I := I) g W x).map_smul c v
      have happ := congrArg
        (fun (φ : TangentSpace I x →ₗ[ℝ] ℝ) => φ w) this
      simp [smul_apply,
             LinearMap.coe_toContinuousLinearMap', smul_eq_mul]}

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.lieDerivMetricLinearMap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.lieDerivMetricLinearMap target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] private lemma lieDerivMetricLinearMap_apply
    (g : SmoothRiemannianMetric I M)
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M)
    (v w : TangentSpace I x) :
    lieDerivMetricLinearMap (I := I) g W x v w =
      lieDerivMetric (I := I) g W x v w := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.lieDerivMetricLinearMap_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.lieDerivMetricLinearMap_apply target :: scope.openDecls } }

noncomputable def lieDerivMetricClm
    (g : SmoothRiemannianMetric I M)
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : T2Space (TangentSpace I x) := inferInstanceAs (T2Space E)
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    (lieDerivMetricLinearMap (I := I) (smoothRiemannianMetricToInfty (I := I) g) W x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.lieDerivMetricClm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.lieDerivMetricClm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.lieDerivMetricClm ``Submission.DifferentialGeometry.PDE.RicciFlow.lieDerivMetricClm

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem lieDerivMetricClm_apply
    (g : SmoothRiemannianMetric I M)
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (x : M) (v w : TangentSpace I x) :
    lieDerivMetricClm (I := I) g W x v w
      = lieDerivMetric (I := I) (smoothRiemannianMetricToInfty (I := I) g) W x v w := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.lieDerivMetricClm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.lieDerivMetricClm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.lieDerivMetricClm_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.lieDerivMetricClm_apply

noncomputable def deTurckRicciRHS
    (g_bg g : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  (-2 : ℝ) • ricciTensor (I := I) (smoothRiemannianMetricToInfty (I := I) g) x +
    lieDerivMetricClm (I := I) g
      (deTurckVF (I := I) (smoothRiemannianMetricToInfty (I := I) g)
        (smoothRiemannianMetricToInfty (I := I) g_bg)) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS ``Submission.DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem deTurckRicciRHS_apply
    (g_bg g : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    deTurckRicciRHS (I := I) g_bg g x v w
      = (-2 : ℝ) * ricciTensor (I := I) g x v w
        + lieDerivMetric (I := I) g (deTurckVF (I := I) g g_bg) x v w := by
  unfold deTurckRicciRHS
  rw [add_apply, add_apply,
      smul_apply, smul_apply]
  rw [lieDerivMetricClm_apply]
  simp only [smul_eq_mul]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS_apply

end RicciFlow
end PDE
end DifferentialGeometry
