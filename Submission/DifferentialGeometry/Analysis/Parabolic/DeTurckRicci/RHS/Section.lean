import Submission.DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.RHS.Defs
import Submission.DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.LieDerivative.Pairing
import Submission.DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Defs
import Submission.DifferentialGeometry.Tensor.Mixed.Field
import Submission.DifferentialGeometry.Tensor.Multilinear.Curry.FiniteNorm
import Submission.DifferentialGeometry.Tensor.RSTensor.Coordinates.Field

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Tensor.Multilinear


open _root_.Submission.DifferentialGeometry.Analysis.Parabolic
noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle _root_.ContinuousLinearMap _root_.Submission.ContinuousLinearMap _root_.Bundle.ContinuousLinearMap
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow


open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.PDE.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private def deTurckRHSModelFun (g_bg g : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x :=
  (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 2 x).symm
    (biForm₂ToModel (TangentSpace I x) (deTurckRicciRHS (I := I) g_bg g x))

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.deTurckRHSModelFun
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.deTurckRHSModelFun target :: scope.openDecls } }

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private theorem deTurckRHSModelFun_eval
    (g_bg g : SmoothRiemannianMetric I M) (x : M) (v : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.eval (deTurckRHSModelFun (I := I) g_bg g x) v =
      deTurckRicciRHS (I := I) g_bg g x (v 0) (v 1) := by
  unfold deTurckRHSModelFun
  rw [Tensor0SSpace.eval_fiber_equiv_symm]
  exact biForm₂ToModel_apply (TangentSpace I x) (deTurckRicciRHS (I := I) g_bg g x) v

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.deTurckRHSModelFun_eval
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.deTurckRHSModelFun_eval target :: scope.openDecls } }

def deTurckRHSField (g_bg g : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ 2 :=
  letI := tensor0SBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
  letI := TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := ∞)
  ⟨fun x => deTurckRHSModelFun (I := I) g_bg g x, by
    let d := Module.finrank ℝ E
    let b : Module.Basis (Fin d) ℝ E := DifferentialGeometry.Tensor.Coordinates.chartModelBasis E
    refine (contMDiff_multilinearSection_iff_coord (TangentSpace I) ∞ b _).mpr
      fun σ x₀ => ?_
    have hcomp : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun x : M =>
          deTurckRicciRHS (I := I) g_bg g x
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ (σ 0) x)
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ (σ 1) x))
        (chartAt H x₀).source :=
      combine_smoothness_of_summands (I := I) g_bg g x₀ (σ 0) (σ 1)
    have hx₀_source : x₀ ∈ (chartAt H x₀).source := mem_chart_source H x₀
    have hx₀_base : x₀ ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet :=
      _root_.FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x₀
    have h_source_nhd : (chartAt H x₀).source ∈ 𝓝 x₀ :=
      (chartAt H x₀).open_source.mem_nhds hx₀_source
    refine ((hcomp x₀ hx₀_source).contMDiffAt h_source_nhd).congr_of_eventuallyEq ?_
    have h_base_nhd :
        (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet ∈ 𝓝 x₀ :=
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds hx₀_base
    filter_upwards [h_base_nhd] with x hx
    rw [continuousMultilinearMap_basis_repr]
    change Tensor0SSpace.eval (deTurckRHSModelFun (I := I) g_bg g x)
        (fun j => (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).symmL ℝ x (b (σ j))) = _
    rw [deTurckRHSModelFun_eval]
    rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.deTurckRHSField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.deTurckRHSField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.deTurckRHSField ``Submission.DifferentialGeometry.PDE.RicciFlow.deTurckRHSField

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
@[simp] theorem deTurckRHSField_eval
    (g_bg g : SmoothRiemannianMetric I M) (x : M) (v : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.eval (deTurckRHSField (I := I) g_bg g x) v =
      deTurckRicciRHS (I := I) g_bg g x (v 0) (v 1) :=
  deTurckRHSModelFun_eval (I := I) g_bg g x v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.deTurckRHSField_eval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.deTurckRHSField_eval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.deTurckRHSField_eval ``Submission.DifferentialGeometry.PDE.RicciFlow.deTurckRHSField_eval

def deTurckRHSMixedSection (g_bg g : SmoothRiemannianMetric I M) :
    Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun x : M => TensorRSSpace 0 2 I x)⟯ :=
  MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
    (E := (TangentSpace I : M → Type _)) ∞ (deTurckRHSField (I := I) g_bg g)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.deTurckRHSMixedSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.deTurckRHSMixedSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.deTurckRHSMixedSection ``Submission.DifferentialGeometry.PDE.RicciFlow.deTurckRHSMixedSection

def deTurckRHSSection (g_bg g : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 0 2 where
  toSection := deTurckRHSMixedSection (I := I) g_bg g
  hasCompactSupport := HasCompactSupport.of_compactSpace _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.deTurckRHSSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.deTurckRHSSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.deTurckRHSSection ``Submission.DifferentialGeometry.PDE.RicciFlow.deTurckRHSSection

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
@[simp] theorem deTurckRHSSection_toSection
    (g_bg g : SmoothRiemannianMetric I M) :
    (deTurckRHSSection (I := I) g_bg g).toSection =
      deTurckRHSMixedSection (I := I) g_bg g := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.deTurckRHSSection_toSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.deTurckRHSSection_toSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.deTurckRHSSection_toSection ``Submission.DifferentialGeometry.PDE.RicciFlow.deTurckRHSSection_toSection

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem deTurckRHSSection_eval
    (g_bg g : SmoothRiemannianMetric I M) (x : M) (v : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.eval
        ((deTurckRHSSection (I := I) g_bg g).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) v =
      deTurckRicciRHS (I := I) g_bg g x (v 0) (v 1) := by
  classical
  rw [deTurckRHSSection_toSection]
  change Tensor0SSpace.eval
      ((MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (deTurckRHSField (I := I) g_bg g x)
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) v = _
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul,
    deTurckRHSField_eval]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.deTurckRHSSection_eval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.deTurckRHSSection_eval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.deTurckRHSSection_eval ``Submission.DifferentialGeometry.PDE.RicciFlow.deTurckRHSSection_eval

end RicciFlow
end PDE
end DifferentialGeometry

end
