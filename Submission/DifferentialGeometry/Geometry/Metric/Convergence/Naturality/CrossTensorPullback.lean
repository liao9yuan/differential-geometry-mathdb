import Submission.DifferentialGeometry.Geometry.Metric.Convergence.Naturality.CrossTensorCovariantDerivative
import Submission.DifferentialGeometry.Tensor.RSTensor.Coordinates.BasisEvaluation
import Submission.DifferentialGeometry.Tensor.RSTensor.Coordinates.BundleBasis

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Submission.DifferentialGeometry.Tensor.Coordinates
open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Integral.Measure
open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [CompleteSpace F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] [T2Space N]

private local instance tensorPullbackSourceC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tensorPullbackSourceC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tensorPullbackSourceC1 target :: scope.openDecls } }
private local instance tensorPullbackTargetC1 : IsManifold J 1 N :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tensorPullbackTargetC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tensorPullbackTargetC1 target :: scope.openDecls } }

private def crossTensorPullbackValue (Phi : M ≃ₘ⟮I, J⟯ N) (x : M)
    (A : Tensor0SSpace 2 J (Phi x)) : Tensor0SSpace 2 I x :=
  Tensor0SSpace.ofModel (I := I) (x := x)
    ((Tensor0SSpace.toModel A).compContinuousLinearMap
      (fun _ : Fin 2 => tangentLinearMapToModel (mfderiv I J Phi x)))

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.crossTensorPullbackValue
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.crossTensorPullbackValue target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [CompleteSpace E] [FiniteDimensional ℝ F] [CompleteSpace F]
  [T2Space M] [T2Space N] in
private theorem crossTensorPullbackValue_apply (Phi : M ≃ₘ⟮I, J⟯ N) (x : M)
    (A : Tensor0SSpace 2 J (Phi x)) (v : Fin 2 → TangentSpace I x) :
    crossTensorPullbackValue Phi x A v = A (fun j => mfderiv I J Phi x (v j)) := by
  change Tensor0SSpace.eval (crossTensorPullbackValue Phi x A) v = _
  rw [crossTensorPullbackValue, Tensor0SSpace.eval_ofModel,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  simp only [tangentLinearMapToModel_apply,
    ContinuousLinearEquiv.symm_apply_apply, Tensor0SSpace.toModel_apply_tangent,
    Tensor0SSpace.eval_eq]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.crossTensorPullbackValue_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.crossTensorPullbackValue_apply target :: scope.openDecls } }

private def crossTensorPullbackCLM (Phi : M ≃ₘ⟮I, J⟯ N) (x : M) :
    Tensor0SSpace 2 J (Phi x) →L[ℝ] Tensor0SSpace 2 I x :=
  LinearMap.toContinuousLinearMap {
    toFun := crossTensorPullbackValue Phi x
    map_add' := by
      intro A B
      apply tensor0SSpace_ext 2 x
      intro v
      simp only [crossTensorPullbackValue_apply, Tensor0SSpace.add_apply]
    map_smul' := by
      intro c A
      apply tensor0SSpace_ext 2 x
      intro v
      simp only [crossTensorPullbackValue_apply, Tensor0SSpace.smul_apply, RingHom.id_apply] }

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.crossTensorPullbackCLM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.crossTensorPullbackCLM target :: scope.openDecls } }


def pullbackTensor02FieldCross (Phi : M ≃ₘ⟮I, J⟯ N)
    (A : Tensor0SField (I := J) (M := N) (n := ∞) 2) :
    Tensor0SField (I := I) (M := M) (n := ∞) 2 := by
  classical
  unfold Tensor0SField
  let := tensor0SBundleTopology (I := I) (M := M) 2
  refine ⟨fun x => crossTensorPullbackValue Phi x (A (Phi x)), ?_⟩
  intro x0
  rw [_root_.Bundle.contMDiffAt_section]
  let coords : M → Tensor0SModel 2 ℝ E := fun x =>
    ((_root_.FiberBundle.trivializationAt (Tensor0SModel 2 ℝ E)
      (fun x : M => Tensor0SSpace 2 I x) x0)
        ⟨x, crossTensorPullbackValue Phi x (A (Phi x))⟩).2
  let eTan := _root_.FiberBundle.trivializationAt E (TangentSpace I : M → Type _) x0
  have hx0 : x0 ∈ eTan.baseSet := _root_.FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x0
  have hframe := eTan.isLocalFrameOn_localFrame_baseSet I (∞ : WithTop ℕ∞) (chartModelBasis E)
  obtain ⟨V, hV⟩ := hframe.exists_contMDiffSection_eqOn_nhd eTan.open_baseSet hx0
  have hcoords : ∀ sigma : Fin 2 → Fin (Module.finrank ℝ E),
      ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun x => eval0SCLE (E := E) 2 (coords x) sigma) x0 := by
    intro sigma
    have hsmooth := (tensor0SField_eval_smooth_slots_contMDiffAt A
      (fun j => pushFwdSectionCross Phi (V (sigma j))) (Phi x0)).comp x0 Phi.contMDiff.contMDiffAt
    refine hsmooth.congr_of_eventuallyEq ?_
    filter_upwards [eTan.open_baseSet.mem_nhds hx0, hV] with x hx hVx
    rw [eval0SCLE_apply]
    dsimp only [coords]
    rw [Tensor0SSpace.trivializationAt_apply, crossTensorPullbackValue_apply]
    apply congrArg (fun slots => A (Phi x) slots)
    funext j
    rw [pushFwdSectionCross_apply_at_image]
    apply congrArg (mfderiv I J Phi x)
    change eTan.symmL ℝ x (chartModelBasis E (sigma j)) = V (sigma j) x
    rw [hVx (sigma j), Bundle.Trivialization.localFrame_apply_of_mem_baseSet (hx := hx)]
    exact eTan.symmL_apply hx _
  have hPi : ContMDiffAt I
      𝓘(ℝ, (Fin 2 → Fin (Module.finrank ℝ E)) → ℝ) ∞
      (fun x => eval0SCLE (E := E) 2 (coords x)) x0 :=
    contMDiffAt_pi_space.mpr hcoords
  have hresult := (eval0SCLE (E := E) 2).symm.toContinuousLinearMap.contMDiffAt.comp x0 hPi
  simpa only [Function.comp_def, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply] using hresult

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pullbackTensor02FieldCross then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pullbackTensor02FieldCross"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pullbackTensor02FieldCross ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pullbackTensor02FieldCross

omit [CompleteSpace E] [T2Space N] in
theorem pullbackTensor02FieldCross_apply (Phi : M ≃ₘ⟮I, J⟯ N)
    (A : Tensor0SField (I := J) (M := N) (n := ∞) 2)
    (x : M) (v : Fin 2 → TangentSpace I x) :
    pullbackTensor02FieldCross Phi A x v = A (Phi x) (fun j => mfderiv I J Phi x (v j)) :=
  crossTensorPullbackValue_apply Phi x (A (Phi x)) v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pullbackTensor02FieldCross_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pullbackTensor02FieldCross_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pullbackTensor02FieldCross_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pullbackTensor02FieldCross_apply

omit [CompleteSpace E] [T2Space N] in
theorem hasDerivWithinAt_pullbackTensor02FieldCross (Phi : M ≃ₘ⟮I, J⟯ N)
    (A : ℝ → Tensor0SField (I := J) (M := N) (n := ∞) 2)
    (A' : Tensor0SField (I := J) (M := N) (n := ∞) 2)
    {times : Set ℝ} {t : ℝ} (x : M)
    (hA : HasDerivWithinAt (fun s => A s (Phi x)) (A' (Phi x)) times t) :
    HasDerivWithinAt (fun s => pullbackTensor02FieldCross Phi (A s) x)
      (pullbackTensor02FieldCross Phi A' x) times t :=
  (crossTensorPullbackCLM Phi x).hasFDerivAt.comp_hasDerivWithinAt t hA

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.hasDerivWithinAt_pullbackTensor02FieldCross then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.hasDerivWithinAt_pullbackTensor02FieldCross"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.hasDerivWithinAt_pullbackTensor02FieldCross ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.hasDerivWithinAt_pullbackTensor02FieldCross


theorem tensor02CovDerivNormWith_pullbackTensor02FieldCross [SigmaCompactSpace M]
    (gcov gnorm : SmoothRiemannianMetric J N) (Phi : M ≃ₘ⟮I, J⟯ N)
    (A : Tensor0SField (I := J) (M := N) (n := ∞) 2) (a : ℕ) (x : M) :
    tensor02CovDerivNormWith a (pullbackTensor02FieldCross Phi A)
        (DifferentialGeometry.Diffeomorph.pullbackMetricCross gcov Phi)
        (DifferentialGeometry.Diffeomorph.pullbackMetricCross gnorm Phi) x =
      tensor02CovDerivNormWith a A gcov gnorm (Phi x) :=
  tensor02CovDerivNormWith_pullbackCross gcov gnorm Phi (pullbackTensor02FieldCross Phi A) A
    (pullbackTensor02FieldCross_apply Phi A) a x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tensor02CovDerivNormWith_pullbackTensor02FieldCross then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tensor02CovDerivNormWith_pullbackTensor02FieldCross"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tensor02CovDerivNormWith_pullbackTensor02FieldCross ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tensor02CovDerivNormWith_pullbackTensor02FieldCross

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
