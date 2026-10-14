import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry

open scoped _root_.Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

def tangentSpaceModelContinuousLinearEquiv (x : M) : TangentSpace I x ≃L[𝕜] E := by
  unfold TangentSpace
  exact ContinuousLinearEquiv.refl 𝕜 E

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.tangentSpaceModelContinuousLinearEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.tangentSpaceModelContinuousLinearEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.tangentSpaceModelContinuousLinearEquiv ``Submission.DifferentialGeometry.tangentSpaceModelContinuousLinearEquiv

theorem tangentSpaceModelContinuousLinearEquiv_apply (x : M)
    (v : TangentSpace I x) : tangentSpaceModelContinuousLinearEquiv (I := I) x v = v := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.tangentSpaceModelContinuousLinearEquiv_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.tangentSpaceModelContinuousLinearEquiv_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.tangentSpaceModelContinuousLinearEquiv_apply ``Submission.DifferentialGeometry.tangentSpaceModelContinuousLinearEquiv_apply

theorem tangentSpaceModelContinuousLinearEquiv_symm_apply (x : M) (v : E) :
    (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm v = v := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.tangentSpaceModelContinuousLinearEquiv_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.tangentSpaceModelContinuousLinearEquiv_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.tangentSpaceModelContinuousLinearEquiv_symm_apply ``Submission.DifferentialGeometry.tangentSpaceModelContinuousLinearEquiv_symm_apply

noncomputable def tangentLinearMapToModel
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
    {x : M} {y : M'} (A : TangentSpace I x →L[𝕜] TangentSpace I' y) : E →L[𝕜] E' :=
  (tangentSpaceModelContinuousLinearEquiv (I := I') y).toContinuousLinearMap.comp
    (A.comp (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm.toContinuousLinearMap)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.tangentLinearMapToModel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.tangentLinearMapToModel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.tangentLinearMapToModel ``Submission.DifferentialGeometry.tangentLinearMapToModel

theorem tangentLinearMapToModel_apply
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
    {x : M} {y : M'} (A : TangentSpace I x →L[𝕜] TangentSpace I' y) (v : E) :
    tangentLinearMapToModel A v =
      tangentSpaceModelContinuousLinearEquiv (I := I') y
        (A ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm v)) := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.tangentLinearMapToModel_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.tangentLinearMapToModel_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.tangentLinearMapToModel_apply ``Submission.DifferentialGeometry.tangentLinearMapToModel_apply

theorem tangentLinearMapToModel_comp
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
    {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''}
    {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H'' M'']
    {x : M} {y : M'} {z : M''}
    (A : TangentSpace I x →L[𝕜] TangentSpace I' y)
    (B : TangentSpace I'' z →L[𝕜] TangentSpace I x) :
    tangentLinearMapToModel (A.comp B) =
      (tangentLinearMapToModel A).comp (tangentLinearMapToModel B) := by
  ext v
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.tangentLinearMapToModel_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.tangentLinearMapToModel_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.tangentLinearMapToModel_comp ``Submission.DifferentialGeometry.tangentLinearMapToModel_comp

theorem tangentLinearMapToModel_injective
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
    {x : M} {y : M'} :
    Function.Injective
      (tangentLinearMapToModel (I := I) (I' := I') (x := x) (y := y)) := by
  intro A B h
  apply ContinuousLinearMap.ext
  intro v
  apply (tangentSpaceModelContinuousLinearEquiv (I := I') y).injective
  have hv := DFunLike.congr_fun h
    (tangentSpaceModelContinuousLinearEquiv (I := I) x v)
  simpa only [tangentLinearMapToModel_apply,
    ContinuousLinearEquiv.symm_apply_apply] using hv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.tangentLinearMapToModel_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.tangentLinearMapToModel_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.tangentLinearMapToModel_injective ``Submission.DifferentialGeometry.tangentLinearMapToModel_injective

noncomputable def tangentLinearMapOfModel
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
    {x : M} {y : M'} (A : E →L[𝕜] E') :
    TangentSpace I x →L[𝕜] TangentSpace I' y :=
  (tangentSpaceModelContinuousLinearEquiv (I := I') y).symm.toContinuousLinearMap.comp
    (A.comp (tangentSpaceModelContinuousLinearEquiv (I := I) x).toContinuousLinearMap)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.tangentLinearMapOfModel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.tangentLinearMapOfModel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.tangentLinearMapOfModel ``Submission.DifferentialGeometry.tangentLinearMapOfModel

theorem tangentLinearMapToModel_ofModel
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
    {x : M} {y : M'} (A : E →L[𝕜] E') :
    tangentLinearMapToModel (tangentLinearMapOfModel (I := I) (I' := I')
      (x := x) (y := y) A) = A := by
  ext v
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.tangentLinearMapToModel_ofModel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.tangentLinearMapToModel_ofModel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.tangentLinearMapToModel_ofModel ``Submission.DifferentialGeometry.tangentLinearMapToModel_ofModel

theorem tangentLinearMapOfModel_toModel
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
    {x : M} {y : M'} (A : TangentSpace I x →L[𝕜] TangentSpace I' y) :
    tangentLinearMapOfModel (I := I) (I' := I') (x := x) (y := y)
      (tangentLinearMapToModel A) = A := by
  apply tangentLinearMapToModel_injective
  rw [tangentLinearMapToModel_ofModel]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.tangentLinearMapOfModel_toModel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.tangentLinearMapOfModel_toModel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.tangentLinearMapOfModel_toModel ``Submission.DifferentialGeometry.tangentLinearMapOfModel_toModel

theorem ModelWithCorners.hasMFDerivAt_model (I : ModelWithCorners 𝕜 E H) {x : H} :
    HasMFDerivAt I 𝓘(𝕜, E) I x
      (tangentLinearMapOfModel (I := I) (I' := 𝓘(𝕜, E))
        (x := x) (y := I x) (ContinuousLinearMap.id 𝕜 E)) := by
  refine ⟨I.continuousAt, ?_⟩
  exact (hasFDerivWithinAt_id (𝕜 := 𝕜) (I x) _).congr'
    I.rightInvOn (Set.mem_range_self x)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.ModelWithCorners
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.ModelWithCorners.hasMFDerivAt_model then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.ModelWithCorners.hasMFDerivAt_model"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.ModelWithCorners.hasMFDerivAt_model ``Submission.DifferentialGeometry.ModelWithCorners.hasMFDerivAt_model

theorem ModelWithCorners.hasMFDerivWithinAt_model
    (I : ModelWithCorners 𝕜 E H) {s : Set H} {x : H} :
    HasMFDerivWithinAt I 𝓘(𝕜, E) I s x
      (tangentLinearMapOfModel (I := I) (I' := 𝓘(𝕜, E))
        (x := x) (y := I x) (ContinuousLinearMap.id 𝕜 E)) :=
  (ModelWithCorners.hasMFDerivAt_model I).hasMFDerivWithinAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.ModelWithCorners.hasMFDerivWithinAt_model then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.ModelWithCorners.hasMFDerivWithinAt_model"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.ModelWithCorners.hasMFDerivWithinAt_model ``Submission.DifferentialGeometry.ModelWithCorners.hasMFDerivWithinAt_model

noncomputable def tangentLinearMapCodomainToModel
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
    {x : M} {y : M'}
    (A : TangentSpace I x →L[𝕜] TangentSpace I' y) :
    TangentSpace I x →L[𝕜] E' :=
  (tangentSpaceModelContinuousLinearEquiv (I := I') y).toContinuousLinearMap.comp A

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.tangentLinearMapCodomainToModel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.tangentLinearMapCodomainToModel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.tangentLinearMapCodomainToModel ``Submission.DifferentialGeometry.tangentLinearMapCodomainToModel

theorem tangentLinearMapCodomainToModel_apply
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
    {x : M} {y : M'}
    (A : TangentSpace I x →L[𝕜] TangentSpace I' y) (v : TangentSpace I x) :
    tangentLinearMapCodomainToModel A v =
      tangentSpaceModelContinuousLinearEquiv (I := I') y (A v) := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.tangentLinearMapCodomainToModel_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.tangentLinearMapCodomainToModel_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.tangentLinearMapCodomainToModel_apply ``Submission.DifferentialGeometry.tangentLinearMapCodomainToModel_apply

theorem tangentLinearMapCodomainToModel_injective
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
    {x : M} {y : M'} :
    Function.Injective
      (tangentLinearMapCodomainToModel (I := I) (I' := I') (x := x) (y := y)) := by
  intro A B h
  apply ContinuousLinearMap.ext
  intro v
  apply (tangentSpaceModelContinuousLinearEquiv (I := I') y).injective
  exact DFunLike.congr_fun h v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.tangentLinearMapCodomainToModel_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.tangentLinearMapCodomainToModel_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.tangentLinearMapCodomainToModel_injective ``Submission.DifferentialGeometry.tangentLinearMapCodomainToModel_injective

theorem tangentLinearMapCodomainToModel_zero
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
    {x : M} {y : M'} :
    tangentLinearMapCodomainToModel
        (0 : TangentSpace I x →L[𝕜] TangentSpace I' y) = 0 := by
  ext v
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.tangentLinearMapCodomainToModel_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.tangentLinearMapCodomainToModel_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.tangentLinearMapCodomainToModel_zero ``Submission.DifferentialGeometry.tangentLinearMapCodomainToModel_zero

noncomputable def modelLinearMapToTangent
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {A : E →L[𝕜] E'} {x : E} {y : E'} :
    TangentSpace 𝓘(𝕜, E) x →L[𝕜] TangentSpace 𝓘(𝕜, E') y :=
  (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(𝕜, E')) y).symm.toContinuousLinearMap.comp
    (A.comp (tangentSpaceModelContinuousLinearEquiv
      (I := 𝓘(𝕜, E)) x).toContinuousLinearMap)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.modelLinearMapToTangent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.modelLinearMapToTangent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.modelLinearMapToTangent ``Submission.DifferentialGeometry.modelLinearMapToTangent

theorem tangentLinearMapToModel_modelLinearMapToTangent
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {A : E →L[𝕜] E'} {x : E} {y : E'} :
    tangentLinearMapToModel
        (modelLinearMapToTangent (x := x) (y := y) (A := A)) = A := by
  ext v
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.tangentLinearMapToModel_modelLinearMapToTangent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.tangentLinearMapToModel_modelLinearMapToTangent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.tangentLinearMapToModel_modelLinearMapToTangent ``Submission.DifferentialGeometry.tangentLinearMapToModel_modelLinearMapToTangent

theorem modelLinearMapToTangent_toSpanSingleton
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {x : 𝕜} {y : E'} (w : E') :
    modelLinearMapToTangent (x := x) (y := y)
        (A := ContinuousLinearMap.toSpanSingleton 𝕜 w) =
      ContinuousLinearMap.smulRight
        (tangentSpaceModelContinuousLinearEquiv
          (I := 𝓘(𝕜, 𝕜)) x).toContinuousLinearMap
        ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(𝕜, E')) y).symm w) := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.modelLinearMapToTangent_toSpanSingleton then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.modelLinearMapToTangent_toSpanSingleton"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.modelLinearMapToTangent_toSpanSingleton ``Submission.DifferentialGeometry.modelLinearMapToTangent_toSpanSingleton

theorem HasFDerivWithinAt.hasMFDerivWithinAt_model
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {f : E → E'} {s : Set E} {x : E} {A : E →L[𝕜] E'}
    (h : HasFDerivWithinAt f A s x) :
    HasMFDerivWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E') f s x
      (modelLinearMapToTangent (x := x) (y := f x) (A := A)) := by
  have hraw := h.hasMFDerivWithinAt
  refine hraw.congr_mfderiv ?_
  apply tangentLinearMapToModel_injective
  rw [tangentLinearMapToModel_modelLinearMapToTangent]
  ext v
  rfl

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.HasFDerivWithinAt
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.HasFDerivWithinAt.hasMFDerivWithinAt_model then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.HasFDerivWithinAt.hasMFDerivWithinAt_model"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.HasFDerivWithinAt.hasMFDerivWithinAt_model ``Submission.DifferentialGeometry.HasFDerivWithinAt.hasMFDerivWithinAt_model

theorem HasFDerivAt.hasMFDerivAt_model
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {f : E → E'} {x : E} {A : E →L[𝕜] E'}
    (h : HasFDerivAt f A x) :
    HasMFDerivAt 𝓘(𝕜, E) 𝓘(𝕜, E') f x
      (modelLinearMapToTangent (x := x) (y := f x) (A := A)) :=
  hasMFDerivWithinAt_univ.mp
    (HasFDerivWithinAt.hasMFDerivWithinAt_model
      (s := Set.univ) h.hasFDerivWithinAt)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.HasFDerivAt
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.HasFDerivAt.hasMFDerivAt_model then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.HasFDerivAt.hasMFDerivAt_model"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.HasFDerivAt.hasMFDerivAt_model ``Submission.DifferentialGeometry.HasFDerivAt.hasMFDerivAt_model

theorem HasMFDerivWithinAt.hasFDerivWithinAt_model
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {f : E → E'} {s : Set E} {x : E}
    {A : TangentSpace 𝓘(𝕜, E) x →L[𝕜] TangentSpace 𝓘(𝕜, E') (f x)}
    (h : HasMFDerivWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E') f s x A) :
    HasFDerivWithinAt f (tangentLinearMapToModel A) s x := by
  let : NormedAddCommGroup (TangentSpace 𝓘(𝕜, E) x) :=
    inferInstanceAs (NormedAddCommGroup E)
  let : NormedSpace 𝕜 (TangentSpace 𝓘(𝕜, E) x) := {
    norm_smul_le a b := by
      change ‖a • (show E from b)‖ ≤ ‖a‖ * ‖(show E from b)‖
      exact norm_smul_le a (show E from b) }
  let : NormedAddCommGroup (TangentSpace 𝓘(𝕜, E') (f x)) :=
    inferInstanceAs (NormedAddCommGroup E')
  let : NormedSpace 𝕜 (TangentSpace 𝓘(𝕜, E') (f x)) := {
    norm_smul_le a b := by
      change ‖a • (show E' from b)‖ ≤ ‖a‖ * ‖(show E' from b)‖
      exact norm_smul_le a (show E' from b) }
  let eIn := tangentSpaceModelContinuousLinearEquiv (I := 𝓘(𝕜, E)) x
  let eOut := tangentSpaceModelContinuousLinearEquiv (I := 𝓘(𝕜, E')) (f x)
  have hraw := h.hasFDerivWithinAt
  have hout := eOut.hasFDerivAt.comp_hasFDerivWithinAt x hraw
  have hin : HasFDerivWithinAt (eIn.symm : E → TangentSpace 𝓘(𝕜, E) x)
      eIn.symm.toContinuousLinearMap s x :=
    eIn.symm.hasFDerivAt.hasFDerivWithinAt
  have hboth := hout.comp x hin (by
    intro y hy
    exact hy)
  convert hboth using 1
  · ext v
    rfl
  · ext v
    rfl

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.HasMFDerivWithinAt
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.HasMFDerivWithinAt.hasFDerivWithinAt_model then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.HasMFDerivWithinAt.hasFDerivWithinAt_model"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.HasMFDerivWithinAt.hasFDerivWithinAt_model ``Submission.DifferentialGeometry.HasMFDerivWithinAt.hasFDerivWithinAt_model

theorem HasMFDerivAt.hasFDerivAt_model
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {f : E → E'} {x : E}
    {A : TangentSpace 𝓘(𝕜, E) x →L[𝕜] TangentSpace 𝓘(𝕜, E') (f x)}
    (h : HasMFDerivAt 𝓘(𝕜, E) 𝓘(𝕜, E') f x A) :
    HasFDerivAt f (tangentLinearMapToModel A) x :=
  (HasMFDerivWithinAt.hasFDerivWithinAt_model
    (s := Set.univ) h.hasMFDerivWithinAt).hasFDerivAt_of_univ

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.HasMFDerivAt
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.HasMFDerivAt.hasFDerivAt_model then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.HasMFDerivAt.hasFDerivAt_model"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.HasMFDerivAt.hasFDerivAt_model ``Submission.DifferentialGeometry.HasMFDerivAt.hasFDerivAt_model

noncomputable def tangentBilinearFormToModel [hI : IsManifold I 1 M] (x : M)
    (A : TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] 𝕜) :
    E →L[𝕜] E →L[𝕜] 𝕜 := by
  let _ := hI
  letI : NormedAddCommGroup (TangentSpace I x) :=
    inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace 𝕜 (TangentSpace I x) := ‹NormedSpace 𝕜 E›
  exact (((A.comp (tangentSpaceModelContinuousLinearEquiv
      (I := I) x).symm.toContinuousLinearMap).flip.comp
    (tangentSpaceModelContinuousLinearEquiv
      (I := I) x).symm.toContinuousLinearMap).flip)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.tangentBilinearFormToModel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.tangentBilinearFormToModel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.tangentBilinearFormToModel ``Submission.DifferentialGeometry.tangentBilinearFormToModel

theorem tangentBilinearFormToModel_apply [IsManifold I 1 M] (x : M)
    (A : TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] 𝕜) (v w : E) :
    tangentBilinearFormToModel (I := I) x A v w =
      A ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm v)
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm w) := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.tangentBilinearFormToModel_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.tangentBilinearFormToModel_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.tangentBilinearFormToModel_apply ``Submission.DifferentialGeometry.tangentBilinearFormToModel_apply

noncomputable def constantModelVectorField (v : E) (x : E) : TangentSpace 𝓘(𝕜, E) x :=
  (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(𝕜, E)) x).symm v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.constantModelVectorField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.constantModelVectorField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.constantModelVectorField ``Submission.DifferentialGeometry.constantModelVectorField

theorem constantModelVectorField_apply (v x : E) :
    tangentSpaceModelContinuousLinearEquiv (I := 𝓘(𝕜, E)) x
        (constantModelVectorField v x) = v := by
  exact (tangentSpaceModelContinuousLinearEquiv
    (I := 𝓘(𝕜, E)) x).apply_symm_apply v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.constantModelVectorField_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.constantModelVectorField_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.constantModelVectorField_apply ``Submission.DifferentialGeometry.constantModelVectorField_apply

theorem mvfderiv_apply_eq_fderivWithin_writtenInExtChartAt
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : M → F} {x : M} (hf : MDifferentiableAt I 𝓘(𝕜, F) f x)
    (v : TangentSpace I x) :
    mvfderiv I f x v =
      fderivWithin 𝕜 (writtenInExtChartAt I 𝓘(𝕜, F) x f) (Set.range I)
        (extChartAt I x x) (tangentSpaceModelContinuousLinearEquiv (I := I) x v) := by
  rw [hf.mvfderiv]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.mvfderiv_apply_eq_fderivWithin_writtenInExtChartAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.mvfderiv_apply_eq_fderivWithin_writtenInExtChartAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.mvfderiv_apply_eq_fderivWithin_writtenInExtChartAt ``Submission.DifferentialGeometry.mvfderiv_apply_eq_fderivWithin_writtenInExtChartAt

theorem mvfderivWithin_model_apply_eq_fderivWithin
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E → F} {s : Set E} {x : E}
    (v : TangentSpace 𝓘(𝕜, E) x) :
    mvfderivWithin 𝓘(𝕜, E) f s x v =
      fderivWithin 𝕜 f s x
        (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(𝕜, E)) x v) := by
  unfold mvfderivWithin
  rw [mfderivWithin_eq_fderivWithin]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.mvfderivWithin_model_apply_eq_fderivWithin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.mvfderivWithin_model_apply_eq_fderivWithin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.mvfderivWithin_model_apply_eq_fderivWithin ``Submission.DifferentialGeometry.mvfderivWithin_model_apply_eq_fderivWithin

theorem mvfderiv_model_apply_eq_fderiv
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E → F} {x : E} (v : TangentSpace 𝓘(𝕜, E) x) :
    mvfderiv 𝓘(𝕜, E) f x v =
      fderiv 𝕜 f x
        (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(𝕜, E)) x v) := by
  rw [← mvfderivWithin_univ, mvfderivWithin_model_apply_eq_fderivWithin,
    fderivWithin_univ]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.mvfderiv_model_apply_eq_fderiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.mvfderiv_model_apply_eq_fderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.mvfderiv_model_apply_eq_fderiv ``Submission.DifferentialGeometry.mvfderiv_model_apply_eq_fderiv

open _root_.Bundle _root_.Manifold in
open scoped _root_.ContDiff in
theorem contMDiff_tangentFiber [IsManifold I 1 M] {n : ℕ∞ω} (p : M) :
    ContMDiff 𝓘(𝕜, E) I.tangent n (fun v : E => (⟨p, v⟩ : TangentBundle I M)) := by
  intro v
  rw [_root_.Bundle.contMDiffAt_totalSpace]
  refine ⟨contMDiffAt_const, ?_⟩
  have hp : p ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) p).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact mem_chart_source H p
  have heq : (fun w : E => (_root_.FiberBundle.trivializationAt E (TangentSpace I) p
      (⟨p, w⟩ : TangentBundle I M)).2) =
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) p).continuousLinearMapAt 𝕜 p := by
    funext w
    exact (congrFun ((_root_.FiberBundle.trivializationAt E (TangentSpace I) p).coe_linearMapAt_of_mem
      (R := 𝕜) hp) w).symm
  change ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, E) n (fun w : E =>
    (_root_.FiberBundle.trivializationAt E (TangentSpace I) p (⟨p, w⟩ : TangentBundle I M)).2) v
  rw [heq]
  exact (show E →L[𝕜] E from
    (_root_.FiberBundle.trivializationAt E (TangentSpace I) p).continuousLinearMapAt 𝕜 p).contMDiff.contMDiffAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.contMDiff_tangentFiber then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.contMDiff_tangentFiber"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.contMDiff_tangentFiber ``Submission.DifferentialGeometry.contMDiff_tangentFiber

end DifferentialGeometry
