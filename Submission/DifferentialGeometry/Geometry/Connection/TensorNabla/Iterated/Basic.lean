import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.RawDefs.MCovariant
import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.RawDefs.Bundled
import Submission.DifferentialGeometry.Tensor.RSTensor.Coordinates.Expansion
import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.Connection.Endomorphism
import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.Regularity.Tensor0S
import Submission.DifferentialGeometry.Bundle.PartialMfderiv.Basic
import Submission.DifferentialGeometry.Bundle.PartialMfderiv.ModelMixed
import Submission.DifferentialGeometry.Geometry.Coordinates.Calculus.FixedBaseDerivative

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry
namespace TensorLieDeriv

noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.IsManifold _root_.ContinuousLinearMap _root_.Submission.ContinuousLinearMap _root_.Bundle.ContinuousLinearMap _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]

section Model

noncomputable def totalCovDerivTensor0SModelAt (s : ℕ)
    (Dα : E →L[𝕜] Tensor0SModel s 𝕜 E) (Γ : E →L[𝕜] E →L[𝕜] E)
    (α : Tensor0SModel s 𝕜 E) : Tensor0SModel (s + 1) 𝕜 E :=
  ContinuousLinearMap.uncurryLeft
    (𝕜 := 𝕜) (n := s) (Ei := fun _ : Fin (s + 1) => E) (G := 𝕜)
    (LinearMap.toContinuousLinearMap
      { toFun := fun X =>
          covariantDerivTensor0SModelAt (𝕜 := 𝕜) (E := E) s
            (Dα X) (Γ X) α
        map_add' := by
          intro X Y
          simp only [map_add]
          rw [covariantDeriv_tensor0SModelAt_apply]
          rw [covariantDeriv_tensor0SModelAt_apply]
          rw [covariantDeriv_tensor0SModelAt_apply]
          rw [lieDeriv_correction_add_right]
          abel
        map_smul' := by
          intro c X
          simp only [map_smul]
          rw [covariantDeriv_tensor0SModelAt_apply]
          rw [covariantDeriv_tensor0SModelAt_apply]
          rw [lieDeriv_correction_smul_right]
          ext slots
          simp [sub_eq_add_neg] })

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.TensorLieDeriv.totalCovDerivTensor0SModelAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.TensorLieDeriv.totalCovDerivTensor0SModelAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.TensorLieDeriv.totalCovDerivTensor0SModelAt ``Submission.DifferentialGeometry.TensorLieDeriv.totalCovDerivTensor0SModelAt

@[simp]
theorem totalCovDeriv_tensor0SModelAt_apply_cons (s : ℕ)
    (Dα : E →L[𝕜] Tensor0SModel s 𝕜 E) (Γ : E →L[𝕜] E →L[𝕜] E)
    (α : Tensor0SModel s 𝕜 E) (X : E) (slots : Fin s → E) :
    totalCovDerivTensor0SModelAt (𝕜 := 𝕜) (E := E) s Dα Γ α
        (Fin.cons X slots) =
      covariantDerivTensor0SModelAt (𝕜 := 𝕜) (E := E) s (Dα X) (Γ X) α slots := by
  unfold totalCovDerivTensor0SModelAt
  rw [ContinuousLinearMap.uncurryLeft_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.TensorLieDeriv.totalCovDeriv_tensor0SModelAt_apply_cons then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.TensorLieDeriv.totalCovDeriv_tensor0SModelAt_apply_cons"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.TensorLieDeriv.totalCovDeriv_tensor0SModelAt_apply_cons ``Submission.DifferentialGeometry.TensorLieDeriv.totalCovDeriv_tensor0SModelAt_apply_cons

end Model

end

end TensorLieDeriv

namespace Tensor0SBundle

noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.IsManifold _root_.ContinuousLinearMap _root_.Submission.ContinuousLinearMap _root_.Bundle.ContinuousLinearMap _root_.Submission.DifferentialGeometry.TensorLieDeriv
open scoped _root_.Manifold _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I (∞ : WithTop ℕ∞) M]

noncomputable def totalNabla0SFun (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x₀ : M) : Tensor0SSpace (s + 1) I x₀ := by
  letI := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (s + 1)
  exact (_root_.FiberBundle.trivializationAt (Tensor0SModel (s + 1) 𝕜 E)
    (fun x : M => Tensor0SSpace (s + 1) I x) x₀).symm x₀
    (totalCovDerivTensor0SModelAt (𝕜 := 𝕜) (E := E) s
      (fderivWithin 𝕜
        (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          s x₀ (fun x => α x))
        (Set.range I) (extChartAt I x₀ x₀))
      (connectionEndomorphismInChartL (𝕜 := 𝕜) (I := I) cov x₀
        (extChartAt I x₀ x₀))
      (tensor0SModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s x₀ x₀ (α x₀)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.totalNabla0SFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.totalNabla0SFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.totalNabla0SFun ``Submission.DifferentialGeometry.Tensor0SBundle.totalNabla0SFun

omit [IsManifold I ∞ M] in
theorem totalNabla0SFun_congr (s : ℕ)
    {cov cov' : CovariantDerivative I E (TangentSpace I : M → Type _)}
    {α β : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s}
    (hcov : cov = cov') (hα : α = β) (x : M) :
    totalNabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s cov α x =
      totalNabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s cov' β x := by
  cases hcov
  cases hα
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.totalNabla0SFun_congr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.totalNabla0SFun_congr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.totalNabla0SFun_congr ``Submission.DifferentialGeometry.Tensor0SBundle.totalNabla0SFun_congr

abbrev TotalNabla0SRegular (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) : Prop :=
  letI := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    (s + 1)
  ContMDiff I (I.prod 𝓘(𝕜, Tensor0SModel (s + 1) 𝕜 E)) (∞ : WithTop ℕ∞)
    (fun x : M =>
      (⟨x, totalNabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s cov α x⟩ :
        _root_.Bundle.TotalSpace (Tensor0SModel (s + 1) 𝕜 E)
          (fun x : M => Tensor0SSpace (s + 1) I x)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.TotalNabla0SRegular then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.TotalNabla0SRegular"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.TotalNabla0SRegular ``Submission.DifferentialGeometry.Tensor0SBundle.TotalNabla0SRegular

noncomputable def totalNabla0S (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (hreg : TotalNabla0SRegular (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      s cov α) :
    Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1) :=
  letI := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    (s + 1)
  ⟨totalNabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    s cov α, hreg⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.totalNabla0S then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.totalNabla0S"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.totalNabla0S ``Submission.DifferentialGeometry.Tensor0SBundle.totalNabla0S

omit [IsManifold I ∞ M] in
@[simp] theorem totalNabla0S_apply (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (hreg : TotalNabla0SRegular (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      s cov α)
    (x : M) :
    totalNabla0S (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s cov α hreg x =
      totalNabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s cov α x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.totalNabla0S_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.totalNabla0S_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.totalNabla0S_apply ``Submission.DifferentialGeometry.Tensor0SBundle.totalNabla0S_apply

omit [IsManifold I ∞ M] in
theorem totalNabla0SFun_apply_tangentConstInChart (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x₀ : M) (X : E) (slots : Fin s → E) :
    totalNabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s cov α x₀
        (Fin.cons (tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ X x₀)
          (fun a : Fin s => tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ (slots a) x₀))
      =
    covariantDerivTensor0SModelAt (𝕜 := 𝕜) (E := E) s
      (fderivWithin 𝕜
        (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          s x₀ (fun x => α x))
        (Set.range I) (extChartAt I x₀ x₀) X)
      (connectionEndomorphismInChartL (𝕜 := 𝕜) (I := I) cov x₀
        (extChartAt I x₀ x₀) X)
      (tensor0SModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s x₀ x₀ (α x₀))
      slots := by
  simp only [tangentConstInChart_apply]
  have hslots :
      Fin.cons
          ((_root_.FiberBundle.trivializationAt E (TangentSpace I : M → Type _) x₀).symmL 𝕜 x₀ X)
          (fun a : Fin s =>
            (_root_.FiberBundle.trivializationAt E (TangentSpace I : M → Type _) x₀).symmL 𝕜 x₀
              (slots a))
        =
      (fun a : Fin (s + 1) =>
        (_root_.FiberBundle.trivializationAt E (TangentSpace I : M → Type _) x₀).symmL 𝕜 x₀
          ((Fin.cons X slots : Fin (s + 1) → E) a)) := by
    funext a
    cases a using Fin.cases <;> simp
  rw [hslots]
  rw [← tensor0SModelAt_apply (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    (s + 1) x₀ x₀
    (totalNabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      s cov α x₀) (Fin.cons X slots)]
  unfold totalNabla0SFun
  rw [tensor0SModelAt_trivializationAt_symm]
  rw [totalCovDeriv_tensor0SModelAt_apply_cons]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.totalNabla0SFun_apply_tangentConstInChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.totalNabla0SFun_apply_tangentConstInChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.totalNabla0SFun_apply_tangentConstInChart ``Submission.DifferentialGeometry.Tensor0SBundle.totalNabla0SFun_apply_tangentConstInChart

omit [IsManifold I ∞ M] in
theorem totalNabla0SFun_apply_section (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x : M) (slots : Fin s → TangentSpace I x) :
    totalNabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s cov α x (Fin.cons (X x) slots) =
      nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s cov X α x slots := by
  classical
  let e := _root_.FiberBundle.trivializationAt E (TangentSpace I : M → Type _) x
  let y₀ : E := extChartAt I x x
  let Xmodel : E := e.continuousLinearMapAt 𝕜 x (X x)
  let slotsModel : Fin s → E := fun a => e.continuousLinearMapAt 𝕜 x (slots a)
  have hXinput :
      tangentConstInChart (𝕜 := 𝕜) (I := I) x Xmodel x = X x := by
    change
      tangentConstInChart (𝕜 := 𝕜) (I := I) x
          ((_root_.FiberBundle.trivializationAt E (TangentSpace I : M → Type _) x).continuousLinearMapAt
            𝕜 x (X x)) x =
        X x
    exact tangentConstInChart_self_continuousLinearMapAt
      (𝕜 := 𝕜) (I := I) x (X x)
  have hslotsInput :
      (fun a : Fin s =>
        tangentConstInChart (𝕜 := 𝕜) (I := I) x (slotsModel a) x) = slots := by
    funext a
    change
      tangentConstInChart (𝕜 := 𝕜) (I := I) x
          ((_root_.FiberBundle.trivializationAt E (TangentSpace I : M → Type _) x).continuousLinearMapAt
            𝕜 x (slots a)) x =
        slots a
    exact tangentConstInChart_self_continuousLinearMapAt
      (𝕜 := 𝕜) (I := I) x (slots a)
  have hinput :
      Fin.cons
          (tangentConstInChart (𝕜 := 𝕜) (I := I) x Xmodel x)
          (fun a : Fin s =>
            tangentConstInChart (𝕜 := 𝕜) (I := I) x (slotsModel a) x)
        =
      (Fin.cons (X x) slots : Fin (s + 1) → TangentSpace I x) := by
    funext a
    cases a using Fin.cases with
    | zero => exact hXinput
    | succ a => exact congrFun hslotsInput a
  have hmpull :
      tangentSpaceModelContinuousLinearEquiv y₀
        (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm
          (fun y : M => X y) (Set.range I) y₀) =
        Xmodel := by
    simp only [y₀, Xmodel, e, VectorField.mpullbackWithin_apply,
      tangentSpaceModelContinuousLinearEquiv_apply]
    rw [extChartAt_to_inv]
    rw [TangentBundle.continuousLinearMapAt_trivializationAt
      (I := I) (x₀ := x) (x := x) (mem_chart_source H x)]
    rw [mfderiv_extChartAt_self]
    exact mfderivWithin_extChartAt_symm_inverse_apply (I := I) (x := x) (X x)
  have htotal := totalNabla0SFun_apply_tangentConstInChart
    (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    s cov α x Xmodel slotsModel
  have hself := nabla0SFun_apply_selfChart_slots
    (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    s cov X α x slotsModel
  have hfixed := fixedChartNabla0SModel_apply_slots
    (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    (n := (∞ : WithTop ℕ∞)) s cov X α x y₀ slotsModel
  calc
    totalNabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s cov α x (Fin.cons (X x) slots)
        =
      totalNabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s cov α x
        (Fin.cons
          (tangentConstInChart (𝕜 := 𝕜) (I := I) x Xmodel x)
          (fun a : Fin s =>
            tangentConstInChart (𝕜 := 𝕜) (I := I) x (slotsModel a) x)) := by
          rw [hinput]
    _ =
      covariantDerivTensor0SModelAt (𝕜 := 𝕜) (E := E) s
        (fderivWithin 𝕜
          (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
            s x (fun x => α x))
          (Set.range I) (extChartAt I x x) Xmodel)
        (connectionEndomorphismInChartL (𝕜 := 𝕜) (I := I) cov x
          (extChartAt I x x) Xmodel)
        (tensor0SModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          s x x (α x))
        slotsModel := htotal
    _ =
      fixedChartNabla0SModel (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s cov X α x y₀ slotsModel := by
          rw [hfixed]
          rw [covariantDeriv_tensor0SModelAt_apply_slots]
          rw [hmpull]
          have hΓ (v : E) :
              connectionEndomorphismInChartL (𝕜 := 𝕜) (I := I) cov x
                  (extChartAt I x x) Xmodel v =
                connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov
                  (fun x => X x) x (extChartAt I x x) v := by
            change
              connectionEndomorphismInChartL (𝕜 := 𝕜) (I := I) cov x
                  (extChartAt I x x)
                  ((_root_.FiberBundle.trivializationAt E (TangentSpace I : M → Type _)
                    x).continuousLinearMapAt 𝕜 x (X x)) v =
                connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov
                  (fun x => X x) x (extChartAt I x x) v
            exact connectionEndomorphismInChartL_apply_center_modelVector
              (𝕜 := 𝕜) (I := I) cov (fun x => X x) x v
          simp_rw [hΓ]
          rw [tensor0SModelInChart_center_eq_tensor0SModelAt
            (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
            s x (fun y => α y)]
    _ =
      (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s cov X α x)
        (fun a : Fin s =>
          tangentConstInChart (𝕜 := 𝕜) (I := I) x (slotsModel a) x) := by
          exact hself.symm
    _ =
      nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s cov X α x slots := by
          rw [hslotsInput]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.totalNabla0SFun_apply_section then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.totalNabla0SFun_apply_section"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.totalNabla0SFun_apply_section ``Submission.DifferentialGeometry.Tensor0SBundle.totalNabla0SFun_apply_section

omit [IsManifold I ∞ M] in
theorem totalNabla0SFun_eval_section (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x : M) (slots : Fin s → TangentSpace I x) :
    Tensor0SSpace.eval
        (totalNabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          s cov α x)
        (Fin.cons (X x) slots) =
      Tensor0SSpace.eval
        (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          s cov X α x)
        slots := by
  exact totalNabla0SFun_apply_section s cov X α x slots

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.totalNabla0SFun_eval_section then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.totalNabla0SFun_eval_section"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.totalNabla0SFun_eval_section ``Submission.DifferentialGeometry.Tensor0SBundle.totalNabla0SFun_eval_section

def TotalNabla0SRealizes (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (nablaAlpha : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1)) : Prop :=
  ∀ (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (x : M) (slots : Fin s → TangentSpace I x),
      nablaAlpha x (Fin.cons (X x) slots) =
        nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          s cov X α x slots

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.TotalNabla0SRealizes then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.TotalNabla0SRealizes"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.TotalNabla0SRealizes ``Submission.DifferentialGeometry.Tensor0SBundle.TotalNabla0SRealizes

def TotalNablaRSRealizes (r s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s)
    (nablaT : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r (s + 1)) : Prop :=
  ∀ (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (x : M) (β : Tensor0SSpace r I x) (slots : Fin s → TangentSpace I x),
      nablaT x β (Fin.cons (X x) slots) =
        nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          r s cov X T x β slots

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.TotalNablaRSRealizes then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.TotalNablaRSRealizes"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.TotalNablaRSRealizes ``Submission.DifferentialGeometry.Tensor0SBundle.TotalNablaRSRealizes

omit [IsManifold I ∞ M] in
theorem TotalNabla0SRealizes.apply {s : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    {α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s}
    {nablaAlpha : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1)}
    (h : TotalNabla0SRealizes (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) s cov α nablaAlpha)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (x : M) (slots : Fin s → TangentSpace I x) :
    nablaAlpha x (Fin.cons (X x) slots) =
    nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s cov X α x slots :=
  h X x slots

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Tensor0SBundle.TotalNabla0SRealizes
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.TotalNabla0SRealizes.apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.TotalNabla0SRealizes.apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.TotalNabla0SRealizes.apply ``Submission.DifferentialGeometry.Tensor0SBundle.TotalNabla0SRealizes.apply

omit [IsManifold I ∞ M] in
theorem totalNabla0S_realizes (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (hreg : TotalNabla0SRegular (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      s cov α) :
    TotalNabla0SRealizes (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      s cov α
      (totalNabla0S (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s cov α hreg) := by
  intro X x slots
  rw [totalNabla0S_apply]
  exact totalNabla0SFun_apply_section
    (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s cov X α x slots

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.totalNabla0S_realizes then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.totalNabla0S_realizes"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.totalNabla0S_realizes ``Submission.DifferentialGeometry.Tensor0SBundle.totalNabla0S_realizes

structure CanonicalSpatialDerivs0S {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (A : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) where
  nablaA : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    (n := (∞ : WithTop ℕ∞)) (s + 1)
  nabla2A : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    (n := (∞ : WithTop ℕ∞)) (s + 2)
  first : TotalNabla0SRealizes (𝕜 := 𝕜) (E := E) (H := H) (I := I)
    (M := M) s cov A nablaA
  second : TotalNabla0SRealizes (𝕜 := 𝕜) (E := E) (H := H) (I := I)
    (M := M) (s + 1) cov nablaA nabla2A

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.CanonicalSpatialDerivs0S then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.CanonicalSpatialDerivs0S"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.CanonicalSpatialDerivs0S ``Submission.DifferentialGeometry.Tensor0SBundle.CanonicalSpatialDerivs0S

theorem TotalNabla0SRealizes.eval_smooth_slots {s : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    {α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s}
    {nablaAlpha : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s + 1)}
    (h : TotalNabla0SRealizes (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) s cov α nablaAlpha)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (V : Fin s → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (x₀ : M) :
    nablaAlpha x₀ (Fin.cons (X x₀) (fun a : Fin s => V a x₀)) =
      mvfderiv (I := I) (fun p : M => α p (fun a : Fin s => V a p))
        x₀ (X x₀) -
        ∑ a : Fin s,
          α x₀
            (Function.update (fun b : Fin s => V b x₀) a
              ((cov (fun p : M => V a p) x₀) (X x₀))) := by
  calc
    nablaAlpha x₀ (Fin.cons (X x₀) (fun a : Fin s => V a x₀))
        = nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
            s cov X α x₀ (fun a : Fin s => V a x₀) := by
          exact h.apply X x₀ (fun a : Fin s => V a x₀)
    _ = mvfderiv (I := I) (fun p : M => α p (fun a : Fin s => V a p))
          x₀ (X x₀) -
          ∑ a : Fin s,
            α x₀
              (Function.update (fun b : Fin s => V b x₀) a
                ((cov (fun p : M => V a p) x₀) (X x₀))) := by
          exact nabla0SFun_eval_smooth_slots
            (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
            cov X V α x₀

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.TotalNabla0SRealizes.eval_smooth_slots then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.TotalNabla0SRealizes.eval_smooth_slots"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.TotalNabla0SRealizes.eval_smooth_slots ``Submission.DifferentialGeometry.Tensor0SBundle.TotalNabla0SRealizes.eval_smooth_slots

theorem TotalNabla0SRealizes.eval_C1_slots {s : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    {α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s}
    {nablaAlpha : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s + 1)}
    (h : TotalNabla0SRealizes (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) s cov α nablaAlpha)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (V : Fin s → (x : M) → TangentSpace I x)
    (x₀ : M)
    (hV_at : ∀ a : Fin s,
      ContMDiffAt I (I.prod 𝓘(𝕜, E)) (1 : WithTop ℕ∞)
        (fun y : M => (⟨y, V a y⟩ : _root_.Bundle.TotalSpace E (TangentSpace I : M → Type _))) x₀) :
    nablaAlpha x₀ (Fin.cons (X x₀) (fun a : Fin s => V a x₀)) =
      mvfderiv (I := I) (fun p : M => α p (fun a : Fin s => V a p))
        x₀ (X x₀) -
        ∑ a : Fin s,
          α x₀
            (Function.update (fun b : Fin s => V b x₀) a
              ((cov (V a) x₀) (X x₀))) := by
  calc
    nablaAlpha x₀ (Fin.cons (X x₀) (fun a : Fin s => V a x₀))
        = nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
            s cov X α x₀ (fun a : Fin s => V a x₀) := by
          exact h.apply X x₀ (fun a : Fin s => V a x₀)
    _ = mvfderiv (I := I) (fun p : M => α p (fun a : Fin s => V a p))
          x₀ (X x₀) -
          ∑ a : Fin s,
            α x₀
              (Function.update (fun b : Fin s => V b x₀) a
                ((cov (V a) x₀) (X x₀))) := by
          exact nabla0SFun_eval_C1_slots
            (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
            cov X V α x₀ hV_at

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.TotalNabla0SRealizes.eval_C1_slots then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.TotalNabla0SRealizes.eval_C1_slots"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.TotalNabla0SRealizes.eval_C1_slots ``Submission.DifferentialGeometry.Tensor0SBundle.TotalNabla0SRealizes.eval_C1_slots

omit [IsManifold I ∞ M] in
theorem TotalNablaRSRealizes.apply {r s : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    {T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s}
    {nablaT : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r (s + 1)}
    (h : TotalNablaRSRealizes (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) r s cov T nablaT)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (x : M) (β : Tensor0SSpace r I x) (slots : Fin s → TangentSpace I x) :
    nablaT x β (Fin.cons (X x) slots) =
      nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        r s cov X T x β slots :=
  h X x β slots

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Tensor0SBundle.TotalNablaRSRealizes
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.TotalNablaRSRealizes.apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.TotalNablaRSRealizes.apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.TotalNablaRSRealizes.apply ``Submission.DifferentialGeometry.Tensor0SBundle.TotalNablaRSRealizes.apply

noncomputable def totalNabla20S (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (hreg1 : TotalNabla0SRegular (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      s cov α)
    (hreg2 : TotalNabla0SRegular (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (s + 1) cov
      (totalNabla0S (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s cov α hreg1)) :
    Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) ((s + 1) + 1) :=
  totalNabla0S (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    (s + 1) cov
    (totalNabla0S (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      s cov α hreg1)
    hreg2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.totalNabla20S then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.totalNabla20S"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.totalNabla20S ``Submission.DifferentialGeometry.Tensor0SBundle.totalNabla20S

noncomputable def totalNabla20SSuccSucc (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (hreg1 : TotalNabla0SRegular (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      s cov α)
    (hreg2 : TotalNabla0SRegular (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (s + 1) cov
      (totalNabla0S (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s cov α hreg1)) :
    Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2) :=
  totalNabla20S (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    s cov α hreg1 hreg2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.totalNabla20SSuccSucc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.totalNabla20SSuccSucc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.totalNabla20SSuccSucc ``Submission.DifferentialGeometry.Tensor0SBundle.totalNabla20SSuccSucc

inductive HigherCovDeriv0SRealizes
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {s : ℕ}
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    (k : ℕ) →
      Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) (k + s) → Prop
  | zero :
      HigherCovDeriv0SRealizes cov α 0
        (by
          simpa :
            Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
              (n := (∞ : WithTop ℕ∞)) (0 + s))
  | succ {k : ℕ}
      {αk : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) (k + s)}
      {αk1 : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) ((k + s) + 1)}
      (hk : HigherCovDeriv0SRealizes cov α k αk)
      (hstep : TotalNabla0SRealizes (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) (k + s) cov αk αk1) :
      HigherCovDeriv0SRealizes cov α (k + 1)
        (by
          simpa [Nat.add_assoc, Nat.succ_add, Nat.add_comm, Nat.add_left_comm] using αk1 :
            Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
              (n := (∞ : WithTop ℕ∞)) ((k + 1) + s))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.HigherCovDeriv0SRealizes then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.HigherCovDeriv0SRealizes"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.HigherCovDeriv0SRealizes ``Submission.DifferentialGeometry.Tensor0SBundle.HigherCovDeriv0SRealizes

inductive HigherCovDerivRSRealizes
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {r s : ℕ}
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s) :
    (k : ℕ) →
      TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) r (k + s) → Prop
  | zero :
      HigherCovDerivRSRealizes cov T 0
        (by
          simpa :
            TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
              (n := (∞ : WithTop ℕ∞)) r (0 + s))
  | succ {k : ℕ}
      {Tk : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) r (k + s)}
      {Tk1 : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) r ((k + s) + 1)}
      (hk : HigherCovDerivRSRealizes cov T k Tk)
      (hstep : TotalNablaRSRealizes (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) r (k + s) cov Tk Tk1) :
      HigherCovDerivRSRealizes cov T (k + 1)
        (by
          simpa [Nat.add_assoc, Nat.succ_add, Nat.add_comm, Nat.add_left_comm] using Tk1 :
            TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
              (n := (∞ : WithTop ℕ∞)) r ((k + 1) + s))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.HigherCovDerivRSRealizes then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.HigherCovDerivRSRealizes"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.HigherCovDerivRSRealizes ``Submission.DifferentialGeometry.Tensor0SBundle.HigherCovDerivRSRealizes

omit [IsManifold I ∞ M] in
theorem higherCovDeriv0SRealizes_two_apply {s : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    {nablaAlpha : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1)}
    {nabla2Alpha : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) ((s + 1) + 1)}
    (h2 : TotalNabla0SRealizes (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) (s + 1) cov nablaAlpha nabla2Alpha)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (x : M) (slots : Fin (s + 1) → TangentSpace I x) :
    nabla2Alpha x (Fin.cons (X x) slots) =
      nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        (s + 1) cov X nablaAlpha x slots :=
  h2.apply X x slots

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.higherCovDeriv0SRealizes_two_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.higherCovDeriv0SRealizes_two_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.higherCovDeriv0SRealizes_two_apply ``Submission.DifferentialGeometry.Tensor0SBundle.higherCovDeriv0SRealizes_two_apply

end

section RealLinearity


open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.IsManifold _root_.ContinuousLinearMap _root_.Submission.ContinuousLinearMap _root_.Bundle.ContinuousLinearMap _root_.Submission.DifferentialGeometry.TensorLieDeriv
open scoped _root_.Manifold _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I (∞ : WithTop ℕ∞) M]

theorem nabla0SFun_sub_cov
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    {s : ℕ}
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (V : Fin s -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x : M) :
    ((nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov X α x) -
        nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov' X α x) (fun a : Fin s => V a x) =
      -∑ a : Fin s,
        α x
          (Function.update (fun b : Fin s => V b x) a
            (((CovariantDerivative.difference cov cov' x) (V a x)) (X x))) := by
  classical
  let slots : Fin s -> TangentSpace I x := fun a => V a x
  have hcov := nabla0SFun_eval_smooth_slots (I := I) cov X V α x
  have hcov' := nabla0SFun_eval_smooth_slots (I := I) cov' X V α x
  have hdiff (a : Fin s) :
      α x
          (Function.update slots a ((cov (fun p : M => V a p) x) (X x))) -
        α x
          (Function.update slots a ((cov' (fun p : M => V a p) x) (X x))) =
        α x
          (Function.update slots a
            (((CovariantDerivative.difference cov cov' x) (V a x)) (X x))) := by
    have hconn :
        ((CovariantDerivative.difference cov cov' x) (V a x)) (X x) =
          ((cov (fun p : M => V a p) x) (X x)) -
            ((cov' (fun p : M => V a p) x) (X x)) := by
      have h :=
        IsCovariantDerivativeOn.difference_apply
          (hcov := cov.isCovariantDerivativeOnUniv)
          (hcov' := cov'.isCovariantDerivativeOnUniv)
          (σ := fun p : M => V a p) (x := x) (hx := by trivial)
          ((V a).contMDiff.contMDiffAt.mdifferentiableAt (by simp))
      exact congrArg (fun L : TangentSpace I x →L[Real] TangentSpace I x => L (X x)) h
    rw [hconn]
    exact ((α x).map_update_sub slots a
      ((cov (fun p : M => V a p) x) (X x))
      ((cov' (fun p : M => V a p) x) (X x))).symm
  let D : Real :=
    (mvfderiv (I := I) (fun p : M => α p (fun a : Fin s => V a p)) x) (X x)
  let Scov : Real :=
    ∑ a : Fin s,
      α x (Function.update slots a ((cov (fun p : M => V a p) x) (X x)))
  let Scov' : Real :=
    ∑ a : Fin s,
      α x (Function.update slots a ((cov' (fun p : M => V a p) x) (X x)))
  let Sdiff : Real :=
    ∑ a : Fin s,
      α x
        (Function.update slots a
          (((CovariantDerivative.difference cov cov' x) (V a x)) (X x)))
  have hsum : Scov - Scov' = Sdiff := by
    dsimp [Scov, Scov', Sdiff]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    exact hdiff a
  change
    (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov X α x) slots -
        (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov' X α x) slots =
      -∑ a : Fin s,
        α x
          (Function.update slots a
            (((CovariantDerivative.difference cov cov' x) (V a x)) (X x)))
  rw [hcov, hcov']
  change (D - Scov) - (D - Scov') = -Sdiff
  rw [← hsum]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.nabla0SFun_sub_cov then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.nabla0SFun_sub_cov"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.nabla0SFun_sub_cov ``Submission.DifferentialGeometry.Tensor0SBundle.nabla0SFun_sub_cov

theorem nabla0SFun_sub_cov_two
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (x : M) :
    ((nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          2 cov X α x) -
        nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          2 cov' X α x)
        (fun q : Fin 2 => if q = 0 then Y x else Z x) =
      -((α x)
          (fun q : Fin 2 =>
            if q = 0 then
              ((CovariantDerivative.difference cov cov' x) (Y x)) (X x)
            else Z x) +
        (α x)
          (fun q : Fin 2 =>
            if q = 0 then Y x
            else ((CovariantDerivative.difference cov cov' x) (Z x)) (X x))) := by
  classical
  let V : Fin 2 -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) :=
    fun q => if q = 0 then Y else Z
  let DY : TangentSpace I x :=
    ((CovariantDerivative.difference cov cov' x) (Y x)) (X x)
  let DZ : TangentSpace I x :=
    ((CovariantDerivative.difference cov cov' x) (Z x)) (X x)
  have hupdate0 :
      Function.update (fun b : Fin 2 => V b x) (0 : Fin 2) DY =
        (fun q : Fin 2 => if q = 0 then DY else Z x) := by
    funext q
    fin_cases q <;> simp [V, DY]
  have hupdate1 :
      Function.update (fun b : Fin 2 => V b x) (1 : Fin 2) DZ =
        (fun q : Fin 2 => if q = 0 then Y x else DZ) := by
    funext q
    fin_cases q <;> simp [V, DZ]
  have h := nabla0SFun_sub_cov (I := I) cov cov' X V α x
  have hslots :
      (fun q : Fin 2 => if q = 0 then Y x else Z x) =
        (fun q : Fin 2 => V q x) := by
    funext q
    fin_cases q <;> simp [V]
  calc
    ((nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          2 cov X α x) -
        nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          2 cov' X α x)
        (fun q : Fin 2 => if q = 0 then Y x else Z x)
        =
      ((nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          2 cov X α x) -
        nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          2 cov' X α x)
        (fun q : Fin 2 => V q x) := by
          rw [hslots]
    _ = -∑ a : Fin 2,
          α x
            (Function.update (fun b : Fin 2 => V b x) a
              (((CovariantDerivative.difference cov cov' x) (V a x)) (X x))) := h
    _ = -((α x)
          (fun q : Fin 2 =>
            if q = 0 then
              ((CovariantDerivative.difference cov cov' x) (Y x)) (X x)
            else Z x) +
        (α x)
          (fun q : Fin 2 =>
            if q = 0 then Y x
            else ((CovariantDerivative.difference cov cov' x) (Z x)) (X x))) := by
          rw [Fin.sum_univ_two]
          simp [V, DY, DZ, hupdate0, hupdate1]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.nabla0SFun_sub_cov_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.nabla0SFun_sub_cov_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.nabla0SFun_sub_cov_two ``Submission.DifferentialGeometry.Tensor0SBundle.nabla0SFun_sub_cov_two

theorem nabla0SFun_add [T2Space M] {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (α β : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x : M) :
    nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        s cov X (α + β) x =
      nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov X α x +
        nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov X β x := by
  classical
  let basis : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
      (TangentSpace I x) :=
    Module.finBasis Real (TangentSpace I x)
  apply ext0S_basis (I := I) basis
  intro idx
  let V : Fin s -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) :=
    fun a =>
      (ContMDiffSection.exists_eq_at
        (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
        x (basis (idx a))).choose
  have hV : ∀ a : Fin s, V a x = basis (idx a) := by
    intro a
    exact
      (ContMDiffSection.exists_eq_at
        (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
        x (basis (idx a))).choose_spec
  have hslots : (fun a : Fin s => V a x) = fun a : Fin s => basis (idx a) := by
    funext a
    exact hV a
  have hsum := nabla0SFun_eval_smooth_slots (I := I) cov X V (α + β) x
  have hα := nabla0SFun_eval_smooth_slots (I := I) cov X V α x
  have hβ := nabla0SFun_eval_smooth_slots (I := I) cov X V β x
  have hfα : MDifferentiableAt I 𝓘(Real, Real)
      (fun p : M => α p (fun a : Fin s => V a p)) x :=
    (tensor0SField_eval_smooth_slots_contMDiffAt (I := I) α V x).mdifferentiableAt
      (by simp)
  have hfβ : MDifferentiableAt I 𝓘(Real, Real)
      (fun p : M => β p (fun a : Fin s => V a p)) x :=
    (tensor0SField_eval_smooth_slots_contMDiffAt (I := I) β V x).mdifferentiableAt
      (by simp)
  have hext :
      mvfderiv (I := I)
          (fun p : M => (α + β) p (fun a : Fin s => V a p)) x (X x) =
        mvfderiv (I := I)
            (fun p : M => α p (fun a : Fin s => V a p)) x (X x) +
          mvfderiv (I := I)
            (fun p : M => β p (fun a : Fin s => V a p)) x (X x) := by
    change
      mvfderiv (I := I)
          ((fun p : M => α p (fun a : Fin s => V a p)) +
            fun p : M => β p (fun a : Fin s => V a p)) x (X x) =
        mvfderiv (I := I)
            (fun p : M => α p (fun a : Fin s => V a p)) x (X x) +
          mvfderiv (I := I)
            (fun p : M => β p (fun a : Fin s => V a p)) x (X x)
    rw [mvfderiv_add hfα hfβ]
    rfl
  simp only [component0S_apply]
  rw [← hslots]
  change
    (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        s cov X (α + β) x) (fun a : Fin s => V a x) =
      (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov X α x) (fun a : Fin s => V a x) +
        (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov X β x) (fun a : Fin s => V a x)
  rw [hsum, hα, hβ, hext]
  have hcorr :
      (∑ a : Fin s,
        ((α + β) x)
          (Function.update (fun b : Fin s => V b x) a
            ((cov (V a) x) (X x)))) =
        (∑ a : Fin s,
          α x (Function.update (fun b : Fin s => V b x) a
            ((cov (V a) x) (X x)))) +
        ∑ a : Fin s,
          β x (Function.update (fun b : Fin s => V b x) a
            ((cov (V a) x) (X x))) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rfl
  rw [hcorr]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.nabla0SFun_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.nabla0SFun_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.nabla0SFun_add ``Submission.DifferentialGeometry.Tensor0SBundle.nabla0SFun_add

theorem nabla0SFun_smul [T2Space M] {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (c : Real)
    (α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x : M) :
    nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        s cov X (c • α) x =
      c • nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov X α x := by
  classical
  let basis : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
      (TangentSpace I x) :=
    Module.finBasis Real (TangentSpace I x)
  apply ext0S_basis (I := I) basis
  intro idx
  let V : Fin s -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) :=
    fun a =>
      (ContMDiffSection.exists_eq_at
        (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
        x (basis (idx a))).choose
  have hV : ∀ a : Fin s, V a x = basis (idx a) := by
    intro a
    exact
      (ContMDiffSection.exists_eq_at
        (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
        x (basis (idx a))).choose_spec
  have hslots : (fun a : Fin s => V a x) = fun a : Fin s => basis (idx a) := by
    funext a
    exact hV a
  have hsmul := nabla0SFun_eval_smooth_slots (I := I) cov X V (c • α) x
  have hα := nabla0SFun_eval_smooth_slots (I := I) cov X V α x
  have hfα : MDifferentiableAt I 𝓘(Real, Real)
      (fun p : M => α p (fun a : Fin s => V a p)) x :=
    (tensor0SField_eval_smooth_slots_contMDiffAt (I := I) α V x).mdifferentiableAt
      (by simp)
  have hext :
      mvfderiv (I := I)
          (fun p : M => (c • α) p (fun a : Fin s => V a p)) x (X x) =
        c *
          mvfderiv (I := I)
            (fun p : M => α p (fun a : Fin s => V a p)) x (X x) := by
    have h := DifferentialGeometry.mvfderiv_const_mul I c hfα
    exact congrArg (fun L : TangentSpace I x →L[Real] Real => L (X x)) h
  simp only [component0S_apply]
  rw [← hslots]
  change
    (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        s cov X (c • α) x) (fun a : Fin s => V a x) =
      c *
        (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov X α x) (fun a : Fin s => V a x)
  rw [hsmul, hα, hext]
  simp only [    ContMDiffSection.coe_smul, Pi.smul_apply]
  have hcorr :
      (∑ a : Fin s,
        (c • α x)
          (Function.update (fun b : Fin s => V b x) a
            ((cov (V a) x) (X x)))) =
        c * ∑ a : Fin s,
          α x (Function.update (fun b : Fin s => V b x) a
            ((cov (V a) x) (X x))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rfl
  rw [hcorr]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.nabla0SFun_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.nabla0SFun_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.nabla0SFun_smul ``Submission.DifferentialGeometry.Tensor0SBundle.nabla0SFun_smul

theorem TotalNabla0SRealizes.add [T2Space M] {s : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    {α β : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s}
    {nablaAlpha nablaBeta :
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) (s + 1)}
    (hα : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) s cov α nablaAlpha)
    (hβ : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) s cov β nablaBeta) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s cov (α + β) (nablaAlpha + nablaBeta) := by
  intro X x slots
  have hα' := hα X x slots
  have hβ' := hβ X x slots
  calc
    (nablaAlpha + nablaBeta) x (Fin.cons (X x) slots)
        = nablaAlpha x (Fin.cons (X x) slots) +
            nablaBeta x (Fin.cons (X x) slots) := rfl
    _ = nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            s cov X α x slots +
          nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            s cov X β x slots := by rw [hα', hβ']
    _ = nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov X (α + β) x slots := by
        rw [nabla0SFun_add (I := I) cov X α β x]
        rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.TotalNabla0SRealizes.add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.TotalNabla0SRealizes.add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.TotalNabla0SRealizes.add ``Submission.DifferentialGeometry.Tensor0SBundle.TotalNabla0SRealizes.add

theorem TotalNabla0SRealizes.smul [T2Space M] {s : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    (c : Real)
    {α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s}
    {nablaAlpha :
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) (s + 1)}
    (hα : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) s cov α nablaAlpha) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s cov (c • α) (c • nablaAlpha) := by
  intro X x slots
  have hα' := hα X x slots
  calc
    (c • nablaAlpha) x (Fin.cons (X x) slots)
        = c • nablaAlpha x (Fin.cons (X x) slots) := rfl
    _ = c • nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov X α x slots := by rw [hα']
    _ = nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov X (c • α) x slots := by
        rw [nabla0SFun_smul (I := I) cov X c α x]
        rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.TotalNabla0SRealizes.smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.TotalNabla0SRealizes.smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.TotalNabla0SRealizes.smul ``Submission.DifferentialGeometry.Tensor0SBundle.TotalNabla0SRealizes.smul

end RealLinearity

end Tensor0SBundle
end DifferentialGeometry
