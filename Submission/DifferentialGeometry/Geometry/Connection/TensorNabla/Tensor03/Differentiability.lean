import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Submission.DifferentialGeometry.Bundle.Equiv
import Submission.DifferentialGeometry.Bundle.Frame
import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.Defs
import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.Differentiability.Cotangent
import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.Differentiability.Tensor

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.FiberBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff


namespace DifferentialGeometry
namespace Geometry
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure

noncomputable local instance modelDualNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.modelDualNormedAddCommGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.modelDualNormedAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.modelDualNormedAddCommGroup ``Submission.DifferentialGeometry.Geometry.Connection.modelDualNormedAddCommGroup

noncomputable local instance modelDualNormedSpace :
    NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.modelDualNormedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.modelDualNormedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.modelDualNormedSpace ``Submission.DifferentialGeometry.Geometry.Connection.modelDualNormedSpace

noncomputable local instance modelBilinearNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.modelBilinearNormedAddCommGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.modelBilinearNormedAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.modelBilinearNormedAddCommGroup ``Submission.DifferentialGeometry.Geometry.Connection.modelBilinearNormedAddCommGroup

noncomputable local instance modelBilinearNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.modelBilinearNormedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.modelBilinearNormedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.modelBilinearNormedSpace ``Submission.DifferentialGeometry.Geometry.Connection.modelBilinearNormedSpace

noncomputable local instance modelTrilinearNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.modelTrilinearNormedAddCommGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.modelTrilinearNormedAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.modelTrilinearNormedAddCommGroup ``Submission.DifferentialGeometry.Geometry.Connection.modelTrilinearNormedAddCommGroup

noncomputable local instance modelTrilinearNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.modelTrilinearNormedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.modelTrilinearNormedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.modelTrilinearNormedSpace ``Submission.DifferentialGeometry.Geometry.Connection.modelTrilinearNormedSpace

noncomputable local instance tangentDualNormedAddCommGroup (x : M) :
    NormedAddCommGroup (TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tangentDualNormedAddCommGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tangentDualNormedAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tangentDualNormedAddCommGroup ``Submission.DifferentialGeometry.Geometry.Connection.tangentDualNormedAddCommGroup

noncomputable local instance tangentDualNormedSpace (x : M) :
    NormedSpace ℝ (TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tangentDualNormedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tangentDualNormedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tangentDualNormedSpace ``Submission.DifferentialGeometry.Geometry.Connection.tangentDualNormedSpace

local instance tangentDualSMulCommClass (x : M) :
    SMulCommClass ℝ ℝ (TangentSpace I x →L[ℝ] ℝ) where
  smul_comm a b f := by
    ext v
    change a * (b * f v) = b * (a * f v)
    ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tangentDualSMulCommClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tangentDualSMulCommClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tangentDualSMulCommClass ``Submission.DifferentialGeometry.Geometry.Connection.tangentDualSMulCommClass

noncomputable local instance tangentBilinearNormedAddCommGroup (x : M) :
    NormedAddCommGroup (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tangentBilinearNormedAddCommGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tangentBilinearNormedAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tangentBilinearNormedAddCommGroup ``Submission.DifferentialGeometry.Geometry.Connection.tangentBilinearNormedAddCommGroup

noncomputable local instance tangentBilinearNormedSpace (x : M) :
    NormedSpace ℝ (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  @ContinuousLinearMap.toNormedSpace ℝ ℝ (TangentSpace I x)
    (TangentSpace I x →L[ℝ] ℝ) _ _ _ _ _ _ (RingHom.id ℝ) _ ℝ _
      (tangentDualNormedSpace (I := I) x) (tangentDualSMulCommClass (I := I) x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tangentBilinearNormedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tangentBilinearNormedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tangentBilinearNormedSpace ``Submission.DifferentialGeometry.Geometry.Connection.tangentBilinearNormedSpace

local instance tangentBilinearSMulCommClass (x : M) :
    SMulCommClass ℝ ℝ
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) where
  smul_comm a b f := by
    ext v w
    change a * (b * f v w) = b * (a * f v w)
    ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tangentBilinearSMulCommClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tangentBilinearSMulCommClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tangentBilinearSMulCommClass ``Submission.DifferentialGeometry.Geometry.Connection.tangentBilinearSMulCommClass

noncomputable local instance tangentTrilinearNormedAddCommGroup (x : M) :
    NormedAddCommGroup
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  @ContinuousLinearMap.toNormedAddCommGroup ℝ ℝ (TangentSpace I x)
    (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
      _ (tangentBilinearNormedAddCommGroup (I := I) x) _ _ _
        (tangentBilinearNormedSpace (I := I) x) (RingHom.id ℝ) _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tangentTrilinearNormedAddCommGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tangentTrilinearNormedAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tangentTrilinearNormedAddCommGroup ``Submission.DifferentialGeometry.Geometry.Connection.tangentTrilinearNormedAddCommGroup

noncomputable local instance tangentTrilinearNormedSpace (x : M) :
    NormedSpace ℝ
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  @ContinuousLinearMap.toNormedSpace ℝ ℝ (TangentSpace I x)
    (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
      _ (tangentBilinearNormedAddCommGroup (I := I) x).toSeminormedAddCommGroup
        _ _ _ (tangentBilinearNormedSpace (I := I) x) (RingHom.id ℝ) _ ℝ _
          (tangentBilinearNormedSpace (I := I) x)
            (tangentBilinearSMulCommClass (I := I) x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tangentTrilinearNormedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tangentTrilinearNormedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tangentTrilinearNormedSpace ``Submission.DifferentialGeometry.Geometry.Connection.tangentTrilinearNormedSpace

section mkHom₃

variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
variable {F₃ : Type*} [NormedAddCommGroup F₃] [NormedSpace ℝ F₃] [FiniteDimensional ℝ F₃]
variable {V₁ : M → Type*} [∀ x, AddCommGroup (V₁ x)] [∀ x, Module ℝ (V₁ x)]
  [∀ x, TopologicalSpace (V₁ x)] [TopologicalSpace (TotalSpace F₁ V₁)]
  [FiberBundle F₁ V₁] [VectorBundle ℝ F₁ V₁] [ContMDiffVectorBundle 1 F₁ V₁ I]
variable {V₂ : M → Type*} [∀ x, AddCommGroup (V₂ x)] [∀ x, Module ℝ (V₂ x)]
  [∀ x, TopologicalSpace (V₂ x)] [TopologicalSpace (TotalSpace F₂ V₂)]
  [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂] [ContMDiffVectorBundle 1 F₂ V₂ I]
variable {V₃ : M → Type*} [∀ x, AddCommGroup (V₃ x)] [∀ x, Module ℝ (V₃ x)]
  [∀ x, TopologicalSpace (V₃ x)] [TopologicalSpace (TotalSpace F₃ V₃)]
  [FiberBundle F₃ V₃] [VectorBundle ℝ F₃ V₃] [ContMDiffVectorBundle 1 F₃ V₃ I]

private noncomputable def mkHom₃FirstSlot
    (Φ : (Π x : M, V₁ x) → (Π x : M, V₂ x) → (Π x : M, V₃ x) → ℝ) (x : M)
    (hΦ₁ : ∀ σ₂ σ₃, MDiffAt (T% σ₂) x → MDiffAt (T% σ₃) x →
      TensorialAt I F₁ (Φ · σ₂ σ₃) x)
    (hΦ₂ : ∀ σ₁ σ₃, MDiffAt (T% σ₁) x → MDiffAt (T% σ₃) x →
      TensorialAt I F₂ (Φ σ₁ · σ₃) x)
    (hΦ₃ : ∀ σ₁ σ₂, MDiffAt (T% σ₁) x → MDiffAt (T% σ₂) x →
      TensorialAt I F₃ (Φ σ₁ σ₂) x) :
    V₁ x →ₗ[ℝ] (V₂ x →L[ℝ] V₃ x →L[ℝ] ℝ) where
  toFun v :=
    TensorialAt.mkHom₂ (Φ (FiberBundle.extend F₁ v)) x
      (fun σ₃ hσ₃ => hΦ₂ (FiberBundle.extend F₁ v) σ₃ (_root_.FiberBundle.mdifferentiableAt_extend ..) hσ₃)
      (fun σ₂ hσ₂ => hΦ₃ (FiberBundle.extend F₁ v) σ₂ (_root_.FiberBundle.mdifferentiableAt_extend ..) hσ₂)
  map_add' v v' := by
    classical
    ext y z
    set σ₂ : Π x : M, V₂ x := FiberBundle.extend F₂ y
    set σ₃ : Π x : M, V₃ x := FiberBundle.extend F₃ z
    have hσ₂ : MDiffAt (T% σ₂) x := _root_.FiberBundle.mdifferentiableAt_extend ..
    have hσ₃ : MDiffAt (T% σ₃) x := _root_.FiberBundle.mdifferentiableAt_extend ..
    have hσ₂x : σ₂ x = y := FiberBundle.extend_apply_self F₂ y
    have hσ₃x : σ₃ x = z := FiberBundle.extend_apply_self F₃ z
    rw [show y = σ₂ x from hσ₂x.symm, show z = σ₃ x from hσ₃x.symm]
    rw [add_apply, add_apply]
    simp only [TensorialAt.mkHom₂_apply _ _ hσ₂ hσ₃]
    have h1 : (FiberBundle.extend F₁ (v + v') : Π x : M, V₁ x) x = v + v' :=
      FiberBundle.extend_apply_self F₁ (v + v')
    have h2 : (FiberBundle.extend F₁ v : Π x : M, V₁ x) x = v :=
      FiberBundle.extend_apply_self F₁ v
    have h3 : (FiberBundle.extend F₁ v' : Π x : M, V₁ x) x = v' :=
      FiberBundle.extend_apply_self F₁ v'
    set τ : Π x : M, V₁ x :=
      (FiberBundle.extend F₁ v : Π x : M, V₁ x) + FiberBundle.extend F₁ v' with hτ_def
    have hτ : MDiffAt (T% τ) x :=
      mdifferentiableAt_add_section (_root_.FiberBundle.mdifferentiableAt_extend ..) (_root_.FiberBundle.mdifferentiableAt_extend ..)
    have hτx : τ x = v + v' := by
      change (FiberBundle.extend F₁ v : Π x : M, V₁ x) x
        + (FiberBundle.extend F₁ v' : Π x : M, V₁ x) x = v + v'
      rw [h2, h3]
    have hpt := (hΦ₁ σ₂ σ₃ hσ₂ hσ₃).pointwise
      (_root_.FiberBundle.mdifferentiableAt_extend ..) hτ (by rw [h1, hτx])
    rw [hpt]
    rw [hτ_def, (hΦ₁ σ₂ σ₃ hσ₂ hσ₃).add (_root_.FiberBundle.mdifferentiableAt_extend ..) (_root_.FiberBundle.mdifferentiableAt_extend ..)]
  map_smul' c v := by
    classical
    ext y z
    set σ₂ : Π x : M, V₂ x := FiberBundle.extend F₂ y
    set σ₃ : Π x : M, V₃ x := FiberBundle.extend F₃ z
    have hσ₂ : MDiffAt (T% σ₂) x := _root_.FiberBundle.mdifferentiableAt_extend ..
    have hσ₃ : MDiffAt (T% σ₃) x := _root_.FiberBundle.mdifferentiableAt_extend ..
    have hσ₂x : σ₂ x = y := FiberBundle.extend_apply_self F₂ y
    have hσ₃x : σ₃ x = z := FiberBundle.extend_apply_self F₃ z
    rw [show y = σ₂ x from hσ₂x.symm, show z = σ₃ x from hσ₃x.symm]
    rw [RingHom.id_apply, smul_apply, smul_apply]
    simp only [TensorialAt.mkHom₂_apply _ _ hσ₂ hσ₃]
    have h1 : (FiberBundle.extend F₁ (c • v) : Π x : M, V₁ x) x = c • v :=
      FiberBundle.extend_apply_self F₁ (c • v)
    have h2 : (FiberBundle.extend F₁ v : Π x : M, V₁ x) x = v :=
      FiberBundle.extend_apply_self F₁ v
    set τ : Π x : M, V₁ x := (fun _ : M => c) • (FiberBundle.extend F₁ v : Π x : M, V₁ x)
      with hτ_def
    have hτ : MDiffAt (T% τ) x :=
      (mdifferentiableAt_const (c := c)).smul_section (_root_.FiberBundle.mdifferentiableAt_extend ..)
    have hτx : τ x = c • v := by
      change c • (FiberBundle.extend F₁ v : Π x : M, V₁ x) x = c • v
      rw [h2]
    have hpt := (hΦ₁ σ₂ σ₃ hσ₂ hσ₃).pointwise
      (_root_.FiberBundle.mdifferentiableAt_extend ..) hτ (by rw [h1, hτx])
    rw [hpt]
    rw [hτ_def, (hΦ₁ σ₂ σ₃ hσ₂ hσ₃).smul (f := fun _ => c) (mdifferentiable_const ..)
        (_root_.FiberBundle.mdifferentiableAt_extend ..)]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Connection.mkHom₃FirstSlot
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Connection.mkHom₃FirstSlot target :: scope.openDecls } }

noncomputable def mkHom₃
    (Φ : (Π x : M, V₁ x) → (Π x : M, V₂ x) → (Π x : M, V₃ x) → ℝ) (x : M)
    (hΦ₁ : ∀ σ₂ σ₃, MDiffAt (T% σ₂) x → MDiffAt (T% σ₃) x →
      TensorialAt I F₁ (Φ · σ₂ σ₃) x)
    (hΦ₂ : ∀ σ₁ σ₃, MDiffAt (T% σ₁) x → MDiffAt (T% σ₃) x →
      TensorialAt I F₂ (Φ σ₁ · σ₃) x)
    (hΦ₃ : ∀ σ₁ σ₂, MDiffAt (T% σ₁) x → MDiffAt (T% σ₂) x →
      TensorialAt I F₃ (Φ σ₁ σ₂) x) :
    V₁ x →L[ℝ] V₂ x →L[ℝ] V₃ x →L[ℝ] ℝ :=
  have : T2Space (V₁ x) := FiberBundle.t2Space F₁ V₁ x
  have : FiniteDimensional ℝ (V₁ x) := VectorBundle.finiteDimensional ℝ F₁ V₁ x
  have : IsTopologicalAddGroup (V₁ x) :=
    (VectorBundle.continuousLinearEquivAt ℝ F₁ V₁ x).toContinuousAddEquiv.isTopologicalAddGroup
  have : ContinuousSMul ℝ (V₁ x) :=
    (VectorBundle.continuousLinearEquivAt ℝ F₁ V₁ x).continuousSMul
  (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := V₁ x)
    (F' := V₂ x →L[ℝ] V₃ x →L[ℝ] ℝ))
      (mkHom₃FirstSlot Φ x hΦ₁ hΦ₂ hΦ₃)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.mkHom₃ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.mkHom₃"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.mkHom₃ ``Submission.DifferentialGeometry.Geometry.Connection.mkHom₃

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem mkHom₃_apply
    {Φ : (Π x : M, V₁ x) → (Π x : M, V₂ x) → (Π x : M, V₃ x) → ℝ} {x : M}
    (hΦ₁ : ∀ σ₂ σ₃, MDiffAt (T% σ₂) x → MDiffAt (T% σ₃) x →
      TensorialAt I F₁ (Φ · σ₂ σ₃) x)
    (hΦ₂ : ∀ σ₁ σ₃, MDiffAt (T% σ₁) x → MDiffAt (T% σ₃) x →
      TensorialAt I F₂ (Φ σ₁ · σ₃) x)
    (hΦ₃ : ∀ σ₁ σ₂, MDiffAt (T% σ₁) x → MDiffAt (T% σ₂) x →
      TensorialAt I F₃ (Φ σ₁ σ₂) x)
    {σ₁ : Π x : M, V₁ x} {σ₂ : Π x : M, V₂ x} {σ₃ : Π x : M, V₃ x}
    (hσ₁ : MDiffAt (T% σ₁) x) (hσ₂ : MDiffAt (T% σ₂) x) (hσ₃ : MDiffAt (T% σ₃) x) :
    mkHom₃ Φ x hΦ₁ hΦ₂ hΦ₃ (σ₁ x) (σ₂ x) (σ₃ x) = Φ σ₁ σ₂ σ₃ := by
  classical
  have hcoe : (mkHom₃ Φ x hΦ₁ hΦ₂ hΦ₃) (σ₁ x) =
      mkHom₃FirstSlot Φ x hΦ₁ hΦ₂ hΦ₃ (σ₁ x) := rfl
  rw [hcoe]
  have hstep : (mkHom₃FirstSlot Φ x hΦ₁ hΦ₂ hΦ₃ (σ₁ x)) (σ₂ x) (σ₃ x) =
      Φ (FiberBundle.extend F₁ (σ₁ x)) σ₂ σ₃ := by
    change (TensorialAt.mkHom₂ (Φ (FiberBundle.extend F₁ (σ₁ x))) x
      (fun σ₃ hσ₃ => hΦ₂ (FiberBundle.extend F₁ (σ₁ x)) σ₃ (_root_.FiberBundle.mdifferentiableAt_extend ..) hσ₃)
      (fun σ₂ hσ₂ => hΦ₃ (FiberBundle.extend F₁ (σ₁ x)) σ₂ (_root_.FiberBundle.mdifferentiableAt_extend ..) hσ₂))
      (σ₂ x) (σ₃ x) = _
    exact TensorialAt.mkHom₂_apply _ _ hσ₂ hσ₃
  rw [hstep]
  exact (hΦ₁ σ₂ σ₃ hσ₂ hσ₃).pointwise (_root_.FiberBundle.mdifferentiableAt_extend ..) hσ₁ (by simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.mkHom₃_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.mkHom₃_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.mkHom₃_apply ``Submission.DifferentialGeometry.Geometry.Connection.mkHom₃_apply

end mkHom₃

local instance tensor01TotalSpaceTopology :
    TopologicalSpace
      (_root_.Bundle.TotalSpace (E →L[ℝ] ℝ) (fun x : M => TangentSpace I x →L[ℝ] ℝ)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id ℝ)
    E (TangentSpace I) ℝ (fun _ : M => ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensor01TotalSpaceTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensor01TotalSpaceTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensor01TotalSpaceTopology ``Submission.DifferentialGeometry.Geometry.Connection.tensor01TotalSpaceTopology

local instance tensor01FiberBundle :
    FiberBundle (E →L[ℝ] ℝ) (fun x : M => TangentSpace I x →L[ℝ] ℝ) :=
  Bundle.ContinuousLinearMap.fiberBundle (RingHom.id ℝ)
    E (TangentSpace I) ℝ (fun _ : M => ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensor01FiberBundle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensor01FiberBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensor01FiberBundle ``Submission.DifferentialGeometry.Geometry.Connection.tensor01FiberBundle

local instance tensor01VectorBundle :
    VectorBundle ℝ (E →L[ℝ] ℝ) (fun x : M => TangentSpace I x →L[ℝ] ℝ) :=
  Bundle.ContinuousLinearMap.vectorBundle (RingHom.id ℝ)
    E (TangentSpace I) ℝ (fun _ : M => ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensor01VectorBundle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensor01VectorBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensor01VectorBundle ``Submission.DifferentialGeometry.Geometry.Connection.tensor01VectorBundle

local instance tensor01ContMDiffVectorBundle :
    ContMDiffVectorBundle ∞ (E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] ℝ) I :=
  ContMDiffVectorBundle.continuousLinearMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensor01ContMDiffVectorBundle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensor01ContMDiffVectorBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensor01ContMDiffVectorBundle ``Submission.DifferentialGeometry.Geometry.Connection.tensor01ContMDiffVectorBundle

local instance tensor02TotalSpaceTopology :
    TopologicalSpace
      (_root_.Bundle.TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
        (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id ℝ)
    E (TangentSpace I) (E →L[ℝ] ℝ) (fun x : M => TangentSpace I x →L[ℝ] ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensor02TotalSpaceTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensor02TotalSpaceTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensor02TotalSpaceTopology ``Submission.DifferentialGeometry.Geometry.Connection.tensor02TotalSpaceTopology

local instance iteratedTensor02FiberBundle :
    FiberBundle (E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  Bundle.ContinuousLinearMap.fiberBundle (RingHom.id ℝ)
    E (TangentSpace I) (E →L[ℝ] ℝ) (fun x : M => TangentSpace I x →L[ℝ] ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.iteratedTensor02FiberBundle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.iteratedTensor02FiberBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.iteratedTensor02FiberBundle ``Submission.DifferentialGeometry.Geometry.Connection.iteratedTensor02FiberBundle

local instance iteratedTensor02VectorBundle :
    VectorBundle ℝ (E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  Bundle.ContinuousLinearMap.vectorBundle (RingHom.id ℝ)
    E (TangentSpace I) (E →L[ℝ] ℝ) (fun x : M => TangentSpace I x →L[ℝ] ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.iteratedTensor02VectorBundle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.iteratedTensor02VectorBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.iteratedTensor02VectorBundle ``Submission.DifferentialGeometry.Geometry.Connection.iteratedTensor02VectorBundle

local instance iteratedTensor02ContMDiffVectorBundle :
    ContMDiffVectorBundle ∞ (E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) I :=
  ContMDiffVectorBundle.continuousLinearMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.iteratedTensor02ContMDiffVectorBundle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.iteratedTensor02ContMDiffVectorBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.iteratedTensor02ContMDiffVectorBundle ``Submission.DifferentialGeometry.Geometry.Connection.iteratedTensor02ContMDiffVectorBundle

local instance tensor03TotalSpaceTopology :
    TopologicalSpace
      (_root_.Bundle.TotalSpace (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
        (fun x : M =>
          TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id ℝ)
    E (TangentSpace I) (E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensor03TotalSpaceTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensor03TotalSpaceTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensor03TotalSpaceTopology ``Submission.DifferentialGeometry.Geometry.Connection.tensor03TotalSpaceTopology

local instance tensor03FiberBundle :
    FiberBundle (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  Bundle.ContinuousLinearMap.fiberBundle (RingHom.id ℝ)
    E (TangentSpace I) (E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensor03FiberBundle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensor03FiberBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensor03FiberBundle ``Submission.DifferentialGeometry.Geometry.Connection.tensor03FiberBundle

local instance tensor03VectorBundle :
    VectorBundle ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  Bundle.ContinuousLinearMap.vectorBundle (RingHom.id ℝ)
    E (TangentSpace I) (E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensor03VectorBundle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensor03VectorBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensor03VectorBundle ``Submission.DifferentialGeometry.Geometry.Connection.tensor03VectorBundle

local instance tensor03ContMDiffVectorBundle :
    ContMDiffVectorBundle ∞ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) I :=
  ContMDiffVectorBundle.continuousLinearMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensor03ContMDiffVectorBundle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensor03ContMDiffVectorBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensor03ContMDiffVectorBundle ``Submission.DifferentialGeometry.Geometry.Connection.tensor03ContMDiffVectorBundle

def MDiffAtTensor03
    (T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (x : M) : Prop :=
  MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ))
    (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
      (E := fun x : M =>
        TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) b (T b)) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.MDiffAtTensor03 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.MDiffAtTensor03"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.MDiffAtTensor03 ``Submission.DifferentialGeometry.Geometry.Connection.MDiffAtTensor03

def tensor03Scalar
    (cov : (Π x : M, TangentSpace I x) →
      (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x))
    (T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) (x : M)
    (X Y Z W : Π x : M, TangentSpace I x) : ℝ :=
  mvfderiv (I := I) (fun b => T b (Y b) (Z b) (W b)) x (X x)
    - T x (cov Y x (X x)) (Z x) (W x)
    - T x (Y x) (cov Z x (X x)) (W x)
    - T x (Y x) (Z x) (cov W x (X x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensor03Scalar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensor03Scalar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensor03Scalar ``Submission.DifferentialGeometry.Geometry.Connection.tensor03Scalar

omit [FiniteDimensional ℝ E] in
lemma mdifferentiableAt_tensor03_apply_one
    {T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    {Y : Π x : M, TangentSpace I x} {x : M}
    (hT : MDiffAtTensor03 T x) (hY : MDiffAt (T% Y) x) :
    MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ))
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) b (T b (Y b))) x :=
  MDifferentiableAt.clm_bundle_apply
    (E₁ := fun x : M => TangentSpace I x)
    (E₂ := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (b := fun b : M => b)
    (ϕ := fun b => T b) (v := fun b => Y b) hT hY

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.mdifferentiableAt_tensor03_apply_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.mdifferentiableAt_tensor03_apply_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.mdifferentiableAt_tensor03_apply_one ``Submission.DifferentialGeometry.Geometry.Connection.mdifferentiableAt_tensor03_apply_one

omit [FiniteDimensional ℝ E] in
lemma mdifferentiableAt_tensor03_apply_two
    {T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    {Y Z : Π x : M, TangentSpace I x} {x : M}
    (hT : MDiffAtTensor03 T x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))
      (fun b : M => TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] ℝ) b (T b (Y b) (Z b))) x :=
  MDifferentiableAt.clm_bundle_apply
    (E₁ := fun x : M => TangentSpace I x)
    (E₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
    (b := fun b : M => b)
    (ϕ := fun b => T b (Y b)) (v := fun b => Z b)
    (mdifferentiableAt_tensor03_apply_one hT hY) hZ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.mdifferentiableAt_tensor03_apply_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.mdifferentiableAt_tensor03_apply_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.mdifferentiableAt_tensor03_apply_two ``Submission.DifferentialGeometry.Geometry.Connection.mdifferentiableAt_tensor03_apply_two

omit [FiniteDimensional ℝ E] in
lemma mdifferentiableAt_tensor03_pairing
    {T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    {Y Z W : Π x : M, TangentSpace I x} {x : M}
    (hT : MDiffAtTensor03 T x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x)
    (hW : MDiffAt (T% W) x) :
    MDifferentiableAt I 𝓘(ℝ, ℝ) (fun b : M => T b (Y b) (Z b) (W b)) x := by
  have h2 : MDifferentiableAt I (I.prod 𝓘(ℝ, ℝ))
      (fun m => TotalSpace.mk' ℝ (E := fun _ : M => ℝ) m (T m (Y m) (Z m) (W m))) x :=
    MDifferentiableAt.clm_bundle_apply
      (E₁ := fun x : M => TangentSpace I x)
      (E₂ := fun _ : M => ℝ)
      (b := fun b : M => b)
      (ϕ := fun b => T b (Y b) (Z b)) (v := fun b => W b)
      (mdifferentiableAt_tensor03_apply_two hT hY hZ) hW
  rw [mdifferentiableAt_totalSpace] at h2
  exact h2.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.mdifferentiableAt_tensor03_pairing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.mdifferentiableAt_tensor03_pairing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.mdifferentiableAt_tensor03_pairing ``Submission.DifferentialGeometry.Geometry.Connection.mdifferentiableAt_tensor03_pairing

end Connection
end Geometry
end DifferentialGeometry

end
