import Submission.DifferentialGeometry.Bundle.Section
import Submission.DifferentialGeometry.Geometry.Connection.Realization.SmoothSections
import Submission.DifferentialGeometry.Bundle.ContinuousLinearMapSection.Basic
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace CovariantDerivative
open _root_.CovariantDerivative

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
variable {V₁ : M → Type*} [TopologicalSpace (TotalSpace F₁ V₁)]
  [∀ x, AddCommGroup (V₁ x)] [∀ x, Module 𝕜 (V₁ x)]
  [∀ x, TopologicalSpace (V₁ x)] [∀ x, IsTopologicalAddGroup (V₁ x)]
  [∀ x, ContinuousSMul 𝕜 (V₁ x)] [FiberBundle F₁ V₁]
variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [FiniteDimensional 𝕜 F₂]
variable {V₂ : M → Type*} [TopologicalSpace (TotalSpace F₂ V₂)]
  [∀ x, AddCommGroup (V₂ x)] [∀ x, Module 𝕜 (V₂ x)]
  [∀ x, TopologicalSpace (V₂ x)] [∀ x, IsTopologicalAddGroup (V₂ x)]
  [∀ x, ContinuousSMul 𝕜 (V₂ x)] [∀ x, T2Space (V₂ x)]
  [FiberBundle F₂ V₂] [VectorBundle 𝕜 F₂ V₂]

private def mapSection (φ : ∀ x, V₁ x ≃ₗ[𝕜] V₂ x)
    (σ : ∀ x, V₁ x) : ∀ x, V₂ x :=
  fun x => φ x (σ x)

open _root_.CovariantDerivative in
def pullbackFiberwiseLinearEquiv
    (φ : ∀ x, V₁ x ≃ₗ[𝕜] V₂ x)
    (hφ : ContMDiff (I.prod 𝓘(𝕜, F₁)) (I.prod 𝓘(𝕜, F₂)) 1
      (fun p : _root_.Bundle.TotalSpace F₁ V₁ => (⟨p.1, φ p.1 p.2⟩ : _root_.Bundle.TotalSpace F₂ V₂)))
    (cov : CovariantDerivative I F₂ V₂) :
    CovariantDerivative I F₁ V₁ where
  toFun σ x :=
    letI : FiniteDimensional 𝕜 (V₂ x) :=
      VectorBundle.finiteDimensional 𝕜 F₂ V₂ x
    (LinearMap.toContinuousLinearMap (φ x).symm.toLinearMap).comp
      (cov (mapSection φ σ) x)
  isCovariantDerivativeOnUniv := by
    constructor
    · intro σ σ' x hσ hσ' hx
      have hmap : MDiffAt (T% (mapSection φ σ)) x := by
        exact hφ.mdifferentiableAt (by norm_num) |>.comp x hσ
      have hmap' : MDiffAt (T% (mapSection φ σ')) x := by
        exact hφ.mdifferentiableAt (by norm_num) |>.comp x hσ'
      ext X
      rw [show mapSection φ (σ + σ') = mapSection φ σ + mapSection φ σ' by
        ext y
        simp [mapSection]]
      rw [cov.isCovariantDerivativeOnUniv.add hmap hmap']
      simp [LinearMap.coe_toContinuousLinearMap']
    · intro σ g x hσ hg hx
      have hmap : MDiffAt (T% (mapSection φ σ)) x := by
        exact hφ.mdifferentiableAt (by norm_num) |>.comp x hσ
      ext X
      rw [show mapSection φ (g • σ) = g • mapSection φ σ by
        ext y
        simp [mapSection]]
      rw [cov.isCovariantDerivativeOnUniv.leibniz hmap hg]
      simp only [ContinuousLinearMap.comp_apply, LinearMap.coe_toContinuousLinearMap',
        LinearEquiv.coe_coe, map_add, map_smul, add_apply, smul_apply,
        ContinuousLinearMap.smulRight_apply]
      rw [show mapSection φ σ x = φ x (σ x) from rfl,
        LinearEquiv.symm_apply_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.pullbackFiberwiseLinearEquiv then
    throwError "Refusing to shadow existing declaration CovariantDerivative.pullbackFiberwiseLinearEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.pullbackFiberwiseLinearEquiv ``Submission.CovariantDerivative.pullbackFiberwiseLinearEquiv

open _root_.CovariantDerivative in
@[simp]
theorem pullbackFiberwiseLinearEquiv_apply
    (φ : ∀ x, V₁ x ≃ₗ[𝕜] V₂ x)
    (hφ : ContMDiff (I.prod 𝓘(𝕜, F₁)) (I.prod 𝓘(𝕜, F₂)) 1
      (fun p : _root_.Bundle.TotalSpace F₁ V₁ => (⟨p.1, φ p.1 p.2⟩ : _root_.Bundle.TotalSpace F₂ V₂)))
    (cov : CovariantDerivative I F₂ V₂) (σ : ∀ x, V₁ x) (x : M)
    (X : TangentSpace I x) :
    pullbackFiberwiseLinearEquiv φ hφ cov σ x X =
      (φ x).symm (cov (fun y => φ y (σ y)) x X) := by
  simp only [pullbackFiberwiseLinearEquiv, ContinuousLinearMap.comp_apply,
    LinearMap.coe_toContinuousLinearMap', LinearEquiv.coe_coe]
  have hmap : (fun y => φ y (σ y)) = mapSection φ σ := by
    funext y
    rfl
  rw [hmap]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.pullbackFiberwiseLinearEquiv_apply then
    throwError "Refusing to shadow existing declaration CovariantDerivative.pullbackFiberwiseLinearEquiv_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.pullbackFiberwiseLinearEquiv_apply ``Submission.CovariantDerivative.pullbackFiberwiseLinearEquiv_apply

open _root_.CovariantDerivative in
theorem pullbackFiberwiseLinearEquiv_trans
    {F₃ : Type*} [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃]
    [FiniteDimensional 𝕜 F₃]
    {V₃ : M → Type*} [TopologicalSpace (_root_.Bundle.TotalSpace F₃ V₃)]
    [∀ x, AddCommGroup (V₃ x)] [∀ x, Module 𝕜 (V₃ x)]
    [∀ x, TopologicalSpace (V₃ x)] [∀ x, IsTopologicalAddGroup (V₃ x)]
    [∀ x, ContinuousSMul 𝕜 (V₃ x)] [∀ x, T2Space (V₃ x)]
    [FiberBundle F₃ V₃] [VectorBundle 𝕜 F₃ V₃]
    (φ : ∀ x, V₁ x ≃ₗ[𝕜] V₂ x)
    (hφ : ContMDiff (I.prod 𝓘(𝕜, F₁)) (I.prod 𝓘(𝕜, F₂)) 1
      (fun p : _root_.Bundle.TotalSpace F₁ V₁ => (⟨p.1, φ p.1 p.2⟩ : _root_.Bundle.TotalSpace F₂ V₂)))
    (ψ : ∀ x, V₂ x ≃ₗ[𝕜] V₃ x)
    (hψ : ContMDiff (I.prod 𝓘(𝕜, F₂)) (I.prod 𝓘(𝕜, F₃)) 1
      (fun p : _root_.Bundle.TotalSpace F₂ V₂ => (⟨p.1, ψ p.1 p.2⟩ : _root_.Bundle.TotalSpace F₃ V₃)))
    (cov : CovariantDerivative I F₃ V₃) :
    pullbackFiberwiseLinearEquiv (fun x => (φ x).trans (ψ x)) (hψ.comp hφ) cov =
      pullbackFiberwiseLinearEquiv φ hφ
        (pullbackFiberwiseLinearEquiv ψ hψ cov) := by
  ext σ x X
  change (φ x).symm ((ψ x).symm (cov (fun y => ψ y (φ y (σ y))) x X)) = _
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.pullbackFiberwiseLinearEquiv_trans then
    throwError "Refusing to shadow existing declaration CovariantDerivative.pullbackFiberwiseLinearEquiv_trans"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.pullbackFiberwiseLinearEquiv_trans ``Submission.CovariantDerivative.pullbackFiberwiseLinearEquiv_trans

open _root_.CovariantDerivative in
theorem map_pullbackFiberwiseLinearEquiv_apply
    (φ : ∀ x, V₁ x ≃ₗ[𝕜] V₂ x)
    (hφ : ContMDiff (I.prod 𝓘(𝕜, F₁)) (I.prod 𝓘(𝕜, F₂)) 1
      (fun p : _root_.Bundle.TotalSpace F₁ V₁ => (⟨p.1, φ p.1 p.2⟩ : _root_.Bundle.TotalSpace F₂ V₂)))
    (cov : CovariantDerivative I F₂ V₂) (σ : ∀ x, V₁ x) (x : M)
    (X : TangentSpace I x) :
    φ x (pullbackFiberwiseLinearEquiv φ hφ cov σ x X) =
      cov (fun y => φ y (σ y)) x X := by
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.map_pullbackFiberwiseLinearEquiv_apply then
    throwError "Refusing to shadow existing declaration CovariantDerivative.map_pullbackFiberwiseLinearEquiv_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.map_pullbackFiberwiseLinearEquiv_apply ``Submission.CovariantDerivative.map_pullbackFiberwiseLinearEquiv_apply

open _root_.CovariantDerivative in
theorem pullbackFiberwiseLinearEquiv_eq_zero_iff
    {φ : ∀ x, V₁ x ≃ₗ[𝕜] V₂ x}
    (hφ : ContMDiff (I.prod 𝓘(𝕜, F₁)) (I.prod 𝓘(𝕜, F₂)) 1
      (fun p : _root_.Bundle.TotalSpace F₁ V₁ => (⟨p.1, φ p.1 p.2⟩ : _root_.Bundle.TotalSpace F₂ V₂)))
    {cov : CovariantDerivative I F₂ V₂} {σ : ∀ x, V₁ x} :
    pullbackFiberwiseLinearEquiv φ hφ cov σ = 0 ↔
      cov (fun x => φ x (σ x)) = 0 := by
  constructor
  · intro h
    funext x
    ext X
    rw [← map_pullbackFiberwiseLinearEquiv_apply φ hφ cov σ x X, h]
    simp
  · intro h
    funext x
    ext X
    rw [pullbackFiberwiseLinearEquiv_apply φ hφ cov σ x X, h]
    simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.pullbackFiberwiseLinearEquiv_eq_zero_iff then
    throwError "Refusing to shadow existing declaration CovariantDerivative.pullbackFiberwiseLinearEquiv_eq_zero_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.pullbackFiberwiseLinearEquiv_eq_zero_iff ``Submission.CovariantDerivative.pullbackFiberwiseLinearEquiv_eq_zero_iff

end CovariantDerivative

namespace CovariantDerivative
open _root_.CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

open _root_.CovariantDerivative in
local instance tangentFiberBundle :
    FiberBundle E (TangentSpace I : M → Type _) :=
  TangentSpace.fiberBundle (I := I) (M := M)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.tangentFiberBundle then
    throwError "Refusing to shadow existing declaration CovariantDerivative.tangentFiberBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.tangentFiberBundle ``Submission.CovariantDerivative.tangentFiberBundle

open _root_.CovariantDerivative in
local instance tangentVectorBundle :
    VectorBundle ℝ E (TangentSpace I : M → Type _) :=
  TangentSpace.vectorBundle (I := I) (M := M)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.tangentVectorBundle then
    throwError "Refusing to shadow existing declaration CovariantDerivative.tangentVectorBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.tangentVectorBundle ``Submission.CovariantDerivative.tangentVectorBundle

variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [FiniteDimensional ℝ F₁]
variable {V₁ : M → Type*} [TopologicalSpace (TotalSpace F₁ V₁)]
  [∀ x, AddCommGroup (V₁ x)] [∀ x, Module ℝ (V₁ x)]
  [∀ x, TopologicalSpace (V₁ x)] [∀ x, IsTopologicalAddGroup (V₁ x)]
  [∀ x, ContinuousSMul ℝ (V₁ x)]
  [FiberBundle F₁ V₁] [VectorBundle ℝ F₁ V₁]
variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  [FiniteDimensional ℝ F₂]
variable {V₂ : M → Type*} [TopologicalSpace (TotalSpace F₂ V₂)]
  [∀ x, AddCommGroup (V₂ x)] [∀ x, Module ℝ (V₂ x)]
  [∀ x, TopologicalSpace (V₂ x)] [∀ x, IsTopologicalAddGroup (V₂ x)]
  [∀ x, ContinuousSMul ℝ (V₂ x)] [∀ x, T2Space (V₂ x)]
  [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂]

open _root_.CovariantDerivative in
local instance covHomV₁Topology :
    TopologicalSpace
      (_root_.Bundle.TotalSpace (E →L[ℝ] F₁) (fun x : M => TangentSpace I x →L[ℝ] V₁ x)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id ℝ)
    E (TangentSpace I) F₁ V₁

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.covHomV₁Topology then
    throwError "Refusing to shadow existing declaration CovariantDerivative.covHomV₁Topology"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.covHomV₁Topology ``Submission.CovariantDerivative.covHomV₁Topology

open _root_.CovariantDerivative in
local instance covHomV₁FiberBundle :
    FiberBundle (E →L[ℝ] F₁) (fun x : M => TangentSpace I x →L[ℝ] V₁ x) :=
  Bundle.ContinuousLinearMap.fiberBundle (RingHom.id ℝ)
    E (TangentSpace I) F₁ V₁

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.covHomV₁FiberBundle then
    throwError "Refusing to shadow existing declaration CovariantDerivative.covHomV₁FiberBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.covHomV₁FiberBundle ``Submission.CovariantDerivative.covHomV₁FiberBundle

open _root_.CovariantDerivative in
local instance covHomV₁VectorBundle :
    VectorBundle ℝ (E →L[ℝ] F₁) (fun x : M => TangentSpace I x →L[ℝ] V₁ x) :=
  Bundle.ContinuousLinearMap.vectorBundle (RingHom.id ℝ)
    E (TangentSpace I) F₁ V₁

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.covHomV₁VectorBundle then
    throwError "Refusing to shadow existing declaration CovariantDerivative.covHomV₁VectorBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.covHomV₁VectorBundle ``Submission.CovariantDerivative.covHomV₁VectorBundle

open _root_.CovariantDerivative in
local instance covHomV₂Topology :
    TopologicalSpace
      (_root_.Bundle.TotalSpace (E →L[ℝ] F₂) (fun x : M => TangentSpace I x →L[ℝ] V₂ x)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id ℝ)
    E (TangentSpace I) F₂ V₂

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.covHomV₂Topology then
    throwError "Refusing to shadow existing declaration CovariantDerivative.covHomV₂Topology"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.covHomV₂Topology ``Submission.CovariantDerivative.covHomV₂Topology

open _root_.CovariantDerivative in
local instance covHomV₂FiberBundle :
    FiberBundle (E →L[ℝ] F₂) (fun x : M => TangentSpace I x →L[ℝ] V₂ x) :=
  Bundle.ContinuousLinearMap.fiberBundle (RingHom.id ℝ)
    E (TangentSpace I) F₂ V₂

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.covHomV₂FiberBundle then
    throwError "Refusing to shadow existing declaration CovariantDerivative.covHomV₂FiberBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.covHomV₂FiberBundle ``Submission.CovariantDerivative.covHomV₂FiberBundle

open _root_.CovariantDerivative in
local instance covHomV₂VectorBundle :
    VectorBundle ℝ (E →L[ℝ] F₂) (fun x : M => TangentSpace I x →L[ℝ] V₂ x) :=
  Bundle.ContinuousLinearMap.vectorBundle (RingHom.id ℝ)
    E (TangentSpace I) F₂ V₂

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.covHomV₂VectorBundle then
    throwError "Refusing to shadow existing declaration CovariantDerivative.covHomV₂VectorBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.covHomV₂VectorBundle ``Submission.CovariantDerivative.covHomV₂VectorBundle

omit [FiniteDimensional ℝ F₁] in
open _root_.CovariantDerivative _root_.CovariantDerivative.ContMDiffCovariantDerivative in
theorem ContMDiffCovariantDerivative.pullbackFiberwiseLinearEquiv
    (φ : ∀ x, V₁ x ≃ₗ[ℝ] V₂ x)
    (hφ : ContMDiff (I.prod 𝓘(ℝ, F₁)) (I.prod 𝓘(ℝ, F₂)) ∞
      (fun p : _root_.Bundle.TotalSpace F₁ V₁ => (⟨p.1, φ p.1 p.2⟩ : _root_.Bundle.TotalSpace F₂ V₂)))
    (hφinv : ContMDiff (I.prod 𝓘(ℝ, F₂)) (I.prod 𝓘(ℝ, F₁)) ∞
      (fun p : _root_.Bundle.TotalSpace F₂ V₂ =>
        (⟨p.1, (φ p.1).symm p.2⟩ : _root_.Bundle.TotalSpace F₁ V₁)))
    (cov : CovariantDerivative I F₂ V₂)
    [_root_.CovariantDerivative.ContMDiffCovariantDerivative cov ∞] :
    _root_.CovariantDerivative.ContMDiffCovariantDerivative
      (pullbackFiberwiseLinearEquiv φ (hφ.of_le (by norm_num)) cov) ∞ where
  contMDiff := by
    constructor
    intro σ hσ
    have hσglobal : ContMDiff I (I.prod 𝓘(ℝ, F₁)) ∞ (T% σ) := by
      rw [← contMDiffOn_univ]
      simpa using hσ
    have hmap : ContMDiff I (I.prod 𝓘(ℝ, F₂)) ∞
        (T% (mapSection φ σ)) := by
      exact (hφ.comp hσglobal).congr fun x => rfl
    have hcovOn :=
      (inferInstance : _root_.CovariantDerivative.ContMDiffCovariantDerivative cov ∞).contMDiff.contMDiff
        hmap.contMDiffOn
    have hcov := contMDiffOn_univ.mp hcovOn
    apply ContMDiff.contMDiffOn
    apply DifferentialGeometry.Geometry.Connection.Realization.contMDiff_clm_section_of_pointwise
      (I := I) (M := M)
    intro Y
    have heval : ContMDiff I (I.prod 𝓘(ℝ, F₂)) ∞
        (T% (fun x => cov (mapSection φ σ) x (Y x))) :=
      ContMDiff.clm_bundle_apply (b := id) hcov Y.contMDiff
    exact (hφinv.comp heval).congr fun x => by
      simp only [pullbackFiberwiseLinearEquiv_apply]
      have hmapEq : (fun y => φ y (σ y)) = mapSection φ σ := by
        funext y
        rfl
      rw [hmapEq]
      rfl

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.CovariantDerivative.ContMDiffCovariantDerivative
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.ContMDiffCovariantDerivative.pullbackFiberwiseLinearEquiv then
    throwError "Refusing to shadow existing declaration CovariantDerivative.ContMDiffCovariantDerivative.pullbackFiberwiseLinearEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.ContMDiffCovariantDerivative.pullbackFiberwiseLinearEquiv ``Submission.CovariantDerivative.ContMDiffCovariantDerivative.pullbackFiberwiseLinearEquiv

end CovariantDerivative
