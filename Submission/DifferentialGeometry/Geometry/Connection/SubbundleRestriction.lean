import Submission.DifferentialGeometry.Geometry.Connection.Subbundle
import Mathlib.Analysis.Normed.Module.ContinuousInverse
import Submission.DifferentialGeometry.Bundle.SmoothSubbundle.Hom

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Set
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
variable [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
variable [∀ x, TopologicalSpace (V x)] [FiberBundle F V]
variable [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
variable [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]

namespace ContMDiffVectorSubbundle

private def fiberRetraction
    (S : ContMDiffVectorSubbundle (I := I) (F := F) (V := V) (n := ∞)) (x : M) :
    V x →L[ℝ] S.fiber x := by
  let _ : FiniteDimensional ℝ (V x) := VectorBundle.finiteDimensional ℝ F V x
  let _ : T2Space (V x) := FiberBundle.t2Space F V x
  exact (ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional
    (f := (S.fiber x).subtypeL) (S.fiber x).injective_subtype).leftInverse

run_cmd do
  let target := ``Submission.ContMDiffVectorSubbundle.fiberRetraction
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `ContMDiffVectorSubbundle.fiberRetraction target :: scope.openDecls } }

private theorem fiberRetraction_apply
    (S : ContMDiffVectorSubbundle (I := I) (F := F) (V := V) (n := ∞))
    (x : M) (v : S.fiber x) : S.fiberRetraction x (v : V x) = v := by
  let _ : FiniteDimensional ℝ (V x) := VectorBundle.finiteDimensional ℝ F V x
  let _ : T2Space (V x) := FiberBundle.t2Space F V x
  exact (ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional
    (f := (S.fiber x).subtypeL) (S.fiber x).injective_subtype).leftInverse_leftInverse v

run_cmd do
  let target := ``Submission.ContMDiffVectorSubbundle.fiberRetraction_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `ContMDiffVectorSubbundle.fiberRetraction_apply target :: scope.openDecls } }

private def projectedCovariantDerivative
    (S : ContMDiffVectorSubbundle (I := I) (F := F) (V := V) (n := ∞))
    (cov : CovariantDerivative I F V) :
    letI := S.totalSpaceTopology
    letI := S.fiberBundle
    CovariantDerivative I (Fin S.rank → ℝ) (fun x => S.fiber x) := by
  letI := S.totalSpaceTopology
  letI := S.fiberBundle
  letI := S.vector_bundle
  letI := S.contMDiffVectorBundle
  let D := fun (σ : (x : M) → S.fiber x) (x : M) =>
    (S.fiberRetraction x).comp (cov (fun y => (σ y : V y)) x)
  have hinc {σ : (x : M) → S.fiber x} {x : M}
      (hσ : MDifferentiableAt I (I.prod 𝓘(ℝ, Fin S.rank → ℝ))
        (fun y => TotalSpace.mk' (Fin S.rank → ℝ) y (σ y)) x) :
      MDifferentiableAt I (I.prod 𝓘(ℝ, F))
        (fun y => TotalSpace.mk' F y (σ y : V y)) x :=
    ((S.contMDiff_subtypeVal (TotalSpace.mk' (Fin S.rank → ℝ) x (σ x))).mdifferentiableAt
      (by simp)).comp x hσ
  refine ⟨D, ?_, ?_⟩
  · intro σ τ x hσ hτ _
    apply ContinuousLinearMap.ext
    intro v
    have h := congrArg (fun A : TangentSpace I x →L[ℝ] V x => S.fiberRetraction x (A v))
      (cov.isCovariantDerivativeOnUniv.add (hinc hσ) (hinc hτ))
    rw [show (fun y => (σ y : V y)) + (fun y => (τ y : V y)) =
      (fun y => (σ y : V y) + (τ y : V y)) by rfl] at h
    simpa only [D, ContinuousLinearMap.comp_apply, add_apply, map_add,
      Pi.add_apply, Submodule.coe_add] using h
  · intro σ f x hσ hf _
    apply ContinuousLinearMap.ext
    intro v
    have h := congrArg (fun A : TangentSpace I x →L[ℝ] V x => S.fiberRetraction x (A v))
      (cov.isCovariantDerivativeOnUniv.leibniz (hinc hσ) hf)
    rw [Pi.smul_def'] at h
    simpa only [D, ContinuousLinearMap.comp_apply, add_apply,
      smul_apply, ContinuousLinearMap.smulRight_apply, map_add, map_smul,
      Pi.smul_apply', Submodule.coe_smul, fiberRetraction_apply] using h

run_cmd do
  let target := ``Submission.ContMDiffVectorSubbundle.projectedCovariantDerivative
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `ContMDiffVectorSubbundle.projectedCovariantDerivative target :: scope.openDecls } }

private theorem projectedCovariantDerivative_apply
    (S : ContMDiffVectorSubbundle (I := I) (F := F) (V := V) (n := ∞))
    (cov : CovariantDerivative I F V) (σ : (x : M) → S.fiber x)
    (x : M) (v : TangentSpace I x) :
    S.projectedCovariantDerivative cov σ x v =
      S.fiberRetraction x (cov (fun y => (σ y : V y)) x v) := rfl

run_cmd do
  let target := ``Submission.ContMDiffVectorSubbundle.projectedCovariantDerivative_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `ContMDiffVectorSubbundle.projectedCovariantDerivative_apply target :: scope.openDecls } }

private theorem projectedCovariantDerivative_subtypeVal
    (S : ContMDiffVectorSubbundle (I := I) (F := F) (V := V) (n := ∞))
    (cov : CovariantDerivative I F V)
    (hcov : DifferentialGeometry.Geometry.Connection.IsCovariantlyInvariantSubmoduleFamily cov S.fiber) :
    letI := S.totalSpaceTopology
    letI := S.fiberBundle
    ∀ (σ : Cₛ^∞⟮I; Fin S.rank → ℝ, fun x => S.fiber x⟯) (x : M) (v : TangentSpace I x),
      (S.projectedCovariantDerivative cov σ x v : V x) =
        cov (fun y => (σ y : V y)) x v := by
  let _ := S.totalSpaceTopology
  let _ := S.fiberBundle
  intro σ x v
  let τ : Cₛ^∞⟮I; F, V⟯ :=
    ⟨fun y => (σ y : V y), (S.contMDiff_section_iff σ).mp σ.contMDiff⟩
  have hmem : cov τ x v ∈ S.fiber x :=
    hcov τ _root_.Set.univ isOpen_univ (fun y _ => (σ y).property) x (_root_.Set.mem_univ x) v
  have h := congrArg Subtype.val (S.fiberRetraction_apply x (⟨cov τ x v, hmem⟩ : S.fiber x))
  simpa only [projectedCovariantDerivative_apply, τ, ContMDiffSection.coeFn_mk] using h

run_cmd do
  let target := ``Submission.ContMDiffVectorSubbundle.projectedCovariantDerivative_subtypeVal
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `ContMDiffVectorSubbundle.projectedCovariantDerivative_subtypeVal target :: scope.openDecls } }

private theorem exists_covariantDerivative_subtypeVal
    (S : ContMDiffVectorSubbundle (I := I) (F := F) (V := V) (n := ∞))
    (cov : CovariantDerivative I F V)
    (hcov : DifferentialGeometry.Geometry.Connection.IsCovariantlyInvariantSubmoduleFamily cov S.fiber) :
    letI := S.totalSpaceTopology
    letI := S.fiberBundle
    ∃ D : CovariantDerivative I (Fin S.rank → ℝ) (fun x => S.fiber x),
      ∀ (σ : Cₛ^∞⟮I; Fin S.rank → ℝ, fun x => S.fiber x⟯)
        (x : M) (v : TangentSpace I x),
        (D σ x v : V x) = cov (fun y => (σ y : V y)) x v := by
  let _ := S.totalSpaceTopology
  let _ := S.fiberBundle
  exact ⟨S.projectedCovariantDerivative cov, S.projectedCovariantDerivative_subtypeVal cov hcov⟩

run_cmd do
  let target := ``Submission.ContMDiffVectorSubbundle.exists_covariantDerivative_subtypeVal
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `ContMDiffVectorSubbundle.exists_covariantDerivative_subtypeVal target :: scope.openDecls } }

end ContMDiffVectorSubbundle

namespace CovariantDerivative
open _root_.CovariantDerivative

open _root_.CovariantDerivative in
def restrict
    (cov : CovariantDerivative I F V)
    (S : ContMDiffVectorSubbundle (I := I) (F := F) (V := V) (n := ∞))
    (hS : DifferentialGeometry.Geometry.Connection.IsCovariantlyInvariantSubmoduleFamily cov S.fiber) :
    letI := S.totalSpaceTopology
    letI := S.fiberBundle
    CovariantDerivative I (Fin S.rank → ℝ) (fun x => S.fiber x) :=
  (S.exists_covariantDerivative_subtypeVal cov hS).choose

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.restrict then
    throwError "Refusing to shadow existing declaration CovariantDerivative.restrict"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.restrict ``Submission.CovariantDerivative.restrict

open _root_.CovariantDerivative in
theorem restrict_subtypeVal
    (cov : CovariantDerivative I F V)
    (S : ContMDiffVectorSubbundle (I := I) (F := F) (V := V) (n := ∞))
    (hS : DifferentialGeometry.Geometry.Connection.IsCovariantlyInvariantSubmoduleFamily cov S.fiber) :
    letI := S.totalSpaceTopology
    letI := S.fiberBundle
    ∀ (σ : Cₛ^∞⟮I; Fin S.rank → ℝ, fun x => S.fiber x⟯)
      (x : M) (v : TangentSpace I x),
      (cov.restrict S hS σ x v : V x) = cov (fun y => (σ y : V y)) x v :=
  (S.exists_covariantDerivative_subtypeVal cov hS).choose_spec

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.restrict_subtypeVal then
    throwError "Refusing to shadow existing declaration CovariantDerivative.restrict_subtypeVal"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.restrict_subtypeVal ``Submission.CovariantDerivative.restrict_subtypeVal

open _root_.CovariantDerivative in
theorem subtypeL_comp_restrict
    (cov : CovariantDerivative I F V)
    (S : ContMDiffVectorSubbundle (I := I) (F := F) (V := V) (n := ∞))
    (hS : DifferentialGeometry.Geometry.Connection.IsCovariantlyInvariantSubmoduleFamily cov S.fiber) :
    letI := S.totalSpaceTopology
    letI := S.fiberBundle
    ∀ (σ : Cₛ^∞⟮I; Fin S.rank → ℝ, fun x => S.fiber x⟯) (x : M),
      (S.fiber x).subtypeL.comp (cov.restrict S hS σ x) =
        cov (fun y => (σ y : V y)) x := by
  let _ := S.totalSpaceTopology
  let _ := S.fiberBundle
  intro σ x
  apply ContinuousLinearMap.ext
  exact cov.restrict_subtypeVal S hS σ x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.subtypeL_comp_restrict then
    throwError "Refusing to shadow existing declaration CovariantDerivative.subtypeL_comp_restrict"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.subtypeL_comp_restrict ``Submission.CovariantDerivative.subtypeL_comp_restrict

open _root_.CovariantDerivative in
theorem contMDiff_restrict [IsManifold I ∞ M]
    (cov : CovariantDerivative I F V)
    (S : ContMDiffVectorSubbundle (I := I) (F := F) (V := V) (n := ∞))
    (hS : DifferentialGeometry.Geometry.Connection.IsCovariantlyInvariantSubmoduleFamily cov S.fiber)
    (hD : _root_.CovariantDerivative.ContMDiffCovariantDerivative cov ∞) :
    letI := S.totalSpaceTopology
    letI := S.fiberBundle
    letI := S.vector_bundle
    ContMDiffCovariantDerivative (cov.restrict S hS) ∞ := by
  let _ := S.totalSpaceTopology
  let _ := S.fiberBundle
  let _ := S.vector_bundle
  let _ := S.contMDiffVectorBundle
  refine ⟨⟨?_⟩⟩
  intro σ hσ
  have hσ' : ContMDiff I (I.prod 𝓘(ℝ, Fin S.rank → ℝ)) ∞
      (fun x => TotalSpace.mk' (Fin S.rank → ℝ) x (σ x)) := by
    simpa [contMDiffOn_univ] using hσ
  let τ : Cₛ^∞⟮I; Fin S.rank → ℝ, fun x => S.fiber x⟯ := ⟨σ, hσ'⟩
  have hamb : ContMDiffOn I (I.prod 𝓘(ℝ, F)) (∞ + 1)
      (fun x => TotalSpace.mk' F x (σ x : V x)) univ := by
    simpa using ((S.contMDiff_section_iff σ).mp hσ').contMDiffOn
  have hA := hD.contMDiff.contMDiff hamb
  apply (S.contMDiffOn_hom_section_iff (cov.restrict S hS σ) _root_.Set.univ).mpr
  apply hA.congr
  intro x hx
  congr 1
  apply ContinuousLinearMap.ext
  intro v
  exact cov.restrict_subtypeVal S hS τ x v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.contMDiff_restrict then
    throwError "Refusing to shadow existing declaration CovariantDerivative.contMDiff_restrict"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.contMDiff_restrict ``Submission.CovariantDerivative.contMDiff_restrict

end CovariantDerivative
