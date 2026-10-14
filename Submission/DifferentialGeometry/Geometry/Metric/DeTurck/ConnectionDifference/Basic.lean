import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set
open scoped _root_.Manifold _root_.Topology _root_.ContDiff

namespace DifferentialGeometry
namespace PDE
namespace DeTurck


open _root_.Submission.DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

def connectionDifference (g g' : SmoothRiemannianMetric I M) :
    Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x :=
  CovariantDerivative.difference (LeviCivita (I := I) g) (LeviCivita (I := I) g')

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.connectionDifference then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.connectionDifference"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.connectionDifference ``Submission.DifferentialGeometry.PDE.DeTurck.connectionDifference

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] [T2Space M] in
@[simp]
theorem connectionDifference_apply (g g' : SmoothRiemannianMetric I M)
    {σ : Π x : M, TangentSpace I x} {x : M} (hσ : MDiffAt (T% σ) x)
    (v : TangentSpace I x) :
    connectionDifference (I := I) g g' x (σ x) v =
      (LeviCivita (I := I) g).toFun σ x v - (LeviCivita (I := I) g').toFun σ x v := by
  have h := IsCovariantDerivativeOn.difference_apply
    (LeviCivita (I := I) g).isCovariantDerivativeOnUniv
    (LeviCivita (I := I) g').isCovariantDerivativeOnUniv
    (x := x) (_root_.Set.mem_univ x) (σ := σ) hσ
  simp only [connectionDifference, CovariantDerivative.difference]
  rw [h]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.connectionDifference_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.connectionDifference_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.connectionDifference_apply ``Submission.DifferentialGeometry.PDE.DeTurck.connectionDifference_apply

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] in
@[simp]
theorem connectionDifference_self (g : SmoothRiemannianMetric I M) :
    connectionDifference (I := I) g g = 0 := by
  classical
  funext x
  apply ContinuousLinearMap.ext
  intro w
  apply ContinuousLinearMap.ext
  intro v
  obtain ⟨σ, hσx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := (TangentSpace I : M → Type _)) x w
  have hσ : MDiffAt (T% fun y => σ y) x := σ.mdifferentiableAt
  have hval : connectionDifference (I := I) g g x (σ x) v =
      (LeviCivita (I := I) g).toFun (fun y => σ y) x v -
        (LeviCivita (I := I) g).toFun (fun y => σ y) x v :=
    connectionDifference_apply (I := I) g g hσ v
  rw [sub_self] at hval
  simpa [hσx] using hval

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.connectionDifference_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.connectionDifference_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.connectionDifference_self ``Submission.DifferentialGeometry.PDE.DeTurck.connectionDifference_self

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private theorem leviCivita_section_contMDiff (g : SmoothRiemannianMetric I M)
    {σ : Π x : M, TangentSpace I x}
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% σ)) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M =>
        (⟨x, (LeviCivita (I := I) g).toFun σ x⟩ :
          _root_.Bundle.TotalSpace (E →L[ℝ] E) (fun x : M =>
            TangentSpace I x →L[ℝ] TangentSpace I x))) := by
  have hσ' : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1) (T% σ) Set.univ := by
    have h_le : ((∞ : WithTop ℕ∞) + 1) ≤ ∞ := by rw [ENat.coe_top_add_one]
    exact (hσ.of_le h_le).contMDiffOn
  have h := LeviCivita_section_contMDiffOn_univ (I := I) g hσ'
  rw [← contMDiffOn_univ]
  exact h

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.DeTurck.leviCivita_section_contMDiff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.DeTurck.leviCivita_section_contMDiff target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem connectionDifference_contMDiff (g g' : SmoothRiemannianMetric I M)
    {σ τ : Π x : M, TangentSpace I x}
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% σ))
    (hτ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% τ)) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M =>
        (⟨x, connectionDifference (I := I) g g' x (σ x) (τ x)⟩ :
          TotalSpace E (TangentSpace I))) := by
  have hcovg := leviCivita_section_contMDiff (I := I) g hσ
  have hcovg' := leviCivita_section_contMDiff (I := I) g' hσ
  have hg : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M =>
        (TotalSpace.mk' E (E := fun y : M => TangentSpace I y) x
          ((LeviCivita (I := I) g).toFun σ x (τ x)))) :=
    ContMDiff.clm_bundle_apply (b := id) hcovg hτ
  have hg' : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M =>
        (TotalSpace.mk' E (E := fun y : M => TangentSpace I y) x
          ((LeviCivita (I := I) g').toFun σ x (τ x)))) :=
    ContMDiff.clm_bundle_apply (b := id) hcovg' hτ
  have hdiff := hg.sub_section hg'
  refine hdiff.congr (fun x => ?_)
  have hσ_at : MDiffAt (T% σ) x := (hσ x).mdifferentiableAt (by simp)
  have hval := connectionDifference_apply (I := I) g g' hσ_at (τ x)
  change (⟨x, connectionDifference (I := I) g g' x (σ x) (τ x)⟩ : _root_.Bundle.TotalSpace E (TangentSpace I)) =
      ⟨x, ((fun y => (LeviCivita (I := I) g).toFun σ y (τ y)) -
        (fun y => (LeviCivita (I := I) g').toFun σ y (τ y))) x⟩
  rw [Pi.sub_apply, hval]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.connectionDifference_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.connectionDifference_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.connectionDifference_contMDiff ``Submission.DifferentialGeometry.PDE.DeTurck.connectionDifference_contMDiff

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem connectionDifference_contMDiffOn (g g' : SmoothRiemannianMetric I M)
    {U : Set M} {σ τ : Π x : M, TangentSpace I x}
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% σ))
    (hτ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (T% τ) U) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M =>
        (⟨x, connectionDifference (I := I) g g' x (σ x) (τ x)⟩ :
          TotalSpace E (TangentSpace I))) U := by
  have hcovg := (leviCivita_section_contMDiff (I := I) g hσ).contMDiffOn (s := U)
  have hcovg' := (leviCivita_section_contMDiff (I := I) g' hσ).contMDiffOn (s := U)
  have hg : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M =>
        (TotalSpace.mk' E (E := fun y : M => TangentSpace I y) x
          ((LeviCivita (I := I) g).toFun σ x (τ x)))) U :=
    ContMDiffOn.clm_bundle_apply (b := id) hcovg hτ
  have hg' : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M =>
        (TotalSpace.mk' E (E := fun y : M => TangentSpace I y) x
          ((LeviCivita (I := I) g').toFun σ x (τ x)))) U :=
    ContMDiffOn.clm_bundle_apply (b := id) hcovg' hτ
  have hdiff := hg.sub_section hg'
  refine hdiff.congr (fun x _hx => ?_)
  have hσ_at : MDiffAt (T% σ) x := (hσ x).mdifferentiableAt (by simp)
  have hval := connectionDifference_apply (I := I) g g' hσ_at (τ x)
  change (⟨x, connectionDifference (I := I) g g' x (σ x) (τ x)⟩ : _root_.Bundle.TotalSpace E (TangentSpace I)) =
      ⟨x, ((fun y => (LeviCivita (I := I) g).toFun σ y (τ y)) -
        (fun y => (LeviCivita (I := I) g').toFun σ y (τ y))) x⟩
  rw [Pi.sub_apply, hval]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.connectionDifference_contMDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.connectionDifference_contMDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.connectionDifference_contMDiffOn ``Submission.DifferentialGeometry.PDE.DeTurck.connectionDifference_contMDiffOn

end DeTurck
end PDE
end DifferentialGeometry
