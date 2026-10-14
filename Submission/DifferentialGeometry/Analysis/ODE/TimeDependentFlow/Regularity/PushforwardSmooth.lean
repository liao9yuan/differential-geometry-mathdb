import Submission.DifferentialGeometry.Analysis.ODE.TimeDependentFlow.DiffeomorphismFamily.ManifoldIntegralFlow
import Submission.DifferentialGeometry.Bundle.VectorField.Pushforward
import Mathlib.Geometry.Manifold.LocalDiffeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


namespace DifferentialGeometry.Analysis.ODE

open _root_.Set _root_.Function _root_.Bundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff

section SpatialAtFixedTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [T2Space M]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M] in
theorem flowFamily_contMDiff_fixed_time
    (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M)) (s : ℝ) :
    ContMDiff I I ∞ (Φ_fam s : M → M) :=
  (Φ_fam s).contMDiff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.flowFamily_contMDiff_fixed_time then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.flowFamily_contMDiff_fixed_time"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.flowFamily_contMDiff_fixed_time ``Submission.DifferentialGeometry.Analysis.ODE.flowFamily_contMDiff_fixed_time

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M] in
theorem flowFamily_mdifferentiableAt_fixed_time
    (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M)) (s : ℝ) (x : M) :
    MDifferentiableAt I I (Φ_fam s : M → M) x := by
  have hinfty : (∞ : WithTop ℕ∞) ≠ 0 := by decide
  exact (Φ_fam s).mdifferentiable hinfty x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.flowFamily_mdifferentiableAt_fixed_time then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.flowFamily_mdifferentiableAt_fixed_time"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.flowFamily_mdifferentiableAt_fixed_time ``Submission.DifferentialGeometry.Analysis.ODE.flowFamily_mdifferentiableAt_fixed_time

end SpatialAtFixedTime

section Pushforward

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem flowFamily_pushforward_contMDiff
    (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M)) (s : ℝ)
    {Y : ∀ x : M, TangentSpace I x}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := TangentSpace I) x (Y x))) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := TangentSpace I) x
        (DifferentialGeometry.Diffeomorph.pushforward (Φ_fam s) Y x)) := by
  exact Diffeomorph.pushforward_contMDiff (I := I) (Φ_fam s) hY

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.flowFamily_pushforward_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.flowFamily_pushforward_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.flowFamily_pushforward_contMDiff ``Submission.DifferentialGeometry.Analysis.ODE.flowFamily_pushforward_contMDiff

end Pushforward

section TimeRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [T2Space M] [CompactSpace M] [SigmaCompactSpace M]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M]
    [CompactSpace M] [SigmaCompactSpace M] in
theorem flowFamily_hasMFDerivWithinAt_time
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (T : ℝ) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hbare : ∀ s : ℝ, 0 < s → s < T → ∀ x : M,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => Φ_fam u x) (_root_.Set.Ici 0) s
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X s (Φ_fam s x))))
    (s : ℝ) (hs : 0 < s) (hsT : s < T) (x : M) :
    HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => Φ_fam u x) (_root_.Set.Ici 0) s
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X s (Φ_fam s x))) :=
  hbare s hs hsT x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.flowFamily_hasMFDerivWithinAt_time then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.flowFamily_hasMFDerivWithinAt_time"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.flowFamily_hasMFDerivWithinAt_time ``Submission.DifferentialGeometry.Analysis.ODE.flowFamily_hasMFDerivWithinAt_time

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M]
    [CompactSpace M] [SigmaCompactSpace M] in
theorem flowFamily_continuousWithinAt_time
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (T : ℝ) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hbare : ∀ s : ℝ, 0 < s → s < T → ∀ x : M,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => Φ_fam u x) (_root_.Set.Ici 0) s
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X s (Φ_fam s x))))
    (s : ℝ) (hs : 0 < s) (hsT : s < T) (x : M) :
    ContinuousWithinAt (fun u : ℝ => Φ_fam u x) (_root_.Set.Ici 0) s :=
  (hbare s hs hsT x).continuousWithinAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.flowFamily_continuousWithinAt_time then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.flowFamily_continuousWithinAt_time"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.flowFamily_continuousWithinAt_time ``Submission.DifferentialGeometry.Analysis.ODE.flowFamily_continuousWithinAt_time

end TimeRegularity

section RegularityPackage

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [CompactSpace M]


omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem flowFamily_regularity
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (T : ℝ) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hbare : ∀ s : ℝ, 0 < s → s < T → ∀ x : M,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => Φ_fam u x) (_root_.Set.Ici 0) s
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X s (Φ_fam s x)))) :
    (∀ s : ℝ, ContMDiff I I ∞ (Φ_fam s : M → M)) ∧
    (∀ (s : ℝ) (Y : ∀ x : M, TangentSpace I x),
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E (E := TangentSpace I) x (Y x)) →
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E (E := TangentSpace I) x
          (DifferentialGeometry.Diffeomorph.pushforward (Φ_fam s) Y x))) ∧
    (∀ (s : ℝ) (x : M), MDifferentiableAt I I (Φ_fam s : M → M) x) ∧
    (∀ s : ℝ, 0 < s → s < T → ∀ x : M,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => Φ_fam u x) (_root_.Set.Ici 0) s
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X s (Φ_fam s x)))) ∧
    (∀ s : ℝ, 0 < s → s < T → ∀ x : M,
      ContinuousWithinAt (fun u : ℝ => Φ_fam u x) (_root_.Set.Ici 0) s) :=
  ⟨fun s => flowFamily_contMDiff_fixed_time Φ_fam s,
   fun s _Y hY => flowFamily_pushforward_contMDiff Φ_fam s hY,
   fun s x => flowFamily_mdifferentiableAt_fixed_time Φ_fam s x,
   hbare,
   fun s hs hsT x => (hbare s hs hsT x).continuousWithinAt⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.ODE.flowFamily_regularity
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.ODE.flowFamily_regularity target :: scope.openDecls } }

end RegularityPackage

end DifferentialGeometry.Analysis.ODE
