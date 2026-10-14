import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.Smooth.MetricFlatBasis

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Connection

attribute [local instance] Fintype.ofFinite Classical.propDecidable

open _root_.Bundle _root_.Submission.Bundle
open _root_.Submission.DifferentialGeometry.Tensor.Coordinates
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]

omit [SigmaCompactSpace M] [T2Space M] in
theorem leviCivitaConnectionOfMetric_homSection_contMDiffAt
    {ι : Type*} [Finite ι]
    (e : _root_.Bundle.Trivialization E (TotalSpace.proj : _root_.Bundle.TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M)
    {σ : (x : M) → TangentSpace I x} {x : M}
    (hx : x ∈ e.baseSet)
    (hσdiff : ∀ᶠ y in 𝓝 x, MDiffAt (T% σ) y)
    (hσ : ContMDiffAt I (I.prod 𝓘(Real, E)) ∞ (T% σ) x) :
    ContMDiffAt I (I.prod 𝓘(Real, E →L[Real] E)) ∞
      (fun y : M =>
        (⟨y, leviCivitaConnectionOfMetric (I := I) g σ y⟩ :
          _root_.Bundle.TotalSpace (E →L[Real] E)
            (fun y : M => TangentSpace I y →L[Real] TangentSpace I y))) x :=
  covariantDerivative_homSection_contMDiffAt_of_coeff
    (I := I) (leviCivitaConnectionOfMetric (I := I) g) e b hx hσdiff hσ
    (fun i k j => lc_christoffel_contMDiffAt (I := I) e b g hx i j k)

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_homSection_contMDiffAt with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_homSection_contMDiffAt"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_homSection_contMDiffAt ``Submission.DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_homSection_contMDiffAt

omit [SigmaCompactSpace M] [T2Space M] in
theorem leviCivitaConnectionOfMetric_homSection_contMDiffAt_one
    {ι : Type*} [Finite ι]
    (e : _root_.Bundle.Trivialization E (TotalSpace.proj : _root_.Bundle.TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M)
    {σ : (x : M) → TangentSpace I x} {x : M}
    (hx : x ∈ e.baseSet)
    (hσdiff : ∀ᶠ y in 𝓝 x, MDiffAt (T% σ) y)
    (hσ : ContMDiffAt I (I.prod 𝓘(Real, E)) (2 : WithTop ℕ∞) (T% σ) x) :
    ContMDiffAt I (I.prod 𝓘(Real, E →L[Real] E)) (1 : WithTop ℕ∞)
      (fun y : M =>
        (⟨y, leviCivitaConnectionOfMetric (I := I) g σ y⟩ :
          _root_.Bundle.TotalSpace (E →L[Real] E)
            (fun y : M => TangentSpace I y →L[Real] TangentSpace I y))) x := by
  exact covariantDerivative_homSection_contMDiffAt_of_coeff_one
    (I := I) (leviCivitaConnectionOfMetric (I := I) g) e b hx hσdiff hσ
    (fun i k j => lc_christoffel_contMDiffAt (I := I) e b g hx i j k)

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_homSection_contMDiffAt_one with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_homSection_contMDiffAt_one"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_homSection_contMDiffAt_one ``Submission.DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_homSection_contMDiffAt_one

omit [SigmaCompactSpace M] [T2Space M] in
theorem leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
    (g : SmoothRiemannianMetric I M) :
    CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (I := I) (E := E) (M := M)
      (leviCivitaConnectionOfMetric (I := I) g) ∞ := by
  intro u hu
  refine ⟨?_⟩
  intro σ hσ x hx
  let e : _root_.Bundle.Trivialization E
      (TotalSpace.proj : _root_.Bundle.TotalSpace E (TangentSpace I : M → Type _) → M) :=
    _root_.FiberBundle.trivializationAt E (TangentSpace I : M → Type _) x
  let b := Module.finBasis Real E
  have hxBase : x ∈ e.baseSet := by
    simp [e]
  have hσAtTop :
      ContMDiffAt I (I.prod 𝓘(Real, E)) ((∞ : WithTop ℕ∞) + 1) (T% σ) x :=
    hσ.contMDiffAt (hu.mem_nhds hx)
  have hσAt :
      ContMDiffAt I (I.prod 𝓘(Real, E)) ∞ (T% σ) x :=
    hσAtTop.of_le (by simp)
  have hσdiff : ∀ᶠ y in 𝓝 x, MDiffAt (T% σ) y := by
    filter_upwards [hu.mem_nhds hx] with y hy
    have hyTop :
        ContMDiffAt I (I.prod 𝓘(Real, E)) ((∞ : WithTop ℕ∞) + 1) (T% σ) y :=
      hσ.contMDiffAt (hu.mem_nhds hy)
    have hyOne :
        ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞) (T% σ) y :=
      hyTop.of_le (by simp)
    exact hyOne.mdifferentiableAt (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  exact
    (leviCivitaConnectionOfMetric_homSection_contMDiffAt
      (I := I) e b g hxBase hσdiff hσAt).contMDiffWithinAt

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally ``Submission.DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally

omit [SigmaCompactSpace M] [T2Space M] in
theorem leviCivitaConnectionOfMetric_contMDiffCovariantDerivative
    (g : SmoothRiemannianMetric I M) :
    CovariantDerivative.ContMDiffCovariantDerivative
      (leviCivitaConnectionOfMetric (I := I) g) ∞ :=
  ⟨leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally (I := I) g
    isOpen_univ⟩

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivative with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivative"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivative ``Submission.DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivative

omit [SigmaCompactSpace M] [T2Space M] in
theorem leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally_one
    (g : SmoothRiemannianMetric I M) :
    CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (I := I) (E := E) (M := M)
      (leviCivitaConnectionOfMetric (I := I) g) (1 : WithTop ℕ∞) := by
  intro u hu
  refine ⟨?_⟩
  intro σ hσ x hx
  let e : _root_.Bundle.Trivialization E
      (TotalSpace.proj : _root_.Bundle.TotalSpace E (TangentSpace I : M → Type _) → M) :=
    _root_.FiberBundle.trivializationAt E (TangentSpace I : M → Type _) x
  let b := Module.finBasis Real E
  have hxBase : x ∈ e.baseSet := by
    simp [e]
  have hσAtTwo :
      ContMDiffAt I (I.prod 𝓘(Real, E)) ((1 : WithTop ℕ∞) + 1) (T% σ) x :=
    hσ.contMDiffAt (hu.mem_nhds hx)
  have hσAt :
      ContMDiffAt I (I.prod 𝓘(Real, E)) (2 : WithTop ℕ∞) (T% σ) x := by
    norm_num at hσAtTwo
    exact hσAtTwo
  have hσdiff : ∀ᶠ y in 𝓝 x, MDiffAt (T% σ) y := by
    filter_upwards [hu.mem_nhds hx] with y hy
    have hyTwo :
        ContMDiffAt I (I.prod 𝓘(Real, E)) ((1 : WithTop ℕ∞) + 1) (T% σ) y :=
      hσ.contMDiffAt (hu.mem_nhds hy)
    have hyOne :
        ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞) (T% σ) y :=
      hyTwo.of_le (by simp : (1 : WithTop ℕ∞) ≤ ((1 : WithTop ℕ∞) + 1))
    exact hyOne.mdifferentiableAt (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  exact
    (leviCivitaConnectionOfMetric_homSection_contMDiffAt_one
      (I := I) e b g hxBase hσdiff hσAt).contMDiffWithinAt

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally_one with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally_one"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally_one ``Submission.DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally_one
end DifferentialGeometry.Geometry.Connection
