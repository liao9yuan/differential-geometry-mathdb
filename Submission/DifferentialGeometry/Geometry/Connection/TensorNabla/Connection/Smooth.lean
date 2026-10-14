import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.Model.Tensor0S
import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.Model.TensorRS
import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.InducedConnection
import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.Model.Smoothness
import Submission.DifferentialGeometry.Bundle.Section
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace CovariantDerivative
open _root_.CovariantDerivative

open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.ContDiff

open _root_.CovariantDerivative in
def ContMDiffCovariantDerivativeLocally
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (k : WithTop ℕ∞) : Prop :=
  ∀ ⦃u : Set M⦄, IsOpen u → ContMDiffCovariantDerivativeOn E k cov.toFun u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.ContMDiffCovariantDerivativeLocally then
    throwError "Refusing to shadow existing declaration CovariantDerivative.ContMDiffCovariantDerivativeLocally"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.ContMDiffCovariantDerivativeLocally ``Submission.CovariantDerivative.ContMDiffCovariantDerivativeLocally

open _root_.CovariantDerivative _root_.CovariantDerivative.ContMDiffCovariantDerivative in
theorem ContMDiffCovariantDerivative.contMDiff_apply
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [VectorBundle 𝕜 E (TangentSpace I : M → Type _)]
    {n : WithTop ℕ∞}
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : _root_.CovariantDerivative.ContMDiffCovariantDerivative cov n)
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (Y : ContMDiffSection I E (n + 1) (TangentSpace I : M → Type _)) :
    ContMDiff I (I.prod 𝓘(𝕜, E)) n
      (fun p : M =>
        (⟨p, (cov (fun q : M => Y q) p) (X p)⟩ :
          TotalSpace E (TangentSpace I : M → Type _))) := by
  have hY :
      ContMDiffOn I (I.prod 𝓘(𝕜, E)) (n + 1)
        (fun p : M =>
          (⟨p, Y p⟩ : _root_.Bundle.TotalSpace E (TangentSpace I : M → Type _))) Set.univ :=
    Y.contMDiff.contMDiffOn
  have hcovY :
      ContMDiffOn I (I.prod 𝓘(𝕜, E →L[𝕜] E)) n
        (fun p : M =>
          (⟨p, cov (fun q : M => Y q) p⟩ :
            _root_.Bundle.TotalSpace (E →L[𝕜] E)
              (fun p : M => TangentSpace I p →L[𝕜] TangentSpace I p))) Set.univ :=
    hcov.contMDiff.contMDiff hY
  have hX :
      ContMDiffOn I (I.prod 𝓘(𝕜, E)) n
        (fun p : M =>
          (⟨p, X p⟩ : _root_.Bundle.TotalSpace E (TangentSpace I : M → Type _))) Set.univ :=
    X.contMDiff.contMDiffOn
  rw [← contMDiffOn_univ]
  simpa using hcovY.clm_bundle_apply hX

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.CovariantDerivative.ContMDiffCovariantDerivative
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.ContMDiffCovariantDerivative.contMDiff_apply then
    throwError "Refusing to shadow existing declaration CovariantDerivative.ContMDiffCovariantDerivative.contMDiff_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.ContMDiffCovariantDerivative.contMDiff_apply ``Submission.CovariantDerivative.ContMDiffCovariantDerivative.contMDiff_apply

end CovariantDerivative
