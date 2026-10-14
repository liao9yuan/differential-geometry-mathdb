import Submission.DifferentialGeometry.Tensor.RSTensor.Functoriality.Pullback
import Submission.DifferentialGeometry.Geometry.Metric.Construction.TensorBumpExtension
import Submission.DifferentialGeometry.Tensor.RSTensor.Coordinates.Derivative

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Filter _root_.Set
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance bumpTimeC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bumpTimeC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bumpTimeC1 target :: scope.openDecls } }


theorem exists_tensor_bump_time_tower (U : TopologicalSpace.Opens M) (r : ℕ)
    (A : ℕ → ℝ → Tensor0SField (I := I) (M := U) (n := ∞) r)
    (χ : M → ℝ) (hχ : ContMDiff I 𝓘(ℝ) ∞ χ) (hsupp : tsupport χ ⊆ (U : Set M))
    (J : Set ℝ) (hA : ∀ q t, t ∈ J → ∀ x : U,
      HasDerivWithinAt (fun s => A q s x) (A (q + 1) t x) J t) :
    ∃ B : ℕ → ℝ → Tensor0SField (I := I) (M := M) (n := ∞) r,
      (∀ q t, ∀ x : M, ∀ hx : x ∈ U, ∀ v : Fin r → TangentSpace I x,
        B q t x v = χ x * A q t ⟨x, hx⟩ v) ∧
      (∀ q t, ∀ x : M, x ∉ U → B q t x = 0) ∧
      ∀ q t, t ∈ J → ∀ x : M, HasDerivWithinAt (fun s => B q s x) (B (q + 1) t x) J t := by
  classical
  choose B hB using fun q t => exists_tensor_bump_extension U r (A q t) χ hχ hsupp
  refine ⟨B, fun q t => (hB q t).1, fun q t => (hB q t).2, ?_⟩
  intro q t ht x
  let basis := Module.finBasis ℝ (TangentSpace I x)
  apply tensor0S_hasDerivWithinAt_of_components basis
  intro slots
  let v : Fin r → TangentSpace I x := fun k => basis (slots k)
  change HasDerivWithinAt (fun s => B q s x v) (B (q + 1) t x v) J t
  by_cases hx : x ∈ U
  · have hd := (tensor0SEvalCLM (I := I) (M := U) (x := ⟨x, hx⟩) v).hasFDerivAt.comp_hasDerivWithinAt
      t (hA q t ht ⟨x, hx⟩)
    have hv : HasDerivWithinAt (fun s => A q s ⟨x, hx⟩ v) (A (q + 1) t ⟨x, hx⟩ v) J t := hd
    have hχv := hv.const_mul (χ x)
    have hχv' := hχv.congr_deriv ((hB (q + 1) t).1 x hx v).symm
    exact hχv'.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s => (hB q s).1 x hx v) ((hB q t).1 x hx v)
  · have hvalue (j : ℕ) (s : ℝ) : B j s x v = 0 := by
      rw [(hB j s).2 x hx]
      rfl
    have hd := (hasDerivWithinAt_const t J (0 : ℝ)).congr_deriv (hvalue (q + 1) t).symm
    exact hd.congr_of_eventuallyEq (Filter.Eventually.of_forall (hvalue q)) (hvalue q t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_tensor_bump_time_tower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_tensor_bump_time_tower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_tensor_bump_time_tower ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_tensor_bump_time_tower

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
