import Submission.DifferentialGeometry.Tensor.RSTensor.Coordinates.CoordinateBasis
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance timeFieldC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.timeFieldC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.timeFieldC1 target :: scope.openDecls } }

theorem tensor0S_hasDerivWithinAt_of_components {n r : ℕ} {x : M}
    (basis : Module.Basis (Fin n) ℝ (TangentSpace I x))
    {A : ℝ → Tensor0SSpace r I x} {A' : Tensor0SSpace r I x} {J : Set ℝ} {t : ℝ}
    (hA : ∀ slots, HasDerivWithinAt (fun s => component0S (I := I) basis (A s) slots)
      (component0S (I := I) basis A' slots) J t) : HasDerivWithinAt A A' J t := by
  have hsum : HasDerivWithinAt
      (fun s => ∑ slots, component0S (I := I) basis (A s) slots • tensor0SBasis (I := I) basis r slots)
      (∑ slots, component0S (I := I) basis A' slots • tensor0SBasis (I := I) basis r slots) J t :=
    HasDerivWithinAt.fun_sum fun slots _ => (hA slots).smul_const (tensor0SBasis (I := I) basis r slots)
  simpa only [← tensor0SBasis_repr, Module.Basis.sum_repr] using hsum

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tensor0S_hasDerivWithinAt_of_components then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tensor0S_hasDerivWithinAt_of_components"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tensor0S_hasDerivWithinAt_of_components ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tensor0S_hasDerivWithinAt_of_components

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
