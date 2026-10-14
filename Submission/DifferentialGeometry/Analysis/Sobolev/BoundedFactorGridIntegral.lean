import Submission.DifferentialGeometry.Analysis.Sobolev.BoundedFactorProductGrid
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory
open scoped _root_.BigOperators

namespace DifferentialGeometry
namespace Combinatorics

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [CompactSpace X] {μ : Measure X} [IsFiniteMeasure μ]

omit [OpensMeasurableSpace X] [CompactSpace X] in
private theorem finOnCpt (μ : _root_.MeasureTheory.Measure X) [_root_.MeasureTheory.IsFiniteMeasure μ] :
    IsFiniteMeasureOnCompacts μ :=
  ⟨fun K _ => MeasureTheory.measure_lt_top μ K⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Combinatorics.finOnCpt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Combinatorics.finOnCpt target :: scope.openDecls } }

theorem boundedFactorCell_integrable (b : X → ℕ → ℝ) (hcont : ∀ l : ℕ, Continuous fun x => b x l)
    (n : ℕ) (e : Fin n → ℕ) :
    Integrable (fun x => ∏ m : Fin n, b x (e m)) μ := by
  have := finOnCpt (X := X) μ
  exact (continuous_finsetProd _ (fun m _ => hcont (e m))).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Combinatorics.boundedFactorCell_integrable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Combinatorics.boundedFactorCell_integrable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Combinatorics.boundedFactorCell_integrable ``Submission.DifferentialGeometry.Combinatorics.boundedFactorCell_integrable

omit [MeasurableSpace X] [OpensMeasurableSpace X] [CompactSpace X] in
theorem boundedFactorGrid_continuous (b : X → ℕ → ℝ) (hcont : ∀ l : ℕ, Continuous fun x => b x l)
    (K k : ℕ) :
    Continuous fun x => boundedFactorGrid (b x) K k := by
  simp only [boundedFactorGrid]
  refine continuous_finsetSum _ (fun n _ => ?_)
  refine continuous_finsetSum _ (fun e _ => ?_)
  exact continuous_finsetProd _ (fun m _ => hcont (e m))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Combinatorics.boundedFactorGrid_continuous then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Combinatorics.boundedFactorGrid_continuous"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Combinatorics.boundedFactorGrid_continuous ``Submission.DifferentialGeometry.Combinatorics.boundedFactorGrid_continuous

theorem boundedFactorGrid_integrable (b : X → ℕ → ℝ) (hcont : ∀ l : ℕ, Continuous fun x => b x l)
    (K k : ℕ) :
    Integrable (fun x => boundedFactorGrid (b x) K k) μ := by
  have := finOnCpt (X := X) μ
  exact (boundedFactorGrid_continuous b hcont K k).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Combinatorics.boundedFactorGrid_integrable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Combinatorics.boundedFactorGrid_integrable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Combinatorics.boundedFactorGrid_integrable ``Submission.DifferentialGeometry.Combinatorics.boundedFactorGrid_integrable

theorem integral_boundedFactorGrid (b : X → ℕ → ℝ) (hcont : ∀ l : ℕ, Continuous fun x => b x l)
    (K k : ℕ) :
    (∫ x, boundedFactorGrid (b x) K k ∂μ) =
      ∑ n ∈ Finset.range (k + 1),
        ∑ e ∈ (Finset.Nat.antidiagonalTuple n k).filter (fun e => ∀ m, e m ≤ K),
          ∫ x, ∏ m : Fin n, b x (e m) ∂μ := by
  have h1 : (fun x => boundedFactorGrid (b x) K k) =
      (fun x => ∑ n ∈ Finset.range (k + 1),
        ∑ e ∈ (Finset.Nat.antidiagonalTuple n k).filter (fun e => ∀ m, e m ≤ K),
          ∏ m : Fin n, b x (e m)) := rfl
  rw [h1, MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro n _
    rw [MeasureTheory.integral_finsetSum]
    intro e _; exact boundedFactorCell_integrable b hcont n e
  · intro n _
    apply MeasureTheory.integrable_finsetSum
    intro e _; exact boundedFactorCell_integrable b hcont n e

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Combinatorics.integral_boundedFactorGrid then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Combinatorics.integral_boundedFactorGrid"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Combinatorics.integral_boundedFactorGrid ``Submission.DifferentialGeometry.Combinatorics.integral_boundedFactorGrid

end Combinatorics
end DifferentialGeometry

end
