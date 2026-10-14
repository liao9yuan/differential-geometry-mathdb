/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BoundaryBranchDescent

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u v

namespace NormalSingularSetTriangulation

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM : Set M}

theorem nonempty_branch_of_complexity_ne_zero (T : NormalSingularSetTriangulation D BdM)
    (h : T.complexity ≠ 0) : Nonempty T.Branch := by
  rw [← not_isEmpty_iff]
  intro hempty
  let _ : Finite T.Branch := T.finite_branch
  have hclosed : T.closedBranchCount = 0 :=
    Finite.card_eq_zero_iff.mpr (Subtype.isEmpty_of_false fun c _ => hempty.false c)
  have hboundary : T.boundaryBranchCount = 0 :=
    Finite.card_eq_zero_iff.mpr (Subtype.isEmpty_of_false fun c _ => hempty.false c)
  exact h (Nat.add_eq_zero_iff.mpr ⟨hclosed, hboundary⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.nonempty_branch_of_complexity_ne_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.nonempty_branch_of_complexity_ne_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.nonempty_branch_of_complexity_ne_zero ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.nonempty_branch_of_complexity_ne_zero

end NormalSingularSetTriangulation

namespace NormalSingularCellData

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM B : Set M}

theorem doublePointSet_eq_empty_of_complexity_eq_zero (hD : NormalSingularCellData D BdM B)
    (h : hD.singularSet.complexity = 0) : doublePointSet D D.domain = ∅ :=
  (doublePointSet_eq_empty_iff_injOn D D.domain).mpr (hD.complexity_eq_zero_iff.mp h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.doublePointSet_eq_empty_of_complexity_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.doublePointSet_eq_empty_of_complexity_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.doublePointSet_eq_empty_of_complexity_eq_zero ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.doublePointSet_eq_empty_of_complexity_eq_zero

theorem exists_complexity_eq_zero_of_descendingSurgery_of_motive
    (motive : ∀ D₀ : SingularTwoCell M, NormalSingularCellData D₀ BdM B → Prop)
    (step : ∀ (D₀ : SingularTwoCell M) (hD₀ : NormalSingularCellData D₀ BdM B),
      hD₀.singularSet.complexity ≠ 0 → motive D₀ hD₀ →
      ∃ S : hD₀.DescendingSurgery, motive S.cell S.normal)
    (hD : NormalSingularCellData D BdM B) (hmotive : motive D hD) :
    ∃ (D' : SingularTwoCell M) (hD' : NormalSingularCellData D' BdM B),
      hD'.singularSet.complexity = 0 ∧ D'.IsNonsingular ∧
      doublePointSet D' D'.domain = ∅ ∧ motive D' hD' := by
  have key : ∀ n : ℕ, ∀ (D₀ : SingularTwoCell M) (hD₀ : NormalSingularCellData D₀ BdM B),
      hD₀.singularSet.complexity = n → motive D₀ hD₀ →
      ∃ (D' : SingularTwoCell M) (hD' : NormalSingularCellData D' BdM B),
        hD'.singularSet.complexity = 0 ∧ D'.IsNonsingular ∧
        doublePointSet D' D'.domain = ∅ ∧ motive D' hD' := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n inductionHypothesis =>
      intro D₀ hD₀ hn hD₀motive
      by_cases hzero : hD₀.singularSet.complexity = 0
      · exact ⟨D₀, hD₀, hzero, hD₀.complexity_eq_zero_iff.mp hzero,
          hD₀.doublePointSet_eq_empty_of_complexity_eq_zero hzero, hD₀motive⟩
      · obtain ⟨S, hS⟩ := step D₀ hD₀ hzero hD₀motive
        refine inductionHypothesis S.normal.singularSet.complexity ?_ S.cell S.normal rfl hS
        rw [← hn]
        exact S.complexity_lt
  exact key hD.singularSet.complexity D hD rfl hmotive

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.exists_complexity_eq_zero_of_descendingSurgery_of_motive then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.exists_complexity_eq_zero_of_descendingSurgery_of_motive"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.exists_complexity_eq_zero_of_descendingSurgery_of_motive ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.exists_complexity_eq_zero_of_descendingSurgery_of_motive

theorem exists_complexity_eq_zero_of_descendingSurgery {X : Type v} [TopologicalSpace X]
    [PathConnectedSpace X] {x : X} {N : Subgroup (FundamentalGroup X x)} {ρ : X → M}
    (step : ∀ (D₀ : SingularTwoCell M) (hD₀ : NormalSingularCellData D₀ BdM B),
      hD₀.singularSet.complexity ≠ 0 →
      (∃ (e : loopCircle ≃ₜ frontier D₀.domain) (δ : freeLoop X),
        (∀ θ, ρ (δ θ) = D₀ (e θ)) ∧ ¬loopClassMeets δ x N) →
      ∃ (S : hD₀.DescendingSurgery) (e : loopCircle ≃ₜ frontier S.cell.domain)
        (δ : freeLoop X), (∀ θ, ρ (δ θ) = S.cell (e θ)) ∧ ¬loopClassMeets δ x N)
    (hD : NormalSingularCellData D BdM B)
    (hloop : ∃ (e : loopCircle ≃ₜ frontier D.domain) (δ : freeLoop X),
      (∀ θ, ρ (δ θ) = D (e θ)) ∧ ¬loopClassMeets δ x N) :
    ∃ (D' : SingularTwoCell M) (hD' : NormalSingularCellData D' BdM B),
      hD'.singularSet.complexity = 0 ∧
      ∃ (e : loopCircle ≃ₜ frontier D'.domain) (δ : freeLoop X),
        (∀ θ, ρ (δ θ) = D' (e θ)) ∧ ¬loopClassMeets δ x N := by
  obtain ⟨D', hD', hzero, -, -, hD'loop⟩ :=
    exists_complexity_eq_zero_of_descendingSurgery_of_motive
      (fun D₀ _ => ∃ (e : loopCircle ≃ₜ frontier D₀.domain) (δ : freeLoop X),
        (∀ θ, ρ (δ θ) = D₀ (e θ)) ∧ ¬loopClassMeets δ x N)
      (fun D₀ hD₀ hne hD₀loop => by
        obtain ⟨S, e, δ, hδ, hδN⟩ := step D₀ hD₀ hne hD₀loop
        exact ⟨S, e, δ, hδ, hδN⟩)
      hD hloop
  exact ⟨D', hD', hzero, hD'loop⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.exists_complexity_eq_zero_of_descendingSurgery then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.exists_complexity_eq_zero_of_descendingSurgery"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.exists_complexity_eq_zero_of_descendingSurgery ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.exists_complexity_eq_zero_of_descendingSurgery

theorem exists_isNonsingular_of_descendingSurgery {X : Type v} [TopologicalSpace X]
    [PathConnectedSpace X] {x : X} {N : Subgroup (FundamentalGroup X x)} {ρ : X → M}
    (step : ∀ (D₀ : SingularTwoCell M) (hD₀ : NormalSingularCellData D₀ BdM B),
      hD₀.singularSet.complexity ≠ 0 →
      (∃ (e : loopCircle ≃ₜ frontier D₀.domain) (δ : freeLoop X),
        (∀ θ, ρ (δ θ) = D₀ (e θ)) ∧ ¬loopClassMeets δ x N) →
      ∃ (S : hD₀.DescendingSurgery) (e : loopCircle ≃ₜ frontier S.cell.domain)
        (δ : freeLoop X), (∀ θ, ρ (δ θ) = S.cell (e θ)) ∧ ¬loopClassMeets δ x N)
    (hD : NormalSingularCellData D BdM B)
    (hloop : ∃ (e : loopCircle ≃ₜ frontier D.domain) (δ : freeLoop X),
      (∀ θ, ρ (δ θ) = D (e θ)) ∧ ¬loopClassMeets δ x N) :
    ∃ (D' : SingularTwoCell M) (hD' : NormalSingularCellData D' BdM B),
      hD'.singularSet.complexity = 0 ∧ D'.IsNonsingular ∧
      doublePointSet D' D'.domain = ∅ ∧
      ∃ (e : loopCircle ≃ₜ frontier D'.domain) (δ : freeLoop X),
        (∀ θ, ρ (δ θ) = D' (e θ)) ∧ ¬loopClassMeets δ x N := by
  obtain ⟨D', hD', hzero, hD'loop⟩ :=
    exists_complexity_eq_zero_of_descendingSurgery step hD hloop
  exact ⟨D', hD', hzero, hD'.complexity_eq_zero_iff.mp hzero,
    hD'.doublePointSet_eq_empty_of_complexity_eq_zero hzero, hD'loop⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.exists_isNonsingular_of_descendingSurgery then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.exists_isNonsingular_of_descendingSurgery"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.exists_isNonsingular_of_descendingSurgery ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.exists_isNonsingular_of_descendingSurgery

end NormalSingularCellData

end DifferentialGeometry.Topology.PiecewiseLinear
