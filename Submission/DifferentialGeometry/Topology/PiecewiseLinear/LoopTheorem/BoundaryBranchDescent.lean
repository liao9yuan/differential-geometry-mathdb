/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BoundaryWordFourArcs
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossSeamResolution

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u v w

namespace NormalSingularCellData

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM B : Set M}

structure DescendingSurgery (hD : NormalSingularCellData D BdM B) where
  cell : SingularTwoCell M
  normal : NormalSingularCellData cell BdM B
  complexity_lt : normal.singularSet.complexity < hD.singularSet.complexity

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.DescendingSurgery then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.DescendingSurgery"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.DescendingSurgery ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.DescendingSurgery

namespace DescendingSurgery

def ofBranchEquiv (hD : NormalSingularCellData D BdM B) {c : hD.singularSet.Branch}
    {G : SingularTwoCell M} (hG : NormalSingularCellData G BdM B)
    (e : hG.singularSet.Branch ≃ {b : hD.singularSet.Branch // b ≠ c}) :
    hD.DescendingSurgery where
  cell := G
  normal := hG
  complexity_lt := hD.singularSet.complexity_lt_of_branchEquiv_compl hG.singularSet e

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.DescendingSurgery.ofBranchEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.DescendingSurgery.ofBranchEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.DescendingSurgery.ofBranchEquiv ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.DescendingSurgery.ofBranchEquiv

theorem ofBranchEquiv_cell (hD : NormalSingularCellData D BdM B) {c : hD.singularSet.Branch}
    {G : SingularTwoCell M} (hG : NormalSingularCellData G BdM B)
    (e : hG.singularSet.Branch ≃ {b : hD.singularSet.Branch // b ≠ c}) :
    (ofBranchEquiv hD hG e).cell = G :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.DescendingSurgery.ofBranchEquiv_cell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.DescendingSurgery.ofBranchEquiv_cell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.DescendingSurgery.ofBranchEquiv_cell ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.DescendingSurgery.ofBranchEquiv_cell

theorem ofBranchEquiv_normal (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} {G : SingularTwoCell M}
    (hG : NormalSingularCellData G BdM B)
    (e : hG.singularSet.Branch ≃ {b : hD.singularSet.Branch // b ≠ c}) :
    (ofBranchEquiv hD hG e).normal = hG :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.DescendingSurgery.ofBranchEquiv_normal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.DescendingSurgery.ofBranchEquiv_normal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.DescendingSurgery.ofBranchEquiv_normal ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.DescendingSurgery.ofBranchEquiv_normal

end DescendingSurgery

end NormalSingularCellData

namespace CrossSeamResolutionData

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM B U : Set M} {hD : NormalSingularCellData D BdM B}
  {c : hD.singularSet.Branch}

def toDescendingSurgery (R : CrossSeamResolutionData hD c U) : hD.DescendingSurgery :=
  NormalSingularCellData.DescendingSurgery.ofBranchEquiv hD R.normal R.branchEquiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamResolutionData.toDescendingSurgery then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamResolutionData.toDescendingSurgery"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamResolutionData.toDescendingSurgery ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamResolutionData.toDescendingSurgery

theorem toDescendingSurgery_cell (R : CrossSeamResolutionData hD c U) :
    R.toDescendingSurgery.cell = R.cell :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamResolutionData.toDescendingSurgery_cell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamResolutionData.toDescendingSurgery_cell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamResolutionData.toDescendingSurgery_cell ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamResolutionData.toDescendingSurgery_cell

theorem toDescendingSurgery_spec (R : CrossSeamResolutionData hD c U) :
    doublePointSet R.toDescendingSurgery.cell R.toDescendingSurgery.cell.domain =
        doublePointSet D D.domain \ hD.singularSet.branchCarrier c ∧
      R.toDescendingSurgery.cell '' R.toDescendingSurgery.cell.domain ⊆ D '' D.domain ∪ U :=
  ⟨R.doublePointSet_eq, R.image_subset⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamResolutionData.toDescendingSurgery_spec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamResolutionData.toDescendingSurgery_spec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamResolutionData.toDescendingSurgery_spec ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamResolutionData.toDescendingSurgery_spec

end CrossSeamResolutionData

namespace NormalSingularCellData

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM B : Set M}

theorem exists_boundary_surgery_candidate_of_boundaryBranch [T2Space M]
    (hD : NormalSingularCellData D BdM B) {c : hD.singularSet.Branch}
    (hc : hD.singularSet.IsBoundaryBranch c) :
    ∃ G : SingularTwoCell M,
      Nonempty (NormalSingularCellData G BdM B) ∧
        doublePointSet G G.domain ⊆ doublePointSet D D.domain ∧
        Disjoint (doublePointSet G G.domain) (hD.singularSet.branchCarrier c) ∧
        G '' G.domain ⊆ D '' D.domain ∧
        ∃ (e : loopCircle ≃ₜ frontier G.domain) (y z : M) (α : Path y z) (ω : Path z y),
          ∀ θ, G (e θ) = pathToCircle (α.trans ω) θ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, G, -,
    -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, himage, -, -, -, -, -, -,
    hsub, hdisjoint, -, hG,
    y, z, α, ω, e, -, -, hparam, -⟩ :=
    hD.exists_boundary_surgery_cell_of_boundaryBranch hc
  exact ⟨G, hG, hsub, hdisjoint, himage, e, y, z, α, ω, hparam⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.exists_boundary_surgery_candidate_of_boundaryBranch then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.exists_boundary_surgery_candidate_of_boundaryBranch"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.exists_boundary_surgery_candidate_of_boundaryBranch ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.exists_boundary_surgery_candidate_of_boundaryBranch

theorem exists_descendingSurgery_of_not_loopClassMeets_or
    {hD : NormalSingularCellData D BdM B} {X : Type v} [TopologicalSpace X]
    [PathConnectedSpace X] {x : X} {N : Subgroup (FundamentalGroup X x)} {ρ : X → M}
    {S₁ S₂ : hD.DescendingSurgery} {δ₁ δ₂ : freeLoop X}
    (e₁ : loopCircle ≃ₜ frontier S₁.cell.domain)
    (e₂ : loopCircle ≃ₜ frontier S₂.cell.domain)
    (h₁ : ∀ θ, ρ (δ₁ θ) = S₁.cell (e₁ θ)) (h₂ : ∀ θ, ρ (δ₂ θ) = S₂.cell (e₂ θ))
    (hdichotomy : ¬loopClassMeets δ₁ x N ∨ ¬loopClassMeets δ₂ x N) :
    ∃ (S : hD.DescendingSurgery) (e : loopCircle ≃ₜ frontier S.cell.domain) (δ : freeLoop X),
      (∀ θ, ρ (δ θ) = S.cell (e θ)) ∧ ¬loopClassMeets δ x N := by
  rcases hdichotomy with h | h
  · exact ⟨S₁, e₁, δ₁, h₁, h⟩
  · exact ⟨S₂, e₂, δ₂, h₂, h⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.exists_descendingSurgery_of_not_loopClassMeets_or then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.exists_descendingSurgery_of_not_loopClassMeets_or"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.exists_descendingSurgery_of_not_loopClassMeets_or ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.exists_descendingSurgery_of_not_loopClassMeets_or

theorem exists_descendingSurgery_not_loopClassMeets_reversing
    {U : Set M} {hD : NormalSingularCellData D BdM B} {c : hD.singularSet.Branch}
    {Gd : SingularTwoCell M} (hGd : NormalSingularCellData Gd BdM B)
    (ebranch : hGd.singularSet.Branch ≃ {b : hD.singularSet.Branch // b ≠ c})
    (R : CrossSeamResolutionData hD c U)
    {Q : Type w} [TopologicalSpace Q] {p' q' u' v' : Q}
    (σ₀ : Path p' q') (τ₀ : Path q' u') (υ₀ : Path u' v') (φ₀ : Path v' p')
    (ev : loopCircle → Q)
    (hev : ∀ θ, ev θ = pathToCircle (σ₀.trans (τ₀.trans (υ₀.trans φ₀))) θ)
    {X : Type v} [TopologicalSpace X] [PathConnectedSpace X] {f : Q → X} {x a b : X}
    {σ υ : Path a b} {τ φ : Path b a}
    (hσ : ∀ t, σ t = f (σ₀ t)) (hτ : ∀ t, τ t = f (τ₀ t)) (hυ : ∀ t, υ t = f (υ₀ t))
    (hφ : ∀ t, φ t = f (φ₀ t)) (γ : freeLoop X) (hγ : ∀ θ, γ θ = f (ev θ))
    {N : Subgroup (FundamentalGroup X x)} [N.Normal] (hγN : ¬loopClassMeets γ x N)
    {ρ : X → M} (edirect : loopCircle ≃ₜ frontier Gd.domain)
    (hdirect : ∀ θ, ρ (pathToCircle (σ.trans υ.symm) θ) = Gd (edirect θ))
    (ecross : loopCircle ≃ₜ frontier R.cell.domain)
    (hcross : ∀ θ, ρ (pathToCircle (σ.trans (φ.trans (υ.trans τ))) θ) = R.cell (ecross θ)) :
    ∃ (S : hD.DescendingSurgery) (e : loopCircle ≃ₜ frontier S.cell.domain) (δ : freeLoop X),
      (∀ θ, ρ (δ θ) = S.cell (e θ)) ∧ ¬loopClassMeets δ x N := by
  refine exists_descendingSurgery_of_not_loopClassMeets_or
    (S₁ := DescendingSurgery.ofBranchEquiv hD hGd ebranch) (S₂ := R.toDescendingSurgery)
    (δ₁ := pathToCircle (σ.trans υ.symm))
    (δ₂ := pathToCircle (σ.trans (φ.trans (υ.trans τ))))
    edirect ecross hdirect hcross ?_
  exact not_loopClassMeets_or_not_loopClassMeets_of_four_boundary_arcs_reversing σ₀ τ₀ υ₀ φ₀
    ev hev (PathConnectedSpace.somePath x a) (PathConnectedSpace.somePath a b) hσ hτ hυ hφ γ hγ
    N hγN

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.exists_descendingSurgery_not_loopClassMeets_reversing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.exists_descendingSurgery_not_loopClassMeets_reversing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.exists_descendingSurgery_not_loopClassMeets_reversing ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.exists_descendingSurgery_not_loopClassMeets_reversing

theorem exists_descendingSurgery_not_loopClassMeets_preserving
    {U : Set M} {hD : NormalSingularCellData D BdM B} {c : hD.singularSet.Branch}
    {Gd : SingularTwoCell M} (hGd : NormalSingularCellData Gd BdM B)
    (ebranch : hGd.singularSet.Branch ≃ {b : hD.singularSet.Branch // b ≠ c})
    (R : CrossSeamResolutionData hD c U)
    {Q : Type w} [TopologicalSpace Q] {p' q' u' v' : Q}
    (σ₀ : Path p' q') (τ₀ : Path q' u') (υ₀ : Path u' v') (φ₀ : Path v' p')
    (ev : loopCircle → Q)
    (hev : ∀ θ, ev θ = pathToCircle (σ₀.trans (τ₀.trans (υ₀.trans φ₀))) θ)
    {X : Type v} [TopologicalSpace X] [PathConnectedSpace X] {f : Q → X} {x a b : X}
    {σ : Path a b} {τ : Path b b} {υ : Path b a} {φ : Path a a}
    (hσ : ∀ t, σ t = f (σ₀ t)) (hτ : ∀ t, τ t = f (τ₀ t)) (hυ : ∀ t, υ t = f (υ₀ t))
    (hφ : ∀ t, φ t = f (φ₀ t)) (γ : freeLoop X) (hγ : ∀ θ, γ θ = f (ev θ))
    {N : Subgroup (FundamentalGroup X x)} [N.Normal] (hγN : ¬loopClassMeets γ x N)
    {ρ : X → M} (edirect : loopCircle ≃ₜ frontier Gd.domain)
    (hdirect : ∀ θ, ρ (pathToCircle (σ.trans υ) θ) = Gd (edirect θ))
    (ecross : loopCircle ≃ₜ frontier R.cell.domain)
    (hcross : ∀ θ,
      ρ (pathToCircle (σ.trans (τ.symm.trans (υ.trans φ.symm))) θ) = R.cell (ecross θ)) :
    ∃ (S : hD.DescendingSurgery) (e : loopCircle ≃ₜ frontier S.cell.domain) (δ : freeLoop X),
      (∀ θ, ρ (δ θ) = S.cell (e θ)) ∧ ¬loopClassMeets δ x N := by
  refine exists_descendingSurgery_of_not_loopClassMeets_or
    (S₁ := DescendingSurgery.ofBranchEquiv hD hGd ebranch) (S₂ := R.toDescendingSurgery)
    (δ₁ := pathToCircle (σ.trans υ))
    (δ₂ := pathToCircle (σ.trans (τ.symm.trans (υ.trans φ.symm))))
    edirect ecross hdirect hcross ?_
  exact not_loopClassMeets_or_not_loopClassMeets_of_four_boundary_arcs_preserving σ₀ τ₀ υ₀ φ₀
    ev hev (PathConnectedSpace.somePath x a) (PathConnectedSpace.somePath a b) hσ hτ hυ hφ γ hγ
    N hγN

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.exists_descendingSurgery_not_loopClassMeets_preserving then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.exists_descendingSurgery_not_loopClassMeets_preserving"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.exists_descendingSurgery_not_loopClassMeets_preserving ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.exists_descendingSurgery_not_loopClassMeets_preserving

end NormalSingularCellData

end DifferentialGeometry.Topology.PiecewiseLinear
