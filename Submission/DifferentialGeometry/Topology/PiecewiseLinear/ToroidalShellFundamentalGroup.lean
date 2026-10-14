/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.FundamentalGroup.Torus
import Submission.DifferentialGeometry.Topology.FundamentalGroup.Retraction
import Submission.DifferentialGeometry.Topology.Homotopy.ConvexProduct
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.ToroidalShell

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [TopologicalSpace E] {Y T₀ T₁ : Set E}

private theorem fundamentalGroup_map_slice_bijective
    {M : Type*} [TopologicalSpace M] (φ : (M × unitInterval) ≃ₜ Y)
    (t : unitInterval) {T : Set E}
    (hT : T = Subtype.val '' (φ '' {p | (p.2 : ℝ) = t})) (hTY : T ⊆ Y) (x : T) :
    Function.Bijective (FundamentalGroup.map
      (⟨Set.inclusion hTY, continuous_inclusion hTY⟩ : C(T, Y)) x) := by
  let f : M → E := fun p => (φ (p, t) : E)
  have hf : _root_.Topology.IsEmbedding f :=
    _root_.Topology.IsEmbedding.subtypeVal.comp (φ.isEmbedding.comp (isEmbedding_prodMkLeft t))
  have hrange : Set.range f = T := by
    rw [hT]
    ext z
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨φ (p, t), ⟨(p, t), rfl, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨p, hp, rfl⟩, rfl⟩
      have ht : p.2 = t := Subtype.ext hp
      exact ⟨p.1, by simp only [f, ← ht]⟩
  let eT := hf.toHomeomorph.trans (Homeomorph.setCongr hrange)
  let e := (φ.symm.toHomotopyEquiv.trans
    (DifferentialGeometry.HomotopyEquiv.productConvex M (convex_Icc (0 : ℝ) 1) t)).trans
    eT.toHomotopyEquiv
  apply bijective_fundamentalGroup_map_of_homotopyEquiv_leftInverse e
  intro z
  apply Subtype.ext
  have hz : (z : E) ∈ Subtype.val '' (φ '' {p | (p.2 : ℝ) = t}) := by
    simpa only [← hT] using z.property
  obtain ⟨y, ⟨p, hp, rfl⟩, hpz⟩ := hz
  have hiz : Set.inclusion hTY z = φ p := Subtype.ext hpz.symm
  change (φ ((φ.symm (Set.inclusion hTY z)).1, t) : E) = z
  rw [hiz, φ.symm_apply_apply]
  have ht : p.2 = t := Subtype.ext hp
  simpa only [← ht, Prod.mk.eta] using hpz

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.fundamentalGroup_map_slice_bijective
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.fundamentalGroup_map_slice_bijective target :: scope.openDecls } }

theorem IsToroidalShell.fundamentalGroup_map_left_bijective
    (hY : IsToroidalShell Y T₀ T₁) (x : T₀) :
    Function.Bijective (FundamentalGroup.map
      (⟨Set.inclusion hY.left_subset, continuous_inclusion hY.left_subset⟩ : C(T₀, Y)) x) := by
  obtain ⟨φ, h₀, _⟩ := hY
  exact fundamentalGroup_map_slice_bijective φ 0 h₀ _ x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.fundamentalGroup_map_left_bijective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.fundamentalGroup_map_left_bijective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.fundamentalGroup_map_left_bijective ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.fundamentalGroup_map_left_bijective

theorem IsToroidalShell.fundamentalGroup_map_right_bijective
    (hY : IsToroidalShell Y T₀ T₁) (x : T₁) :
    Function.Bijective (FundamentalGroup.map
      (⟨Set.inclusion hY.right_subset, continuous_inclusion hY.right_subset⟩ : C(T₁, Y)) x) := by
  obtain ⟨φ, _, h₁⟩ := hY
  exact fundamentalGroup_map_slice_bijective φ 1 h₁ _ x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.fundamentalGroup_map_right_bijective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.fundamentalGroup_map_right_bijective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.fundamentalGroup_map_right_bijective ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.fundamentalGroup_map_right_bijective

theorem IsToroidalShell.nonempty_fundamentalGroup_mulEquiv_intProd
    (hY : IsToroidalShell Y T₀ T₁) (x : Y) :
    Nonempty (FundamentalGroup Y x ≃* Multiplicative ℤ × Multiplicative ℤ) := by
  obtain ⟨φ, _, _⟩ := hY
  let p := φ.symm x
  let e := φ.symm.toHomotopyEquiv.trans
    (DifferentialGeometry.HomotopyEquiv.productConvex _ (convex_Icc (0 : ℝ) 1) p.2)
  exact ⟨(fundamentalGroupMulEquivOfHomotopyEquiv e x p.1 rfl).trans
    (fundamentalGroupTorusEquivIntProd p.1)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.nonempty_fundamentalGroup_mulEquiv_intProd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.nonempty_fundamentalGroup_mulEquiv_intProd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.nonempty_fundamentalGroup_mulEquiv_intProd ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.nonempty_fundamentalGroup_mulEquiv_intProd

theorem IsToroidalShell.isMulCommutative_fundamentalGroup
    (hY : IsToroidalShell Y T₀ T₁) (x : Y) : IsMulCommutative (FundamentalGroup Y x) := by
  obtain ⟨e⟩ := hY.nonempty_fundamentalGroup_mulEquiv_intProd x
  apply isMulCommutative_iff.mpr
  intro a b
  apply e.injective
  simp only [map_mul, mul_comm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.isMulCommutative_fundamentalGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.isMulCommutative_fundamentalGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.isMulCommutative_fundamentalGroup ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.isMulCommutative_fundamentalGroup

theorem IsToroidalShell.nonempty_fundamentalGroup_interior_mulEquiv_intProd
    {Y T₀ T₁ : Set (EuclideanSpace ℝ (Fin 3))} (hY : IsToroidalShell Y T₀ T₁)
    (x : interior Y) :
    Nonempty (FundamentalGroup (interior Y) x ≃* Multiplicative ℤ × Multiplicative ℤ) := by
  obtain ⟨φ⟩ := hY.nonempty_homeomorph_interior
  let p := φ.symm x
  let e := φ.symm.toHomotopyEquiv.trans
    (DifferentialGeometry.HomotopyEquiv.productConvex _ (convex_Ioo (0 : ℝ) 1) p.2)
  exact ⟨(fundamentalGroupMulEquivOfHomotopyEquiv e x p.1 rfl).trans
    (fundamentalGroupTorusEquivIntProd p.1)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.nonempty_fundamentalGroup_interior_mulEquiv_intProd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.nonempty_fundamentalGroup_interior_mulEquiv_intProd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.nonempty_fundamentalGroup_interior_mulEquiv_intProd ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.nonempty_fundamentalGroup_interior_mulEquiv_intProd

theorem IsToroidalShell.isMulCommutative_fundamentalGroup_interior
    {Y T₀ T₁ : Set (EuclideanSpace ℝ (Fin 3))} (hY : IsToroidalShell Y T₀ T₁)
    (x : interior Y) : IsMulCommutative (FundamentalGroup (interior Y) x) := by
  obtain ⟨e⟩ := hY.nonempty_fundamentalGroup_interior_mulEquiv_intProd x
  apply isMulCommutative_iff.mpr
  intro a b
  apply e.injective
  simp only [map_mul, mul_comm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.isMulCommutative_fundamentalGroup_interior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.isMulCommutative_fundamentalGroup_interior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.isMulCommutative_fundamentalGroup_interior ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.isMulCommutative_fundamentalGroup_interior

end DifferentialGeometry.Topology.PiecewiseLinear
