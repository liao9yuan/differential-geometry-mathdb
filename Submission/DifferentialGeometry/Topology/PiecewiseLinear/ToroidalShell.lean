/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.Manifold.CylinderImage
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.MoiseChain
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SeparatingSurface
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Geometry.Manifold.Instances.Sphere

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "TorusModel" =>
  (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ×
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)

private instance connectedSpaceCircle :
    ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
  isConnected_iff_connectedSpace.mp (isConnected_sphere
    (by rw [← Module.finrank_eq_rank']; norm_num) 0 zero_le_one)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.connectedSpaceCircle
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.connectedSpaceCircle target :: scope.openDecls } }

private noncomputable instance torusProductChartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin 3)) (TorusModel × ℝ) := by
  let H := (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × ℝ
  let e : H ≃L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [H, Module.finrank_prod])
  let _ : ChartedSpace H (TorusModel × ℝ) := inferInstanceAs
    (ChartedSpace (ModelProd (ModelProd (EuclideanSpace ℝ (Fin 1))
      (EuclideanSpace ℝ (Fin 1))) ℝ) (TorusModel × ℝ))
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 3)) H := e.symm.toHomeomorph.chartedSpace
  exact ChartedSpace.comp (EuclideanSpace ℝ (Fin 3)) H (TorusModel × ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.torusProductChartedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.torusProductChartedSpace target :: scope.openDecls } }

variable {E : Type*} [TopologicalSpace E] {X B₀ B₁ : Set E}

private theorem image_toroidal_shell_slice
    (φ : (TorusModel × unitInterval) ≃ₜ X) (t : unitInterval) :
    Subtype.val '' (φ '' {p | (p.2 : ℝ) = t}) =
      range (fun s : TorusModel => (φ (s, t) : E)) := by
  ext x
  constructor
  · rintro ⟨y, ⟨⟨s, u⟩, hu, rfl⟩, rfl⟩
    have hut : u = t := Subtype.ext hu
    subst u
    exact ⟨s, rfl⟩
  · rintro ⟨s, rfl⟩
    exact ⟨φ (s, t), ⟨(s, t), rfl, rfl⟩, rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.image_toroidal_shell_slice
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.image_toroidal_shell_slice target :: scope.openDecls } }

theorem IsToroidalShell.isCompact (h : IsToroidalShell X B₀ B₁) : IsCompact X := by
  obtain ⟨φ, -, -⟩ := h
  let _ : CompactSpace X := φ.compactSpace
  exact isCompact_iff_compactSpace.mpr inferInstance

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.isCompact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.isCompact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.isCompact ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.isCompact

theorem IsToroidalShell.locallyPathConnectedSpace (h : IsToroidalShell X B₀ B₁) :
    LocallyPathConnectedSpace X := by
  obtain ⟨φ, _, _⟩ := h
  let _ : LocallyPathConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 1)) _
  let _ : LocallyPathConnectedSpace unitInterval := (convex_Icc (0 : ℝ) 1).locallyPathConnectedSpace
  exact φ.symm.isOpenEmbedding.locallyPathConnectedSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.locallyPathConnectedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.locallyPathConnectedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.locallyPathConnectedSpace ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.locallyPathConnectedSpace

theorem IsToroidalShell.isConnected (h : IsToroidalShell X B₀ B₁) : IsConnected X := by
  obtain ⟨φ, -, -⟩ := h
  have hrange : _root_.Set.range (fun p : TorusModel × unitInterval => (φ p : E)) = X := by
    rw [← Function.comp_def, _root_.Set.range_comp, φ.surjective.range_eq, _root_.Set.image_univ, Subtype.range_val]
  rw [← hrange]
  exact isConnected_range (continuous_subtype_val.comp φ.continuous)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.isConnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.isConnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.isConnected ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.isConnected

theorem IsToroidalShell.isCompact_left (h : IsToroidalShell X B₀ B₁) : IsCompact B₀ := by
  obtain ⟨φ, rfl, -⟩ := h
  rw [show {p : TorusModel × unitInterval | (p.2 : ℝ) = 0} =
    {p | (p.2 : ℝ) = (0 : unitInterval)} from rfl, image_toroidal_shell_slice]
  exact isCompact_range (continuous_subtype_val.comp
    (φ.continuous.comp (continuous_id.prodMk continuous_const)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.isCompact_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.isCompact_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.isCompact_left ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.isCompact_left

theorem IsToroidalShell.isCompact_right (h : IsToroidalShell X B₀ B₁) : IsCompact B₁ := by
  obtain ⟨φ, -, rfl⟩ := h
  rw [show {p : TorusModel × unitInterval | (p.2 : ℝ) = 1} =
    {p | (p.2 : ℝ) = (1 : unitInterval)} from rfl, image_toroidal_shell_slice]
  exact isCompact_range (continuous_subtype_val.comp
    (φ.continuous.comp (continuous_id.prodMk continuous_const)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.isCompact_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.isCompact_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.isCompact_right ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.isCompact_right

theorem IsToroidalShell.isConnected_left (h : IsToroidalShell X B₀ B₁) :
    IsConnected B₀ := by
  obtain ⟨φ, rfl, -⟩ := h
  rw [show {p : TorusModel × unitInterval | (p.2 : ℝ) = 0} =
    {p | (p.2 : ℝ) = (0 : unitInterval)} from rfl, image_toroidal_shell_slice]
  exact isConnected_range (continuous_subtype_val.comp
    (φ.continuous.comp (continuous_id.prodMk continuous_const)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.isConnected_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.isConnected_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.isConnected_left ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.isConnected_left

theorem IsToroidalShell.isConnected_right (h : IsToroidalShell X B₀ B₁) :
    IsConnected B₁ := by
  obtain ⟨φ, -, rfl⟩ := h
  rw [show {p : TorusModel × unitInterval | (p.2 : ℝ) = 1} =
    {p | (p.2 : ℝ) = (1 : unitInterval)} from rfl, image_toroidal_shell_slice]
  exact isConnected_range (continuous_subtype_val.comp
    (φ.continuous.comp (continuous_id.prodMk continuous_const)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.isConnected_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.isConnected_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.isConnected_right ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.isConnected_right

theorem IsToroidalShell.left_subset (h : IsToroidalShell X B₀ B₁) : B₀ ⊆ X := by
  obtain ⟨φ, rfl, -⟩ := h
  rintro x ⟨y, -, rfl⟩
  exact y.property

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.left_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.left_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.left_subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.left_subset

theorem IsToroidalShell.right_subset (h : IsToroidalShell X B₀ B₁) : B₁ ⊆ X := by
  obtain ⟨φ, -, rfl⟩ := h
  rintro x ⟨y, -, rfl⟩
  exact y.property

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.right_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.right_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.right_subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.right_subset

theorem IsToroidalShell.disjoint (h : IsToroidalShell X B₀ B₁) : Disjoint B₀ B₁ := by
  obtain ⟨φ, rfl, rfl⟩ := h
  apply disjoint_left.mpr
  rintro x ⟨y, ⟨p, hp, rfl⟩, hpx⟩ ⟨z, ⟨q, hq, rfl⟩, hqx⟩
  have hpq : p = q := φ.injective (Subtype.ext (hpx.trans hqx.symm))
  subst q
  have : (0 : ℝ) = 1 := hp.symm.trans hq
  exact zero_ne_one this

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.disjoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.disjoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.disjoint ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.disjoint

theorem IsToroidalShell.frontier_eq
    {X B₀ B₁ : Set (EuclideanSpace ℝ (Fin 3))} (h : IsToroidalShell X B₀ B₁) :
    frontier X = B₀ ∪ B₁ := by
  obtain ⟨φ, rfl, rfl⟩ := h
  let g : TorusModel × unitInterval → EuclideanSpace ℝ (Fin 3) :=
    fun p => (φ p : EuclideanSpace ℝ (Fin 3))
  have hrange : _root_.Set.range g = X := by
    change _root_.Set.range (Subtype.val ∘ φ) = X
    rw [_root_.Set.range_comp, φ.surjective.range_eq, _root_.Set.image_univ, Subtype.range_val]
  have hi : Function.Injective g := Subtype.val_injective.comp φ.injective
  have hc : Continuous g := continuous_subtype_val.comp φ.continuous
  have hf := frontier_range_prod_unitInterval g hc hi
  rw [hrange] at hf
  simpa only [← _root_.Set.image_comp, g, Function.comp_def] using hf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.frontier_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.frontier_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.frontier_eq ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.frontier_eq

theorem IsToroidalShell.nonempty_homeomorph_interior
    {X B₀ B₁ : Set (EuclideanSpace ℝ (Fin 3))} (h : IsToroidalShell X B₀ B₁) :
    Nonempty ((TorusModel × _root_.Set.Ioo (0 : ℝ) 1) ≃ₜ interior X) := by
  obtain ⟨φ, -, -⟩ := h
  let g : TorusModel × unitInterval → EuclideanSpace ℝ (Fin 3) :=
    fun p => (φ p : EuclideanSpace ℝ (Fin 3))
  have hrange : _root_.Set.range g = X := by
    change _root_.Set.range (Subtype.val ∘ φ) = X
    rw [_root_.Set.range_comp, φ.surjective.range_eq, _root_.Set.image_univ, Subtype.range_val]
  have hi : Function.Injective g := Subtype.val_injective.comp φ.injective
  have hc : Continuous g := continuous_subtype_val.comp φ.continuous
  exact ⟨(prodIooHomeomorphInteriorRange g hc hi).trans
    (Homeomorph.setCongr (congrArg interior hrange))⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.nonempty_homeomorph_interior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.nonempty_homeomorph_interior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.nonempty_homeomorph_interior ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.nonempty_homeomorph_interior

theorem IsToroidalShell.subset_interior_of_separates
    {X B₀ B₁ C : Set (EuclideanSpace ℝ (Fin 3))} (h : IsToroidalShell X B₀ B₁)
    (hC : IsPreconnected C) (hsep : Separates C B₀ B₁) : C ⊆ interior X := by
  apply hsep.subset_interior_of_disjoint_frontier hC h.isConnected.isPreconnected
  · obtain ⟨x, hx⟩ := h.isConnected_left.nonempty
    exact ⟨x, hx, h.left_subset hx⟩
  · obtain ⟨x, hx⟩ := h.isConnected_right.nonempty
    exact ⟨x, hx, h.right_subset hx⟩
  · rw [h.frontier_eq]
    exact disjoint_left.mpr fun x hx hxB => hxB.elim
      (fun hx₀ => hsep.left_subset_compl hx₀ hx)
      (fun hx₁ => hsep.right_subset_compl hx₁ hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.subset_interior_of_separates then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.subset_interior_of_separates"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.subset_interior_of_separates ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.subset_interior_of_separates

open _root_.Classical in
theorem IsToroidalShell.exists_connected_separating_surface
    {X B₀ B₁ : Set (EuclideanSpace ℝ (Fin 3))} (h : IsToroidalShell X B₀ B₁) :
    ∃ (L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) (hLfin : L.faces.Finite),
      letI := hLfin.to_subtype
      IsCombinatorialManifold 2 L ∧ IsConnected L.space ∧ IsOrientable 2 L ∧
      IsTwoSided L.space ∧ L.space ⊆ interior X ∧ Separates L.space B₀ B₁ := by
  obtain ⟨L, hfin, hL, hc, ho, ht, -, hsep⟩ :=
    PiecewiseLinear.exists_connected_separating_surface (by simp :
      Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3)
      h.isCompact_left h.isConnected_left h.isCompact_right.isClosed h.isConnected_right
      h.disjoint isOpen_univ (_root_.Set.subset_univ _)
  let _ := hfin.to_subtype
  refine ⟨L, hfin, hL, hc, ho, ht, ?_, hsep⟩
  exact h.subset_interior_of_separates hc.isPreconnected hsep

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.exists_connected_separating_surface then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.exists_connected_separating_surface"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.exists_connected_separating_surface ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.exists_connected_separating_surface

open _root_.Classical in
theorem IsToroidalShell.exists_connected_separating_surface_bettiOne_min
    {X B₀ B₁ : Set (EuclideanSpace ℝ (Fin 3))} (h : IsToroidalShell X B₀ B₁) :
    ∃ (L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) (hLfin : L.faces.Finite),
      letI := hLfin.to_subtype
      IsCombinatorialManifold 2 L ∧ IsConnected L.space ∧ IsOrientable 2 L ∧
      IsTwoSided L.space ∧ L.space ⊆ interior X ∧ Separates L.space B₀ B₁ ∧
      ∀ (M : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))), M.faces.Finite →
        IsCombinatorialManifold 2 M → IsConnected M.space → Separates M.space B₀ B₁ →
        Homology.bettiOne L.space ≤ Homology.bettiOne M.space := by
  obtain ⟨L, hfin, hL, hc, ho, ht, -, hsep, hmin⟩ :=
    PiecewiseLinear.exists_connected_separating_surface_bettiOne_min (by simp :
      Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3)
      h.isCompact_left h.isConnected_left h.isCompact_right.isClosed h.isConnected_right
      h.disjoint isOpen_univ (_root_.Set.subset_univ _)
  let _ : Finite L.faces := hfin.to_subtype
  refine ⟨L, hfin, hL, hc, ho, ht, h.subset_interior_of_separates hc.isPreconnected hsep,
    hsep, ?_⟩
  intro M hMfin hM hMc hMsep
  exact hmin M hMfin hM hMc (_root_.Set.subset_univ _) hMsep

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.exists_connected_separating_surface_bettiOne_min then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.exists_connected_separating_surface_bettiOne_min"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.exists_connected_separating_surface_bettiOne_min ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsToroidalShell.exists_connected_separating_surface_bettiOne_min

end DifferentialGeometry.Topology.PiecewiseLinear
