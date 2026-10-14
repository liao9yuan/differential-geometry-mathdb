import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34MarkedCellSides

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

def section34SquareSign (a b : Bool) : (ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ) :=
  (if a then LinearEquiv.neg ℝ else LinearEquiv.refl ℝ ℝ).prodCongr
    (if b then LinearEquiv.neg ℝ else LinearEquiv.refl ℝ ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34SquareSign then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34SquareSign"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34SquareSign ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34SquareSign

def section34CellSign (a b : Bool) : ((ℝ × ℝ) × ℝ) ≃ₗ[ℝ] ((ℝ × ℝ) × ℝ) :=
  (section34SquareSign a b).prodCongr (LinearEquiv.refl ℝ ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34CellSign then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34CellSign"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34CellSign ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34CellSign

def section34SpokeSignPerm (a b : Bool) : Equiv.Perm (Fin 4) :=
  (if a then Equiv.swap 0 2 else Equiv.refl _).trans
    (if b then Equiv.swap 1 3 else Equiv.refl _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34SpokeSignPerm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34SpokeSignPerm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34SpokeSignPerm ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34SpokeSignPerm

private theorem square_sign_involutive (a b : Bool) :
    Function.Involutive (section34SquareSign a b) := by
  intro p
  cases a <;> cases b <;> simp [section34SquareSign]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.square_sign_involutive
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.square_sign_involutive target :: scope.openDecls } }

private theorem square_sign_mapsTo (a b : Bool) :
    MapsTo (section34SquareSign a b) spliceSquare spliceSquare := by
  rintro ⟨x, y⟩ ⟨⟨hx₀, hx₁⟩, ⟨hy₀, hy₁⟩⟩
  cases a <;> cases b <;>
    simp only [section34SquareSign, Bool.false_eq_true, ↓reduceIte, LinearEquiv.prodCongr_apply,
      LinearEquiv.refl_apply, LinearEquiv.neg_apply, spliceSquare,
      _root_.Set.mem_prod, _root_.Set.mem_Icc] <;>
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.square_sign_mapsTo
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.square_sign_mapsTo target :: scope.openDecls } }

private theorem square_sign_image (a b : Bool) :
    section34SquareSign a b '' spliceSquare = spliceSquare := by
  apply Subset.antisymm (image_subset_iff.mpr (square_sign_mapsTo a b))
  intro p hp
  exact ⟨section34SquareSign a b p, square_sign_mapsTo a b hp,
    square_sign_involutive a b p⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.square_sign_image
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.square_sign_image target :: scope.openDecls } }

private theorem square_sign_leaf (a b : Bool) (i : Fin 4) :
    section34SquareSign a b (fourSpokeModelLeaf i) =
      fourSpokeModelLeaf (section34SpokeSignPerm a b i) := by
  cases a <;> cases b <;> fin_cases i <;>
    norm_num [section34SquareSign, section34SpokeSignPerm, fourSpokeModelLeaf,
      Equiv.swap_apply_def, Fin.ext_iff]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.square_sign_leaf
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.square_sign_leaf target :: scope.openDecls } }

theorem section34_cell_sign_axis (a b : Bool) (t : ℝ) :
    section34CellSign a b (0, t) = (0, t) := by
  simp [section34CellSign]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34_cell_sign_axis then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34_cell_sign_axis"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34_cell_sign_axis ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34_cell_sign_axis

theorem section34_cell_sign_face_image (a b : Bool) (T : Set ℝ) :
    section34CellSign a b '' (spliceSquare ×ˢ T) = spliceSquare ×ˢ T := by
  change Prod.map (section34SquareSign a b) id '' _ = _
  rw [_root_.Set.prodMap_image_prod, square_sign_image, _root_.Set.image_id]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34_cell_sign_face_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34_cell_sign_face_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34_cell_sign_face_image ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34_cell_sign_face_image

theorem section34_cell_sign_ribbon_image (a b : Bool) (i : Fin 4) :
    section34CellSign a b '' section34MarkedRibbon i =
      section34MarkedRibbon (section34SpokeSignPerm a b i) := by
  change Prod.map (section34SquareSign a b) id '' _ = _
  rw [section34MarkedRibbon, _root_.Set.prodMap_image_prod, _root_.Set.image_id]
  have h := image_segment ℝ (section34SquareSign a b).toLinearMap.toAffineMap
    (0 : ℝ × ℝ) (fourSpokeModelLeaf i)
  change section34SquareSign a b '' _ =
    segment ℝ (section34SquareSign a b 0)
      (section34SquareSign a b (fourSpokeModelLeaf i)) at h
  rw [map_zero, square_sign_leaf] at h
  rw [h]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34_cell_sign_ribbon_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34_cell_sign_ribbon_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34_cell_sign_ribbon_image ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34_cell_sign_ribbon_image

theorem isPLHomeomorphOn_section34_cell_sign (a b : Bool) :
    IsPLHomeomorphOn (section34CellSign a b) spliceCylinder spliceCylinder := by
  have hpoly := isHPolytope_spliceCylinder.isPolyhedron
  have h := isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hpoly
    ((isPiecewiseAffineOn_of_affine
      (section34CellSign a b).toLinearMap.toAffineMap isOpen_univ).mono_of_isPolyhedron
        hpoly (_root_.Set.subset_univ _)) (section34CellSign a b).injective.injOn.bijOn_image
  change IsPLHomeomorphOn (section34CellSign a b) spliceCylinder
    (section34CellSign a b '' (spliceSquare ×ˢ _root_.Set.Icc (0 : ℝ) 1)) at h
  rwa [section34_cell_sign_face_image] at h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_section34_cell_sign then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_section34_cell_sign"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_section34_cell_sign ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_section34_cell_sign

end DifferentialGeometry.Topology.PiecewiseLinear
