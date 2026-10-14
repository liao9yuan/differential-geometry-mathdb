import Submission.DifferentialGeometry.Topology.Simplex.Face
import Submission.DifferentialGeometry.Topology.Simplex.BoundaryRetraction
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set

namespace DifferentialGeometry.Simplex

universe u

variable {n : ℕ}

def faceToBoundary (i : Fin (n + 2)) :
    C(stdSimplex ℝ (Fin (n + 1)), boundary (Fin (n + 2))) :=
  ⟨fun p => ⟨stdSimplex.map i.succAbove p, ⟨i, map_succAbove_apply_pivot i p⟩⟩,
    (stdSimplex.continuous_map i.succAbove).subtype_mk _⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.faceToBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.faceToBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.faceToBoundary ``Submission.DifferentialGeometry.Simplex.faceToBoundary

@[simp]
theorem faceToBoundary_val (i : Fin (n + 2))
    (p : stdSimplex ℝ (Fin (n + 1))) :
    (faceToBoundary i p).val = stdSimplex.map i.succAbove p := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.faceToBoundary_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.faceToBoundary_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.faceToBoundary_val ``Submission.DifferentialGeometry.Simplex.faceToBoundary_val

theorem faceToBoundary_injective (i : Fin (n + 2)) :
    Function.Injective (faceToBoundary i) := by
  intro p q h
  apply Subtype.ext
  funext j
  have hj := congrArg (fun z : boundary (Fin (n + 2)) => z.val.val (i.succAbove j)) h
  exact (map_succAbove_apply_image i p j).symm.trans
    (hj.trans (map_succAbove_apply_image i q j))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.faceToBoundary_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.faceToBoundary_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.faceToBoundary_injective ``Submission.DifferentialGeometry.Simplex.faceToBoundary_injective

private def faceInterior (i : Fin (n + 2)) : Set (boundary (Fin (n + 2))) :=
  {p | ∀ j : Fin (n + 1), 0 < p.val.val (i.succAbove j)}

run_cmd do
  let target := ``Submission.DifferentialGeometry.Simplex.faceInterior
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Simplex.faceInterior target :: scope.openDecls } }

private theorem faceInterior_pivot_eq_zero (i : Fin (n + 2))
    {p : boundary (Fin (n + 2))} (hp : p ∈ faceInterior i) : p.val.val i = 0 := by
  obtain ⟨j, hj⟩ := p.property
  by_cases hji : j = i
  · exact hji ▸ hj
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hji
    exact False.elim ((ne_of_gt (hp k)) hj)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Simplex.faceInterior_pivot_eq_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Simplex.faceInterior_pivot_eq_zero target :: scope.openDecls } }

private def faceFromBoundary (i : Fin (n + 2))
    (p : boundary (Fin (n + 2))) : stdSimplex ℝ (Fin (n + 1)) :=
  if hp : p.val.val i = 0 then faceDelete i ⟨p.val, hp⟩ else stdSimplex.barycenter

run_cmd do
  let target := ``Submission.DifferentialGeometry.Simplex.faceFromBoundary
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Simplex.faceFromBoundary target :: scope.openDecls } }

private theorem faceFromBoundary_apply (i : Fin (n + 2))
    {p : boundary (Fin (n + 2))} (hp : p.val.val i = 0) :
    faceFromBoundary i p = faceDelete i ⟨p.val, hp⟩ := by
  simp [faceFromBoundary, hp]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Simplex.faceFromBoundary_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Simplex.faceFromBoundary_apply target :: scope.openDecls } }

private theorem faceFromBoundary_faceToBoundary (i : Fin (n + 2))
    (p : stdSimplex ℝ (Fin (n + 1))) :
    faceFromBoundary i (faceToBoundary i p) = p := by
  rw [faceFromBoundary_apply i (map_succAbove_apply_pivot i p)]
  exact faceDelete_faceInsert i p

run_cmd do
  let target := ``Submission.DifferentialGeometry.Simplex.faceFromBoundary_faceToBoundary
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Simplex.faceFromBoundary_faceToBoundary target :: scope.openDecls } }

def faceOpenPartialHomeomorph (i : Fin (n + 2)) :
    OpenPartialHomeomorph (stdSimplex ℝ (Fin (n + 1))) (boundary (Fin (n + 2))) where
  toFun := faceToBoundary i
  invFun := faceFromBoundary i
  source := (boundary (Fin (n + 1)))ᶜ
  target := faceInterior i
  map_source' := by
    intro p hp j
    change 0 < (stdSimplex.map i.succAbove p).val (i.succAbove j)
    rw [map_succAbove_apply_image]
    exact lt_of_le_of_ne (p.property.1 j) (Ne.symm (fun hj => hp ⟨j, hj⟩))
  map_target' := by
    intro p hp
    rw [faceFromBoundary_apply i (faceInterior_pivot_eq_zero i hp)]
    rintro ⟨j, hj⟩
    exact (ne_of_gt (hp j)) hj
  left_inv' := fun p _ => faceFromBoundary_faceToBoundary i p
  right_inv' := by
    intro p hp
    rw [faceFromBoundary_apply i (faceInterior_pivot_eq_zero i hp)]
    apply Subtype.ext
    change stdSimplex.map i.succAbove (faceDelete i ⟨p.val, _⟩) = p.val
    exact congrArg Subtype.val (faceInsert_faceDelete i ⟨p.val, faceInterior_pivot_eq_zero i hp⟩)
  open_source := isClosed_boundary.isOpen_compl
  open_target := by
    change IsOpen {p : boundary (Fin (n + 2)) | ∀ j : Fin (n + 1), 0 < p.val.val (i.succAbove j)}
    simp only [_root_.Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro j
    exact isOpen_lt continuous_const ((continuous_apply (i.succAbove j)).comp
      (continuous_subtype_val.comp continuous_subtype_val))
  continuousOn_toFun := (faceToBoundary i).continuous.continuousOn
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    let f : C(faceInterior i, face i) :=
      ⟨fun p => ⟨p.val.val, faceInterior_pivot_eq_zero i p.property⟩,
        (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
    have he : (fun p : faceInterior i => faceFromBoundary i p.val) =
        fun p : faceInterior i => faceDelete i (f p) := by
      funext p
      exact faceFromBoundary_apply i (faceInterior_pivot_eq_zero i p.property)
    change Continuous (fun p : faceInterior i => faceFromBoundary i p.val)
    rw [he]
    exact (faceDelete i).continuous.comp f.continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.faceOpenPartialHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.faceOpenPartialHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.faceOpenPartialHomeomorph ``Submission.DifferentialGeometry.Simplex.faceOpenPartialHomeomorph

@[simp]
theorem faceOpenPartialHomeomorph_apply (i : Fin (n + 2))
    (p : stdSimplex ℝ (Fin (n + 1))) :
    faceOpenPartialHomeomorph i p = faceToBoundary i p := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.faceOpenPartialHomeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.faceOpenPartialHomeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.faceOpenPartialHomeomorph_apply ``Submission.DifferentialGeometry.Simplex.faceOpenPartialHomeomorph_apply

@[simp]
theorem faceOpenPartialHomeomorph_source (i : Fin (n + 2)) :
    (faceOpenPartialHomeomorph i).source = (boundary (Fin (n + 1)))ᶜ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.faceOpenPartialHomeomorph_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.faceOpenPartialHomeomorph_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.faceOpenPartialHomeomorph_source ``Submission.DifferentialGeometry.Simplex.faceOpenPartialHomeomorph_source

@[simp]
theorem faceOpenPartialHomeomorph_target (i : Fin (n + 2)) :
    (faceOpenPartialHomeomorph i).target =
      {p | ∀ j : Fin (n + 1), 0 < p.val.val (i.succAbove j)} := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.faceOpenPartialHomeomorph_target then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.faceOpenPartialHomeomorph_target"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.faceOpenPartialHomeomorph_target ``Submission.DifferentialGeometry.Simplex.faceOpenPartialHomeomorph_target


def liftedFaceToBoundary (i : Fin (n + 2)) :
    C(ULift.{u} (stdSimplex ℝ (Fin (n + 1))), ULift.{u} (boundary (Fin (n + 2)))) :=
  ⟨fun p => ULift.up (faceToBoundary i p.down),
    continuous_uliftUp.comp ((faceToBoundary i).continuous.comp continuous_uliftDown)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.liftedFaceToBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.liftedFaceToBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.liftedFaceToBoundary ``Submission.DifferentialGeometry.Simplex.liftedFaceToBoundary

theorem liftedFaceToBoundary_injective (i : Fin (n + 2)) :
    Function.Injective (liftedFaceToBoundary.{u} i) := by
  intro p q h
  apply ULift.ext
  exact faceToBoundary_injective i (congrArg ULift.down h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.liftedFaceToBoundary_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.liftedFaceToBoundary_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.liftedFaceToBoundary_injective ``Submission.DifferentialGeometry.Simplex.liftedFaceToBoundary_injective

def liftedFaceOpenPartialHomeomorph (i : Fin (n + 2)) :
    OpenPartialHomeomorph (ULift.{u} (stdSimplex ℝ (Fin (n + 1))))
      (ULift.{u} (boundary (Fin (n + 2)))) :=
  (Homeomorph.ulift.transOpenPartialHomeomorph
    (faceOpenPartialHomeomorph i)).transHomeomorph Homeomorph.ulift.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.liftedFaceOpenPartialHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.liftedFaceOpenPartialHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.liftedFaceOpenPartialHomeomorph ``Submission.DifferentialGeometry.Simplex.liftedFaceOpenPartialHomeomorph

@[simp]
theorem liftedFaceOpenPartialHomeomorph_apply (i : Fin (n + 2))
    (p : ULift.{u} (stdSimplex ℝ (Fin (n + 1)))) :
    liftedFaceOpenPartialHomeomorph i p = liftedFaceToBoundary i p := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.liftedFaceOpenPartialHomeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.liftedFaceOpenPartialHomeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.liftedFaceOpenPartialHomeomorph_apply ``Submission.DifferentialGeometry.Simplex.liftedFaceOpenPartialHomeomorph_apply

@[simp]
theorem liftedFaceOpenPartialHomeomorph_source (i : Fin (n + 2)) :
    (liftedFaceOpenPartialHomeomorph.{u} i).source =
      {p | p.down ∈ (boundary (Fin (n + 1)))ᶜ} := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.liftedFaceOpenPartialHomeomorph_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.liftedFaceOpenPartialHomeomorph_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.liftedFaceOpenPartialHomeomorph_source ``Submission.DifferentialGeometry.Simplex.liftedFaceOpenPartialHomeomorph_source

theorem liftedFaceToBoundary_mapsTo (i : Fin (n + 2))
    (p : ULift.{u} (stdSimplex ℝ (Fin (n + 1)))) :
    _root_.Set.MapsTo (liftedFaceToBoundary i) ({p}ᶜ : Set _)
      ({liftedFaceToBoundary i p}ᶜ : Set _) :=
  fun _ hq h => hq (liftedFaceToBoundary_injective i h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.liftedFaceToBoundary_mapsTo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.liftedFaceToBoundary_mapsTo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.liftedFaceToBoundary_mapsTo ``Submission.DifferentialGeometry.Simplex.liftedFaceToBoundary_mapsTo

end DifferentialGeometry.Simplex
