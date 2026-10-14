import Submission.DifferentialGeometry.Topology.Homotopy.CubeInterior
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeHomeomorphism

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.Topology

universe u v

open _root_.Set

def cubeCoordinateInclusion (N : Type u) : C(N → unitInterval, N → ℝ) :=
  ⟨fun x i => (x i : ℝ), by fun_prop⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.cubeCoordinateInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.cubeCoordinateInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.cubeCoordinateInclusion ``Submission.DifferentialGeometry.Topology.cubeCoordinateInclusion

theorem cubeCoordinateInclusion_injective (N : Type u) :
    Function.Injective (cubeCoordinateInclusion N) := by
  intro x y h
  funext i
  exact Subtype.ext (congrFun h i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.cubeCoordinateInclusion_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.cubeCoordinateInclusion_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.cubeCoordinateInclusion_injective ``Submission.DifferentialGeometry.Topology.cubeCoordinateInclusion_injective

private def openCube (N : Type u) : Set (N → ℝ) :=
  {x | ∀ i, 0 < x i ∧ x i < 1}

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.openCube
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.openCube target :: scope.openDecls } }

private theorem isOpen_openCube (N : Type u) [Finite N] : IsOpen (openCube N) := by
  have h : openCube N = ⋂ i : N, (fun x : N → ℝ => x i) ⁻¹' _root_.Set.Ioo (0 : ℝ) 1 := by
    ext x
    simp only [openCube, _root_.Set.mem_ofPred_eq, _root_.Set.mem_iInter, _root_.Set.mem_preimage, _root_.Set.mem_Ioo]
  rw [h]
  exact isOpen_iInter_of_finite fun i => isOpen_Ioo.preimage (continuous_apply i)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.isOpen_openCube
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.isOpen_openCube target :: scope.openDecls } }

private def cubeInteriorCoordinateHomeomorph (N : Type u) :
    cubeInterior N ≃ₜ openCube N where
  toFun x := ⟨cubeCoordinateInclusion N x, x.property⟩
  invFun x := ⟨fun i => ⟨x.val i, (x.property i).1.le, (x.property i).2.le⟩, x.property⟩
  left_inv x := by rfl
  right_inv x := by rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    exact ((continuous_apply i).comp continuous_subtype_val).subtype_mk _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.cubeInteriorCoordinateHomeomorph
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.cubeInteriorCoordinateHomeomorph target :: scope.openDecls } }

theorem cubeCoordinateInclusion_mapsTo_pointComplement (N : Type u)
    (p : N → unitInterval) :
    _root_.Set.MapsTo (cubeCoordinateInclusion N) ({p}ᶜ : Set (N → unitInterval))
      ({cubeCoordinateInclusion N p}ᶜ : Set (N → ℝ)) :=
  fun _ hx => (cubeCoordinateInclusion_injective N).ne hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.cubeCoordinateInclusion_mapsTo_pointComplement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.cubeCoordinateInclusion_mapsTo_pointComplement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.cubeCoordinateInclusion_mapsTo_pointComplement ``Submission.DifferentialGeometry.Topology.cubeCoordinateInclusion_mapsTo_pointComplement

theorem integralRelativeHomologyMap_cubeCoordinateInclusion_bijective
    (N : Type u) [Finite N] (k : ℕ) (p : N → unitInterval) (hp : p ∈ cubeInterior N) :
    Function.Bijective (integralRelativeHomologyMap k (cubeCoordinateInclusion N)
      (cubeCoordinateInclusion_mapsTo_pointComplement N p)) := by
  let f := cubeCoordinateInclusion N
  let e := cubeInteriorCoordinateHomeomorph N
  have hUV : _root_.Set.MapsTo f (cubeInterior N) (openCube N) := fun _ h => h
  let Jx := integralLocalHomologyNeighborhoodIso k p (cubeInterior N) (isOpen_cubeInterior N) hp
  let Jy := integralLocalHomologyNeighborhoodIso k (f p) (openCube N) (isOpen_openCube N) (hUV hp)
  let L := integralLocalHomologyHomeomorphIso k e (⟨p, hp⟩ : cubeInterior N)
  have h := integralLocalHomologyNeighborhoodIso_map k f p
    (cubeCoordinateInclusion_mapsTo_pointComplement N p) (cubeInterior N) (openCube N)
    (isOpen_cubeInterior N) (isOpen_openCube N) hUV hp
  change (integralRelativeHomologyMap k f _).comp Jx.hom.hom =
    Jy.hom.hom.comp L.hom.hom at h
  have hcomp : Function.Bijective ((integralRelativeHomologyMap k f
      (cubeCoordinateInclusion_mapsTo_pointComplement N p)).comp Jx.hom.hom) := by
    rw [h]
    exact Jy.toLinearEquiv.bijective.comp L.toLinearEquiv.bijective
  exact (Function.Bijective.of_comp_iff _ Jx.toLinearEquiv.bijective).mp hcomp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeHomologyMap_cubeCoordinateInclusion_bijective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeHomologyMap_cubeCoordinateInclusion_bijective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeHomologyMap_cubeCoordinateInclusion_bijective ``Submission.DifferentialGeometry.Topology.integralRelativeHomologyMap_cubeCoordinateInclusion_bijective


def liftedCubeCoordinateInclusion (N : Type u) :
    C(ULift.{v} (N → unitInterval), ULift.{v} (N → ℝ)) :=
  ⟨fun x => ULift.up (cubeCoordinateInclusion N x.down), by fun_prop⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedCubeCoordinateInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedCubeCoordinateInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedCubeCoordinateInclusion ``Submission.DifferentialGeometry.Topology.liftedCubeCoordinateInclusion

theorem liftedCubeCoordinateInclusion_injective (N : Type u) :
    Function.Injective (liftedCubeCoordinateInclusion.{u,v} N) := by
  intro x y h
  apply ULift.ext
  exact cubeCoordinateInclusion_injective N (congrArg ULift.down h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedCubeCoordinateInclusion_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedCubeCoordinateInclusion_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedCubeCoordinateInclusion_injective ``Submission.DifferentialGeometry.Topology.liftedCubeCoordinateInclusion_injective

theorem liftedCubeCoordinateInclusion_mapsTo_pointComplement (N : Type u)
    (p : ULift.{v} (N → unitInterval)) :
    _root_.Set.MapsTo (liftedCubeCoordinateInclusion N) ({p}ᶜ : Set (ULift.{v} (N → unitInterval)))
      ({liftedCubeCoordinateInclusion N p}ᶜ : Set (ULift.{v} (N → ℝ))) :=
  fun _ hx => (liftedCubeCoordinateInclusion_injective N).ne hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedCubeCoordinateInclusion_mapsTo_pointComplement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedCubeCoordinateInclusion_mapsTo_pointComplement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedCubeCoordinateInclusion_mapsTo_pointComplement ``Submission.DifferentialGeometry.Topology.liftedCubeCoordinateInclusion_mapsTo_pointComplement

private def liftedCubeInterior (N : Type u) : Set (ULift.{v} (N → unitInterval)) :=
  {x | x.down ∈ cubeInterior N}

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.liftedCubeInterior
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.liftedCubeInterior target :: scope.openDecls } }

private def liftedOpenCube (N : Type u) : Set (ULift.{v} (N → ℝ)) :=
  {x | ∀ i, 0 < x.down i ∧ x.down i < 1}

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.liftedOpenCube
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.liftedOpenCube target :: scope.openDecls } }

private theorem isOpen_liftedCubeInterior (N : Type u) [Finite N] :
    IsOpen (liftedCubeInterior.{u,v} N) :=
  (isOpen_cubeInterior N).preimage continuous_uliftDown

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.isOpen_liftedCubeInterior
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.isOpen_liftedCubeInterior target :: scope.openDecls } }

private theorem isOpen_liftedOpenCube (N : Type u) [Finite N] :
    IsOpen (liftedOpenCube.{u,v} N) := by
  have h : liftedOpenCube.{u,v} N =
      ⋂ i : N, (fun x : ULift.{v} (N → ℝ) => x.down i) ⁻¹' _root_.Set.Ioo (0 : ℝ) 1 := by
    ext x
    simp only [liftedOpenCube, _root_.Set.mem_ofPred_eq, _root_.Set.mem_iInter, _root_.Set.mem_preimage, _root_.Set.mem_Ioo]
  rw [h]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_Ioo.preimage ((continuous_apply i).comp continuous_uliftDown)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.isOpen_liftedOpenCube
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.isOpen_liftedOpenCube target :: scope.openDecls } }

private def liftedCubeInteriorCoordinateHomeomorph (N : Type u) :
    liftedCubeInterior.{u,v} N ≃ₜ liftedOpenCube.{u,v} N where
  toFun x := ⟨liftedCubeCoordinateInclusion N x, x.property⟩
  invFun x := ⟨ULift.up (fun i => ⟨x.val.down i,
    (x.property i).1.le, (x.property i).2.le⟩), x.property⟩
  left_inv x := by rfl
  right_inv x := by rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_uliftUp.comp
    apply continuous_pi
    intro i
    exact ((continuous_apply i).comp
      (continuous_uliftDown.comp continuous_subtype_val)).subtype_mk _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.liftedCubeInteriorCoordinateHomeomorph
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.liftedCubeInteriorCoordinateHomeomorph target :: scope.openDecls } }

theorem integralRelativeHomologyMap_liftedCubeCoordinateInclusion_bijective
    (N : Type u) [Finite N] (k : ℕ) (p : ULift.{v} (N → unitInterval))
    (hp : p.down ∈ cubeInterior N) :
    Function.Bijective (integralRelativeHomologyMap k (liftedCubeCoordinateInclusion N)
      (liftedCubeCoordinateInclusion_mapsTo_pointComplement N p)) := by
  let f := liftedCubeCoordinateInclusion N
  let e := liftedCubeInteriorCoordinateHomeomorph.{u,v} N
  have hUV : _root_.Set.MapsTo f (liftedCubeInterior N) (liftedOpenCube N) := fun _ h => h
  let Jx := integralLocalHomologyNeighborhoodIso k p (liftedCubeInterior N)
    (isOpen_liftedCubeInterior N) hp
  let Jy := integralLocalHomologyNeighborhoodIso k (f p) (liftedOpenCube N)
    (isOpen_liftedOpenCube N) (hUV hp)
  let L := integralLocalHomologyHomeomorphIso k e (⟨p, hp⟩ : liftedCubeInterior N)
  have h := integralLocalHomologyNeighborhoodIso_map k f p
    (liftedCubeCoordinateInclusion_mapsTo_pointComplement N p)
    (liftedCubeInterior N) (liftedOpenCube N)
    (isOpen_liftedCubeInterior N) (isOpen_liftedOpenCube N) hUV hp
  change (integralRelativeHomologyMap k f _).comp Jx.hom.hom =
    Jy.hom.hom.comp L.hom.hom at h
  have hcomp : Function.Bijective ((integralRelativeHomologyMap k f
      (liftedCubeCoordinateInclusion_mapsTo_pointComplement N p)).comp Jx.hom.hom) := by
    rw [h]
    exact Jy.toLinearEquiv.bijective.comp L.toLinearEquiv.bijective
  exact (Function.Bijective.of_comp_iff _ Jx.toLinearEquiv.bijective).mp hcomp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeHomologyMap_liftedCubeCoordinateInclusion_bijective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeHomologyMap_liftedCubeCoordinateInclusion_bijective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeHomologyMap_liftedCubeCoordinateInclusion_bijective ``Submission.DifferentialGeometry.Topology.integralRelativeHomologyMap_liftedCubeCoordinateInclusion_bijective


end DifferentialGeometry.Topology
