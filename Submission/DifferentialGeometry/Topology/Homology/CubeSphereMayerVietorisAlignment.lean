import Submission.DifferentialGeometry.Topology.Homology.CubeSphereDegreeUnit
import Submission.DifferentialGeometry.Topology.Homology.LiftedSphereRelativeBridge

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology _root_.ContinuousMap _root_.Set _root_.Metric _root_.Module
open scoped _root_.Topology
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace DifferentialGeometry.Topology

universe u

theorem integralSphereTopHomologyEquiv_succ_apply {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (n : ℕ) (hd : _root_.Module.finrank ℝ E = n + 3)
    (c : integralSingularHomology (n + 2) (_root_.Metric.sphere (0 : E) 1)) :
    integralSphereTopHomologyEquiv (n + 1) E hd c =
      integralSphereTopHomologyEquiv n
        (ℝ ∙ ((-(unitSpherePointOfFinrankPos (E := E) (by omega)) :
          _root_.Metric.sphere (0 : E) 1) : E))ᗮ
        (unitSpherePoleHyperplane_finrank (n + 2) (by omega)
          (-(unitSpherePointOfFinrankPos (E := E) (by omega))))
        (integralSphereHomologyShiftEquiv n
          (unitSpherePointOfFinrankPos (E := E) (by omega)) c) := by
  rw [integralSphereTopHomologyEquiv, Nat.recAux_succ, LinearEquiv.trans_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSphereTopHomologyEquiv_succ_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSphereTopHomologyEquiv_succ_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSphereTopHomologyEquiv_succ_apply ``Submission.DifferentialGeometry.Topology.integralSphereTopHomologyEquiv_succ_apply

abbrev CubeSphereMayerVietorisSource :=
  integralSingularHomology 3 (_root_.Metric.sphere (0 : liftedSphereSpace.{u} 2) 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.CubeSphereMayerVietorisSource then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.CubeSphereMayerVietorisSource"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.CubeSphereMayerVietorisSource ``Submission.DifferentialGeometry.Topology.CubeSphereMayerVietorisSource

def integralSphereHomologyShiftEquiv_cubeSphereFundamentalClass
    {B : Type u} [AddCommGroup B] [Module ℤ B]
    (f : CubeSphereMayerVietorisSource.{u} ≃ₗ[ℤ] B)
    (τ : B ≃ₗ[ℤ] integralSingularHomology 2 (liftedHomotopySphere.{u} 1)) : Prop :=
  τ (f (hurewiczCubeClass cubeSphereUnliftedLoop.{u})) = squareSphereFundamentalClass.{u} ∨
    τ (f (hurewiczCubeClass cubeSphereUnliftedLoop.{u})) = -squareSphereFundamentalClass.{u}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSphereHomologyShiftEquiv_cubeSphereFundamentalClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSphereHomologyShiftEquiv_cubeSphereFundamentalClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSphereHomologyShiftEquiv_cubeSphereFundamentalClass ``Submission.DifferentialGeometry.Topology.integralSphereHomologyShiftEquiv_cubeSphereFundamentalClass

theorem isSphereHomologyGenerator_cubeSphereFundamentalClass_iff_isUnit_apply_trans
    {B : Type u} [AddCommGroup B] [Module ℤ B]
    (f : CubeSphereMayerVietorisSource.{u} ≃ₗ[ℤ] B) (g : B ≃ₗ[ℤ] ℤ) :
    IsSphereHomologyGenerator.{u} 2 cubeSphereFundamentalClass.{u} ↔
      IsUnit (g (f (hurewiczCubeClass cubeSphereUnliftedLoop.{u}))) := by
  rw [isSphereHomologyGenerator_cubeSphereFundamentalClass_iff_unliftedCoordinate_isUnit]
  exact (isUnit_apply_iff_isUnit_apply_of_linearEquiv_trans f g
    (integralSphereTopHomologyEquiv 2 (liftedSphereSpace.{u} 2) (liftedSphereSpace_finrank 2))
    (hurewiczCubeClass cubeSphereUnliftedLoop.{u})).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isSphereHomologyGenerator_cubeSphereFundamentalClass_iff_isUnit_apply_trans then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isSphereHomologyGenerator_cubeSphereFundamentalClass_iff_isUnit_apply_trans"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isSphereHomologyGenerator_cubeSphereFundamentalClass_iff_isUnit_apply_trans ``Submission.DifferentialGeometry.Topology.isSphereHomologyGenerator_cubeSphereFundamentalClass_iff_isUnit_apply_trans

theorem isSphereHomologyGenerator_cubeSphereFundamentalClass_of_isUnit_apply_trans
    {B : Type u} [AddCommGroup B] [Module ℤ B]
    (f : CubeSphereMayerVietorisSource.{u} ≃ₗ[ℤ] B) (g : B ≃ₗ[ℤ] ℤ)
    (h : IsUnit (g (f (hurewiczCubeClass cubeSphereUnliftedLoop.{u})))) :
    IsSphereHomologyGenerator.{u} 2 cubeSphereFundamentalClass.{u} :=
  (isSphereHomologyGenerator_cubeSphereFundamentalClass_iff_isUnit_apply_trans f g).mpr h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isSphereHomologyGenerator_cubeSphereFundamentalClass_of_isUnit_apply_trans then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isSphereHomologyGenerator_cubeSphereFundamentalClass_of_isUnit_apply_trans"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isSphereHomologyGenerator_cubeSphereFundamentalClass_of_isUnit_apply_trans ``Submission.DifferentialGeometry.Topology.isSphereHomologyGenerator_cubeSphereFundamentalClass_of_isUnit_apply_trans

theorem cubeSphereFundamentalClass_ne_zero_of_isUnit_apply_trans
    {B : Type u} [AddCommGroup B] [Module ℤ B]
    (f : CubeSphereMayerVietorisSource.{u} ≃ₗ[ℤ] B) (g : B ≃ₗ[ℤ] ℤ)
    (h : IsUnit (g (f (hurewiczCubeClass cubeSphereUnliftedLoop.{u})))) :
    cubeSphereFundamentalClass.{u} ≠ 0 :=
  IsSphereHomologyGenerator.ne_zero 2
    (isSphereHomologyGenerator_cubeSphereFundamentalClass_of_isUnit_apply_trans f g h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.cubeSphereFundamentalClass_ne_zero_of_isUnit_apply_trans then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.cubeSphereFundamentalClass_ne_zero_of_isUnit_apply_trans"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.cubeSphereFundamentalClass_ne_zero_of_isUnit_apply_trans ``Submission.DifferentialGeometry.Topology.cubeSphereFundamentalClass_ne_zero_of_isUnit_apply_trans

theorem isSphereHomologyGenerator_cubeSphereFundamentalClass_iff_squareSphereFundamentalClass
    {B : Type u} [AddCommGroup B] [Module ℤ B]
    (f : CubeSphereMayerVietorisSource.{u} ≃ₗ[ℤ] B) (g : B ≃ₗ[ℤ] ℤ)
    (τ : B ≃ₗ[ℤ] integralSingularHomology 2 (liftedHomotopySphere.{u} 1))
    (halign : integralSphereHomologyShiftEquiv_cubeSphereFundamentalClass f τ) :
    IsSphereHomologyGenerator.{u} 2 cubeSphereFundamentalClass.{u} ↔
      IsSphereHomologyGenerator.{u} 1 squareSphereFundamentalClass.{u} := by
  rw [isSphereHomologyGenerator_cubeSphereFundamentalClass_iff_isUnit_apply_trans f g,
    isSphereHomologyGenerator_squareSphereFundamentalClass_iff_coordinate, ← Int.isUnit_iff]
  rcases halign with h | h
  · have himg : f (hurewiczCubeClass cubeSphereUnliftedLoop.{u}) =
        τ.symm squareSphereFundamentalClass.{u} := by
      rw [← h, LinearEquiv.symm_apply_apply]
    rw [himg]
    exact isUnit_apply_iff_isUnit_apply_of_linearEquiv_trans τ.symm g
      (integralLiftedSphereTopEquiv.{u} 1) squareSphereFundamentalClass.{u}
  · have himg : f (hurewiczCubeClass cubeSphereUnliftedLoop.{u}) =
        -(τ.symm squareSphereFundamentalClass.{u}) := by
      rw [← map_neg τ.symm squareSphereFundamentalClass.{u}, ← h,
        LinearEquiv.symm_apply_apply]
    rw [himg, map_neg, IsUnit.neg_iff]
    exact isUnit_apply_iff_isUnit_apply_of_linearEquiv_trans τ.symm g
      (integralLiftedSphereTopEquiv.{u} 1) squareSphereFundamentalClass.{u}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isSphereHomologyGenerator_cubeSphereFundamentalClass_iff_squareSphereFundamentalClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isSphereHomologyGenerator_cubeSphereFundamentalClass_iff_squareSphereFundamentalClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isSphereHomologyGenerator_cubeSphereFundamentalClass_iff_squareSphereFundamentalClass ``Submission.DifferentialGeometry.Topology.isSphereHomologyGenerator_cubeSphereFundamentalClass_iff_squareSphereFundamentalClass

theorem isSphereHomologyGenerator_cubeSphereFundamentalClass_of_squareSphereFundamentalClass
    {B : Type u} [AddCommGroup B] [Module ℤ B]
    (f : CubeSphereMayerVietorisSource.{u} ≃ₗ[ℤ] B) (g : B ≃ₗ[ℤ] ℤ)
    (τ : B ≃ₗ[ℤ] integralSingularHomology 2 (liftedHomotopySphere.{u} 1))
    (halign : integralSphereHomologyShiftEquiv_cubeSphereFundamentalClass f τ)
    (hsq : IsSphereHomologyGenerator.{u} 1 squareSphereFundamentalClass.{u}) :
    IsSphereHomologyGenerator.{u} 2 cubeSphereFundamentalClass.{u} :=
  (isSphereHomologyGenerator_cubeSphereFundamentalClass_iff_squareSphereFundamentalClass
    f g τ halign).mpr hsq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isSphereHomologyGenerator_cubeSphereFundamentalClass_of_squareSphereFundamentalClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isSphereHomologyGenerator_cubeSphereFundamentalClass_of_squareSphereFundamentalClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isSphereHomologyGenerator_cubeSphereFundamentalClass_of_squareSphereFundamentalClass ``Submission.DifferentialGeometry.Topology.isSphereHomologyGenerator_cubeSphereFundamentalClass_of_squareSphereFundamentalClass

theorem isSphereHomologyGenerator_cubeSphereFundamentalClass_of_squareRelativeFunctional
    {B : Type u} [AddCommGroup B] [Module ℤ B]
    (f : CubeSphereMayerVietorisSource.{u} ≃ₗ[ℤ] B) (g : B ≃ₗ[ℤ] ℤ)
    (τ : B ≃ₗ[ℤ] integralSingularHomology 2 (liftedHomotopySphere.{u} 1))
    (halign : integralSphereHomologyShiftEquiv_cubeSphereFundamentalClass f τ)
    (hrel : ∃ ψ : integralRelativeHomology 2 (liftedSphereBasepoint.{u}) →ₗ[ℤ] ℤ,
      ψ (integralAbsoluteToRelative 2 (liftedSphereBasepoint.{u})
        squareSphereFundamentalClass.{u}) = 1) :
    IsSphereHomologyGenerator.{u} 2 cubeSphereFundamentalClass.{u} :=
  isSphereHomologyGenerator_cubeSphereFundamentalClass_of_squareSphereFundamentalClass
    f g τ halign
    (squareSphereFundamentalClass_isSphereHomologyGenerator_iff_exists_relative_functional.mpr hrel)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isSphereHomologyGenerator_cubeSphereFundamentalClass_of_squareRelativeFunctional then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isSphereHomologyGenerator_cubeSphereFundamentalClass_of_squareRelativeFunctional"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isSphereHomologyGenerator_cubeSphereFundamentalClass_of_squareRelativeFunctional ``Submission.DifferentialGeometry.Topology.isSphereHomologyGenerator_cubeSphereFundamentalClass_of_squareRelativeFunctional

end DifferentialGeometry.Topology
