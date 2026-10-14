import Submission.DifferentialGeometry.Geometry.Metric.RicciSoliton.Models
import Submission.DifferentialGeometry.Geometry.Metric.RicciSoliton.CylinderIsometry
import Submission.DifferentialGeometry.Geometry.Metric.Quotient
import Submission.DifferentialGeometry.Geometry.Metric.Pullback.Euclidean
import Submission.DifferentialGeometry.Geometry.Metric.Pullback.Product
import Submission.DifferentialGeometry.Geometry.Metric.Sphere.FreeOrthogonalAction
import Submission.DifferentialGeometry.Geometry.Metric.Sphere.Isometry.Representation
import Submission.DifferentialGeometry.Geometry.Metric.Sphere.Isometry.OrthogonalAction
import Submission.DifferentialGeometry.Topology.ProperlyDiscontinuousAction
import Submission.DifferentialGeometry.Topology.Manifold.Quotient
import Submission.DifferentialGeometry.Topology.ProjectiveSpace.PuncturedThree
import Mathlib.GroupTheory.OrderOfElement

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Geometry

def cylinderAntipodal :
    Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real →
      Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real :=
  fun x => (-x.1, x.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderAntipodal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderAntipodal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderAntipodal ``Submission.DifferentialGeometry.Geometry.cylinderAntipodal

def cylinderDiagonal :
    Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real →
      Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real :=
  fun x => (-x.1, -x.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderDiagonal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderDiagonal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderDiagonal ``Submission.DifferentialGeometry.Geometry.cylinderDiagonal

private noncomputable def roundTwoSphereAntipodalDiffeomorph :
    Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 ≃ₘ⟮𝓡 2, 𝓡 2⟯
      Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 := by
  let : Fact (Module.finrank Real (EuclideanSpace Real (Fin 3)) = 2 + 1) :=
    ⟨by simp⟩
  exact sphereDiffeo (n := 2) (LinearIsometryEquiv.neg Real)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.roundTwoSphereAntipodalDiffeomorph
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.roundTwoSphereAntipodalDiffeomorph target :: scope.openDecls } }

noncomputable def cylinderAntipodalDiffeomorph :
    (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)
      ≃ₘ⟮(𝓡 2).prod 𝓘(Real, Real), (𝓡 2).prod 𝓘(Real, Real)⟯
        Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real :=
  roundTwoSphereAntipodalDiffeomorph.prodCongr
    (Diffeomorph.refl 𝓘(Real, Real) Real ∞)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderAntipodalDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderAntipodalDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderAntipodalDiffeomorph ``Submission.DifferentialGeometry.Geometry.cylinderAntipodalDiffeomorph

noncomputable def cylinderDiagonalDiffeomorph :
    (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)
      ≃ₘ⟮(𝓡 2).prod 𝓘(Real, Real), (𝓡 2).prod 𝓘(Real, Real)⟯
        Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real :=
  roundTwoSphereAntipodalDiffeomorph.prodCongr
    (ContinuousLinearEquiv.neg Real).toDiffeomorph

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderDiagonalDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderDiagonalDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderDiagonalDiffeomorph ``Submission.DifferentialGeometry.Geometry.cylinderDiagonalDiffeomorph

theorem cylinderAntipodal_apply
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    cylinderAntipodal x = (-x.1, x.2) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderAntipodal_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderAntipodal_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderAntipodal_apply ``Submission.DifferentialGeometry.Geometry.cylinderAntipodal_apply

theorem cylinderDiagonal_apply
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    cylinderDiagonal x = (-x.1, -x.2) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderDiagonal_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderDiagonal_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderDiagonal_apply ``Submission.DifferentialGeometry.Geometry.cylinderDiagonal_apply

private theorem roundTwoSphereAntipodalDiffeomorph_apply
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) :
    roundTwoSphereAntipodalDiffeomorph x = -x := by
  apply Subtype.ext
  simp [roundTwoSphereAntipodalDiffeomorph]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.roundTwoSphereAntipodalDiffeomorph_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.roundTwoSphereAntipodalDiffeomorph_apply target :: scope.openDecls } }

theorem cylinderAntipodalDiffeomorph_apply
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    cylinderAntipodalDiffeomorph x = cylinderAntipodal x := by
  apply Prod.ext
  · exact roundTwoSphereAntipodalDiffeomorph_apply x.1
  · rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderAntipodalDiffeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderAntipodalDiffeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderAntipodalDiffeomorph_apply ``Submission.DifferentialGeometry.Geometry.cylinderAntipodalDiffeomorph_apply

theorem cylinderDiagonalDiffeomorph_apply
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    cylinderDiagonalDiffeomorph x = cylinderDiagonal x := by
  apply Prod.ext
  · exact roundTwoSphereAntipodalDiffeomorph_apply x.1
  · rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderDiagonalDiffeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderDiagonalDiffeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderDiagonalDiffeomorph_apply ``Submission.DifferentialGeometry.Geometry.cylinderDiagonalDiffeomorph_apply

theorem cylinderAntipodal_involutive (x :
    Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    cylinderAntipodal (cylinderAntipodal x) = x := by
  apply Prod.ext
  · simp [cylinderAntipodal]
  · simp [cylinderAntipodal]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderAntipodal_involutive then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderAntipodal_involutive"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderAntipodal_involutive ``Submission.DifferentialGeometry.Geometry.cylinderAntipodal_involutive

theorem cylinderDiagonal_involutive (x :
    Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    cylinderDiagonal (cylinderDiagonal x) = x := by
  apply Prod.ext
  · simp [cylinderDiagonal]
  · simp [cylinderDiagonal]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderDiagonal_involutive then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderDiagonal_involutive"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderDiagonal_involutive ``Submission.DifferentialGeometry.Geometry.cylinderDiagonal_involutive

theorem cylinderAntipodal_potential (x :
    Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    roundThreeCylinderShrinkerPotential (cylinderAntipodal x) =
      roundThreeCylinderShrinkerPotential x := by
  simp [cylinderAntipodal, roundThreeCylinderShrinkerPotential_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderAntipodal_potential then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderAntipodal_potential"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderAntipodal_potential ``Submission.DifferentialGeometry.Geometry.cylinderAntipodal_potential

theorem cylinderDiagonal_potential (x :
    Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    roundThreeCylinderShrinkerPotential (cylinderDiagonal x) =
      roundThreeCylinderShrinkerPotential x := by
  simp [cylinderDiagonal, roundThreeCylinderShrinkerPotential_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderDiagonal_potential then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderDiagonal_potential"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderDiagonal_potential ``Submission.DifferentialGeometry.Geometry.cylinderDiagonal_potential

theorem cylinderAntipodal_fixed_point_free (x :
    Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    cylinderAntipodal x ≠ x := by
  intro h
  have hsphere : -x.1 = x.1 := congrArg Prod.fst h
  have hzero : (x.1 : EuclideanSpace Real (Fin 3)) = 0 := by
    apply_fun (fun z : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
      (z : EuclideanSpace Real (Fin 3))) at hsphere
    have hamb : -(x.1 : EuclideanSpace Real (Fin 3)) = x.1 := by
      simpa using hsphere
    ext i
    have hi := congrArg (fun z : EuclideanSpace Real (Fin 3) => z i) hamb
    simp only [PiLp.neg_apply, PiLp.zero_apply] at hi ⊢
    linarith
  have hnorm := x.1.2
  rw [hzero] at hnorm
  norm_num at hnorm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderAntipodal_fixed_point_free then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderAntipodal_fixed_point_free"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderAntipodal_fixed_point_free ``Submission.DifferentialGeometry.Geometry.cylinderAntipodal_fixed_point_free

theorem cylinderDiagonal_fixed_point_free (x :
    Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    cylinderDiagonal x ≠ x := by
  intro h
  have hsphere : -x.1 = x.1 := congrArg Prod.fst h
  have hzero : (x.1 : EuclideanSpace Real (Fin 3)) = 0 := by
    apply_fun (fun z : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
      (z : EuclideanSpace Real (Fin 3))) at hsphere
    have hamb : -(x.1 : EuclideanSpace Real (Fin 3)) = x.1 := by
      simpa using hsphere
    ext i
    have hi := congrArg (fun z : EuclideanSpace Real (Fin 3) => z i) hamb
    simp only [PiLp.neg_apply, PiLp.zero_apply] at hi ⊢
    linarith
  have hnorm := x.1.2
  rw [hzero] at hnorm
  norm_num at hnorm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderDiagonal_fixed_point_free then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderDiagonal_fixed_point_free"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderDiagonal_fixed_point_free ``Submission.DifferentialGeometry.Geometry.cylinderDiagonal_fixed_point_free

theorem gaussianPotential_affine_preserving_shift_eq_zero
    (epsilon shift : Real)
    (hpreserve : ∀ s : Real,
      gaussianPotential (E := Real) (epsilon * s + shift) =
        gaussianPotential (E := Real) s) :
    shift = 0 := by
  have hzero := hpreserve 0
  simp only [gaussianPotential_apply, Real.norm_eq_abs] at hzero
  have hsq : shift ^ 2 = 0 := by
    simpa using hzero
  nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.gaussianPotential_affine_preserving_shift_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.gaussianPotential_affine_preserving_shift_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.gaussianPotential_affine_preserving_shift_eq_zero ``Submission.DifferentialGeometry.Geometry.gaussianPotential_affine_preserving_shift_eq_zero

theorem roundThreeCylinderShrinkerPotential_affine_line_preserving_shift_eq_zero
    (y : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1)
    (epsilon shift : Real)
    (hpreserve : ∀ s : Real,
      roundThreeCylinderShrinkerPotential (y, epsilon * s + shift) =
        roundThreeCylinderShrinkerPotential (y, s)) :
    shift = 0 := by
  have hzero := hpreserve 0
  simp only [_root_.MulZeroClass.mul_zero, zero_add, roundThreeCylinderShrinkerPotential_apply] at hzero
  nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.roundThreeCylinderShrinkerPotential_affine_line_preserving_shift_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.roundThreeCylinderShrinkerPotential_affine_line_preserving_shift_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.roundThreeCylinderShrinkerPotential_affine_line_preserving_shift_eq_zero ``Submission.DifferentialGeometry.Geometry.roundThreeCylinderShrinkerPotential_affine_line_preserving_shift_eq_zero

theorem roundThreeCylinderShrinkerPotential_affine_line_preserving_iff
    (y : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1)
    (epsilon shift : Real) :
    (∀ s : Real,
      roundThreeCylinderShrinkerPotential (y, epsilon * s + shift) =
        roundThreeCylinderShrinkerPotential (y, s)) ↔
      (epsilon = 1 ∨ epsilon = -1) ∧ shift = 0 := by
  constructor
  · intro hpreserve
    have hshift :=
      roundThreeCylinderShrinkerPotential_affine_line_preserving_shift_eq_zero
        y epsilon shift hpreserve
    subst shift
    have hone := hpreserve 1
    simp only [mul_one, add_zero, roundThreeCylinderShrinkerPotential_apply,
      one_pow] at hone
    refine ⟨sq_eq_one_iff.mp ?_, rfl⟩
    nlinarith
  · rintro ⟨hepsilon, rfl⟩ s
    rcases hepsilon with rfl | rfl <;>
      simp [roundThreeCylinderShrinkerPotential_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.roundThreeCylinderShrinkerPotential_affine_line_preserving_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.roundThreeCylinderShrinkerPotential_affine_line_preserving_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.roundThreeCylinderShrinkerPotential_affine_line_preserving_iff ``Submission.DifferentialGeometry.Geometry.roundThreeCylinderShrinkerPotential_affine_line_preserving_iff

variable {Γ : Type*}

theorem finite_of_properlyDiscontinuousSMul_of_roundThreeCylinderShrinkerPotential_invariant
    [SMul Γ (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)]
    [ProperlyDiscontinuousSMul Γ
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)]
    (hpotential : ∀ (γ : Γ) x,
      roundThreeCylinderShrinkerPotential (γ • x) =
        roundThreeCylinderShrinkerPotential x) :
    Finite Γ := by
  apply ProperlyDiscontinuousSMul.finite_of_isCompact_mapsTo
    (Γ := Γ)
    (T := Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)
    (K := roundThreeCylinderCentralSlice)
    isCompact_roundThreeCylinderCentralSlice
  · refine ⟨(⟨EuclideanSpace.single 0 1, ?_⟩, (0 : Real)), rfl⟩
    simp [PiLp.norm_single]
  · intro γ x hx
    rw [← roundThreeCylinderShrinkerPotential_eq_one_iff] at hx ⊢
    rw [hpotential γ x]
    exact hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.finite_of_properlyDiscontinuousSMul_of_roundThreeCylinderShrinkerPotential_invariant then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.finite_of_properlyDiscontinuousSMul_of_roundThreeCylinderShrinkerPotential_invariant"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.finite_of_properlyDiscontinuousSMul_of_roundThreeCylinderShrinkerPotential_invariant ``Submission.DifferentialGeometry.Geometry.finite_of_properlyDiscontinuousSMul_of_roundThreeCylinderShrinkerPotential_invariant

private theorem roundTwoSphereAntipodalDiffeomorph_pullbackMetric :
    Diffeomorph.pullbackMetric roundTwoSphereShrinkerMetric
        roundTwoSphereAntipodalDiffeomorph =
      roundTwoSphereShrinkerMetric := by
  let : Fact (Module.finrank Real (EuclideanSpace Real (Fin 3)) = 2 + 1) :=
    ⟨by simp⟩
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [Diffeomorph.pullbackMetric_inner]
  change (roundSphereShrinkerMetric
        (A := EuclideanSpace Real (Fin 3)) (n := 2) (by decide)).inner
      (sphereDiffeo (n := 2) (LinearIsometryEquiv.neg Real) x)
        (mfderiv (𝓡 2) (𝓡 2)
          (sphereDiffeo (n := 2) (LinearIsometryEquiv.neg Real)) x v)
        (mfderiv (𝓡 2) (𝓡 2)
          (sphereDiffeo (n := 2) (LinearIsometryEquiv.neg Real)) x w) =
      (roundSphereShrinkerMetric
        (A := EuclideanSpace Real (Fin 3)) (n := 2) (by decide)).inner x v w
  rw [roundSphereShrinkerMetric, scaleMetric_inner, scaleMetric_inner]
  exact congrArg
    (fun z : Real => roundSphereShrinkerRadius 2 ^ 2 * z)
    (roundInner_sphereDiffeo (n := 2)
      (LinearIsometryEquiv.neg Real) x v w)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.roundTwoSphereAntipodalDiffeomorph_pullbackMetric
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.roundTwoSphereAntipodalDiffeomorph_pullbackMetric target :: scope.openDecls } }

theorem cylinderAntipodalDiffeomorph_pullbackMetric :
    Diffeomorph.pullbackMetric roundThreeCylinderShrinkerMetric
        cylinderAntipodalDiffeomorph =
      roundThreeCylinderShrinkerMetric := by
  rw [roundThreeCylinderShrinkerMetric,
    cylinderAntipodalDiffeomorph,
    Diffeomorph.pullbackMetric_prodCongr,
    roundTwoSphereAntipodalDiffeomorph_pullbackMetric,
    Diffeomorph.pullbackMetric_refl]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderAntipodalDiffeomorph_pullbackMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderAntipodalDiffeomorph_pullbackMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderAntipodalDiffeomorph_pullbackMetric ``Submission.DifferentialGeometry.Geometry.cylinderAntipodalDiffeomorph_pullbackMetric

theorem cylinderDiagonalDiffeomorph_pullbackMetric :
    Diffeomorph.pullbackMetric roundThreeCylinderShrinkerMetric
        cylinderDiagonalDiffeomorph =
      roundThreeCylinderShrinkerMetric := by
  have hneg :
      Diffeomorph.pullbackMetric (euclideanMetric (E := Real))
          (ContinuousLinearEquiv.neg Real).toDiffeomorph =
        euclideanMetric := by
    have hdiffeo :
        (ContinuousLinearEquiv.neg Real).toDiffeomorph =
          (LinearIsometryEquiv.neg Real : Real ≃ₗᵢ[Real] Real).toContinuousLinearEquiv.toDiffeomorph := by
      apply Diffeomorph.ext
      intro x
      rfl
    rw [hdiffeo]
    exact
      LinearIsometryEquiv.pullbackMetric_euclidean
        (E := Real) (LinearIsometryEquiv.neg Real)
  rw [roundThreeCylinderShrinkerMetric,
    cylinderDiagonalDiffeomorph,
    Diffeomorph.pullbackMetric_prodCongr,
    roundTwoSphereAntipodalDiffeomorph_pullbackMetric,
    hneg]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderDiagonalDiffeomorph_pullbackMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderDiagonalDiffeomorph_pullbackMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderDiagonalDiffeomorph_pullbackMetric ``Submission.DifferentialGeometry.Geometry.cylinderDiagonalDiffeomorph_pullbackMetric

theorem cylinderAntipodalDiffeomorph_potential :
    roundThreeCylinderShrinkerPotential.comp
        cylinderAntipodalDiffeomorph.toContMDiffMap =
      roundThreeCylinderShrinkerPotential := by
  apply ContMDiffMap.ext
  intro x
  change roundThreeCylinderShrinkerPotential
      (cylinderAntipodalDiffeomorph x) =
    roundThreeCylinderShrinkerPotential x
  rw [cylinderAntipodalDiffeomorph_apply]
  exact cylinderAntipodal_potential x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderAntipodalDiffeomorph_potential then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderAntipodalDiffeomorph_potential"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderAntipodalDiffeomorph_potential ``Submission.DifferentialGeometry.Geometry.cylinderAntipodalDiffeomorph_potential

theorem cylinderDiagonalDiffeomorph_potential :
    roundThreeCylinderShrinkerPotential.comp
        cylinderDiagonalDiffeomorph.toContMDiffMap =
      roundThreeCylinderShrinkerPotential := by
  apply ContMDiffMap.ext
  intro x
  change roundThreeCylinderShrinkerPotential
      (cylinderDiagonalDiffeomorph x) =
    roundThreeCylinderShrinkerPotential x
  rw [cylinderDiagonalDiffeomorph_apply]
  exact cylinderDiagonal_potential x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderDiagonalDiffeomorph_potential then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderDiagonalDiffeomorph_potential"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderDiagonalDiffeomorph_potential ``Submission.DifferentialGeometry.Geometry.cylinderDiagonalDiffeomorph_potential

theorem cylinderAntipodalDiffeomorph_fixed_point_free
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    cylinderAntipodalDiffeomorph x ≠ x := by
  rw [cylinderAntipodalDiffeomorph_apply]
  exact cylinderAntipodal_fixed_point_free x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderAntipodalDiffeomorph_fixed_point_free then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderAntipodalDiffeomorph_fixed_point_free"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderAntipodalDiffeomorph_fixed_point_free ``Submission.DifferentialGeometry.Geometry.cylinderAntipodalDiffeomorph_fixed_point_free

theorem cylinderDiagonalDiffeomorph_fixed_point_free
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    cylinderDiagonalDiffeomorph x ≠ x := by
  rw [cylinderDiagonalDiffeomorph_apply]
  exact cylinderDiagonal_fixed_point_free x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderDiagonalDiffeomorph_fixed_point_free then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderDiagonalDiffeomorph_fixed_point_free"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderDiagonalDiffeomorph_fixed_point_free ``Submission.DifferentialGeometry.Geometry.cylinderDiagonalDiffeomorph_fixed_point_free

private theorem perm_orderOf_eq_two {X : Type*} [Nonempty X]
    (phi : Equiv.Perm X) (hinvolutive : Function.Involutive phi)
    (hfree : ∀ x, phi x ≠ x) :
    orderOf phi = 2 := by
  apply orderOf_eq_prime
  · ext x
    exact hinvolutive x
  · intro h
    obtain ⟨x⟩ := ‹Nonempty X›
    exact hfree x (by rw [h]; rfl)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.perm_orderOf_eq_two
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.perm_orderOf_eq_two target :: scope.openDecls } }

private theorem mem_zpowers_perm_order_two_iff {X : Type*}
    (phi : Equiv.Perm X) (horder : orderOf phi = 2) (psi : Equiv.Perm X) :
    psi ∈ Subgroup.zpowers phi ↔ psi = 1 ∨ psi = phi := by
  classical
  have hfinite : IsOfFinOrder phi :=
    orderOf_pos_iff.mp (by rw [horder]; exact Nat.zero_lt_two)
  constructor
  · intro hpsi
    have hrange := hfinite.mem_zpowers_iff_mem_range_orderOf.mp hpsi
    rw [horder] at hrange
    rcases Finset.mem_image.mp hrange with ⟨n, hn, rfl⟩
    simp only [Finset.mem_range] at hn
    interval_cases n <;> simp
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.mem_zpowers_perm_order_two_iff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.mem_zpowers_perm_order_two_iff target :: scope.openDecls } }

noncomputable def cylinderAntipodalGroup : Subgroup (Equiv.Perm
    (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)) :=
  Subgroup.zpowers cylinderAntipodalDiffeomorph.toEquiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderAntipodalGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderAntipodalGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderAntipodalGroup ``Submission.DifferentialGeometry.Geometry.cylinderAntipodalGroup

noncomputable def cylinderDiagonalGroup : Subgroup (Equiv.Perm
    (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)) :=
  Subgroup.zpowers cylinderDiagonalDiffeomorph.toEquiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderDiagonalGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderDiagonalGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderDiagonalGroup ``Submission.DifferentialGeometry.Geometry.cylinderDiagonalGroup

instance cylinderAntipodalGroupSMul :
    SMul cylinderAntipodalGroup
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) where
  smul gamma x := gamma.1 x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderAntipodalGroupSMul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderAntipodalGroupSMul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderAntipodalGroupSMul ``Submission.DifferentialGeometry.Geometry.cylinderAntipodalGroupSMul

instance cylinderDiagonalGroupSMul :
    SMul cylinderDiagonalGroup
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) where
  smul gamma x := gamma.1 x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderDiagonalGroupSMul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderDiagonalGroupSMul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderDiagonalGroupSMul ``Submission.DifferentialGeometry.Geometry.cylinderDiagonalGroupSMul

instance cylinderAntipodalGroupMulAction :
    MulAction cylinderAntipodalGroup
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :=
  MulAction.instMulAction cylinderAntipodalGroup

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderAntipodalGroupMulAction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderAntipodalGroupMulAction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderAntipodalGroupMulAction ``Submission.DifferentialGeometry.Geometry.cylinderAntipodalGroupMulAction

instance cylinderDiagonalGroupMulAction :
    MulAction cylinderDiagonalGroup
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :=
  MulAction.instMulAction cylinderDiagonalGroup

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderDiagonalGroupMulAction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderDiagonalGroupMulAction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderDiagonalGroupMulAction ``Submission.DifferentialGeometry.Geometry.cylinderDiagonalGroupMulAction

theorem cylinderAntipodalGroup_orderOf :
    orderOf cylinderAntipodalDiffeomorph.toEquiv = 2 := by
  let : Nonempty (Metric.sphere
      (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :=
    ⟨⟨Classical.choice
      (NormedSpace.sphere_nonempty.mpr zero_le_one).to_subtype, 0⟩⟩
  apply perm_orderOf_eq_two
  · intro x
    change cylinderAntipodalDiffeomorph
        (cylinderAntipodalDiffeomorph x) = x
    rw [cylinderAntipodalDiffeomorph_apply,
      cylinderAntipodalDiffeomorph_apply]
    exact cylinderAntipodal_involutive x
  · exact cylinderAntipodalDiffeomorph_fixed_point_free

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderAntipodalGroup_orderOf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderAntipodalGroup_orderOf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderAntipodalGroup_orderOf ``Submission.DifferentialGeometry.Geometry.cylinderAntipodalGroup_orderOf

theorem cylinderDiagonalGroup_orderOf :
    orderOf cylinderDiagonalDiffeomorph.toEquiv = 2 := by
  let : Nonempty (Metric.sphere
      (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :=
    ⟨⟨Classical.choice
      (NormedSpace.sphere_nonempty.mpr zero_le_one).to_subtype, 0⟩⟩
  apply perm_orderOf_eq_two
  · intro x
    change cylinderDiagonalDiffeomorph
        (cylinderDiagonalDiffeomorph x) = x
    rw [cylinderDiagonalDiffeomorph_apply,
      cylinderDiagonalDiffeomorph_apply]
    exact cylinderDiagonal_involutive x
  · exact cylinderDiagonalDiffeomorph_fixed_point_free

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderDiagonalGroup_orderOf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderDiagonalGroup_orderOf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderDiagonalGroup_orderOf ``Submission.DifferentialGeometry.Geometry.cylinderDiagonalGroup_orderOf

theorem cylinderAntipodalGroup_eq_one_or_generator
    (psi : cylinderAntipodalGroup) :
    psi.1 = 1 ∨ psi.1 = cylinderAntipodalDiffeomorph.toEquiv := by
  exact (mem_zpowers_perm_order_two_iff _
    cylinderAntipodalGroup_orderOf psi.1).mp psi.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderAntipodalGroup_eq_one_or_generator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderAntipodalGroup_eq_one_or_generator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderAntipodalGroup_eq_one_or_generator ``Submission.DifferentialGeometry.Geometry.cylinderAntipodalGroup_eq_one_or_generator

theorem cylinderDiagonalGroup_eq_one_or_generator
    (psi : cylinderDiagonalGroup) :
    psi.1 = 1 ∨ psi.1 = cylinderDiagonalDiffeomorph.toEquiv := by
  exact (mem_zpowers_perm_order_two_iff _
    cylinderDiagonalGroup_orderOf psi.1).mp psi.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderDiagonalGroup_eq_one_or_generator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderDiagonalGroup_eq_one_or_generator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderDiagonalGroup_eq_one_or_generator ``Submission.DifferentialGeometry.Geometry.cylinderDiagonalGroup_eq_one_or_generator

noncomputable instance cylinderAntipodalGroupFinite :
    Finite cylinderAntipodalGroup := by
  have hfinite : IsOfFinOrder cylinderAntipodalDiffeomorph.toEquiv :=
    orderOf_pos_iff.mp (by
      rw [cylinderAntipodalGroup_orderOf]
      exact Nat.zero_lt_two)
  exact Finite.of_equiv
    (Fin (orderOf cylinderAntipodalDiffeomorph.toEquiv))
    (finEquivZPowers hfinite)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderAntipodalGroupFinite then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderAntipodalGroupFinite"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderAntipodalGroupFinite ``Submission.DifferentialGeometry.Geometry.cylinderAntipodalGroupFinite

noncomputable instance cylinderDiagonalGroupFinite :
    Finite cylinderDiagonalGroup := by
  have hfinite : IsOfFinOrder cylinderDiagonalDiffeomorph.toEquiv :=
    orderOf_pos_iff.mp (by
      rw [cylinderDiagonalGroup_orderOf]
      exact Nat.zero_lt_two)
  exact Finite.of_equiv
    (Fin (orderOf cylinderDiagonalDiffeomorph.toEquiv))
    (finEquivZPowers hfinite)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderDiagonalGroupFinite then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderDiagonalGroupFinite"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderDiagonalGroupFinite ``Submission.DifferentialGeometry.Geometry.cylinderDiagonalGroupFinite

noncomputable def cylinderAntipodalGroupGenerator : cylinderAntipodalGroup :=
  ⟨cylinderAntipodalDiffeomorph.toEquiv, Subgroup.mem_zpowers _⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderAntipodalGroupGenerator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderAntipodalGroupGenerator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderAntipodalGroupGenerator ``Submission.DifferentialGeometry.Geometry.cylinderAntipodalGroupGenerator

noncomputable def cylinderDiagonalGroupGenerator : cylinderDiagonalGroup :=
  ⟨cylinderDiagonalDiffeomorph.toEquiv, Subgroup.mem_zpowers _⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderDiagonalGroupGenerator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderDiagonalGroupGenerator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderDiagonalGroupGenerator ``Submission.DifferentialGeometry.Geometry.cylinderDiagonalGroupGenerator

theorem cylinderAntipodalGroupGenerator_smul
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    @SMul.smul cylinderAntipodalGroup
        (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)
        cylinderAntipodalGroupMulAction.toSMul
        cylinderAntipodalGroupGenerator x =
      cylinderAntipodalDiffeomorph x :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderAntipodalGroupGenerator_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderAntipodalGroupGenerator_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderAntipodalGroupGenerator_smul ``Submission.DifferentialGeometry.Geometry.cylinderAntipodalGroupGenerator_smul

theorem cylinderDiagonalGroupGenerator_smul
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    @SMul.smul cylinderDiagonalGroup
        (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)
        cylinderDiagonalGroupMulAction.toSMul
        cylinderDiagonalGroupGenerator x =
      cylinderDiagonalDiffeomorph x :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderDiagonalGroupGenerator_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderDiagonalGroupGenerator_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderDiagonalGroupGenerator_smul ``Submission.DifferentialGeometry.Geometry.cylinderDiagonalGroupGenerator_smul

instance cylinderAntipodalGroupContinuousConstSMul :
    ContinuousConstSMul cylinderAntipodalGroup
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) where
  continuous_const_smul psi := by
    rcases cylinderAntipodalGroup_eq_one_or_generator psi with hpsi | hpsi
    · change Continuous (psi.1 :
        Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real → _)
      rw [hpsi]
      exact continuous_id
    · change Continuous (psi.1 :
        Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real → _)
      rw [hpsi]
      exact cylinderAntipodalDiffeomorph.continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderAntipodalGroupContinuousConstSMul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderAntipodalGroupContinuousConstSMul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderAntipodalGroupContinuousConstSMul ``Submission.DifferentialGeometry.Geometry.cylinderAntipodalGroupContinuousConstSMul

instance cylinderDiagonalGroupContinuousConstSMul :
    ContinuousConstSMul cylinderDiagonalGroup
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) where
  continuous_const_smul psi := by
    rcases cylinderDiagonalGroup_eq_one_or_generator psi with hpsi | hpsi
    · change Continuous (psi.1 :
        Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real → _)
      rw [hpsi]
      exact continuous_id
    · change Continuous (psi.1 :
        Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real → _)
      rw [hpsi]
      exact cylinderDiagonalDiffeomorph.continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderDiagonalGroupContinuousConstSMul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderDiagonalGroupContinuousConstSMul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderDiagonalGroupContinuousConstSMul ``Submission.DifferentialGeometry.Geometry.cylinderDiagonalGroupContinuousConstSMul

instance cylinderAntipodalGroupIsCancelSMul :
    IsCancelSMul cylinderAntipodalGroup
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) := by
  rw [isCancelSMul_iff_eq_one_of_smul_eq]
  intro psi x hpsi
  rcases cylinderAntipodalGroup_eq_one_or_generator psi with h | h
  · exact Subtype.ext h
  · exfalso
    change psi.1 x = x at hpsi
    rw [h] at hpsi
    exact cylinderAntipodalDiffeomorph_fixed_point_free x hpsi

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderAntipodalGroupIsCancelSMul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderAntipodalGroupIsCancelSMul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderAntipodalGroupIsCancelSMul ``Submission.DifferentialGeometry.Geometry.cylinderAntipodalGroupIsCancelSMul

instance cylinderDiagonalGroupIsCancelSMul :
    IsCancelSMul cylinderDiagonalGroup
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) := by
  rw [isCancelSMul_iff_eq_one_of_smul_eq]
  intro psi x hpsi
  rcases cylinderDiagonalGroup_eq_one_or_generator psi with h | h
  · exact Subtype.ext h
  · exfalso
    change psi.1 x = x at hpsi
    rw [h] at hpsi
    exact cylinderDiagonalDiffeomorph_fixed_point_free x hpsi

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderDiagonalGroupIsCancelSMul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderDiagonalGroupIsCancelSMul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderDiagonalGroupIsCancelSMul ``Submission.DifferentialGeometry.Geometry.cylinderDiagonalGroupIsCancelSMul

private theorem cylinderAntipodalDiffeomorph_toEquiv_ne_one :
    cylinderAntipodalDiffeomorph.toEquiv ≠ 1 := by
  intro h
  have horder := cylinderAntipodalGroup_orderOf
  rw [h, orderOf_one] at horder
  omega

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.cylinderAntipodalDiffeomorph_toEquiv_ne_one
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.cylinderAntipodalDiffeomorph_toEquiv_ne_one target :: scope.openDecls } }

private theorem cylinderDiagonalDiffeomorph_toEquiv_ne_one :
    cylinderDiagonalDiffeomorph.toEquiv ≠ 1 := by
  intro h
  have horder := cylinderDiagonalGroup_orderOf
  rw [h, orderOf_one] at horder
  omega

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.cylinderDiagonalDiffeomorph_toEquiv_ne_one
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.cylinderDiagonalDiffeomorph_toEquiv_ne_one target :: scope.openDecls } }

theorem cylinderAntipodalGroup_ne_bot :
    cylinderAntipodalGroup ≠ (⊥ : Subgroup (Equiv.Perm
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real))) := by
  intro h
  have hmem : cylinderAntipodalDiffeomorph.toEquiv ∈
      (⊥ : Subgroup (Equiv.Perm
        (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real))) := by
    rw [← h]
    exact Subgroup.mem_zpowers _
  have hone : cylinderAntipodalDiffeomorph.toEquiv = 1 := by
    simpa using hmem
  exact cylinderAntipodalDiffeomorph_toEquiv_ne_one hone

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderAntipodalGroup_ne_bot then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderAntipodalGroup_ne_bot"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderAntipodalGroup_ne_bot ``Submission.DifferentialGeometry.Geometry.cylinderAntipodalGroup_ne_bot

theorem cylinderDiagonalGroup_ne_bot :
    cylinderDiagonalGroup ≠ (⊥ : Subgroup (Equiv.Perm
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real))) := by
  intro h
  have hmem : cylinderDiagonalDiffeomorph.toEquiv ∈
      (⊥ : Subgroup (Equiv.Perm
        (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real))) := by
    rw [← h]
    exact Subgroup.mem_zpowers _
  have hone : cylinderDiagonalDiffeomorph.toEquiv = 1 := by
    simpa using hmem
  exact cylinderDiagonalDiffeomorph_toEquiv_ne_one hone

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderDiagonalGroup_ne_bot then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderDiagonalGroup_ne_bot"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderDiagonalGroup_ne_bot ``Submission.DifferentialGeometry.Geometry.cylinderDiagonalGroup_ne_bot

theorem cylinderAntipodalGroup_ne_cylinderDiagonalGroup :
    cylinderAntipodalGroup ≠ cylinderDiagonalGroup := by
  intro h
  have hmem : cylinderAntipodalDiffeomorph.toEquiv ∈ cylinderDiagonalGroup := by
    rw [← h]
    exact Subgroup.mem_zpowers _
  let psi : cylinderDiagonalGroup :=
    ⟨cylinderAntipodalDiffeomorph.toEquiv, hmem⟩
  rcases cylinderDiagonalGroup_eq_one_or_generator psi with hone | heq
  · change cylinderAntipodalDiffeomorph.toEquiv = 1 at hone
    exact cylinderAntipodalDiffeomorph_toEquiv_ne_one hone
  · let y : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 :=
      ⟨EuclideanSpace.single 0 1, by simp [PiLp.norm_single]⟩
    have hact := congrArg
      (fun e : Equiv.Perm
        (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) => e (y, 1)) heq
    change cylinderAntipodalDiffeomorph (y, 1) =
      cylinderDiagonalDiffeomorph (y, 1) at hact
    rw [cylinderAntipodalDiffeomorph_apply,
      cylinderDiagonalDiffeomorph_apply] at hact
    have hsnd := congrArg Prod.snd hact
    simp [cylinderAntipodal, cylinderDiagonal] at hsnd
    norm_num at hsnd

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderAntipodalGroup_ne_cylinderDiagonalGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderAntipodalGroup_ne_cylinderDiagonalGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderAntipodalGroup_ne_cylinderDiagonalGroup ``Submission.DifferentialGeometry.Geometry.cylinderAntipodalGroup_ne_cylinderDiagonalGroup

noncomputable def cylinderAntipodalGroupDiffeomorph
    (psi : cylinderAntipodalGroup) :
    (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)
      ≃ₘ⟮(𝓡 2).prod 𝓘(Real, Real), (𝓡 2).prod 𝓘(Real, Real)⟯
        Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real := by
  classical
  exact if psi.1 = 1 then
      Diffeomorph.refl ((𝓡 2).prod 𝓘(Real, Real))
        (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) ∞
    else cylinderAntipodalDiffeomorph

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderAntipodalGroupDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderAntipodalGroupDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderAntipodalGroupDiffeomorph ``Submission.DifferentialGeometry.Geometry.cylinderAntipodalGroupDiffeomorph

noncomputable def cylinderDiagonalGroupDiffeomorph
    (psi : cylinderDiagonalGroup) :
    (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)
      ≃ₘ⟮(𝓡 2).prod 𝓘(Real, Real), (𝓡 2).prod 𝓘(Real, Real)⟯
        Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real := by
  classical
  exact if psi.1 = 1 then
      Diffeomorph.refl ((𝓡 2).prod 𝓘(Real, Real))
        (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) ∞
    else cylinderDiagonalDiffeomorph

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderDiagonalGroupDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderDiagonalGroupDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderDiagonalGroupDiffeomorph ``Submission.DifferentialGeometry.Geometry.cylinderDiagonalGroupDiffeomorph

theorem cylinderAntipodalGroupDiffeomorph_apply
    (psi : cylinderAntipodalGroup)
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    cylinderAntipodalGroupDiffeomorph psi x = psi.1 x := by
  rcases cylinderAntipodalGroup_eq_one_or_generator psi with h | h
  · simp [cylinderAntipodalGroupDiffeomorph, h]
  · simp [cylinderAntipodalGroupDiffeomorph, h,
      cylinderAntipodalDiffeomorph_toEquiv_ne_one]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderAntipodalGroupDiffeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderAntipodalGroupDiffeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderAntipodalGroupDiffeomorph_apply ``Submission.DifferentialGeometry.Geometry.cylinderAntipodalGroupDiffeomorph_apply

theorem cylinderDiagonalGroupDiffeomorph_apply
    (psi : cylinderDiagonalGroup)
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    cylinderDiagonalGroupDiffeomorph psi x = psi.1 x := by
  rcases cylinderDiagonalGroup_eq_one_or_generator psi with h | h
  · simp [cylinderDiagonalGroupDiffeomorph, h]
  · simp [cylinderDiagonalGroupDiffeomorph, h,
      cylinderDiagonalDiffeomorph_toEquiv_ne_one]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderDiagonalGroupDiffeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderDiagonalGroupDiffeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderDiagonalGroupDiffeomorph_apply ``Submission.DifferentialGeometry.Geometry.cylinderDiagonalGroupDiffeomorph_apply

instance cylinderAntipodalGroupContMDiffConstSMul :
    ContMDiffConstSMul
      ((modelWithCornersSelf Real (EuclideanSpace Real (Fin 2))).prod
        (modelWithCornersSelf Real Real)) ∞
      cylinderAntipodalGroup
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) where
  contMDiff_const_smul psi := by
    change ContMDiff ((𝓡 2).prod 𝓘(Real, Real))
      ((𝓡 2).prod 𝓘(Real, Real)) ∞
      (psi.1 : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real → _)
    refine (cylinderAntipodalGroupDiffeomorph psi).contMDiff.congr ?_
    exact fun x => (cylinderAntipodalGroupDiffeomorph_apply psi x).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderAntipodalGroupContMDiffConstSMul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderAntipodalGroupContMDiffConstSMul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderAntipodalGroupContMDiffConstSMul ``Submission.DifferentialGeometry.Geometry.cylinderAntipodalGroupContMDiffConstSMul

instance cylinderDiagonalGroupContMDiffConstSMul :
    ContMDiffConstSMul
      ((modelWithCornersSelf Real (EuclideanSpace Real (Fin 2))).prod
        (modelWithCornersSelf Real Real)) ∞
      cylinderDiagonalGroup
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) where
  contMDiff_const_smul psi := by
    change ContMDiff ((𝓡 2).prod 𝓘(Real, Real))
      ((𝓡 2).prod 𝓘(Real, Real)) ∞
      (psi.1 : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real → _)
    refine (cylinderDiagonalGroupDiffeomorph psi).contMDiff.congr ?_
    exact fun x => (cylinderDiagonalGroupDiffeomorph_apply psi x).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderDiagonalGroupContMDiffConstSMul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderDiagonalGroupContMDiffConstSMul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderDiagonalGroupContMDiffConstSMul ``Submission.DifferentialGeometry.Geometry.cylinderDiagonalGroupContMDiffConstSMul

theorem cylinderAntipodalGroupDiffeomorph_pullbackMetric
    (psi : cylinderAntipodalGroup) :
    Diffeomorph.pullbackMetric roundThreeCylinderShrinkerMetric
        (cylinderAntipodalGroupDiffeomorph psi) =
      roundThreeCylinderShrinkerMetric := by
  rcases cylinderAntipodalGroup_eq_one_or_generator psi with h | h
  · simp [cylinderAntipodalGroupDiffeomorph, h,
      Diffeomorph.pullbackMetric_refl]
  · simpa [cylinderAntipodalGroupDiffeomorph, h,
      cylinderAntipodalDiffeomorph_toEquiv_ne_one] using
        cylinderAntipodalDiffeomorph_pullbackMetric

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderAntipodalGroupDiffeomorph_pullbackMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderAntipodalGroupDiffeomorph_pullbackMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderAntipodalGroupDiffeomorph_pullbackMetric ``Submission.DifferentialGeometry.Geometry.cylinderAntipodalGroupDiffeomorph_pullbackMetric

theorem cylinderDiagonalGroupDiffeomorph_pullbackMetric
    (psi : cylinderDiagonalGroup) :
    Diffeomorph.pullbackMetric roundThreeCylinderShrinkerMetric
        (cylinderDiagonalGroupDiffeomorph psi) =
      roundThreeCylinderShrinkerMetric := by
  rcases cylinderDiagonalGroup_eq_one_or_generator psi with h | h
  · simp [cylinderDiagonalGroupDiffeomorph, h,
      Diffeomorph.pullbackMetric_refl]
  · simpa [cylinderDiagonalGroupDiffeomorph, h,
      cylinderDiagonalDiffeomorph_toEquiv_ne_one] using
        cylinderDiagonalDiffeomorph_pullbackMetric

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderDiagonalGroupDiffeomorph_pullbackMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderDiagonalGroupDiffeomorph_pullbackMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderDiagonalGroupDiffeomorph_pullbackMetric ``Submission.DifferentialGeometry.Geometry.cylinderDiagonalGroupDiffeomorph_pullbackMetric

theorem cylinderAntipodalGroupDiffeomorph_potential
    (psi : cylinderAntipodalGroup) :
    roundThreeCylinderShrinkerPotential.comp
        (cylinderAntipodalGroupDiffeomorph psi).toContMDiffMap =
      roundThreeCylinderShrinkerPotential := by
  rcases cylinderAntipodalGroup_eq_one_or_generator psi with h | h
  · rw [show cylinderAntipodalGroupDiffeomorph psi =
        Diffeomorph.refl ((𝓡 2).prod 𝓘(Real, Real))
          (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) ∞ by
      simp [cylinderAntipodalGroupDiffeomorph, h]]
    apply ContMDiffMap.ext
    intro x
    rfl
  · simpa [cylinderAntipodalGroupDiffeomorph, h,
      cylinderAntipodalDiffeomorph_toEquiv_ne_one] using
        cylinderAntipodalDiffeomorph_potential

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderAntipodalGroupDiffeomorph_potential then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderAntipodalGroupDiffeomorph_potential"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderAntipodalGroupDiffeomorph_potential ``Submission.DifferentialGeometry.Geometry.cylinderAntipodalGroupDiffeomorph_potential

theorem cylinderDiagonalGroupDiffeomorph_potential
    (psi : cylinderDiagonalGroup) :
    roundThreeCylinderShrinkerPotential.comp
        (cylinderDiagonalGroupDiffeomorph psi).toContMDiffMap =
      roundThreeCylinderShrinkerPotential := by
  rcases cylinderDiagonalGroup_eq_one_or_generator psi with h | h
  · rw [show cylinderDiagonalGroupDiffeomorph psi =
        Diffeomorph.refl ((𝓡 2).prod 𝓘(Real, Real))
          (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) ∞ by
      simp [cylinderDiagonalGroupDiffeomorph, h]]
    apply ContMDiffMap.ext
    intro x
    rfl
  · simpa [cylinderDiagonalGroupDiffeomorph, h,
      cylinderDiagonalDiffeomorph_toEquiv_ne_one] using
        cylinderDiagonalDiffeomorph_potential

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderDiagonalGroupDiffeomorph_potential then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderDiagonalGroupDiffeomorph_potential"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderDiagonalGroupDiffeomorph_potential ``Submission.DifferentialGeometry.Geometry.cylinderDiagonalGroupDiffeomorph_potential

abbrev CylinderAntipodalQuotient := MulAction.orbitRel.Quotient
  cylinderAntipodalGroup
    (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.CylinderAntipodalQuotient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.CylinderAntipodalQuotient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.CylinderAntipodalQuotient ``Submission.DifferentialGeometry.Geometry.CylinderAntipodalQuotient

abbrev CylinderDiagonalQuotient := MulAction.orbitRel.Quotient
  cylinderDiagonalGroup
    (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.CylinderDiagonalQuotient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.CylinderDiagonalQuotient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.CylinderDiagonalQuotient ``Submission.DifferentialGeometry.Geometry.CylinderDiagonalQuotient

def cylinderAntipodalQuotientMap
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    CylinderAntipodalQuotient := Quotient.mk'' x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderAntipodalQuotientMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderAntipodalQuotientMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderAntipodalQuotientMap ``Submission.DifferentialGeometry.Geometry.cylinderAntipodalQuotientMap

def cylinderDiagonalQuotientMap
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    CylinderDiagonalQuotient := Quotient.mk'' x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderDiagonalQuotientMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderDiagonalQuotientMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderDiagonalQuotientMap ``Submission.DifferentialGeometry.Geometry.cylinderDiagonalQuotientMap

theorem cylinderAntipodalQuotientMap_isQuotientCoveringMap :
    IsQuotientCoveringMap cylinderAntipodalQuotientMap
      cylinderAntipodalGroup := by
  exact isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderAntipodalQuotientMap_isQuotientCoveringMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderAntipodalQuotientMap_isQuotientCoveringMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderAntipodalQuotientMap_isQuotientCoveringMap ``Submission.DifferentialGeometry.Geometry.cylinderAntipodalQuotientMap_isQuotientCoveringMap

theorem cylinderDiagonalQuotientMap_isQuotientCoveringMap :
    IsQuotientCoveringMap cylinderDiagonalQuotientMap
      cylinderDiagonalGroup := by
  exact isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderDiagonalQuotientMap_isQuotientCoveringMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderDiagonalQuotientMap_isQuotientCoveringMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderDiagonalQuotientMap_isQuotientCoveringMap ``Submission.DifferentialGeometry.Geometry.cylinderDiagonalQuotientMap_isQuotientCoveringMap

theorem cylinderAntipodalQuotientMap_isCoveringMap :
    IsCoveringMap cylinderAntipodalQuotientMap :=
  cylinderAntipodalQuotientMap_isQuotientCoveringMap.isCoveringMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderAntipodalQuotientMap_isCoveringMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderAntipodalQuotientMap_isCoveringMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderAntipodalQuotientMap_isCoveringMap ``Submission.DifferentialGeometry.Geometry.cylinderAntipodalQuotientMap_isCoveringMap

theorem cylinderDiagonalQuotientMap_isCoveringMap :
    IsCoveringMap cylinderDiagonalQuotientMap :=
  cylinderDiagonalQuotientMap_isQuotientCoveringMap.isCoveringMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderDiagonalQuotientMap_isCoveringMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderDiagonalQuotientMap_isCoveringMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderDiagonalQuotientMap_isCoveringMap ``Submission.DifferentialGeometry.Geometry.cylinderDiagonalQuotientMap_isCoveringMap

theorem cylinderAntipodalQuotientMap_isLocalDiffeomorph :
    IsLocalDiffeomorph ((𝓡 2).prod 𝓘(Real, Real))
      ((𝓡 2).prod 𝓘(Real, Real)) ∞ cylinderAntipodalQuotientMap := by
  exact MulAction.isLocalDiffeomorph_quotientMk_of_properlyDiscontinuousSMul
    ((𝓡 2).prod 𝓘(Real, Real))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderAntipodalQuotientMap_isLocalDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderAntipodalQuotientMap_isLocalDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderAntipodalQuotientMap_isLocalDiffeomorph ``Submission.DifferentialGeometry.Geometry.cylinderAntipodalQuotientMap_isLocalDiffeomorph

theorem cylinderDiagonalQuotientMap_isLocalDiffeomorph :
    IsLocalDiffeomorph ((𝓡 2).prod 𝓘(Real, Real))
      ((𝓡 2).prod 𝓘(Real, Real)) ∞ cylinderDiagonalQuotientMap := by
  exact MulAction.isLocalDiffeomorph_quotientMk_of_properlyDiscontinuousSMul
    ((𝓡 2).prod 𝓘(Real, Real))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderDiagonalQuotientMap_isLocalDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderDiagonalQuotientMap_isLocalDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderDiagonalQuotientMap_isLocalDiffeomorph ``Submission.DifferentialGeometry.Geometry.cylinderDiagonalQuotientMap_isLocalDiffeomorph

theorem cylinderAntipodalQuotientMap_surjective :
    Function.Surjective cylinderAntipodalQuotientMap :=
  cylinderAntipodalQuotientMap_isQuotientCoveringMap.surjective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderAntipodalQuotientMap_surjective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderAntipodalQuotientMap_surjective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderAntipodalQuotientMap_surjective ``Submission.DifferentialGeometry.Geometry.cylinderAntipodalQuotientMap_surjective

theorem cylinderDiagonalQuotientMap_surjective :
    Function.Surjective cylinderDiagonalQuotientMap :=
  cylinderDiagonalQuotientMap_isQuotientCoveringMap.surjective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderDiagonalQuotientMap_surjective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderDiagonalQuotientMap_surjective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderDiagonalQuotientMap_surjective ``Submission.DifferentialGeometry.Geometry.cylinderDiagonalQuotientMap_surjective

theorem cylinderAntipodalQuotientMap_eq_iff_mem_orbit
    {x y : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real} :
    cylinderAntipodalQuotientMap x = cylinderAntipodalQuotientMap y ↔
      x ∈ MulAction.orbit cylinderAntipodalGroup y :=
  cylinderAntipodalQuotientMap_isQuotientCoveringMap.apply_eq_iff_mem_orbit

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderAntipodalQuotientMap_eq_iff_mem_orbit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderAntipodalQuotientMap_eq_iff_mem_orbit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderAntipodalQuotientMap_eq_iff_mem_orbit ``Submission.DifferentialGeometry.Geometry.cylinderAntipodalQuotientMap_eq_iff_mem_orbit

theorem cylinderDiagonalQuotientMap_eq_iff_mem_orbit
    {x y : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real} :
    cylinderDiagonalQuotientMap x = cylinderDiagonalQuotientMap y ↔
      x ∈ MulAction.orbit cylinderDiagonalGroup y :=
  cylinderDiagonalQuotientMap_isQuotientCoveringMap.apply_eq_iff_mem_orbit

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderDiagonalQuotientMap_eq_iff_mem_orbit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderDiagonalQuotientMap_eq_iff_mem_orbit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderDiagonalQuotientMap_eq_iff_mem_orbit ``Submission.DifferentialGeometry.Geometry.cylinderDiagonalQuotientMap_eq_iff_mem_orbit

theorem cylinderAntipodalQuotientMap_eq_iff
    {x y : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real} :
    cylinderAntipodalQuotientMap x = cylinderAntipodalQuotientMap y ↔
      x = y ∨ x = cylinderAntipodalDiffeomorph y := by
  rw [cylinderAntipodalQuotientMap_eq_iff_mem_orbit]
  constructor
  · rintro ⟨psi, rfl⟩
    rcases cylinderAntipodalGroup_eq_one_or_generator psi with h | h
    · left
      change psi.1 y = y
      rw [h]
      rfl
    · right
      change psi.1 y = cylinderAntipodalDiffeomorph y
      rw [h]
      rfl
  · rintro (rfl | h)
    · exact MulAction.mem_orbit_self _
    · rw [h]
      refine ⟨cylinderAntipodalGroupGenerator, ?_⟩
      exact cylinderAntipodalGroupGenerator_smul y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderAntipodalQuotientMap_eq_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderAntipodalQuotientMap_eq_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderAntipodalQuotientMap_eq_iff ``Submission.DifferentialGeometry.Geometry.cylinderAntipodalQuotientMap_eq_iff

theorem cylinderDiagonalQuotientMap_eq_iff
    {x y : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real} :
    cylinderDiagonalQuotientMap x = cylinderDiagonalQuotientMap y ↔
      x = y ∨ x = cylinderDiagonalDiffeomorph y := by
  rw [cylinderDiagonalQuotientMap_eq_iff_mem_orbit]
  constructor
  · rintro ⟨psi, rfl⟩
    rcases cylinderDiagonalGroup_eq_one_or_generator psi with h | h
    · left
      change psi.1 y = y
      rw [h]
      rfl
    · right
      change psi.1 y = cylinderDiagonalDiffeomorph y
      rw [h]
      rfl
  · rintro (rfl | h)
    · exact MulAction.mem_orbit_self _
    · rw [h]
      refine ⟨cylinderDiagonalGroupGenerator, ?_⟩
      exact cylinderDiagonalGroupGenerator_smul y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderDiagonalQuotientMap_eq_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderDiagonalQuotientMap_eq_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderDiagonalQuotientMap_eq_iff ``Submission.DifferentialGeometry.Geometry.cylinderDiagonalQuotientMap_eq_iff

theorem cylinderAntipodalQuotientMap_metricFiberCompatible :
    metricFiberCompatible roundThreeCylinderShrinkerMetric
      cylinderAntipodalQuotientMap
      cylinderAntipodalQuotientMap_isLocalDiffeomorph := by
  intro x y hxy
  rcases cylinderAntipodalQuotientMap_eq_iff.mp hxy with h | h
  · subst x
    cases hxy
    rfl
  · subst x
    let Phi := cylinderAntipodalDiffeomorph
    have hcomp : cylinderAntipodalQuotientMap ∘
        (Phi : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real → _) =
      cylinderAntipodalQuotientMap := by
      funext z
      exact cylinderAntipodalQuotientMap_eq_iff.mpr (Or.inr rfl)
    exact localPushInner_eq_of_fiber_preserving_isometry
      roundThreeCylinderShrinkerMetric cylinderAntipodalQuotientMap
      cylinderAntipodalQuotientMap_isLocalDiffeomorph Phi hcomp
      cylinderAntipodalDiffeomorph_pullbackMetric y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderAntipodalQuotientMap_metricFiberCompatible then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderAntipodalQuotientMap_metricFiberCompatible"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderAntipodalQuotientMap_metricFiberCompatible ``Submission.DifferentialGeometry.Geometry.cylinderAntipodalQuotientMap_metricFiberCompatible

theorem cylinderDiagonalQuotientMap_metricFiberCompatible :
    metricFiberCompatible roundThreeCylinderShrinkerMetric
      cylinderDiagonalQuotientMap
      cylinderDiagonalQuotientMap_isLocalDiffeomorph := by
  intro x y hxy
  rcases cylinderDiagonalQuotientMap_eq_iff.mp hxy with h | h
  · subst x
    cases hxy
    rfl
  · subst x
    let Phi := cylinderDiagonalDiffeomorph
    have hcomp : cylinderDiagonalQuotientMap ∘
        (Phi : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real → _) =
      cylinderDiagonalQuotientMap := by
      funext z
      exact cylinderDiagonalQuotientMap_eq_iff.mpr (Or.inr rfl)
    exact localPushInner_eq_of_fiber_preserving_isometry
      roundThreeCylinderShrinkerMetric cylinderDiagonalQuotientMap
      cylinderDiagonalQuotientMap_isLocalDiffeomorph Phi hcomp
      cylinderDiagonalDiffeomorph_pullbackMetric y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderDiagonalQuotientMap_metricFiberCompatible then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderDiagonalQuotientMap_metricFiberCompatible"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderDiagonalQuotientMap_metricFiberCompatible ``Submission.DifferentialGeometry.Geometry.cylinderDiagonalQuotientMap_metricFiberCompatible

noncomputable def cylinderAntipodalQuotientMetric :
    SmoothRiemannianMetric ((𝓡 2).prod 𝓘(Real, Real))
      CylinderAntipodalQuotient :=
  descendedMetric roundThreeCylinderShrinkerMetric
    cylinderAntipodalQuotientMap
    cylinderAntipodalQuotientMap_isLocalDiffeomorph
    cylinderAntipodalQuotientMap_surjective
    cylinderAntipodalQuotientMap_metricFiberCompatible

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderAntipodalQuotientMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderAntipodalQuotientMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderAntipodalQuotientMetric ``Submission.DifferentialGeometry.Geometry.cylinderAntipodalQuotientMetric

noncomputable def cylinderDiagonalQuotientMetric :
    SmoothRiemannianMetric ((𝓡 2).prod 𝓘(Real, Real))
      CylinderDiagonalQuotient :=
  descendedMetric roundThreeCylinderShrinkerMetric
    cylinderDiagonalQuotientMap
    cylinderDiagonalQuotientMap_isLocalDiffeomorph
    cylinderDiagonalQuotientMap_surjective
    cylinderDiagonalQuotientMap_metricFiberCompatible

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderDiagonalQuotientMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderDiagonalQuotientMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderDiagonalQuotientMetric ``Submission.DifferentialGeometry.Geometry.cylinderDiagonalQuotientMetric

theorem localPullMetric_cylinderAntipodalQuotientMetric :
    localPullMetric cylinderAntipodalQuotientMetric
        cylinderAntipodalQuotientMap
        cylinderAntipodalQuotientMap_isLocalDiffeomorph =
      roundThreeCylinderShrinkerMetric :=
  localPullMetric_descendedMetric roundThreeCylinderShrinkerMetric
    cylinderAntipodalQuotientMap
    cylinderAntipodalQuotientMap_isLocalDiffeomorph
    cylinderAntipodalQuotientMap_surjective
    cylinderAntipodalQuotientMap_metricFiberCompatible

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.localPullMetric_cylinderAntipodalQuotientMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.localPullMetric_cylinderAntipodalQuotientMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.localPullMetric_cylinderAntipodalQuotientMetric ``Submission.DifferentialGeometry.Geometry.localPullMetric_cylinderAntipodalQuotientMetric

theorem localPullMetric_cylinderDiagonalQuotientMetric :
    localPullMetric cylinderDiagonalQuotientMetric
        cylinderDiagonalQuotientMap
        cylinderDiagonalQuotientMap_isLocalDiffeomorph =
      roundThreeCylinderShrinkerMetric :=
  localPullMetric_descendedMetric roundThreeCylinderShrinkerMetric
    cylinderDiagonalQuotientMap
    cylinderDiagonalQuotientMap_isLocalDiffeomorph
    cylinderDiagonalQuotientMap_surjective
    cylinderDiagonalQuotientMap_metricFiberCompatible

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.localPullMetric_cylinderDiagonalQuotientMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.localPullMetric_cylinderDiagonalQuotientMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.localPullMetric_cylinderDiagonalQuotientMetric ``Submission.DifferentialGeometry.Geometry.localPullMetric_cylinderDiagonalQuotientMetric

theorem cylinderAntipodalQuotientMetric_complete :
    RiemannianMetricComplete cylinderAntipodalQuotientMetric :=
  RiemannianMetricComplete.of_coveringMap_localPullMetric
    roundThreeCylinderShrinkerMetric cylinderAntipodalQuotientMetric
    cylinderAntipodalQuotientMap_isLocalDiffeomorph
    cylinderAntipodalQuotientMap_isCoveringMap
    cylinderAntipodalQuotientMap_surjective
    localPullMetric_cylinderAntipodalQuotientMetric
    roundThreeCylinderShrinkerMetric_complete

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderAntipodalQuotientMetric_complete then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderAntipodalQuotientMetric_complete"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderAntipodalQuotientMetric_complete ``Submission.DifferentialGeometry.Geometry.cylinderAntipodalQuotientMetric_complete

theorem cylinderDiagonalQuotientMetric_complete :
    RiemannianMetricComplete cylinderDiagonalQuotientMetric :=
  RiemannianMetricComplete.of_coveringMap_localPullMetric
    roundThreeCylinderShrinkerMetric cylinderDiagonalQuotientMetric
    cylinderDiagonalQuotientMap_isLocalDiffeomorph
    cylinderDiagonalQuotientMap_isCoveringMap
    cylinderDiagonalQuotientMap_surjective
    localPullMetric_cylinderDiagonalQuotientMetric
    roundThreeCylinderShrinkerMetric_complete

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderDiagonalQuotientMetric_complete then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderDiagonalQuotientMetric_complete"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderDiagonalQuotientMetric_complete ``Submission.DifferentialGeometry.Geometry.cylinderDiagonalQuotientMetric_complete

private theorem cylinderDiagonalOrbitRel_iff_threeSphereAwayFromRealProjectivePunctureOrbitRel
    (x y : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    MulAction.orbitRel cylinderDiagonalGroup _ x y ↔
      MulAction.orbitRel
        (realProjectiveSpaceAntipodalGroup
          (EuclideanSpace Real (Fin 4)))
        threeSphereAwayFromRealProjectivePuncture
        (twoSphereProdRealHomeomorphThreeSphereAwayFromRealProjectivePuncture x)
        (twoSphereProdRealHomeomorphThreeSphereAwayFromRealProjectivePuncture y) := by
  have hsource : MulAction.orbitRel cylinderDiagonalGroup _ x y ↔
      cylinderDiagonalQuotientMap x = cylinderDiagonalQuotientMap y :=
    ⟨Quotient.sound, Quotient.exact⟩
  have htarget :
      MulAction.orbitRel
          (realProjectiveSpaceAntipodalGroup
            (EuclideanSpace Real (Fin 4)))
          threeSphereAwayFromRealProjectivePuncture
          (twoSphereProdRealHomeomorphThreeSphereAwayFromRealProjectivePuncture x)
          (twoSphereProdRealHomeomorphThreeSphereAwayFromRealProjectivePuncture y) ↔
        realProjectiveSpaceQuotientMap
            ((twoSphereProdRealHomeomorphThreeSphereAwayFromRealProjectivePuncture x :
              threeSphereAwayFromRealProjectivePuncture) :
                Metric.sphere (0 : EuclideanSpace Real (Fin 4)) 1) =
          realProjectiveSpaceQuotientMap
            ((twoSphereProdRealHomeomorphThreeSphereAwayFromRealProjectivePuncture y :
              threeSphereAwayFromRealProjectivePuncture) :
                Metric.sphere (0 : EuclideanSpace Real (Fin 4)) 1) := by
    rw [SubMulAction.orbitRel_of_subMul]
    change MulAction.orbitRel
        (realProjectiveSpaceAntipodalGroup
          (EuclideanSpace Real (Fin 4)))
        (Metric.sphere (0 : EuclideanSpace Real (Fin 4)) 1)
        ((twoSphereProdRealHomeomorphThreeSphereAwayFromRealProjectivePuncture x :
          threeSphereAwayFromRealProjectivePuncture) :
            Metric.sphere (0 : EuclideanSpace Real (Fin 4)) 1)
        ((twoSphereProdRealHomeomorphThreeSphereAwayFromRealProjectivePuncture y :
          threeSphereAwayFromRealProjectivePuncture) :
            Metric.sphere (0 : EuclideanSpace Real (Fin 4)) 1) ↔ _
    exact ⟨Quotient.sound, Quotient.exact⟩
  rw [hsource, htarget, cylinderDiagonalQuotientMap_eq_iff,
    realProjectiveSpaceQuotientMap_eq_iff]
  constructor
  · rintro (rfl | hxy)
    · exact Or.inl rfl
    · right
      rw [hxy, cylinderDiagonalDiffeomorph_apply]
      exact congrArg Subtype.val
        (twoSphereProdRealHomeomorphThreeSphereAwayFromRealProjectivePuncture_diagonal y)
  · rintro (hxy | hxy)
    · left
      apply twoSphereProdRealHomeomorphThreeSphereAwayFromRealProjectivePuncture.injective
      exact Subtype.ext hxy
    · right
      apply twoSphereProdRealHomeomorphThreeSphereAwayFromRealProjectivePuncture.injective
      apply Subtype.ext
      apply Subtype.ext
      rw [cylinderDiagonalDiffeomorph_apply, cylinderDiagonal_apply,
        twoSphereProdRealHomeomorphThreeSphereAwayFromRealProjectivePuncture_diagonal]
      exact hxy

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.cylinderDiagonalOrbitRel_iff_threeSphereAwayFromRealProjectivePunctureOrbitRel
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.cylinderDiagonalOrbitRel_iff_threeSphereAwayFromRealProjectivePunctureOrbitRel target :: scope.openDecls } }

private noncomputable def cylinderDiagonalQuotientHomeomorphThreeSphereAwayFromRealProjectivePunctureQuotient :
    CylinderDiagonalQuotient ≃ₜ
      ThreeSphereAwayFromRealProjectivePunctureQuotient :=
  Homeomorph.Quotient.congr
    twoSphereProdRealHomeomorphThreeSphereAwayFromRealProjectivePuncture
    cylinderDiagonalOrbitRel_iff_threeSphereAwayFromRealProjectivePunctureOrbitRel

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.cylinderDiagonalQuotientHomeomorphThreeSphereAwayFromRealProjectivePunctureQuotient
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.cylinderDiagonalQuotientHomeomorphThreeSphereAwayFromRealProjectivePunctureQuotient target :: scope.openDecls } }

noncomputable def cylinderDiagonalQuotientHomeomorph :
    CylinderDiagonalQuotient ≃ₜ PuncturedRealProjectiveThreeSpace :=
  cylinderDiagonalQuotientHomeomorphThreeSphereAwayFromRealProjectivePunctureQuotient.trans
    threeSphereAwayFromRealProjectivePunctureQuotientHomeomorph

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderDiagonalQuotientHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderDiagonalQuotientHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderDiagonalQuotientHomeomorph ``Submission.DifferentialGeometry.Geometry.cylinderDiagonalQuotientHomeomorph

theorem cylinderDiagonalQuotientHomeomorph_apply
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    cylinderDiagonalQuotientHomeomorph (cylinderDiagonalQuotientMap x) =
      ⟨realProjectiveSpaceQuotientMap
          ((twoSphereProdRealHomeomorphThreeSphereAwayFromRealProjectivePuncture x :
            threeSphereAwayFromRealProjectivePuncture) :
              Metric.sphere (0 : EuclideanSpace Real (Fin 4)) 1),
        (twoSphereProdRealHomeomorphThreeSphereAwayFromRealProjectivePuncture x).2⟩ :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderDiagonalQuotientHomeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderDiagonalQuotientHomeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderDiagonalQuotientHomeomorph_apply ``Submission.DifferentialGeometry.Geometry.cylinderDiagonalQuotientHomeomorph_apply

theorem cylinderDiagonalQuotientHomeomorph_symm_apply
    (z : threeSphereAwayFromRealProjectivePuncture) :
    cylinderDiagonalQuotientHomeomorph.symm
        ⟨realProjectiveSpaceQuotientMap z.1, z.2⟩ =
      cylinderDiagonalQuotientMap
        (twoSphereProdRealHomeomorphThreeSphereAwayFromRealProjectivePuncture.symm z) := by
  apply cylinderDiagonalQuotientHomeomorph.injective
  rw [Homeomorph.apply_symm_apply,
    cylinderDiagonalQuotientHomeomorph_apply,
    Homeomorph.apply_symm_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderDiagonalQuotientHomeomorph_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderDiagonalQuotientHomeomorph_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderDiagonalQuotientHomeomorph_symm_apply ``Submission.DifferentialGeometry.Geometry.cylinderDiagonalQuotientHomeomorph_symm_apply

theorem cylinderAntipodalQuotientMap_lift_unique {Y : Type*}
    (F : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real → Y)
    (hinvariant : ∀ psi : cylinderAntipodalGroup, ∀ x, F (psi.1 x) = F x) :
    ∃! Fbar : CylinderAntipodalQuotient → Y,
      Fbar ∘ cylinderAntipodalQuotientMap = F := by
  let Fbar : CylinderAntipodalQuotient → Y :=
    Quotient.lift F (by
      intro x y hxy
      rcases hxy with ⟨psi, rfl⟩
      exact hinvariant psi y)
  refine ⟨Fbar, ?_, ?_⟩
  · funext x
    rfl
  · intro G hG
    funext q
    induction q using Quotient.inductionOn with
    | _ x => exact congrFun hG x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderAntipodalQuotientMap_lift_unique then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderAntipodalQuotientMap_lift_unique"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderAntipodalQuotientMap_lift_unique ``Submission.DifferentialGeometry.Geometry.cylinderAntipodalQuotientMap_lift_unique

theorem cylinderDiagonalQuotientMap_lift_unique {Y : Type*}
    (F : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real → Y)
    (hinvariant : ∀ psi : cylinderDiagonalGroup, ∀ x, F (psi.1 x) = F x) :
    ∃! Fbar : CylinderDiagonalQuotient → Y,
      Fbar ∘ cylinderDiagonalQuotientMap = F := by
  let Fbar : CylinderDiagonalQuotient → Y :=
    Quotient.lift F (by
      intro x y hxy
      rcases hxy with ⟨psi, rfl⟩
      exact hinvariant psi y)
  refine ⟨Fbar, ?_, ?_⟩
  · funext x
    rfl
  · intro G hG
    funext q
    induction q using Quotient.inductionOn with
    | _ x => exact congrFun hG x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderDiagonalQuotientMap_lift_unique then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderDiagonalQuotientMap_lift_unique"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderDiagonalQuotientMap_lift_unique ``Submission.DifferentialGeometry.Geometry.cylinderDiagonalQuotientMap_lift_unique

private theorem cylinderAntipodalPotential_respects
    {x y : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real}
    (hxy : MulAction.orbitRel cylinderAntipodalGroup _ x y) :
    roundThreeCylinderShrinkerPotential x =
      roundThreeCylinderShrinkerPotential y := by
  rcases hxy with ⟨psi, rfl⟩
  rcases cylinderAntipodalGroup_eq_one_or_generator psi with h | h
  · change roundThreeCylinderShrinkerPotential (psi.1 y) = _
    rw [h]
    rfl
  · change roundThreeCylinderShrinkerPotential (psi.1 y) = _
    rw [h]
    exact cylinderAntipodal_potential y

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.cylinderAntipodalPotential_respects
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.cylinderAntipodalPotential_respects target :: scope.openDecls } }

private theorem cylinderDiagonalPotential_respects
    {x y : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real}
    (hxy : MulAction.orbitRel cylinderDiagonalGroup _ x y) :
    roundThreeCylinderShrinkerPotential x =
      roundThreeCylinderShrinkerPotential y := by
  rcases hxy with ⟨psi, rfl⟩
  rcases cylinderDiagonalGroup_eq_one_or_generator psi with h | h
  · change roundThreeCylinderShrinkerPotential (psi.1 y) = _
    rw [h]
    rfl
  · change roundThreeCylinderShrinkerPotential (psi.1 y) = _
    rw [h]
    exact cylinderDiagonal_potential y

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.cylinderDiagonalPotential_respects
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.cylinderDiagonalPotential_respects target :: scope.openDecls } }

private noncomputable def cylinderAntipodalQuotientPotentialFn :
    CylinderAntipodalQuotient → Real :=
  Quotient.lift roundThreeCylinderShrinkerPotential
    (fun _ _ h => cylinderAntipodalPotential_respects h)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.cylinderAntipodalQuotientPotentialFn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.cylinderAntipodalQuotientPotentialFn target :: scope.openDecls } }

private noncomputable def cylinderDiagonalQuotientPotentialFn :
    CylinderDiagonalQuotient → Real :=
  Quotient.lift roundThreeCylinderShrinkerPotential
    (fun _ _ h => cylinderDiagonalPotential_respects h)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.cylinderDiagonalQuotientPotentialFn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.cylinderDiagonalQuotientPotentialFn target :: scope.openDecls } }

noncomputable def cylinderAntipodalQuotientPotential :
    C^∞⟮(𝓡 2).prod 𝓘(Real, Real), CylinderAntipodalQuotient; Real⟯ :=
  ⟨cylinderAntipodalQuotientPotentialFn,
    cylinderAntipodalQuotientMap_isLocalDiffeomorph.contMDiff_of_comp_of_surjective
      cylinderAntipodalQuotientMap_surjective (by
        have heq : cylinderAntipodalQuotientPotentialFn ∘
            cylinderAntipodalQuotientMap = roundThreeCylinderShrinkerPotential := by
          funext x
          rfl
        rw [heq]
        exact roundThreeCylinderShrinkerPotential.contMDiff)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderAntipodalQuotientPotential then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderAntipodalQuotientPotential"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderAntipodalQuotientPotential ``Submission.DifferentialGeometry.Geometry.cylinderAntipodalQuotientPotential

noncomputable def cylinderDiagonalQuotientPotential :
    C^∞⟮(𝓡 2).prod 𝓘(Real, Real), CylinderDiagonalQuotient; Real⟯ :=
  ⟨cylinderDiagonalQuotientPotentialFn,
    cylinderDiagonalQuotientMap_isLocalDiffeomorph.contMDiff_of_comp_of_surjective
      cylinderDiagonalQuotientMap_surjective (by
        have heq : cylinderDiagonalQuotientPotentialFn ∘
            cylinderDiagonalQuotientMap = roundThreeCylinderShrinkerPotential := by
          funext x
          rfl
        rw [heq]
        exact roundThreeCylinderShrinkerPotential.contMDiff)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderDiagonalQuotientPotential then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderDiagonalQuotientPotential"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderDiagonalQuotientPotential ``Submission.DifferentialGeometry.Geometry.cylinderDiagonalQuotientPotential

theorem cylinderAntipodalQuotientPotential_apply
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    cylinderAntipodalQuotientPotential (cylinderAntipodalQuotientMap x) =
      roundThreeCylinderShrinkerPotential x :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderAntipodalQuotientPotential_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderAntipodalQuotientPotential_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderAntipodalQuotientPotential_apply ``Submission.DifferentialGeometry.Geometry.cylinderAntipodalQuotientPotential_apply

theorem cylinderDiagonalQuotientPotential_apply
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    cylinderDiagonalQuotientPotential (cylinderDiagonalQuotientMap x) =
      roundThreeCylinderShrinkerPotential x :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderDiagonalQuotientPotential_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderDiagonalQuotientPotential_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderDiagonalQuotientPotential_apply ``Submission.DifferentialGeometry.Geometry.cylinderDiagonalQuotientPotential_apply

theorem cylinderAntipodalQuotientPotential_continuous :
    Continuous cylinderAntipodalQuotientPotential := by
  exact cylinderAntipodalQuotientPotential.contMDiff.continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderAntipodalQuotientPotential_continuous then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderAntipodalQuotientPotential_continuous"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderAntipodalQuotientPotential_continuous ``Submission.DifferentialGeometry.Geometry.cylinderAntipodalQuotientPotential_continuous

theorem cylinderDiagonalQuotientPotential_continuous :
    Continuous cylinderDiagonalQuotientPotential := by
  exact cylinderDiagonalQuotientPotential.contMDiff.continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderDiagonalQuotientPotential_continuous then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderDiagonalQuotientPotential_continuous"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderDiagonalQuotientPotential_continuous ``Submission.DifferentialGeometry.Geometry.cylinderDiagonalQuotientPotential_continuous

theorem normalizedGradientRicciSoliton_cylinderAntipodalQuotient :
    normalizedGradientRicciSoliton cylinderAntipodalQuotientMetric
      cylinderAntipodalQuotientPotential :=
  normalizedGradientRicciSoliton_of_surjective_localPullMetric
    normalizedGradientRicciSoliton_roundThreeCylinder
    cylinderAntipodalQuotientMetric_complete
    cylinderAntipodalQuotientMap_isLocalDiffeomorph
    cylinderAntipodalQuotientMap_surjective
    localPullMetric_cylinderAntipodalQuotientMetric
    (fun x ↦ (cylinderAntipodalQuotientPotential_apply x).symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.normalizedGradientRicciSoliton_cylinderAntipodalQuotient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.normalizedGradientRicciSoliton_cylinderAntipodalQuotient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.normalizedGradientRicciSoliton_cylinderAntipodalQuotient ``Submission.DifferentialGeometry.Geometry.normalizedGradientRicciSoliton_cylinderAntipodalQuotient

theorem normalizedGradientRicciSoliton_cylinderDiagonalQuotient :
    normalizedGradientRicciSoliton cylinderDiagonalQuotientMetric
      cylinderDiagonalQuotientPotential :=
  normalizedGradientRicciSoliton_of_surjective_localPullMetric
    normalizedGradientRicciSoliton_roundThreeCylinder
    cylinderDiagonalQuotientMetric_complete
    cylinderDiagonalQuotientMap_isLocalDiffeomorph
    cylinderDiagonalQuotientMap_surjective
    localPullMetric_cylinderDiagonalQuotientMetric
    (fun x ↦ (cylinderDiagonalQuotientPotential_apply x).symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.normalizedGradientRicciSoliton_cylinderDiagonalQuotient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.normalizedGradientRicciSoliton_cylinderDiagonalQuotient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.normalizedGradientRicciSoliton_cylinderDiagonalQuotient ``Submission.DifferentialGeometry.Geometry.normalizedGradientRicciSoliton_cylinderDiagonalQuotient

private theorem cylinderAntipodalToRealProjectivePlaneProduct_respects
    {x y : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real}
    (hxy : MulAction.orbitRel cylinderAntipodalGroup _ x y) :
    (realProjectivePlaneQuotientMap x.1, x.2) =
      (realProjectivePlaneQuotientMap y.1, y.2) := by
  rcases hxy with ⟨psi, rfl⟩
  rcases cylinderAntipodalGroup_eq_one_or_generator psi with hpsi | hpsi
  · change (realProjectivePlaneQuotientMap (psi.1 y).1, (psi.1 y).2) = _
    rw [hpsi]
    rfl
  · change (realProjectivePlaneQuotientMap (psi.1 y).1, (psi.1 y).2) = _
    rw [hpsi]
    rw [Diffeomorph.coe_toEquiv, cylinderAntipodalDiffeomorph_apply]
    apply Prod.ext
    · rw [realProjectivePlaneQuotientMap_eq_iff]
      right
      exact realProjectivePlaneAntipodalHomeomorph_coe y.1
    · rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.cylinderAntipodalToRealProjectivePlaneProduct_respects
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.cylinderAntipodalToRealProjectivePlaneProduct_respects target :: scope.openDecls } }

private def cylinderAntipodalToRealProjectivePlaneProduct :
    CylinderAntipodalQuotient → RealProjectivePlane × Real :=
  Quotient.lift
    (fun x => (realProjectivePlaneQuotientMap x.1, x.2))
    (fun _ _ hxy =>
      cylinderAntipodalToRealProjectivePlaneProduct_respects hxy)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.cylinderAntipodalToRealProjectivePlaneProduct
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.cylinderAntipodalToRealProjectivePlaneProduct target :: scope.openDecls } }

private theorem realProjectivePlaneProductToCylinderAntipodal_respects
    (s : Real) {x y : Metric.sphere
      (0 : EuclideanSpace Real (Fin 3)) 1}
    (hxy : MulAction.orbitRel realProjectivePlaneAntipodalGroup _ x y) :
    cylinderAntipodalQuotientMap (x, s) =
      cylinderAntipodalQuotientMap (y, s) := by
  have hquotient : realProjectivePlaneQuotientMap x =
      realProjectivePlaneQuotientMap y :=
    Quotient.sound hxy
  rw [realProjectivePlaneQuotientMap_eq_iff] at hquotient
  rcases hquotient with rfl | hxy
  · rfl
  · rw [cylinderAntipodalQuotientMap_eq_iff]
    right
    rw [cylinderAntipodalDiffeomorph_apply]
    apply Prod.ext
    · exact Subtype.ext hxy
    · rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.realProjectivePlaneProductToCylinderAntipodal_respects
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.realProjectivePlaneProductToCylinderAntipodal_respects target :: scope.openDecls } }

private def realProjectivePlaneProductToCylinderAntipodal :
    RealProjectivePlane × Real → CylinderAntipodalQuotient :=
  fun q => Quotient.lift
    (fun x => cylinderAntipodalQuotientMap (x, q.2))
    (fun _ _ hxy =>
      realProjectivePlaneProductToCylinderAntipodal_respects q.2 hxy) q.1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.realProjectivePlaneProductToCylinderAntipodal
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.realProjectivePlaneProductToCylinderAntipodal target :: scope.openDecls } }

private noncomputable def cylinderAntipodalQuotientEquivRealProjectivePlaneProd :
    CylinderAntipodalQuotient ≃ RealProjectivePlane × Real where
  toFun := cylinderAntipodalToRealProjectivePlaneProduct
  invFun := realProjectivePlaneProductToCylinderAntipodal
  left_inv q := by
    induction q using Quotient.inductionOn with
    | _ x => rfl
  right_inv q := by
    rcases q with ⟨q, s⟩
    induction q using Quotient.inductionOn with
    | _ x => rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.cylinderAntipodalQuotientEquivRealProjectivePlaneProd
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.cylinderAntipodalQuotientEquivRealProjectivePlaneProd target :: scope.openDecls } }

private theorem cylinderAntipodalToRealProjectivePlaneProduct_continuous :
    Continuous cylinderAntipodalToRealProjectivePlaneProduct := by
  exact ((continuous_quotient_mk'.comp continuous_fst).prodMk
    continuous_snd).quotient_lift
      (fun x y hxy =>
        cylinderAntipodalToRealProjectivePlaneProduct_respects hxy)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.cylinderAntipodalToRealProjectivePlaneProduct_continuous
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.cylinderAntipodalToRealProjectivePlaneProduct_continuous target :: scope.openDecls } }

private theorem realProjectivePlaneProductToCylinderAntipodal_continuous :
    Continuous realProjectivePlaneProductToCylinderAntipodal := by
  let qmap : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real →
      RealProjectivePlane × Real :=
    Prod.map realProjectivePlaneQuotientMap id
  have hqmap : IsOpenQuotientMap qmap :=
    realProjectivePlaneQuotientMap_isOpenQuotientMap.prodMap
      IsOpenQuotientMap.id
  rw [hqmap.isQuotientMap.continuous_iff]
  convert continuous_quotient_mk' using 1
  ext x
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.realProjectivePlaneProductToCylinderAntipodal_continuous
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.realProjectivePlaneProductToCylinderAntipodal_continuous target :: scope.openDecls } }

noncomputable def cylinderAntipodalQuotientHomeomorph :
    CylinderAntipodalQuotient ≃ₜ RealProjectivePlane × Real where
  toEquiv := cylinderAntipodalQuotientEquivRealProjectivePlaneProd
  continuous_toFun :=
    cylinderAntipodalToRealProjectivePlaneProduct_continuous
  continuous_invFun :=
    realProjectivePlaneProductToCylinderAntipodal_continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderAntipodalQuotientHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderAntipodalQuotientHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderAntipodalQuotientHomeomorph ``Submission.DifferentialGeometry.Geometry.cylinderAntipodalQuotientHomeomorph

theorem cylinderAntipodalQuotientHomeomorph_apply
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    cylinderAntipodalQuotientHomeomorph
        (cylinderAntipodalQuotientMap x) =
      (realProjectivePlaneQuotientMap x.1, x.2) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderAntipodalQuotientHomeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderAntipodalQuotientHomeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderAntipodalQuotientHomeomorph_apply ``Submission.DifferentialGeometry.Geometry.cylinderAntipodalQuotientHomeomorph_apply

theorem cylinderAntipodalQuotientHomeomorph_symm_apply
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) (s : Real) :
    cylinderAntipodalQuotientHomeomorph.symm
        (realProjectivePlaneQuotientMap x, s) =
      cylinderAntipodalQuotientMap (x, s) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderAntipodalQuotientHomeomorph_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderAntipodalQuotientHomeomorph_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderAntipodalQuotientHomeomorph_symm_apply ``Submission.DifferentialGeometry.Geometry.cylinderAntipodalQuotientHomeomorph_symm_apply

theorem noncompactSpace_orbitRelQuotient_of_roundThreeCylinderShrinkerPotential_invariant
    {Gamma : Type*} [Group Gamma]
    [MulAction Gamma
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)]
    (hpotential : ∀ (gamma : Gamma) x,
      roundThreeCylinderShrinkerPotential (gamma • x) =
        roundThreeCylinderShrinkerPotential x) :
    NoncompactSpace (MulAction.orbitRel.Quotient Gamma
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)) := by
  let Fbar : MulAction.orbitRel.Quotient Gamma
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) → Real :=
    Quotient.lift roundThreeCylinderShrinkerPotential (by
      intro x y hxy
      rcases hxy with ⟨gamma, rfl⟩
      exact hpotential gamma y)
  have hFbar : Continuous Fbar :=
    roundThreeCylinderShrinkerPotential.contMDiff.continuous.quotient_lift
      (by
        intro x y hxy
        rcases hxy with ⟨gamma, rfl⟩
        exact hpotential gamma y)
  refine not_compactSpace_iff.mp ?_
  intro hcompact
  let _ : CompactSpace (MulAction.orbitRel.Quotient Gamma
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)) := hcompact
  obtain ⟨C, hC⟩ := (isCompact_range hFbar).bddAbove
  let y : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 :=
    ⟨EuclideanSpace.single 0 1, by simp [PiLp.norm_single]⟩
  have hle : Fbar (Quotient.mk'' (y, 2 * (|C| + 1))) ≤ C :=
    hC ⟨_, rfl⟩
  change roundThreeCylinderShrinkerPotential (y, 2 * (|C| + 1)) ≤ C at hle
  rw [roundThreeCylinderShrinkerPotential_apply] at hle
  nlinarith [abs_nonneg C, le_abs_self C]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.noncompactSpace_orbitRelQuotient_of_roundThreeCylinderShrinkerPotential_invariant then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.noncompactSpace_orbitRelQuotient_of_roundThreeCylinderShrinkerPotential_invariant"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.noncompactSpace_orbitRelQuotient_of_roundThreeCylinderShrinkerPotential_invariant ``Submission.DifferentialGeometry.Geometry.noncompactSpace_orbitRelQuotient_of_roundThreeCylinderShrinkerPotential_invariant

def roundThreeCylinderSolitonAutomorphism
    (psi : Equiv.Perm
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)) : Prop :=
  ∃ Phi :
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)
        ≃ₘ⟮(𝓡 2).prod 𝓘(Real, Real), (𝓡 2).prod 𝓘(Real, Real)⟯
          Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real,
    Phi.toEquiv = psi ∧
      Diffeomorph.pullbackMetric roundThreeCylinderShrinkerMetric Phi =
        roundThreeCylinderShrinkerMetric ∧
      ∀ x, roundThreeCylinderShrinkerPotential (Phi x) =
        roundThreeCylinderShrinkerPotential x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.roundThreeCylinderSolitonAutomorphism then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.roundThreeCylinderSolitonAutomorphism"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.roundThreeCylinderSolitonAutomorphism ``Submission.DifferentialGeometry.Geometry.roundThreeCylinderSolitonAutomorphism

theorem noncompactSpace_orbitRelQuotient_of_roundThreeCylinderSolitonAutomorphism
    (Gamma : Subgroup (Equiv.Perm
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)))
    (hsoliton : ∀ gamma : Gamma,
      roundThreeCylinderSolitonAutomorphism gamma.1) :
    NoncompactSpace (MulAction.orbitRel.Quotient Gamma
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)) := by
  apply noncompactSpace_orbitRelQuotient_of_roundThreeCylinderShrinkerPotential_invariant
  intro gamma x
  obtain ⟨Phi, hPhi, _, hpotential⟩ := hsoliton gamma
  change roundThreeCylinderShrinkerPotential (gamma.1 x) = _
  rw [← hPhi]
  exact hpotential x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.noncompactSpace_orbitRelQuotient_of_roundThreeCylinderSolitonAutomorphism then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.noncompactSpace_orbitRelQuotient_of_roundThreeCylinderSolitonAutomorphism"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.noncompactSpace_orbitRelQuotient_of_roundThreeCylinderSolitonAutomorphism ``Submission.DifferentialGeometry.Geometry.noncompactSpace_orbitRelQuotient_of_roundThreeCylinderSolitonAutomorphism

private theorem roundThreeCylinderSolitonAutomorphism_mem_cases
    (Gamma : Subgroup (Equiv.Perm
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)))
    (hsoliton : ∀ gamma : Gamma,
      roundThreeCylinderSolitonAutomorphism gamma.1)
    (hfree : ∀ (gamma : Gamma)
      (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real),
      gamma.1 x = x → gamma = 1)
    (gamma : Gamma) :
    gamma.1 = 1 ∨
      gamma.1 = cylinderAntipodalDiffeomorph.toEquiv ∨
      gamma.1 = cylinderDiagonalDiffeomorph.toEquiv := by
  classical
  let : Fact
      (Module.finrank Real (EuclideanSpace Real (Fin 3)) = 2 + 1) :=
    ⟨by simp⟩
  choose Phi hPhiEquiv hPhiMetric hPhiPotential using hsoliton
  have hPhiApply (gamma : Gamma) (x : Metric.sphere
      (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
      Phi gamma x = gamma.1 x := by
    change (Phi gamma).toEquiv x = gamma.1 x
    exact congrArg (fun e : Equiv.Perm
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) => e x)
      (hPhiEquiv gamma)
  let phi (gamma : Gamma) :=
    roundThreeCylinderCentralSliceDiffeomorph (Phi gamma) (hPhiPotential gamma)
  have hphiMetric (gamma : Gamma) :
      Diffeomorph.pullbackMetric roundTwoSphereShrinkerMetric (phi gamma) =
        roundTwoSphereShrinkerMetric :=
    roundThreeCylinderCentralSliceDiffeomorph_pullbackMetric
      (Phi gamma) (hPhiPotential gamma) (hPhiMetric gamma)
  have hphiOne (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) :
      phi 1 x = x := by
    have h := roundThreeCylinderCentralSliceDiffeomorph_apply
      (Phi 1) (hPhiPotential 1) x
    rw [hPhiApply] at h
    have h' := congrArg Prod.fst h
    simpa using h'.symm
  have hphiMul (gamma delta : Gamma)
      (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) :
      phi (gamma * delta) x = phi gamma (phi delta x) := by
    have hprod := roundThreeCylinderCentralSliceDiffeomorph_apply
      (Phi (gamma * delta)) (hPhiPotential (gamma * delta)) x
    have hdelta := roundThreeCylinderCentralSliceDiffeomorph_apply
      (Phi delta) (hPhiPotential delta) x
    have hgamma := roundThreeCylinderCentralSliceDiffeomorph_apply
      (Phi gamma) (hPhiPotential gamma) (phi delta x)
    rw [hPhiApply] at hprod hdelta hgamma
    change gamma.1 (delta.1 (x, 0)) = _ at hprod
    rw [hdelta, hgamma] at hprod
    exact (congrArg Prod.fst hprod).symm
  have hphiIso (gamma : Gamma)
      (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1)
      (v w : TangentSpace (𝓡 2) x) :
      roundTwoSphereShrinkerMetric.inner x v w =
        roundTwoSphereShrinkerMetric.inner (phi gamma x)
          (mfderiv (𝓡 2) (𝓡 2) (phi gamma) x v)
          (mfderiv (𝓡 2) (𝓡 2) (phi gamma) x w) := by
    have h := Diffeomorph.pullbackMetric_inner
      roundTwoSphereShrinkerMetric (phi gamma) x v w
    rw [hphiMetric gamma] at h
    exact h
  have hphiFree : ∀ (gamma : Gamma)
      (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1),
      phi gamma x = x → gamma = 1 := by
    intro gamma x hx
    have h := roundThreeCylinderCentralSliceDiffeomorph_apply
      (Phi gamma) (hPhiPotential gamma) x
    rw [hPhiApply] at h
    have hfix : gamma.1 (x, 0) = (x, 0) := by
      rw [h]
      exact Prod.ext hx rfl
    exact hfree gamma (x, 0) hfix
  obtain ⟨rho, hrho⟩ := orth_rep_of_iso
    (E := EuclideanSpace Real (Fin 3)) (n := 2)
    phi (by norm_num) hphiOne hphiMul (by
      intro gamma x v w
      have h := hphiIso gamma x v w
      have hscaled := h
      simp only [roundTwoSphereShrinkerMetric, roundSphereShrinkerMetric,
        scaleMetric_inner] at hscaled
      exact mul_left_cancel₀
        (ne_of_gt (sq_pos_of_pos (roundSphereShrinkerRadius_pos (n := 2) (by decide))))
        hscaled)
  have hphiFree' : ∀ (gamma : Gamma)
      (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1),
      sphereDiffeo (n := 2) (rho gamma) x = x → gamma = 1 := by
    intro gamma x hx
    apply hphiFree gamma x
    rw [← hrho gamma]
    exact hx
  have hcase (gamma : Gamma) :
      rho gamma = 1 ∨ rho gamma = LinearIsometryEquiv.neg Real := by
    exact orth_rep_apply_eq_one_or_neg_of_free_sphere_action rho hphiFree' gamma
  have hphiRep (gamma : Gamma) :
      sphereDiffeo (n := 2) (rho gamma) = phi gamma := hrho gamma
  have hcases (gamma : Gamma) :
      gamma.1 = 1 ∨ gamma.1 = cylinderAntipodalDiffeomorph.toEquiv ∨
        gamma.1 = cylinderDiagonalDiffeomorph.toEquiv := by
    by_cases hgamma : gamma = 1
    · left
      subst gamma
      rfl
    · have hnormal := roundThreeCylinderDiffeomorph_eq_prodCongr_refl_or_neg
        (Phi gamma) (hPhiPotential gamma) (hPhiMetric gamma)
      rcases hnormal with hnormal | hnormal
      · rcases hcase gamma with hρ | hρ
        · have hφ : ∀ x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1,
              phi gamma x = x := by
            intro x
            rw [← hphiRep gamma, hρ]
            apply Subtype.ext
            rfl
          have hmap : gamma.1 = 1 := by
            apply Equiv.ext
            intro x
            rw [← hPhiEquiv gamma, hnormal]
            change (phi gamma x.1, x.2) = x
            exact Prod.ext (hφ x.1) (by rfl)
          exact (hgamma (Subtype.ext hmap)).elim
        · right; left
          apply Equiv.ext
          intro x
          rw [← hPhiEquiv gamma, hnormal]
          rw [Diffeomorph.coe_toEquiv, Diffeomorph.coe_prodCongr]
          change (phi gamma x.1, x.2) = _
          have hφ : phi gamma x.1 = -x.1 := by
            rw [← hphiRep gamma, hρ]
            apply Subtype.ext
            rfl
          change (phi gamma x.1, x.2) = cylinderAntipodalDiffeomorph x
          rw [cylinderAntipodalDiffeomorph_apply]
          exact Prod.ext hφ (by rfl)
      · rcases hcase gamma with hρ | hρ
        · have hφ : ∀ x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1,
              phi gamma x = x := by
            intro x
            rw [← hphiRep gamma, hρ]
            apply Subtype.ext
            rfl
          have hfix : gamma.1 (⟨EuclideanSpace.single 0 1, by
              simp [PiLp.norm_single]⟩, 0) =
              (⟨EuclideanSpace.single 0 1, by simp [PiLp.norm_single]⟩, 0) := by
            rw [← hPhiEquiv gamma, hnormal]
            rw [Diffeomorph.coe_toEquiv, Diffeomorph.coe_prodCongr]
            change (phi gamma _, (ContinuousLinearEquiv.neg Real) 0) = _
            exact Prod.ext (hφ _) (by simp only [map_zero])
          exact (hgamma (hfree gamma _ hfix)).elim
        · right; right
          apply Equiv.ext
          intro x
          rw [← hPhiEquiv gamma, hnormal]
          rw [Diffeomorph.coe_toEquiv, Diffeomorph.coe_prodCongr]
          change (phi gamma x.1, (ContinuousLinearEquiv.neg Real) x.2) = _
          have hφ : phi gamma x.1 = -x.1 := by
            rw [← hphiRep gamma, hρ]
            apply Subtype.ext
            rfl
          rw [Diffeomorph.coe_toEquiv]
          change (phi gamma x.1, (ContinuousLinearEquiv.neg Real) x.2) =
            cylinderDiagonalDiffeomorph x
          rw [cylinderDiagonalDiffeomorph_apply]
          exact Prod.ext hφ (by simp [cylinderDiagonal])
  exact hcases gamma

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.roundThreeCylinderSolitonAutomorphism_mem_cases
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.roundThreeCylinderSolitonAutomorphism_mem_cases target :: scope.openDecls } }

theorem roundThreeCylinderSolitonAutomorphism_subgroup_eq_bot_or_antipodal_or_diagonal
    (Gamma : Subgroup (Equiv.Perm
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)))
    (hsoliton : ∀ gamma : Gamma,
      roundThreeCylinderSolitonAutomorphism gamma.1)
    (hfree : ∀ (gamma : Gamma)
      (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real),
      gamma.1 x = x → gamma = 1) :
    Gamma = ⊥ ∨ Gamma = cylinderAntipodalGroup ∨
      Gamma = cylinderDiagonalGroup := by
  classical
  have hnotBoth : ∀ (ha : cylinderAntipodalDiffeomorph.toEquiv ∈ Gamma)
      (hd : cylinderDiagonalDiffeomorph.toEquiv ∈ Gamma), False := by
    intro ha hd
    let ga : Gamma := ⟨cylinderAntipodalDiffeomorph.toEquiv, ha⟩
    let gd : Gamma := ⟨cylinderDiagonalDiffeomorph.toEquiv, hd⟩
    let y : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 :=
      ⟨EuclideanSpace.single 0 1, by simp [PiLp.norm_single]⟩
    have hfix : (ga * gd).1 (y, 0) = (y, 0) := by
      change ga.1 (gd.1 (y, 0)) = (y, 0)
      change cylinderAntipodalDiffeomorph.toEquiv
          (cylinderDiagonalDiffeomorph.toEquiv (y, 0)) = (y, 0)
      rw [Diffeomorph.coe_toEquiv, Diffeomorph.coe_toEquiv,
        cylinderDiagonalDiffeomorph_apply, cylinderAntipodalDiffeomorph_apply]
      simp [cylinderAntipodal, cylinderDiagonal]
    have hprod : ga * gd = 1 := hfree (ga * gd) (y, 0) hfix
    have hact := congrArg (fun gamma : Gamma => gamma.1 (y, 1)) hprod
    change ga.1 (gd.1 (y, 1)) = (y, 1) at hact
    change cylinderAntipodalDiffeomorph.toEquiv
        (cylinderDiagonalDiffeomorph.toEquiv (y, 1)) = (y, 1) at hact
    rw [Diffeomorph.coe_toEquiv, Diffeomorph.coe_toEquiv,
      cylinderDiagonalDiffeomorph_apply, cylinderAntipodalDiffeomorph_apply] at hact
    have hsnd := congrArg Prod.snd hact
    simp [cylinderAntipodal, cylinderDiagonal] at hsnd
    norm_num at hsnd
  by_cases ha : ∃ gamma : Gamma,
      gamma.1 = cylinderAntipodalDiffeomorph.toEquiv
  · obtain ⟨gammaA, hgammaA⟩ := ha
    have ha_mem : cylinderAntipodalDiffeomorph.toEquiv ∈ Gamma := by
      simpa [hgammaA] using gammaA.property
    have hnotD : ∀ gamma : Gamma,
        gamma.1 ≠ cylinderDiagonalDiffeomorph.toEquiv := by
      intro gamma hgamma
      apply hnotBoth ha_mem
      simpa [hgamma] using gamma.property
    right; left
    apply le_antisymm
    · intro gamma hgamma
      change gamma ∈ Subgroup.zpowers cylinderAntipodalDiffeomorph.toEquiv
      rcases roundThreeCylinderSolitonAutomorphism_mem_cases
        Gamma hsoliton hfree ⟨gamma, hgamma⟩ with h1 | ha' | hd'
      · change gamma = 1 at h1
        rw [h1]
        exact Subgroup.one_mem _
      · change gamma = cylinderAntipodalDiffeomorph.toEquiv at ha'
        rw [ha']
        exact Subgroup.mem_zpowers _
      · exact (hnotD ⟨gamma, hgamma⟩ hd').elim
    · change Subgroup.zpowers cylinderAntipodalDiffeomorph.toEquiv ≤ Gamma
      exact Subgroup.zpowers_le.mpr ha_mem
  · by_cases hd : ∃ gamma : Gamma,
        gamma.1 = cylinderDiagonalDiffeomorph.toEquiv
    · obtain ⟨gammaD, hgammaD⟩ := hd
      have hd_mem : cylinderDiagonalDiffeomorph.toEquiv ∈ Gamma := by
        simpa [hgammaD] using gammaD.property
      have hnotA : ∀ gamma : Gamma,
          gamma.1 ≠ cylinderAntipodalDiffeomorph.toEquiv := by
        intro gamma hgamma
        exact ha ⟨gamma, hgamma⟩
      right; right
      apply le_antisymm
      · intro gamma hgamma
        change gamma ∈ Subgroup.zpowers cylinderDiagonalDiffeomorph.toEquiv
        rcases roundThreeCylinderSolitonAutomorphism_mem_cases
          Gamma hsoliton hfree ⟨gamma, hgamma⟩ with h1 | ha' | hd'
        · change gamma = 1 at h1
          rw [h1]
          exact Subgroup.one_mem _
        · exact (hnotA ⟨gamma, hgamma⟩ ha').elim
        · change gamma = cylinderDiagonalDiffeomorph.toEquiv at hd'
          rw [hd']
          exact Subgroup.mem_zpowers _
      · change Subgroup.zpowers cylinderDiagonalDiffeomorph.toEquiv ≤ Gamma
        exact Subgroup.zpowers_le.mpr hd_mem
    · left
      apply (Subgroup.eq_bot_iff_forall Gamma).mpr
      intro gamma hgamma
      rcases roundThreeCylinderSolitonAutomorphism_mem_cases
        Gamma hsoliton hfree ⟨gamma, hgamma⟩ with h1 | ha' | hd'
      · change gamma = 1 at h1
        exact h1
      · exact (ha ⟨⟨gamma, hgamma⟩, ha'⟩).elim
      · exact (hd ⟨⟨gamma, hgamma⟩, hd'⟩).elim

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.roundThreeCylinderSolitonAutomorphism_subgroup_eq_bot_or_antipodal_or_diagonal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.roundThreeCylinderSolitonAutomorphism_subgroup_eq_bot_or_antipodal_or_diagonal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.roundThreeCylinderSolitonAutomorphism_subgroup_eq_bot_or_antipodal_or_diagonal ``Submission.DifferentialGeometry.Geometry.roundThreeCylinderSolitonAutomorphism_subgroup_eq_bot_or_antipodal_or_diagonal

theorem roundThreeCylinderSolitonAutomorphism_subgroup_eq_trichotomy
    (Gamma : Subgroup (Equiv.Perm
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)))
    (hsoliton : ∀ gamma : Gamma,
      roundThreeCylinderSolitonAutomorphism gamma.1)
    (hfree : ∀ (gamma : Gamma)
      (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real),
      gamma.1 x = x → gamma = 1) :
    (Gamma = ⊥ ∧ Gamma ≠ cylinderAntipodalGroup ∧
      Gamma ≠ cylinderDiagonalGroup) ∨
    (Gamma = cylinderAntipodalGroup ∧ Gamma ≠ ⊥ ∧
      Gamma ≠ cylinderDiagonalGroup) ∨
    (Gamma = cylinderDiagonalGroup ∧ Gamma ≠ ⊥ ∧
      Gamma ≠ cylinderAntipodalGroup) := by
  rcases
      roundThreeCylinderSolitonAutomorphism_subgroup_eq_bot_or_antipodal_or_diagonal
        Gamma hsoliton hfree with hGamma | hGamma | hGamma
  · subst Gamma
    exact Or.inl ⟨rfl, cylinderAntipodalGroup_ne_bot.symm,
      cylinderDiagonalGroup_ne_bot.symm⟩
  · subst Gamma
    exact Or.inr (Or.inl ⟨rfl, cylinderAntipodalGroup_ne_bot,
      cylinderAntipodalGroup_ne_cylinderDiagonalGroup⟩)
  · subst Gamma
    exact Or.inr (Or.inr ⟨rfl, cylinderDiagonalGroup_ne_bot,
      cylinderAntipodalGroup_ne_cylinderDiagonalGroup.symm⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.roundThreeCylinderSolitonAutomorphism_subgroup_eq_trichotomy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.roundThreeCylinderSolitonAutomorphism_subgroup_eq_trichotomy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.roundThreeCylinderSolitonAutomorphism_subgroup_eq_trichotomy ``Submission.DifferentialGeometry.Geometry.roundThreeCylinderSolitonAutomorphism_subgroup_eq_trichotomy

end DifferentialGeometry.Geometry
