import Submission.DifferentialGeometry.Topology.Manifold.SphereOrientation
import Submission.DifferentialGeometry.Geometry.Metric.Sphere.Isometry.OrthogonalAction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Manifold _root_.Metric _root_.Module
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry

open _root_.Submission.DifferentialGeometry.Geometry

universe u

private instance _root_.Submission.DifferentialGeometry.instFactEqNatFinrankRealEuclideanSpaceFinOfNatHAdd_differentialGeometry : Fact (_root_.Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) :=
  ⟨by rw [finrank_euclideanSpace_fin]⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.instFactEqNatFinrankRealEuclideanSpaceFinOfNatHAdd_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.instFactEqNatFinrankRealEuclideanSpaceFinOfNatHAdd_differentialGeometry target :: scope.openDecls } }

private abbrev RoundSphereE4 := EuclideanSpace ℝ (Fin 4)

run_cmd do
  let target := ``Submission.DifferentialGeometry.RoundSphereE4
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.RoundSphereE4 target :: scope.openDecls } }
private abbrev RoundSphereS3 := _root_.Metric.sphere (0 : RoundSphereE4) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.RoundSphereS3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.RoundSphereS3 target :: scope.openDecls } }

private theorem sphereOutwardDeterminant_eq_basisFunDet
    (y : RoundSphereS3) (c : _root_.Module.Basis (Fin 3) ℝ (TangentSpace (𝓡 3) y)) :
    sphereOutwardDeterminant 3 y c =
      ((EuclideanSpace.basisFun (Fin 4) ℝ).toBasis).det
        (fun j => Fin.cases (motive := fun _ => RoundSphereE4) (y : RoundSphereE4)
          (fun k => dIncl (n := 3) y (c k)) j) := by
  rw [Module.Basis.det_apply]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.sphereOutwardDeterminant_eq_basisFunDet
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.sphereOutwardDeterminant_eq_basisFunDet target :: scope.openDecls } }

theorem sphereOutwardDeterminant_sphereDiffeo
    (e : RoundSphereE4 ≃ₗᵢ[ℝ] RoundSphereE4) (x : RoundSphereS3)
    (b : _root_.Module.Basis (Fin 3) ℝ (TangentSpace (𝓡 3) x)) :
    sphereOutwardDeterminant 3 (sphereDiffeo (n := 3) e x)
        (b.map (((sphereDiffeo (n := 3) e).mfderivToContinuousLinearEquiv
          (by simp) x).toLinearEquiv)) =
      LinearMap.det (e.toLinearEquiv : RoundSphereE4 →ₗ[ℝ] RoundSphereE4)
        * sphereOutwardDeterminant 3 x b := by
  have hv : (fun j => Fin.cases (motive := fun _ => RoundSphereE4)
        ((sphereDiffeo (n := 3) e x : RoundSphereS3) : RoundSphereE4)
        (fun k => dIncl (n := 3) (sphereDiffeo (n := 3) e x)
          ((b.map (((sphereDiffeo (n := 3) e).mfderivToContinuousLinearEquiv
            (by simp) x).toLinearEquiv)) k)) j) =
      (e.toLinearEquiv : RoundSphereE4 →ₗ[ℝ] RoundSphereE4) ∘
        (fun j => Fin.cases (motive := fun _ => RoundSphereE4) (x : RoundSphereE4)
          (fun k => dIncl (n := 3) x (b k)) j) := by
    funext j
    induction j using Fin.cases with
    | zero =>
      simp only [Function.comp_apply, Fin.cases_zero, sphereDiffeo_coe]
      rfl
    | succ k =>
      simp only [Function.comp_apply, Fin.cases_succ, Module.Basis.map_apply,
        ContinuousLinearEquiv.coe_toLinearEquiv]
      exact mfderiv_incl_sphereDiffeo (n := 3) e x (b k)
  rw [sphereOutwardDeterminant_eq_basisFunDet (sphereDiffeo (n := 3) e x) _,
    sphereOutwardDeterminant_eq_basisFunDet x b, hv, Module.Basis.det_comp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.sphereOutwardDeterminant_sphereDiffeo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.sphereOutwardDeterminant_sphereDiffeo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.sphereOutwardDeterminant_sphereDiffeo ``Submission.DifferentialGeometry.sphereOutwardDeterminant_sphereDiffeo

namespace Geometry

theorem sphereDiffeo_preservesOrientation_of_det_eq_one
    (e : RoundSphereE4 ≃ₗᵢ[ℝ] RoundSphereE4)
    (hdet : LinearMap.det (e.toLinearEquiv : RoundSphereE4 →ₗ[ℝ] RoundSphereE4) = 1) :
    (sphereDiffeo (n := 3) e).preservesOrientation
      (sphereOrientation 3 (by decide)) (sphereOrientation 3 (by decide)) := by
  intro x
  let L : TangentSpace (𝓡 3) x ≃ₗ[ℝ]
      TangentSpace (𝓡 3) (sphereDiffeo (n := 3) e x) :=
    (((sphereDiffeo (n := 3) e).mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv)
  let b : _root_.Module.Basis (Fin 3) ℝ (TangentSpace (𝓡 3) x) :=
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  have hkey : b.orientation = (sphereOrientation 3 (by decide)).orientation x ↔
      (b.map L).orientation =
        (sphereOrientation 3 (by decide)).orientation (sphereDiffeo (n := 3) e x) := by
    rw [sphereOrientation_characterization 3 (by decide) x b,
      sphereOrientation_characterization 3 (by decide) _ (b.map L),
      sphereOutwardDeterminant_sphereDiffeo, hdet, one_mul]
  rcases b.orientation_eq_or_eq_neg
    ((sphereOrientation 3 (by decide)).orientation x) with hb | hb
  · have hmap : (b.map L).orientation =
        (sphereOrientation 3 (by decide)).orientation (sphereDiffeo (n := 3) e x) :=
      hkey.mp hb.symm
    change Orientation.map (Fin 3) L ((sphereOrientation 3 (by decide)).orientation x) =
      (sphereOrientation 3 (by decide)).orientation (sphereDiffeo (n := 3) e x)
    rw [hb, ← Module.Basis.orientation_map b L]
    exact hmap
  · have hne : b.orientation ≠ (sphereOrientation 3 (by decide)).orientation x := by
      intro h
      exact Module.Ray.ne_neg_self b.orientation (h.trans hb)
    change Orientation.map (Fin 3) L ((sphereOrientation 3 (by decide)).orientation x) =
      (sphereOrientation 3 (by decide)).orientation (sphereDiffeo (n := 3) e x)
    rw [hb, Orientation.map_neg, ← Module.Basis.orientation_map b L]
    rcases Module.Basis.orientation_eq_or_eq_neg (b.map L)
      ((sphereOrientation 3 (by decide)).orientation (sphereDiffeo (n := 3) e x)) with
      hcon | hcon
    · exact absurd (hkey.mpr hcon.symm) hne
    · exact hcon.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.sphereDiffeo_preservesOrientation_of_det_eq_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.sphereDiffeo_preservesOrientation_of_det_eq_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.sphereDiffeo_preservesOrientation_of_det_eq_one ``Submission.DifferentialGeometry.Geometry.sphereDiffeo_preservesOrientation_of_det_eq_one

end Geometry
end DifferentialGeometry
