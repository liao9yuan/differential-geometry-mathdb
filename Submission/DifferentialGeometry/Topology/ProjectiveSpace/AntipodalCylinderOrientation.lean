import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ThreeFrameOrientation
import Submission.DifferentialGeometry.Topology.ProjectiveSpace.CylinderHalfTurnFrame
import Submission.DifferentialGeometry.Topology.VectorField.PartialDiffeomorphLinearization

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Module _root_.Submission.Module
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold _root_.ContDiff

local notation "S" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "CI" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

private local instance antipodalCylinderDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.antipodalCylinderDimension
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.antipodalCylinderDimension target :: scope.openDecls } }

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M]

private theorem three_orientation_ne_of_middle_vector_neg
    (b₀ b₁ : _root_.Module.Basis (Fin 3) ℝ ThreeSpace)
    (hfirst : b₁ 0 = b₀ 0) (hsecond : b₁ 1 = -(b₀ 1))
    (hthird : b₁ 2 = b₀ 2) : b₀.orientation ≠ b₁.orientation := by
  intro horientation
  have hdet : b₀.det b₁ = -1 := by
    rw [Basis.det_apply, Matrix.det_fin_three]
    simp [Basis.toMatrix_apply, hfirst, hsecond, hthird]
  have hpos := (b₀.orientation_eq_iff_det_pos b₁).mp horientation
  rw [hdet] at hpos
  norm_num at hpos

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.three_orientation_ne_of_middle_vector_neg
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.three_orientation_ne_of_middle_vector_neg target :: scope.openDecls } }

theorem not_antipodal_product_localDiffeomorphAt_zero
    (o : TangentOrientationSection M) (q : S × ℝ → M)
    (hq : ∀ y : S, IsLocalDiffeomorphAt CI ThreeModel ∞ q (y, 0))
    (hantipodal : ∀ p : S × ℝ, q (-p.1, p.2) = q p) : False := by
  let γ : ℝ → M := fun t => q (sphereEquator t, 0)
  let B : (t : ℝ) → _root_.Module.Basis (Fin 3) ℝ (TangentSpace ThreeModel (γ t)) := fun t =>
    (cylinderHalfTurnBasis t).map
      ((hq (sphereEquator t)).mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv
  have hB (t : ℝ) (i : Fin 3) : B t i =
      mfderiv CI ThreeModel q (sphereEquator t, 0) (cylinderHalfTurnBasis t i) := rfl
  have hγ : Continuous γ := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hq (sphereEquator t)).contMDiffAt.continuousAt.comp
      (f := fun r : ℝ => (sphereEquator r, (0 : ℝ)))
      (sphereEquator_smooth.continuous.prodMk continuous_const).continuousAt
  have hcontinuous : ∀ i : Fin 3, Continuous (fun t =>
      TotalSpace.mk' ThreeSpace (E := TangentSpace ThreeModel) (γ t) (B t i)) := by
    intro i
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (DifferentialGeometry.VectorField.contMDiffAt_tangentMap
      (p := ⟨(sphereEquator t, 0), cylinderHalfTurnBasis t i⟩)
      (hq (sphereEquator t)).contMDiffAt (m := 0) (by simp)).continuousAt.comp
      (f := fun r : ℝ =>
        (⟨(sphereEquator r, 0), cylinderHalfTurnBasis r i⟩ : TangentBundle CI (S × ℝ)))
      (cylinderHalfTurnBasis_continuous i).continuousAt
  have hloop : γ 0 = γ Real.pi := by
    change q (sphereEquator 0, 0) = q (sphereEquator Real.pi, 0)
    rw [sphereEquator_pi]
    exact (hantipodal (sphereEquator 0, 0)).symm
  have horientation : (B 0).orientation = (B Real.pi).orientation :=
    three_orientation_frame_orientation_eq_of_loop o γ hγ B hcontinuous 0 Real.pi hloop
  have hcomp : q ∘ cylinderAntipodalProductDiffeomorph = q := by
    funext p
    exact hantipodal p
  have hd (y : S) (v : TangentSpace CI (y, (0 : ℝ))) :
      mfderiv CI ThreeModel q (-y, 0)
        (mfderiv CI CI cylinderAntipodalProductDiffeomorph (y, 0) v) =
          mfderiv CI ThreeModel q (y, 0) v := by
    have hc := mfderiv_comp_apply (x := (y, 0))
      ((hq (-y)).mdifferentiableAt (by simp))
      (cylinderAntipodalProductDiffeomorph.contMDiff.mdifferentiableAt (by simp)) v
    rw [hcomp] at hc
    exact hc.symm
  have hfirst : B Real.pi 0 = B 0 0 := by
    rw [hB, cylinderHalfTurnBasis_pi_zero, sphereEquator_pi]
    exact (hd (sphereEquator 0) (cylinderHalfTurnBasis 0 0)).trans (hB 0 0).symm
  have hsecond : B Real.pi 1 = -(B 0 1) := by
    rw [hB, cylinderHalfTurnBasis_pi_one, sphereEquator_pi]
    let v : TangentSpace CI (-sphereEquator 0, (0 : ℝ)) :=
      mfderiv CI CI cylinderAntipodalProductDiffeomorph (sphereEquator 0, (0 : ℝ))
        (cylinderHalfTurnBasis 0 1)
    change mfderiv CI ThreeModel q (-sphereEquator 0, (0 : ℝ)) (-v) = -(B 0 1)
    rw [map_neg]
    apply congrArg (fun z : ThreeSpace => -z)
    exact (hd (sphereEquator 0) (cylinderHalfTurnBasis 0 1)).trans (hB 0 1).symm
  have hthird : B Real.pi 2 = B 0 2 := by
    rw [hB, cylinderHalfTurnBasis_pi_two, sphereEquator_pi]
    exact (hd (sphereEquator 0) (cylinderHalfTurnBasis 0 2)).trans (hB 0 2).symm
  exact three_orientation_ne_of_middle_vector_neg (B 0) (B Real.pi)
    hfirst hsecond hthird horientation

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.not_antipodal_product_localDiffeomorphAt_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.not_antipodal_product_localDiffeomorphAt_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.not_antipodal_product_localDiffeomorphAt_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.not_antipodal_product_localDiffeomorphAt_zero

theorem not_antipodal_product_localDiffeomorph
    (o : TangentOrientationSection M) (q : S × ℝ → M)
    (hq : IsLocalDiffeomorph CI ThreeModel ∞ q)
    (hantipodal : ∀ p : S × ℝ, q (-p.1, p.2) = q p) : False :=
  not_antipodal_product_localDiffeomorphAt_zero o q (fun y => hq (y, 0)) hantipodal

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.not_antipodal_product_localDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.not_antipodal_product_localDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.not_antipodal_product_localDiffeomorph ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.not_antipodal_product_localDiffeomorph

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
