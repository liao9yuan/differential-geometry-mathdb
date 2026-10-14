import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CylinderAxialNormalization

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry
open scoped _root_.Manifold _root_.ContDiff

private local instance shrinkingCylinderSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.shrinkingCylinderSphereDimension
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.shrinkingCylinderSphereDimension target :: scope.openDecls } }


def scalarOneShrinkingCylinderMetric (s : ℝ) (hs : s < 1) :
    SmoothRiemannianMetric SpatialNeckCylinderModel SpatialNeckCylinder :=
  DifferentialGeometry.Diffeomorph.pullbackMetric
    (scaleMetric (2 * (1 - s)) (mul_pos (by norm_num) (sub_pos.mpr hs)) unitCylinderMetric)
    (cylinderAxialScale (Real.sqrt (2 * (1 - s)))
      (ne_of_gt (Real.sqrt_pos.mpr (mul_pos (by norm_num) (sub_pos.mpr hs))))).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarOneShrinkingCylinderMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarOneShrinkingCylinderMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarOneShrinkingCylinderMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarOneShrinkingCylinderMetric


theorem scalarOneShrinkingCylinderMetric_inner (s : ℝ) (hs : s < 1)
    (y : SpatialNeckSphere) (z : ℝ) (v w : TangentSpace (𝓡 2) y) (a b : ℝ) :
    (scalarOneShrinkingCylinderMetric s hs).inner (y, z) (v, a) (w, b) =
      2 * (1 - s) * (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner y v w +
        a * b := by
  let c : ℝ := 2 * (1 - s)
  have hc : 0 < c := mul_pos (by norm_num) (sub_pos.mpr hs)
  have hsqrt : Real.sqrt c ≠ 0 := (Real.sqrt_pos.mpr hc).ne'
  have hcoefficient : c * ((Real.sqrt c)⁻¹ * (Real.sqrt c)⁻¹) = 1 := by
    rw [← pow_two, inv_pow, Real.sq_sqrt hc.le, mul_inv_cancel₀ hc.ne']
  have hpull := DifferentialGeometry.Diffeomorph.pullbackMetric_inner
    (scaleMetric c hc unitCylinderMetric) (cylinderAxialScale (Real.sqrt c) hsqrt).symm
      (y, z) (v, a) (w, b)
  have hdiff (V : TangentSpace SpatialNeckCylinderModel (y, z)) :
      mfderiv SpatialNeckCylinderModel SpatialNeckCylinderModel
        (cylinderAxialScale (Real.sqrt c) hsqrt).symm (y, z) V =
        (V.1, (Real.sqrt c)⁻¹ * V.2) := by
    have heq := congrArg
      (fun Phi : SpatialNeckCylinder ≃ₘ⟮SpatialNeckCylinderModel, SpatialNeckCylinderModel⟯
          SpatialNeckCylinder =>
        (mfderiv SpatialNeckCylinderModel SpatialNeckCylinderModel Phi (y, z) V :
          EuclideanSpace ℝ (Fin 2) × ℝ))
      (cylinderAxialScale_symm (Real.sqrt c) hsqrt)
    exact heq.trans (cylinderAxialScale_mfderiv (Real.sqrt c)⁻¹ (inv_ne_zero hsqrt) (y, z) V)
  have hinner := congrArg₂
    (fun V W : EuclideanSpace ℝ (Fin 2) × ℝ =>
      unitCylinderMetric.inner (y, (Real.sqrt c)⁻¹ * z) V W)
    (hdiff (v, a)) (hdiff (w, b))
  have hformula := hinner.trans
    (unitCylinderMetric_inner y ((Real.sqrt c)⁻¹ * z) v w
      ((Real.sqrt c)⁻¹ * a) ((Real.sqrt c)⁻¹ * b))
  apply hpull.trans
  simp only [scaleMetric_inner]
  apply (congrArg (fun r : ℝ => c * r) hformula).trans
  calc
    c * ((roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner y v w +
        ((Real.sqrt c)⁻¹ * a) * ((Real.sqrt c)⁻¹ * b)) =
      c * (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner y v w +
        (c * ((Real.sqrt c)⁻¹ * (Real.sqrt c)⁻¹)) * (a * b) := by ring
    _ = _ := by rw [hcoefficient]; ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarOneShrinkingCylinderMetric_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarOneShrinkingCylinderMetric_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarOneShrinkingCylinderMetric_inner ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarOneShrinkingCylinderMetric_inner


theorem scalarOneShrinkingCylinderMetric_zero :
    scalarOneShrinkingCylinderMetric 0 (by norm_num) = doubleSphereCylinderMetric := by
  apply SmoothRiemannianMetric.ext_inner
  rintro ⟨y, z⟩ ⟨v, a⟩ ⟨w, b⟩
  apply (scalarOneShrinkingCylinderMetric_inner 0 (by norm_num) y z v w a b).trans
  apply Eq.trans _ (doubleSphereCylinderMetric_inner y z v w a b).symm
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarOneShrinkingCylinderMetric_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarOneShrinkingCylinderMetric_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarOneShrinkingCylinderMetric_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarOneShrinkingCylinderMetric_zero

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
