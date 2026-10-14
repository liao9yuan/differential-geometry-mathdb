import Submission.DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.Sphere.DoublePunctured
import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.SphereCapFillingIsometry
import Submission.DifferentialGeometry.Topology.Manifold.BallChartAffine
import Submission.DifferentialGeometry.Topology.Manifold.SphereIsometryOrientation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Function
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.Topology

open _root_.Submission.OrientationAssembly
open _root_.Submission.DifferentialGeometry.Topology.Manifold

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.E3 target :: scope.openDecls } }
private abbrev E4 := EuclideanSpace ℝ (Fin 4)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.E4
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.E4 target :: scope.openDecls } }
private abbrev S3 := Metric.sphere (0 : E4) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.S3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.S3 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.instFactEqNatFinrankRealE4HAddOfNat : Fact (Module.finrank ℝ E4 = 3 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.instFactEqNatFinrankRealE4HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.instFactEqNatFinrankRealE4HAddOfNat target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.instNegCarrierStandardThreeSphere : Neg standardThreeSphere.Carrier := inferInstanceAs (Neg S3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.instNegCarrierStandardThreeSphere
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.instNegCarrierStandardThreeSphere target :: scope.openDecls } }

theorem exists_oriented_stereographic_ballChart (P : S3) :
    ∃ A : E3 ≃ₗᵢ[ℝ] E3,
      (A = LinearIsometryEquiv.refl ℝ E3 ∨ A = LinearIsometryEquiv.neg ℝ) ∧
      ∃ c : OrientedBallChart standardThreeSphere.toClosedOrientedManifold,
        ∀ x, c.chart x = (SphereUnitFilling.sphereBallChart P).chart (A x) := by
  let A₁ : SphereUnitFilling.E3 ≃ₗᵢ[ℝ] SphereUnitFilling.E3 :=
    LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ (Fin 3))
  let oSph : SmoothOrientation (𝓡 3) SphereUnitFilling.S3 :=
    smoothOrientationOfManifoldOrientation (𝓡 3)
      (reindexManifoldOrientation (𝓡 3) csIdx standardThreeSphere.orientation)
  let oF : SmoothOrientation 𝓘(ℝ, SphereUnitFilling.E3) SphereUnitFilling.E3 :=
    pullbackSmoothOrientation 𝓘(ℝ, SphereUnitFilling.E3) (𝓡 3)
      (fun u => SphereUnitFilling.sphereChartPartialIso A₁ P u)
      (SphereUnitFilling.contMDiff_sphereChartPartialIso A₁ P)
      (SphereUnitFilling.bijective_mfderiv_sphereChartPartialIso A₁ P) oSph
  let oE : SmoothOrientation 𝓘(ℝ, SphereUnitFilling.E3) SphereUnitFilling.E3 :=
    euclideanSmoothOrientation SphereUnitFilling.E3 stdOrientationModel
  rcases smoothOrientation_eq_or_eq_neg 𝓘(ℝ, SphereUnitFilling.E3) oF oE 0 with hcase | hcase
  · have hle : oF = oE := Subtype.ext (funext hcase)
    exact ⟨A₁, Or.inl rfl, orientedBallChartOfPullbackSmoothOrientation A₁ P hle,
      fun _ => rfl⟩
  · let A₂ : SphereUnitFilling.E3 ≃ₗᵢ[ℝ] SphereUnitFilling.E3 :=
    (LinearIsometryEquiv.neg ℝ : SphereUnitFilling.E3 ≃ₗᵢ[ℝ] SphereUnitFilling.E3)
    have hmfA₂ : ∀ u : SphereUnitFilling.E3,
        mfderiv 𝓘(ℝ, SphereUnitFilling.E3) 𝓘(ℝ, SphereUnitFilling.E3)
          (fun u => A₂ u) u = A₂.toContinuousLinearEquiv.toContinuousLinearMap := by
      intro u
      exact ContinuousLinearMap.mfderiv_eq (𝕜 := ℝ)
        (f := (A₂ : SphereUnitFilling.E3 →L[ℝ] SphereUnitFilling.E3)) (x := u)
    have hA₂ : ContMDiff 𝓘(ℝ, SphereUnitFilling.E3) 𝓘(ℝ, SphereUnitFilling.E3) ∞
        (fun u => A₂ u) := A₂.toContinuousLinearEquiv.toContinuousLinearMap.contMDiff
    have hbA₂ : ∀ u, _root_.Function.Bijective (mfderiv 𝓘(ℝ, SphereUnitFilling.E3)
        𝓘(ℝ, SphereUnitFilling.E3) (fun u => A₂ u) u) := by
      intro u
      rw [hmfA₂ u]
      exact A₂.toContinuousLinearEquiv.bijective
    have hneg : oF = euclideanSmoothOrientation SphereUnitFilling.E3 (-stdOrientationModel) := by
      have h1 : oF = negSmoothOrientation 𝓘(ℝ, SphereUnitFilling.E3) oE := by
        refine Subtype.ext (funext (fun x => ?_))
        rw [negSmoothOrientation_apply]
        exact hcase x
      exact h1.trans (negSmoothOrientation_euclideanSmoothOrientation stdOrientationModel)
    have hApull : pullbackSmoothOrientation 𝓘(ℝ, SphereUnitFilling.E3)
        𝓘(ℝ, SphereUnitFilling.E3) (fun u => A₂ u) hA₂ hbA₂
        (euclideanSmoothOrientation SphereUnitFilling.E3 (-stdOrientationModel)) = oE := by
      refine Subtype.ext (funext (fun x => ?_))
      rw [pullbackSmoothOrientation_eq_iff]
      rw [euclideanSmoothOrientation_apply, euclideanSmoothOrientation_apply]
      have hD : differentialEquivOfBijective 𝓘(ℝ, SphereUnitFilling.E3)
          𝓘(ℝ, SphereUnitFilling.E3) (fun u => A₂ u) hbA₂ x
          = A₂.toContinuousLinearEquiv := by
        apply ContinuousLinearEquiv.ext
        funext v
        rw [differentialEquivOfBijective_apply, hmfA₂ x]
        rfl
      rw [hD]
      exact tangentOrientationEquiv_negLinearEquiv stdOrientationModel
    have h₂ : pullbackSmoothOrientation 𝓘(ℝ, SphereUnitFilling.E3) (𝓡 3)
        (fun u => SphereUnitFilling.sphereChartPartialIso A₂ P u)
        (SphereUnitFilling.contMDiff_sphereChartPartialIso A₂ P)
        (SphereUnitFilling.bijective_mfderiv_sphereChartPartialIso A₂ P) oSph = oE := by
      refine Subtype.ext (funext (fun x => ?_))
      have hcomp := pullbackSmoothOrientation_comp_apply 𝓘(ℝ, SphereUnitFilling.E3)
        𝓘(ℝ, SphereUnitFilling.E3) (𝓡 3) (fun u : SphereUnitFilling.E3 => A₂ u)
        (fun v : SphereUnitFilling.E3 => SphereUnitFilling.sphereChartPartialIso A₁ P v)
        hA₂ (SphereUnitFilling.contMDiff_sphereChartPartialIso A₁ P) hbA₂
        (SphereUnitFilling.bijective_mfderiv_sphereChartPartialIso A₁ P)
        (SphereUnitFilling.bijective_mfderiv_sphereChartPartialIso A₂ P) oSph x
      erw [hcomp]
      have hinner : pullbackSmoothOrientation 𝓘(ℝ, SphereUnitFilling.E3) (𝓡 3)
          (fun v : SphereUnitFilling.E3 => SphereUnitFilling.sphereChartPartialIso A₁ P v)
          (SphereUnitFilling.contMDiff_sphereChartPartialIso A₁ P)
          (SphereUnitFilling.bijective_mfderiv_sphereChartPartialIso A₁ P) oSph = oF := rfl
      rw [hinner, hneg, hApull]
    exact ⟨A₂, Or.inr rfl, orientedBallChartOfPullbackSmoothOrientation A₂ P h₂,
      fun _ => rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_oriented_stereographic_ballChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_oriented_stereographic_ballChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_oriented_stereographic_ballChart ``Submission.DifferentialGeometry.Topology.exists_oriented_stereographic_ballChart

theorem sphereAntipodalDiffeomorph_preserves_orientation_three :
    (sphereAntipodalDiffeomorph (E := E4) (n := 3)).preservesOrientation
      standardThreeSphere.orientation standardThreeSphere.orientation := by
  have hdet : LinearMap.det
      ((LinearIsometryEquiv.neg ℝ : E4 ≃ₗᵢ[ℝ] E4).toLinearEquiv : E4 →ₗ[ℝ] E4) = 1 := by
    have hmap : ((LinearIsometryEquiv.neg ℝ : E4 ≃ₗᵢ[ℝ] E4).toLinearEquiv : E4 →ₗ[ℝ] E4) =
        (-1 : ℝ) • (LinearMap.id : E4 →ₗ[ℝ] E4) := by
      ext v
      simp
    rw [hmap, LinearMap.det_smul, LinearMap.det_id]
    norm_num
  have heq : sphereAntipodalDiffeomorph (E := E4) (n := 3) =
      Geometry.sphereDiffeo (n := 3) (LinearIsometryEquiv.neg ℝ : E4 ≃ₗᵢ[ℝ] E4) := by
    ext x
    rfl
  rw [heq]
  exact Geometry.sphereDiffeo_preservesOrientation_of_det_eq_one _ hdet

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereAntipodalDiffeomorph_preserves_orientation_three then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereAntipodalDiffeomorph_preserves_orientation_three"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereAntipodalDiffeomorph_preserves_orientation_three ``Submission.DifferentialGeometry.Topology.sphereAntipodalDiffeomorph_preserves_orientation_three

def antipodalOrientedSphereBallChart
    (c : OrientedBallChart standardThreeSphere.toClosedOrientedManifold) :
    OrientedBallChart standardThreeSphere.toClosedOrientedManifold where
  chart := compPartialDiffeomorph c.chart (sphereAntipodalDiffeomorph (E := E4) (n := 3))
  closedBall_subset_source := c.closedBall_subset_source
  preserves_orientation := preservesOrientation_compPartialDiffeomorph c.chart
    standardThreeSphere.orientation standardThreeSphere.orientation
    (sphereAntipodalDiffeomorph (E := E4) (n := 3))
    sphereAntipodalDiffeomorph_preserves_orientation_three c.preserves_orientation

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.antipodalOrientedSphereBallChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.antipodalOrientedSphereBallChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.antipodalOrientedSphereBallChart ``Submission.DifferentialGeometry.Topology.antipodalOrientedSphereBallChart

theorem antipodalOrientedSphereBallChart_apply
    (c : OrientedBallChart standardThreeSphere.toClosedOrientedManifold) (x : E3) :
    (antipodalOrientedSphereBallChart c).chart x = -(c.chart x : S3) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.antipodalOrientedSphereBallChart_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.antipodalOrientedSphereBallChart_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.antipodalOrientedSphereBallChart_apply ``Submission.DifferentialGeometry.Topology.antipodalOrientedSphereBallChart_apply

theorem exists_oriented_stereographic_small_ballCharts (P : S3) :
    ∃ A : E3 ≃ₗᵢ[ℝ] E3,
      (A = LinearIsometryEquiv.refl ℝ E3 ∨ A = LinearIsometryEquiv.neg ℝ) ∧
      ∃ c d : OrientedBallChart standardThreeSphere.toClosedOrientedManifold,
        (∀ x, c.chart x = (stereographicSmallBallChart P).chart (A x)) ∧
        (∀ x, d.chart x = (oppositeStereographicSmallBallChart P).chart (A x)) ∧
        (∀ x, d.chart x = -(c.chart x : S3)) ∧
        Disjoint (c.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2) := by
  obtain ⟨A, hA, c₀, hc₀⟩ := exists_oriented_stereographic_ballChart P
  let c := c₀.affine 0 (1 / 4) (by norm_num) (by norm_num)
  let d := antipodalOrientedSphereBallChart c
  have hc (x : E3) : c.chart x = (stereographicSmallBallChart P).chart (A x) := by
    rw [show c.chart x = c₀.chart (0 + (1 / 4 : ℝ) • x) from rfl, zero_add, hc₀]
    change (SphereUnitFilling.sphereBallChart P).chart (A ((1 / 4 : ℝ) • x)) =
      (SphereUnitFilling.sphereBallChart P).chart ((1 / 4 : ℝ) • A x)
    rw [map_smul]
  have hd (x : E3) : d.chart x = (oppositeStereographicSmallBallChart P).chart (A x) := by
    rw [show d.chart x = -(c.chart x : S3) from rfl, hc, oppositeStereographicSmallBallChart_apply]
    rfl
  refine ⟨A, hA, c, d, hc, hd, fun _ => rfl, ?_⟩
  apply (stereographicSmallBallChart_disjoint P).mono
  · rintro y ⟨x, hx, rfl⟩
    refine ⟨A x, ?_, (hc x).symm⟩
    simpa only [Metric.mem_closedBall, dist_zero_right, A.norm_map] using hx
  · rintro y ⟨x, hx, rfl⟩
    refine ⟨A x, ?_, (hd x).symm⟩
    simpa only [Metric.mem_closedBall, dist_zero_right, A.norm_map] using hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_oriented_stereographic_small_ballCharts then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_oriented_stereographic_small_ballCharts"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_oriented_stereographic_small_ballCharts ``Submission.DifferentialGeometry.Topology.exists_oriented_stereographic_small_ballCharts

end DifferentialGeometry.Topology
