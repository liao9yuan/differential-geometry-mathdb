import Submission.DifferentialGeometry.Geometry.Metric.Sphere.Round.Metric
import Submission.DifferentialGeometry.Geometry.Metric.Pullback.Basic
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section


open _root_.Bundle _root_.Manifold _root_.Set _root_.Metric _root_.Module
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.RealInnerProductSpace

namespace DifferentialGeometry
namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {n : ℕ} [Fact (finrank ℝ E = n + 1)]

noncomputable def sphereMap (e : E ≃ₗᵢ[ℝ] E) :
    sphere (0 : E) 1 → _root_.Metric.sphere (0 : E) 1 :=
  Set.codRestrict (fun x : _root_.Metric.sphere (0 : E) 1 => (e (x : E) : E)) (_root_.Metric.sphere (0 : E) 1)
    (fun x => by
      rw [mem_sphere_zero_iff_norm, e.norm_map]
      exact mem_sphere_zero_iff_norm.mp x.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.sphereMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.sphereMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.sphereMap ``Submission.DifferentialGeometry.Geometry.sphereMap

omit [FiniteDimensional ℝ E] in
@[simp] theorem sphereMap_coe (e : E ≃ₗᵢ[ℝ] E) (x : _root_.Metric.sphere (0 : E) 1) :
    (sphereMap e x : E) = e (x : E) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.sphereMap_coe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.sphereMap_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.sphereMap_coe ``Submission.DifferentialGeometry.Geometry.sphereMap_coe

theorem sphereMap_contMDiff (e : E ≃ₗᵢ[ℝ] E) :
    ContMDiff (𝓡 n) (𝓡 n) ∞ (sphereMap e) :=
  ContMDiff.codRestrict_sphere
    (e.toContinuousLinearMap.contMDiff.comp contMDiff_coe_sphere) _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.sphereMap_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.sphereMap_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.sphereMap_contMDiff ``Submission.DifferentialGeometry.Geometry.sphereMap_contMDiff

noncomputable def sphereDiffeo (e : E ≃ₗᵢ[ℝ] E) :
    _root_.Metric.sphere (0 : E) 1 ≃ₘ⟮𝓡 n, 𝓡 n⟯ _root_.Metric.sphere (0 : E) 1 where
  toFun := sphereMap e
  invFun := sphereMap e.symm
  left_inv x := Subtype.ext (by simp)
  right_inv x := Subtype.ext (by simp)
  contMDiff_toFun := sphereMap_contMDiff (n := n) e
  contMDiff_invFun := sphereMap_contMDiff (n := n) e.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.sphereDiffeo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.sphereDiffeo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.sphereDiffeo ``Submission.DifferentialGeometry.Geometry.sphereDiffeo

@[simp] theorem sphereDiffeo_coe (e : E ≃ₗᵢ[ℝ] E) (x : _root_.Metric.sphere (0 : E) 1) :
    ((sphereDiffeo (n := n) e x : _root_.Metric.sphere (0 : E) 1) : E) = e (x : E) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.sphereDiffeo_coe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.sphereDiffeo_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.sphereDiffeo_coe ``Submission.DifferentialGeometry.Geometry.sphereDiffeo_coe

theorem sphereDiffeo_inj :
    Function.Injective (sphereDiffeo (E := E) (n := n)) := by
  intro e f hef
  apply LinearIsometryEquiv.ext
  intro x
  by_cases hx : x = 0
  · subst x
    simp
  let y : _root_.Metric.sphere (0 : E) 1 :=
    ⟨‖x‖⁻¹ • x, by
      rw [mem_sphere_zero_iff_norm, norm_smul]
      simp [hx]⟩
  have hxy : ‖x‖ • (y : E) = x := by
    dsimp [y]
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]
  have hpoint :
      sphereDiffeo (n := n) e y = sphereDiffeo (n := n) f y := by
    rw [hef]
  have hamb : e (y : E) = f (y : E) := by
    simpa only [sphereDiffeo_coe] using congrArg Subtype.val hpoint
  calc
    e x = e (‖x‖ • (y : E)) := congrArg e hxy.symm
    _ = ‖x‖ • e (y : E) := map_smul e ‖x‖ (y : E)
    _ = ‖x‖ • f (y : E) := congrArg (fun z : E => ‖x‖ • z) hamb
    _ = f (‖x‖ • (y : E)) := (map_smul f ‖x‖ (y : E)).symm
    _ = f x := congrArg f hxy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.sphereDiffeo_inj then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.sphereDiffeo_inj"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.sphereDiffeo_inj ``Submission.DifferentialGeometry.Geometry.sphereDiffeo_inj

private theorem mfderiv_lie_apply (e : E ≃ₗᵢ[ℝ] E) (y w : E) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (⇑e) y w = e w := by
  have h : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (⇑e) y = e.toContinuousLinearMap := by
    rw [mfderiv_eq_fderiv, show (⇑e : E → E) = ⇑(e.toContinuousLinearMap) from rfl]
    simp only [ContinuousLinearMap.fderiv]
    rfl
  rw [h]; rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.mfderiv_lie_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.mfderiv_lie_apply target :: scope.openDecls } }

theorem mfderiv_incl_sphereDiffeo (e : E ≃ₗᵢ[ℝ] E) (x : _root_.Metric.sphere (0 : E) 1)
    (v : TangentSpace (𝓡 n) x) :
    dIncl (n := n) (sphereDiffeo (n := n) e x)
        (mfderiv (𝓡 n) (𝓡 n) (sphereDiffeo (n := n) e) x v)
      = e (dIncl (n := n) x v) := by
  have h0 : (∞ : WithTop ℕ∞) ≠ 0 := by decide
  have hφ : MDifferentiableAt (𝓡 n) (𝓡 n) (sphereDiffeo (n := n) e) x :=
    (sphereDiffeo (n := n) e).contMDiff.mdifferentiableAt h0
  have hι_φx : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) ((↑) : _root_.Metric.sphere (0 : E) 1 → E)
      (sphereDiffeo (n := n) e x) := contMDiff_coe_sphere.mdifferentiableAt h0
  have hι_x : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) ((↑) : _root_.Metric.sphere (0 : E) 1 → E) x :=
    contMDiff_coe_sphere.mdifferentiableAt h0
  have he : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (⇑e) ((x : _root_.Metric.sphere (0 : E) 1) : E) :=
    e.toContinuousLinearMap.contMDiff.mdifferentiableAt h0
  have hcomp : ((↑) : _root_.Metric.sphere (0 : E) 1 → E) ∘ ⇑(sphereDiffeo (n := n) e)
      = ⇑e ∘ ((↑) : _root_.Metric.sphere (0 : E) 1 → E) := by
    funext y; exact sphereDiffeo_coe e y
  have e1 := mfderiv_comp x hι_φx hφ
  have e2 := mfderiv_comp x he hι_x
  change mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : _root_.Metric.sphere (0 : E) 1 → E) (sphereDiffeo (n := n) e x)
        (mfderiv (𝓡 n) (𝓡 n) (sphereDiffeo (n := n) e) x v)
      = e (mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : _root_.Metric.sphere (0 : E) 1 → E) x v)
  rw [← ContinuousLinearMap.comp_apply, ← e1, hcomp, e2]
  exact mfderiv_lie_apply e _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.mfderiv_incl_sphereDiffeo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.mfderiv_incl_sphereDiffeo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.mfderiv_incl_sphereDiffeo ``Submission.DifferentialGeometry.Geometry.mfderiv_incl_sphereDiffeo

theorem roundInner_sphereDiffeo (e : E ≃ₗᵢ[ℝ] E) (x : _root_.Metric.sphere (0 : E) 1)
    (v w : TangentSpace (𝓡 n) x) :
    roundInner (sphereDiffeo (n := n) e x)
        (mfderiv (𝓡 n) (𝓡 n) (sphereDiffeo (n := n) e) x v)
        (mfderiv (𝓡 n) (𝓡 n) (sphereDiffeo (n := n) e) x w)
      = roundInner (n := n) x v w := by
  rw [roundInner_apply, roundInner_apply,
    mfderiv_incl_sphereDiffeo, mfderiv_incl_sphereDiffeo]
  exact e.inner_map_map _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.roundInner_sphereDiffeo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.roundInner_sphereDiffeo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.roundInner_sphereDiffeo ``Submission.DifferentialGeometry.Geometry.roundInner_sphereDiffeo

theorem pullbackMetric_round_eq (e : E ≃ₗᵢ[ℝ] E) :
    Diffeomorph.pullbackMetric (roundMetric (E := E) (n := n)) (sphereDiffeo (n := n) e)
      = roundMetric := by
  have hinner : (fun x => Diffeomorph.pullbackInner (roundMetric (E := E) (n := n))
        (sphereDiffeo (n := n) e) x) = (roundMetric (E := E) (n := n)).inner := by
    funext x
    refine ContinuousLinearMap.ext fun v => ContinuousLinearMap.ext fun w => ?_
    change (Diffeomorph.pullbackMetric (roundMetric (E := E) (n := n))
        (sphereDiffeo (n := n) e)).inner x v w = (roundMetric (E := E) (n := n)).inner x v w
    rw [Diffeomorph.pullbackMetric_inner]
    exact roundInner_sphereDiffeo e x v w
  unfold Diffeomorph.pullbackMetric
  congr 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.pullbackMetric_round_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.pullbackMetric_round_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.pullbackMetric_round_eq ``Submission.DifferentialGeometry.Geometry.pullbackMetric_round_eq

end Geometry
end DifferentialGeometry
