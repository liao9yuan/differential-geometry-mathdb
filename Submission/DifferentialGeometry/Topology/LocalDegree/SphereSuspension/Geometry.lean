import Submission.DifferentialGeometry.Topology.LocalDegree.SphereSuspension.RadialExtension
import Submission.DifferentialGeometry.Topology.LocalDegree.SphereCover

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
open _root_.Metric _root_.Set
open scoped _root_.RealInnerProductSpace
noncomputable section
namespace DifferentialGeometry.LocalDegree
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (K : Submodule ℝ E) [K.HasOrthogonalProjection]


def orthogonalRadialExtension (f : C(_root_.Metric.sphere (0 : K) 1, _root_.Metric.sphere (0 : K) 1)) : C(E, E) where
  toFun x := (sphereRadialExtension f (K.orthogonalProjectionOnto x) : E) + Kᗮ.starProjection x
  continuous_toFun :=
    (continuous_subtype_val.comp ((sphereRadialExtension f).continuous.comp
      K.orthogonalProjectionOnto.continuous)).add Kᗮ.starProjection.continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.orthogonalRadialExtension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.orthogonalRadialExtension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.orthogonalRadialExtension ``Submission.DifferentialGeometry.LocalDegree.orthogonalRadialExtension


@[simp]
theorem orthogonalRadialExtension_norm
    (f : C(_root_.Metric.sphere (0 : K) 1, _root_.Metric.sphere (0 : K) 1)) (x : E) :
    ‖orthogonalRadialExtension K f x‖ = ‖x‖ := by
  have hi : ⟪(sphereRadialExtension f (K.orthogonalProjectionOnto x) : E),
      Kᗮ.starProjection x⟫ = 0 :=
    (K.mem_orthogonal _).mp (Kᗮ.starProjection_apply_mem x) _ (Subtype.coe_prop _)
  have hn := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hi
  simp only [← sq] at hn
  change ‖orthogonalRadialExtension K f x‖ ^ 2 =
    ‖sphereRadialExtension f (K.orthogonalProjectionOnto x)‖ ^ 2 +
      ‖Kᗮ.orthogonalProjectionOnto x‖ ^ 2 at hn
  rw [sphereRadialExtension_norm, ← Submodule.norm_sq_eq_add_norm_sq_projection] at hn
  nlinarith [norm_nonneg (orthogonalRadialExtension K f x), norm_nonneg x]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.orthogonalRadialExtension_norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.orthogonalRadialExtension_norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.orthogonalRadialExtension_norm ``Submission.DifferentialGeometry.LocalDegree.orthogonalRadialExtension_norm


@[simp]
theorem orthogonalRadialExtension_projection
    (f : C(_root_.Metric.sphere (0 : K) 1, _root_.Metric.sphere (0 : K) 1)) (x : E) :
    K.orthogonalProjectionOnto (orthogonalRadialExtension K f x) =
      sphereRadialExtension f (K.orthogonalProjectionOnto x) := by
  change K.orthogonalProjectionOnto (_ + _) = _
  rw [map_add, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,
    Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal (Kᗮ.starProjection_apply_mem x), add_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.orthogonalRadialExtension_projection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.orthogonalRadialExtension_projection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.orthogonalRadialExtension_projection ``Submission.DifferentialGeometry.LocalDegree.orthogonalRadialExtension_projection


theorem orthogonalRadialExtension_orthogonalProjection
    (f : C(_root_.Metric.sphere (0 : K) 1, _root_.Metric.sphere (0 : K) 1)) (x : E) :
    Kᗮ.starProjection (orthogonalRadialExtension K f x) = Kᗮ.starProjection x := by
  rw [Submodule.starProjection_orthogonal_val]
  change ((sphereRadialExtension f (K.orthogonalProjectionOnto x) : E) + Kᗮ.starProjection x) -
    (K.orthogonalProjectionOnto (orthogonalRadialExtension K f x) : E) = _
  rw [orthogonalRadialExtension_projection, add_sub_cancel_left]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.orthogonalRadialExtension_orthogonalProjection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.orthogonalRadialExtension_orthogonalProjection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.orthogonalRadialExtension_orthogonalProjection ``Submission.DifferentialGeometry.LocalDegree.orthogonalRadialExtension_orthogonalProjection


@[simp]
theorem orthogonalRadialExtension_of_mem_orthogonal
    (f : C(_root_.Metric.sphere (0 : K) 1, _root_.Metric.sphere (0 : K) 1)) {x : E} (hx : x ∈ Kᗮ) :
    orthogonalRadialExtension K f x = x := by
  change (sphereRadialExtension f (K.orthogonalProjectionOnto x) : E) + Kᗮ.starProjection x = x
  rw [Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal hx,
    sphereRadialExtension_zero, Submodule.coe_zero, zero_add,
    (Kᗮ.starProjection_eq_self_iff).mpr hx]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.orthogonalRadialExtension_of_mem_orthogonal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.orthogonalRadialExtension_of_mem_orthogonal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.orthogonalRadialExtension_of_mem_orthogonal ``Submission.DifferentialGeometry.LocalDegree.orthogonalRadialExtension_of_mem_orthogonal


theorem orthogonalRadialExtension_eq_of_mem_orthogonal_iff
    (f : C(_root_.Metric.sphere (0 : K) 1, _root_.Metric.sphere (0 : K) 1)) {x z : E} (hz : z ∈ Kᗮ) :
    orthogonalRadialExtension K f x = z ↔ x = z := by
  constructor
  · intro h
    have hp := congrArg K.orthogonalProjectionOnto h
    rw [orthogonalRadialExtension_projection,
      Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal hz] at hp
    have hn := congrArg _root_.Norm.norm hp
    rw [sphereRadialExtension_norm, norm_zero, norm_eq_zero] at hn
    have hx : x ∈ Kᗮ := (K.orthogonalProjectionOnto_eq_zero_iff).mp hn
    rwa [orthogonalRadialExtension_of_mem_orthogonal K f hx] at h
  · intro h
    rw [h]
    exact orthogonalRadialExtension_of_mem_orthogonal K f hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.orthogonalRadialExtension_eq_of_mem_orthogonal_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.orthogonalRadialExtension_eq_of_mem_orthogonal_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.orthogonalRadialExtension_eq_of_mem_orthogonal_iff ``Submission.DifferentialGeometry.LocalDegree.orthogonalRadialExtension_eq_of_mem_orthogonal_iff


def orthogonalSphereSuspension (f : C(_root_.Metric.sphere (0 : K) 1, _root_.Metric.sphere (0 : K) 1)) :
    C(_root_.Metric.sphere (0 : E) 1, _root_.Metric.sphere (0 : E) 1) := by
  let g : C(E, E) := orthogonalRadialExtension K f
  have hg : ∀ x : _root_.Metric.sphere (0 : E) 1, g x ∈ _root_.Metric.sphere (0 : E) 1 := by
    intro x
    rw [_root_.Metric.mem_sphere, dist_zero_right]
    exact (orthogonalRadialExtension_norm K f x).trans (norm_eq_of_mem_sphere x)
  exact ⟨fun x ↦ ⟨g x, hg x⟩,
    (g.continuous.comp continuous_subtype_val).subtype_mk hg⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.orthogonalSphereSuspension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.orthogonalSphereSuspension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.orthogonalSphereSuspension ``Submission.DifferentialGeometry.LocalDegree.orthogonalSphereSuspension


@[simp]
theorem orthogonalSphereSuspension_apply
    (f : C(_root_.Metric.sphere (0 : K) 1, _root_.Metric.sphere (0 : K) 1)) (x : _root_.Metric.sphere (0 : E) 1) :
    (orthogonalSphereSuspension K f x : E) =
      (sphereRadialExtension f (K.orthogonalProjectionOnto x) : E) + Kᗮ.starProjection x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.orthogonalSphereSuspension_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.orthogonalSphereSuspension_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.orthogonalSphereSuspension_apply ``Submission.DifferentialGeometry.LocalDegree.orthogonalSphereSuspension_apply


theorem orthogonalRadialExtension_sphere
    (f : C(_root_.Metric.sphere (0 : K) 1, _root_.Metric.sphere (0 : K) 1)) (v : _root_.Metric.sphere (0 : K) 1) :
    orthogonalRadialExtension K f (v.val : E) = (f v).val := by
  change (sphereRadialExtension f (K.orthogonalProjectionOnto v.val) : E) +
    Kᗮ.starProjection v.val = _
  rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,
    sphereRadialExtension_sphere, Submodule.starProjection_orthogonal_apply_eq_zero v.val.property,
    add_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.orthogonalRadialExtension_sphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.orthogonalRadialExtension_sphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.orthogonalRadialExtension_sphere ``Submission.DifferentialGeometry.LocalDegree.orthogonalRadialExtension_sphere


def equatorSphereSuspension (v : _root_.Metric.sphere (0 : E) 1)
    (f : C(EquatorialSphere v, EquatorialSphere v)) : C(_root_.Metric.sphere (0 : E) 1, _root_.Metric.sphere (0 : E) 1) :=
  orthogonalSphereSuspension (ℝ ∙ (v : E))ᗮ f

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.equatorSphereSuspension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.equatorSphereSuspension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.equatorSphereSuspension ``Submission.DifferentialGeometry.LocalDegree.equatorSphereSuspension

private theorem pole_mem_doubleOrthogonal (v : _root_.Metric.sphere (0 : E) 1) :
    (v : E) ∈ (ℝ ∙ (v : E))ᗮᗮ :=
  (ℝ ∙ (v : E)).le_orthogonal_orthogonal (Submodule.mem_span_singleton_self _)

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.pole_mem_doubleOrthogonal
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.pole_mem_doubleOrthogonal target :: scope.openDecls } }


@[simp]
theorem equatorSphereSuspension_eq_north_iff (v : _root_.Metric.sphere (0 : E) 1)
    (f : C(EquatorialSphere v, EquatorialSphere v)) (x : _root_.Metric.sphere (0 : E) 1) :
    equatorSphereSuspension v f x = v ↔ x = v := by
  rw [Subtype.ext_iff, Subtype.ext_iff]
  exact orthogonalRadialExtension_eq_of_mem_orthogonal_iff _ f (pole_mem_doubleOrthogonal v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.equatorSphereSuspension_eq_north_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.equatorSphereSuspension_eq_north_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.equatorSphereSuspension_eq_north_iff ``Submission.DifferentialGeometry.LocalDegree.equatorSphereSuspension_eq_north_iff


@[simp]
theorem equatorSphereSuspension_eq_south_iff (v : _root_.Metric.sphere (0 : E) 1)
    (f : C(EquatorialSphere v, EquatorialSphere v)) (x : _root_.Metric.sphere (0 : E) 1) :
    equatorSphereSuspension v f x = -v ↔ x = -v := by
  rw [Subtype.ext_iff, Subtype.ext_iff]
  exact orthogonalRadialExtension_eq_of_mem_orthogonal_iff _ f
    ((ℝ ∙ (v : E))ᗮᗮ.neg_mem (pole_mem_doubleOrthogonal v))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.equatorSphereSuspension_eq_south_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.equatorSphereSuspension_eq_south_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.equatorSphereSuspension_eq_south_iff ``Submission.DifferentialGeometry.LocalDegree.equatorSphereSuspension_eq_south_iff


theorem equatorSphereSuspension_height (v : _root_.Metric.sphere (0 : E) 1)
    (f : C(EquatorialSphere v, EquatorialSphere v)) (x : _root_.Metric.sphere (0 : E) 1) :
    ⟪(v : E), (equatorSphereSuspension v f x : E)⟫ = ⟪(v : E), (x : E)⟫ := by
  let K : Submodule ℝ E := (ℝ ∙ (v : E))ᗮ
  have hv : Kᗮ.starProjection (v : E) = v :=
    Kᗮ.starProjection_eq_self_iff.mpr (pole_mem_doubleOrthogonal v)
  calc
    _ = ⟪Kᗮ.starProjection (v : E), (equatorSphereSuspension v f x : E)⟫ := by rw [hv]
    _ = ⟪(v : E), Kᗮ.starProjection (equatorSphereSuspension v f x : E)⟫ :=
      Submodule.inner_starProjection_left_eq_right Kᗮ _ _
    _ = ⟪(v : E), Kᗮ.starProjection (x : E)⟫ := by
      change ⟪(v : E), Kᗮ.starProjection (orthogonalRadialExtension K f x)⟫ = _
      rw [orthogonalRadialExtension_orthogonalProjection]
    _ = ⟪Kᗮ.starProjection (v : E), (x : E)⟫ :=
      (Submodule.inner_starProjection_left_eq_right Kᗮ _ _).symm
    _ = _ := by rw [hv]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.equatorSphereSuspension_height then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.equatorSphereSuspension_height"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.equatorSphereSuspension_height ``Submission.DifferentialGeometry.LocalDegree.equatorSphereSuspension_height

end DifferentialGeometry.LocalDegree
