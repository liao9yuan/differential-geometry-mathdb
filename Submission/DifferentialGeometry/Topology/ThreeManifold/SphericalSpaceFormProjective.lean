import Submission.DifferentialGeometry.Topology.ThreeManifold.PoincareStandard
import Submission.DifferentialGeometry.Topology.ThreeManifold.PoincareStandardClassification
import Submission.DifferentialGeometry.Geometry.Metric.Sphere.Quotient.SpaceFormGroup
import Mathlib.Analysis.InnerProductSpace.PiL2

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology

private abbrev ProjectiveSphereSpace := EuclideanSpace ℝ (Fin 4)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ProjectiveSphereSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ProjectiveSphereSpace target :: scope.openDecls } }
private abbrev ProjectiveSphereThree := Metric.sphere (0 : ProjectiveSphereSpace) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ProjectiveSphereThree
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ProjectiveSphereThree target :: scope.openDecls } }

private noncomputable def antipodalIsometry :
    ProjectiveSphereSpace ≃ₗᵢ[ℝ] ProjectiveSphereSpace :=
  LinearIsometryEquiv.neg ℝ

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.antipodalIsometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.antipodalIsometry target :: scope.openDecls } }

private theorem antipodalIsometry_mul_self : antipodalIsometry * antipodalIsometry = 1 := by
  refine LinearIsometryEquiv.ext fun v => ?_
  simp [antipodalIsometry, LinearIsometryEquiv.coe_neg]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.antipodalIsometry_mul_self
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.antipodalIsometry_mul_self target :: scope.openDecls } }

private theorem antipodalIsometry_inv : antipodalIsometry⁻¹ = antipodalIsometry := by
  rw [inv_eq_iff_mul_eq_one]
  exact antipodalIsometry_mul_self

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.antipodalIsometry_inv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.antipodalIsometry_inv target :: scope.openDecls } }

private theorem antipodalIsometry_fixed_point_free (x : ProjectiveSphereThree) :
    DifferentialGeometry.Geometry.sphereDiffeo (n := 3) antipodalIsometry x ≠ x := by
  intro h
  have hx : -(x : ProjectiveSphereSpace) = (x : ProjectiveSphereSpace) := by
    have hval := congrArg (fun z : ProjectiveSphereThree => (z : ProjectiveSphereSpace)) h
    simpa [antipodalIsometry, LinearIsometryEquiv.coe_neg] using hval
  exact ne_neg_of_mem_unit_sphere ℝ x (Subtype.ext hx.symm)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.antipodalIsometry_fixed_point_free
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.antipodalIsometry_fixed_point_free target :: scope.openDecls } }

private theorem antipodalIsometry_ne_one : antipodalIsometry ≠ 1 := by
  intro h
  have hx := antipodalIsometry_fixed_point_free
    (⟨EuclideanSpace.single 0 1, by simp⟩ : ProjectiveSphereThree)
  rw [h] at hx
  exact hx (Subtype.ext (by simp))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.antipodalIsometry_ne_one
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.antipodalIsometry_ne_one target :: scope.openDecls } }

namespace SphericalSpaceFormGroup

noncomputable def antipodal : SphericalSpaceFormGroup where
  group :=
    { carrier := {g | g = 1 ∨ g = antipodalIsometry}
      one_mem' := Or.inl rfl
      mul_mem' := by
        intro x y hx hy
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
        · exact Or.inl (one_mul 1)
        · exact Or.inr (one_mul _)
        · exact Or.inr (mul_one _)
        · exact Or.inl antipodalIsometry_mul_self
      inv_mem' := by
        intro x hx
        rcases hx with rfl | rfl
        · exact Or.inl inv_one
        · exact Or.inr antipodalIsometry_inv }
  finite := by
    have hfin : ({g : ProjectiveSphereSpace ≃ₗᵢ[ℝ] ProjectiveSphereSpace |
        g = 1 ∨ g = antipodalIsometry} : Set _).Finite := by
      rw [show {g : ProjectiveSphereSpace ≃ₗᵢ[ℝ] ProjectiveSphereSpace |
          g = 1 ∨ g = antipodalIsometry} = _root_.Insert.insert antipodalIsometry {1} by
        ext g
        simp [or_comm]]
      exact (Set.finite_singleton 1).insert antipodalIsometry
    exact hfin.to_subtype
  positive := by
    intro γ
    rcases γ.2 with h | h
    · rw [h]
      exact DifferentialGeometry.Geometry.sphereDiffeo_preservesOrientation_of_det_eq_one _
        (by
          change LinearMap.det (1 : ProjectiveSphereSpace →ₗ[ℝ] ProjectiveSphereSpace) = 1
          exact LinearMap.det_id)
    · rw [h]
      exact DifferentialGeometry.Geometry.sphereDiffeo_preservesOrientation_of_fixed_point_free _
        antipodalIsometry_fixed_point_free
  free := by
    intro γ x hx
    rcases γ.2 with h | h
    · exact Subtype.ext h
    · rw [h] at hx
      exact absurd hx (antipodalIsometry_fixed_point_free x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalSpaceFormGroup.antipodal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalSpaceFormGroup.antipodal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalSpaceFormGroup.antipodal ``Submission.DifferentialGeometry.Topology.SphericalSpaceFormGroup.antipodal

theorem not_subsingleton_antipodal_group : ¬ Subsingleton ↥antipodal.group := by
  intro h
  refine antipodalIsometry_ne_one (congrArg Subtype.val (h.elim
    (⟨antipodalIsometry, Or.inr rfl⟩ : ↥antipodal.group) 1))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalSpaceFormGroup.not_subsingleton_antipodal_group then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalSpaceFormGroup.not_subsingleton_antipodal_group"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalSpaceFormGroup.not_subsingleton_antipodal_group ``Submission.DifferentialGeometry.Topology.SphericalSpaceFormGroup.not_subsingleton_antipodal_group

theorem not_subsingleton_fundamentalGroup_antipodal (p : antipodal.manifold.Carrier) :
    ¬ Subsingleton (FundamentalGroup antipodal.manifold.Carrier p) := fun h =>
  not_subsingleton_antipodal_group
    (@Equiv.subsingleton _ _ (fundamentalGroupManifoldEquiv antipodal p).symm h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalSpaceFormGroup.not_subsingleton_fundamentalGroup_antipodal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalSpaceFormGroup.not_subsingleton_fundamentalGroup_antipodal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalSpaceFormGroup.not_subsingleton_fundamentalGroup_antipodal ``Submission.DifferentialGeometry.Topology.SphericalSpaceFormGroup.not_subsingleton_fundamentalGroup_antipodal

theorem isStandardFactor_antipodal : isStandardFactor antipodal.manifold :=
  isStandardFactor_spherical antipodal

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalSpaceFormGroup.isStandardFactor_antipodal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalSpaceFormGroup.isStandardFactor_antipodal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalSpaceFormGroup.isStandardFactor_antipodal ``Submission.DifferentialGeometry.Topology.SphericalSpaceFormGroup.isStandardFactor_antipodal

theorem exists_isStandardFactor_not_subsingleton_group :
    ∃ G : SphericalSpaceFormGroup, ¬ Subsingleton ↥G.group ∧ isStandardFactor G.manifold :=
  ⟨antipodal, not_subsingleton_antipodal_group, isStandardFactor_antipodal⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalSpaceFormGroup.exists_isStandardFactor_not_subsingleton_group then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalSpaceFormGroup.exists_isStandardFactor_not_subsingleton_group"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalSpaceFormGroup.exists_isStandardFactor_not_subsingleton_group ``Submission.DifferentialGeometry.Topology.SphericalSpaceFormGroup.exists_isStandardFactor_not_subsingleton_group

theorem exists_isStandardFactor_nonsimplyConnected :
    ∃ N : ConnectedClosedOrientedManifold.{0} 3, isStandardFactor N ∧
      ∀ p : N.Carrier, ¬ Subsingleton (FundamentalGroup N.Carrier p) :=
  ⟨antipodal.manifold, isStandardFactor_antipodal,
    not_subsingleton_fundamentalGroup_antipodal⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalSpaceFormGroup.exists_isStandardFactor_nonsimplyConnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalSpaceFormGroup.exists_isStandardFactor_nonsimplyConnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalSpaceFormGroup.exists_isStandardFactor_nonsimplyConnected ``Submission.DifferentialGeometry.Topology.SphericalSpaceFormGroup.exists_isStandardFactor_nonsimplyConnected

theorem isPoincareStandard_antipodal :
    isPoincareStandard antipodal.manifold.Carrier :=
  isPoincareStandard_of_standard_factor antipodal.manifold isStandardFactor_antipodal

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalSpaceFormGroup.isPoincareStandard_antipodal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalSpaceFormGroup.isPoincareStandard_antipodal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalSpaceFormGroup.isPoincareStandard_antipodal ``Submission.DifferentialGeometry.Topology.SphericalSpaceFormGroup.isPoincareStandard_antipodal

theorem isPoincareStandard_connectedSum_antipodal :
    isPoincareStandard (connectedSum antipodal.manifold antipodal.manifold).Carrier :=
  isPoincareStandard_connectedSum_of_standardFactor antipodal.manifold antipodal.manifold
    isStandardFactor_antipodal isStandardFactor_antipodal

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalSpaceFormGroup.isPoincareStandard_connectedSum_antipodal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalSpaceFormGroup.isPoincareStandard_connectedSum_antipodal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalSpaceFormGroup.isPoincareStandard_connectedSum_antipodal ``Submission.DifferentialGeometry.Topology.SphericalSpaceFormGroup.isPoincareStandard_connectedSum_antipodal

theorem nonempty_connectedSum_antipodal :
    Nonempty (connectedSum antipodal.manifold antipodal.manifold).Carrier :=
  inferInstance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalSpaceFormGroup.nonempty_connectedSum_antipodal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalSpaceFormGroup.nonempty_connectedSum_antipodal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalSpaceFormGroup.nonempty_connectedSum_antipodal ``Submission.DifferentialGeometry.Topology.SphericalSpaceFormGroup.nonempty_connectedSum_antipodal

end SphericalSpaceFormGroup

end DifferentialGeometry.Topology
