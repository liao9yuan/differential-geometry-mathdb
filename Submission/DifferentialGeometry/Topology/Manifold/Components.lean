import Submission.DifferentialGeometry.Topology.Manifold.ClosedOriented
import Submission.DifferentialGeometry.Topology.Manifold.OpenSubtype
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Homeomorph.Lemmas

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Manifold _root_.Set _root_.TopologicalSpace
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology.ClosedOrientedManifold

universe u

variable {n : ℕ} (M : ClosedOrientedManifold.{u} n)

def componentSet (C : ConnectedComponents M.Carrier) : Set M.Carrier :=
  {x | ConnectedComponents.mk x = C}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedOrientedManifold.componentSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedOrientedManifold.componentSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedOrientedManifold.componentSet ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.componentSet

@[simp]
theorem mem_componentSet (C : ConnectedComponents M.Carrier) (x : M.Carrier) :
    x ∈ componentSet M C ↔ ConnectedComponents.mk x = C := Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedOrientedManifold.mem_componentSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedOrientedManifold.mem_componentSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedOrientedManifold.mem_componentSet ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.mem_componentSet

@[simp]
theorem componentSet_mk (x : M.Carrier) :
    componentSet M (ConnectedComponents.mk x) = connectedComponent x := by
  ext y
  exact ConnectedComponents.coe_eq_coe'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedOrientedManifold.componentSet_mk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedOrientedManifold.componentSet_mk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedOrientedManifold.componentSet_mk ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.componentSet_mk

theorem componentSet_nonempty (C : ConnectedComponents M.Carrier) :
    (componentSet M C).Nonempty :=
  ConnectedComponents.surjective_coe C

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedOrientedManifold.componentSet_nonempty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedOrientedManifold.componentSet_nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedOrientedManifold.componentSet_nonempty ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.componentSet_nonempty

theorem isOpen_componentSet (C : ConnectedComponents M.Carrier) :
    IsOpen (componentSet M C) := by
  let := ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin n)) M.Carrier
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe C
  rw [componentSet_mk]
  exact isOpen_connectedComponent

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedOrientedManifold.isOpen_componentSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedOrientedManifold.isOpen_componentSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedOrientedManifold.isOpen_componentSet ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.isOpen_componentSet

theorem isClosed_componentSet (C : ConnectedComponents M.Carrier) :
    IsClosed (componentSet M C) := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe C
  rw [componentSet_mk]
  exact isClosed_connectedComponent

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedOrientedManifold.isClosed_componentSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedOrientedManifold.isClosed_componentSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedOrientedManifold.isClosed_componentSet ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.isClosed_componentSet

theorem isCompact_componentSet (C : ConnectedComponents M.Carrier) :
    IsCompact (componentSet M C) :=
  (isClosed_componentSet M C).isCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedOrientedManifold.isCompact_componentSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedOrientedManifold.isCompact_componentSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedOrientedManifold.isCompact_componentSet ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.isCompact_componentSet

theorem isConnected_componentSet (C : ConnectedComponents M.Carrier) :
    IsConnected (componentSet M C) := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe C
  rw [componentSet_mk]
  exact isConnected_connectedComponent

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedOrientedManifold.isConnected_componentSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedOrientedManifold.isConnected_componentSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedOrientedManifold.isConnected_componentSet ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.isConnected_componentSet

theorem finite_components : Finite (ConnectedComponents M.Carrier) := by
  let := ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin n)) M.Carrier
  infer_instance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedOrientedManifold.finite_components then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedOrientedManifold.finite_components"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedOrientedManifold.finite_components ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.finite_components

theorem isEmpty_components_iff :
    IsEmpty (ConnectedComponents M.Carrier) ↔ IsEmpty M.Carrier :=
  ConnectedComponents.isEmpty_iff_isEmpty

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedOrientedManifold.isEmpty_components_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedOrientedManifold.isEmpty_components_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedOrientedManifold.isEmpty_components_iff ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.isEmpty_components_iff

def componentOpen (C : ConnectedComponents M.Carrier) : _root_.TopologicalSpace.Opens M.Carrier :=
  ⟨componentSet M C, isOpen_componentSet M C⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedOrientedManifold.componentOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedOrientedManifold.componentOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedOrientedManifold.componentOpen ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.componentOpen

@[simp]
theorem componentOpen_coe (C : ConnectedComponents M.Carrier) :
    (componentOpen M C : Set M.Carrier) = componentSet M C := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedOrientedManifold.componentOpen_coe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedOrientedManifold.componentOpen_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedOrientedManifold.componentOpen_coe ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.componentOpen_coe

def componentInclusion (C : ConnectedComponents M.Carrier) : componentOpen M C → M.Carrier :=
  Subtype.val

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedOrientedManifold.componentInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedOrientedManifold.componentInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedOrientedManifold.componentInclusion ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.componentInclusion

theorem componentInclusion_contMDiff (C : ConnectedComponents M.Carrier) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (componentInclusion M C) :=
  contMDiff_subtype_val

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedOrientedManifold.componentInclusion_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedOrientedManifold.componentInclusion_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedOrientedManifold.componentInclusion_contMDiff ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.componentInclusion_contMDiff

theorem componentInclusion_mfderiv_bijective (C : ConnectedComponents M.Carrier)
    (x : componentOpen M C) :
    Function.Bijective (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (componentInclusion M C) x) := by
  change Function.Bijective (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (Subtype.val : componentOpen M C → M.Carrier) x)
  rw [mfderiv_subtype_val]
  exact Function.bijective_id

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedOrientedManifold.componentInclusion_mfderiv_bijective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedOrientedManifold.componentInclusion_mfderiv_bijective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedOrientedManifold.componentInclusion_mfderiv_bijective ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.componentInclusion_mfderiv_bijective

def componentInclusionTangentEquiv (C : ConnectedComponents M.Carrier)
    (x : componentOpen M C) :
    TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x ≃ₗ[ℝ] TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (componentInclusion M C x) :=
  LinearEquiv.ofBijective
    (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (componentInclusion M C) x).toLinearMap
    (componentInclusion_mfderiv_bijective M C x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedOrientedManifold.componentInclusionTangentEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedOrientedManifold.componentInclusionTangentEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedOrientedManifold.componentInclusionTangentEquiv ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.componentInclusionTangentEquiv

@[simp]
theorem componentInclusionTangentEquiv_apply (C : ConnectedComponents M.Carrier)
    (x : componentOpen M C) (v : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :
    componentInclusionTangentEquiv M C x v =
      mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (componentInclusion M C) x v := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedOrientedManifold.componentInclusionTangentEquiv_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedOrientedManifold.componentInclusionTangentEquiv_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedOrientedManifold.componentInclusionTangentEquiv_apply ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.componentInclusionTangentEquiv_apply

def componentTangentOrientation (C : ConnectedComponents M.Carrier) (x : componentOpen M C) :
    Orientation ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) (Fin n) :=
  Orientation.map (Fin n) (componentInclusionTangentEquiv M C x).symm
    (M.orientation.orientation (componentInclusion M C x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedOrientedManifold.componentTangentOrientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedOrientedManifold.componentTangentOrientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedOrientedManifold.componentTangentOrientation ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.componentTangentOrientation

theorem componentInclusionTangentEquiv_eq_refl (C : ConnectedComponents M.Carrier)
    (x : componentOpen M C) :
    componentInclusionTangentEquiv M C x =
      LinearEquiv.refl ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) := by
  refine LinearEquiv.ext fun v => ?_
  rw [componentInclusionTangentEquiv_apply]
  change mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
    (Subtype.val : componentOpen M C → M.Carrier) x v = v
  rw [DifferentialGeometry.mfderiv_subtype_val]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedOrientedManifold.componentInclusionTangentEquiv_eq_refl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedOrientedManifold.componentInclusionTangentEquiv_eq_refl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedOrientedManifold.componentInclusionTangentEquiv_eq_refl ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.componentInclusionTangentEquiv_eq_refl

@[simp]
theorem componentTangentOrientation_apply (C : ConnectedComponents M.Carrier)
    (x : componentOpen M C) :
    componentTangentOrientation M C x = M.orientation.orientation x.1 := by
  rw [componentTangentOrientation]
  erw [componentInclusionTangentEquiv_eq_refl M C x, LinearEquiv.refl_symm,
    Orientation.map_refl]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedOrientedManifold.componentTangentOrientation_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedOrientedManifold.componentTangentOrientation_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedOrientedManifold.componentTangentOrientation_apply ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.componentTangentOrientation_apply

theorem componentTangentOrientation_locally_constant (C : ConnectedComponents M.Carrier) :
    ∀ p x : componentOpen M C,
    ∀ hx : x ∈ (_root_.FiberBundle.trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) p).baseSet,
    ∃ U : Set (componentOpen M C), IsOpen U ∧ x ∈ U ∧
      ∃ hU : U ⊆ (_root_.FiberBundle.trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) p).baseSet,
      ∀ y : componentOpen M C, ∀ hy : y ∈ U,
        Orientation.map (Fin n)
          (tangentChartEquiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (componentOpen M C) p y (hU hy))
          (componentTangentOrientation M C y) =
        Orientation.map (Fin n)
          (tangentChartEquiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (componentOpen M C) p x hx)
          (componentTangentOrientation M C x) := by
  simpa only [ManifoldOrientation.restrictOpen_orientation, componentTangentOrientation_apply M C]
    using (M.orientation.restrictOpen (componentOpen M C)).locally_constant

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedOrientedManifold.componentTangentOrientation_locally_constant then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedOrientedManifold.componentTangentOrientation_locally_constant"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedOrientedManifold.componentTangentOrientation_locally_constant ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.componentTangentOrientation_locally_constant

def componentOrientation (C : ConnectedComponents M.Carrier) :
    ManifoldOrientation 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (componentOpen M C) n where
  dimension_eq := M.orientation.dimension_eq
  orientation := componentTangentOrientation M C
  locally_constant := componentTangentOrientation_locally_constant M C

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedOrientedManifold.componentOrientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedOrientedManifold.componentOrientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedOrientedManifold.componentOrientation ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.componentOrientation

theorem componentInclusion_preservesOrientation (C : ConnectedComponents M.Carrier)
    (x : componentOpen M C) :
    Orientation.map (Fin n) (componentInclusionTangentEquiv M C x)
      ((componentOrientation M C).orientation x) =
        M.orientation.orientation (componentInclusion M C x) :=
  (Orientation.map (Fin n) (componentInclusionTangentEquiv M C x)).apply_symm_apply _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedOrientedManifold.componentInclusion_preservesOrientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedOrientedManifold.componentInclusion_preservesOrientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedOrientedManifold.componentInclusion_preservesOrientation ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.componentInclusion_preservesOrientation

def component (C : ConnectedComponents M.Carrier) : ConnectedClosedOrientedManifold.{u} n where
  Carrier := componentOpen M C
  compact := isCompact_iff_compactSpace.mp (isCompact_componentSet M C)
  orientation := componentOrientation M C
  connected := isConnected_iff_connectedSpace.mp (isConnected_componentSet M C)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedOrientedManifold.component then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedOrientedManifold.component"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedOrientedManifold.component ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.component

@[simp]
theorem component_carrier (C : ConnectedComponents M.Carrier) :
    (component M C).Carrier = {x : M.Carrier // ConnectedComponents.mk x = C} := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedOrientedManifold.component_carrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedOrientedManifold.component_carrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedOrientedManifold.component_carrier ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.component_carrier

@[simp]
theorem component_orientation (C : ConnectedComponents M.Carrier) :
    (component M C).orientation = componentOrientation M C := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedOrientedManifold.component_orientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedOrientedManifold.component_orientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedOrientedManifold.component_orientation ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.component_orientation

theorem componentSet_eq_univ_of_preconnectedSpace [PreconnectedSpace M.Carrier]
    (C : ConnectedComponents M.Carrier) : componentSet M C = univ := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe C
  rw [componentSet_mk, PreconnectedSpace.connectedComponent_eq_univ]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedOrientedManifold.componentSet_eq_univ_of_preconnectedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedOrientedManifold.componentSet_eq_univ_of_preconnectedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedOrientedManifold.componentSet_eq_univ_of_preconnectedSpace ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.componentSet_eq_univ_of_preconnectedSpace

theorem componentOpen_eq_top_of_preconnectedSpace [PreconnectedSpace M.Carrier]
    (C : ConnectedComponents M.Carrier) : componentOpen M C = ⊤ := by
  ext x
  simp [componentSet_eq_univ_of_preconnectedSpace M C]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedOrientedManifold.componentOpen_eq_top_of_preconnectedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedOrientedManifold.componentOpen_eq_top_of_preconnectedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedOrientedManifold.componentOpen_eq_top_of_preconnectedSpace ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.componentOpen_eq_top_of_preconnectedSpace

def componentDiffeomorph [PreconnectedSpace M.Carrier] (C : ConnectedComponents M.Carrier) :
    M.Carrier ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯
      componentOpen M C where
  toEquiv :=
    { toFun := fun x => ⟨x, by rw [componentOpen_eq_top_of_preconnectedSpace M C]; trivial⟩
      invFun := fun x => x.1
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  contMDiff_toFun := by
    refine (ContMDiff.subtypeVal_comp_iff (componentOpen M C) _).mp ?_
    exact contMDiff_id
  contMDiff_invFun := contMDiff_subtype_val

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedOrientedManifold.componentDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedOrientedManifold.componentDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedOrientedManifold.componentDiffeomorph ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.componentDiffeomorph

end DifferentialGeometry.Topology.ClosedOrientedManifold

namespace DifferentialGeometry.Topology.ClosedOrientedManifold

universe u
variable {n : ℕ} (M : ClosedOrientedManifold.{u} n)

def componentUnionHomeomorph : (Σ K, (M.component K).Carrier) ≃ₜ M.Carrier := by
  let f : (Σ K, (M.component K).Carrier) → M.Carrier := fun p => p.snd.val
  have hf : Continuous f := continuous_sigma fun _ => continuous_subtype_val
  have hi : Function.Injective f := by
    rintro ⟨K, x⟩ ⟨L, y⟩ h
    have hK : K = L := x.property.symm.trans ((congrArg ConnectedComponents.mk h).trans y.property)
    subst L
    have hxy : x = y := Subtype.ext h
    subst y
    rfl
  have hs : Function.Surjective f := fun x => ⟨⟨ConnectedComponents.mk x, ⟨x, rfl⟩⟩, rfl⟩
  let := M.finite_components
  let := Fintype.ofFinite (ConnectedComponents M.Carrier)
  exact IsHomeomorph.homeomorph f (isHomeomorph_iff_continuous_bijective.mpr ⟨hf, hi, hs⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedOrientedManifold.componentUnionHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedOrientedManifold.componentUnionHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedOrientedManifold.componentUnionHomeomorph ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.componentUnionHomeomorph

theorem componentUnionHomeomorph_apply (K : ConnectedComponents M.Carrier)
    (x : (M.component K).Carrier) : M.componentUnionHomeomorph ⟨K, x⟩ = x.val := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedOrientedManifold.componentUnionHomeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedOrientedManifold.componentUnionHomeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedOrientedManifold.componentUnionHomeomorph_apply ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.componentUnionHomeomorph_apply

end DifferentialGeometry.Topology.ClosedOrientedManifold
