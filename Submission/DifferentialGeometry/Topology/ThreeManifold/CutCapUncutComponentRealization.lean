import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens
import Submission.DifferentialGeometry.Topology.Manifold.ComponentDiffeomorph
import Submission.DifferentialGeometry.Topology.ThreeManifold.CutCapIncidence
import Submission.DifferentialGeometry.Topology.ThreeManifold.PoincareStandard

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology

universe u

namespace ClosedOrientedManifold

namespace OrientedDiffeomorph

variable {n : ℕ} {M N : ClosedOrientedManifold.{u} n}

noncomputable def componentDiffeomorph (e : OrientedDiffeomorph M N)
    (C : ConnectedComponents M.Carrier) :
    M.componentOpen C ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)),
        𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯
      N.componentOpen (e.1.continuous.connectedComponentsMap C) :=
  ClosedOrientedManifold.diffeomorphComponent e.val C

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedOrientedManifold.OrientedDiffeomorph.componentDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedOrientedManifold.OrientedDiffeomorph.componentDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedOrientedManifold.OrientedDiffeomorph.componentDiffeomorph ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.OrientedDiffeomorph.componentDiffeomorph

@[simp]
theorem componentDiffeomorph_apply (e : OrientedDiffeomorph M N)
    (C : ConnectedComponents M.Carrier) (x : M.componentOpen C) :
    (componentDiffeomorph e C x).1 = e.1 x.1 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedOrientedManifold.OrientedDiffeomorph.componentDiffeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedOrientedManifold.OrientedDiffeomorph.componentDiffeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedOrientedManifold.OrientedDiffeomorph.componentDiffeomorph_apply ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.OrientedDiffeomorph.componentDiffeomorph_apply

@[simp]
theorem componentDiffeomorph_symm_apply (e : OrientedDiffeomorph M N)
    (C : ConnectedComponents M.Carrier)
    (y : N.componentOpen (e.1.continuous.connectedComponentsMap C)) :
    ((componentDiffeomorph e C).symm y).1 = e.1.symm y.1 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedOrientedManifold.OrientedDiffeomorph.componentDiffeomorph_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedOrientedManifold.OrientedDiffeomorph.componentDiffeomorph_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedOrientedManifold.OrientedDiffeomorph.componentDiffeomorph_symm_apply ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.OrientedDiffeomorph.componentDiffeomorph_symm_apply

theorem componentDiffeomorph_apply_eq (e : OrientedDiffeomorph M N)
    (C : ConnectedComponents M.Carrier) (x : M.componentOpen C) :
    ∀ v : TangentSpace (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) x,
      (componentDiffeomorph e C).mfderivToContinuousLinearEquiv
        (by simp : (∞ : ℕ∞ω) ≠ 0) x v =
        e.1.mfderivToContinuousLinearEquiv (by simp : (∞ : ℕ∞ω) ≠ 0) x.1 v := by
  intro v
  change mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (⇑(componentDiffeomorph e C)) x v =
    mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (⇑e.1)
      x.1 v
  rw [← DifferentialGeometry.mfderiv_subtypeVal_comp (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (f := ⇑(componentDiffeomorph e C)) x]
  rw [show (fun y : M.componentOpen C => ((componentDiffeomorph e C y :
        N.componentOpen (e.1.continuous.connectedComponentsMap C)) : N.Carrier)) =
      (fun y : M.componentOpen C => e.1 y.1) from rfl]
  rw [DifferentialGeometry.mfderiv_restrict_open e.1 (M.componentOpen C) x]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedOrientedManifold.OrientedDiffeomorph.componentDiffeomorph_apply_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedOrientedManifold.OrientedDiffeomorph.componentDiffeomorph_apply_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedOrientedManifold.OrientedDiffeomorph.componentDiffeomorph_apply_eq ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.OrientedDiffeomorph.componentDiffeomorph_apply_eq

theorem componentDiffeomorph_preservesOrientation (e : OrientedDiffeomorph M N)
    (C : ConnectedComponents M.Carrier) :
    (componentDiffeomorph e C).preservesOrientation (M.componentOrientation C)
      (N.componentOrientation (e.1.continuous.connectedComponentsMap C)) := by
  intro x
  have hlin : ((componentDiffeomorph e C).mfderivToContinuousLinearEquiv
        (by simp : (∞ : ℕ∞ω) ≠ 0) x).toLinearEquiv =
      (e.1.mfderivToContinuousLinearEquiv (by simp : (∞ : ℕ∞ω) ≠ 0) x.1).toLinearEquiv :=
    LinearEquiv.ext fun v => componentDiffeomorph_apply_eq e C x v
  have hsrc : (M.componentOrientation C).orientation x = M.orientation.orientation x.1 :=
    ClosedOrientedManifold.componentTangentOrientation_apply M C x
  have htgt : (N.componentOrientation (e.1.continuous.connectedComponentsMap C)).orientation
        ((componentDiffeomorph e C) x) = N.orientation.orientation (e.1 x.1) := by
    change N.componentTangentOrientation (e.1.continuous.connectedComponentsMap C)
        ((componentDiffeomorph e C) x) = N.orientation.orientation (e.1 x.1)
    rw [ClosedOrientedManifold.componentTangentOrientation_apply]
    rfl
  rw [hsrc, htgt, hlin]
  exact e.2 x.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedOrientedManifold.OrientedDiffeomorph.componentDiffeomorph_preservesOrientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedOrientedManifold.OrientedDiffeomorph.componentDiffeomorph_preservesOrientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedOrientedManifold.OrientedDiffeomorph.componentDiffeomorph_preservesOrientation ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.OrientedDiffeomorph.componentDiffeomorph_preservesOrientation

noncomputable def component (e : OrientedDiffeomorph M N) (C : ConnectedComponents M.Carrier) :
    OrientedDiffeomorph (M.component C).toClosedOrientedManifold
      (N.component (e.1.continuous.connectedComponentsMap C)).toClosedOrientedManifold :=
  ⟨componentDiffeomorph e C, componentDiffeomorph_preservesOrientation e C⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedOrientedManifold.OrientedDiffeomorph.component then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedOrientedManifold.OrientedDiffeomorph.component"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedOrientedManifold.OrientedDiffeomorph.component ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.OrientedDiffeomorph.component

end OrientedDiffeomorph

end ClosedOrientedManifold

namespace SphericalCutCapTransition

variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

local instance instCoreChartedSpace : ChartedSpace (EuclideanHalfSpace 3) E.tubes.core :=
  E.capping.coreCharts

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.instCoreChartedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.instCoreChartedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.instCoreChartedSpace ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.instCoreChartedSpace

local instance instCoreIsManifold : IsManifold (𝓡∂ 3) ∞ E.tubes.core :=
  E.capping.coreSmooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.instCoreIsManifold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.instCoreIsManifold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.instCoreIsManifold ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.instCoreIsManifold

theorem componentSet_inter_range_tube_eq_empty (C : ConnectedComponents M.Carrier)
    (hC : E.cutIndices C = ∅) (a : E.tubes.Index) :
    ClosedOrientedManifold.componentSet M C ∩ _root_.Set.range (E.tubes.tube a) = ∅ := by
  classical
  rw [Set.eq_empty_iff_forall_notMem]
  rintro y ⟨hyC, hyT⟩
  have hsub : _root_.Set.range (E.tubes.tube a) ⊆ ClosedOrientedManifold.componentSet M C :=
    (E.tubes.isPreconnected_range_tube a).subset_isClopen
      ⟨ClosedOrientedManifold.isClosed_componentSet M C,
        ClosedOrientedManifold.isOpen_componentSet M C⟩ ⟨y, hyT, hyC⟩
  have hmem : a ∈ E.cutIndices C :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ a, fun z => hsub ⟨z, rfl⟩⟩
  rw [hC] at hmem
  exact Finset.notMem_empty a hmem

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.componentSet_inter_range_tube_eq_empty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.componentSet_inter_range_tube_eq_empty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.componentSet_inter_range_tube_eq_empty ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.componentSet_inter_range_tube_eq_empty

theorem boundarySphere_notMem_componentSet (C : ConnectedComponents M.Carrier)
    (hC : E.cutIndices C = ∅) (b : E.tubes.Boundary)
    (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    E.tubes.boundarySphere b z ∉ ClosedOrientedManifold.componentSet M C := by
  intro hy
  have hdisj : ClosedOrientedManifold.componentSet M C ∩ _root_.Set.range (E.tubes.tube b.1) = ∅ :=
    E.componentSet_inter_range_tube_eq_empty C hC b.1
  rw [Set.eq_empty_iff_forall_notMem] at hdisj
  exact hdisj _ ⟨hy, ⟨(z, SphericalTubeSystem.boundaryLevel b.2), rfl⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.boundarySphere_notMem_componentSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.boundarySphere_notMem_componentSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.boundarySphere_notMem_componentSet ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.boundarySphere_notMem_componentSet

def coreComponentSet (C : ConnectedComponents M.Carrier) : Set E.tubes.core :=
  {x | (x : M.Carrier) ∈ ClosedOrientedManifold.componentSet M C}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.coreComponentSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.coreComponentSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.coreComponentSet ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.coreComponentSet

theorem mem_coreComponentSet_iff (C : ConnectedComponents M.Carrier) (x : E.tubes.core) :
    x ∈ E.coreComponentSet C ↔ (x : M.Carrier) ∈ ClosedOrientedManifold.componentSet M C :=
  Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.mem_coreComponentSet_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.mem_coreComponentSet_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.mem_coreComponentSet_iff ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.mem_coreComponentSet_iff

theorem isInteriorPoint_of_mem_coreComponentSet (C : ConnectedComponents M.Carrier)
    (hC : E.cutIndices C = ∅) {x : E.tubes.core} (hx : x ∈ E.coreComponentSet C) :
    (𝓡∂ 3).IsInteriorPoint x := by
  by_contra hnot
  have hb : (𝓡∂ 3).IsBoundaryPoint x :=
    (ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint x).mpr hnot
  have hmem : x ∈ (𝓡∂ 3).boundary E.tubes.core := hb
  rw [E.capping.core_boundary] at hmem
  obtain ⟨b, z, hz⟩ := mem_iUnion.mp hmem
  refine E.boundarySphere_notMem_componentSet C hC b z ?_
  have hx' : (x : M.Carrier) ∈ ClosedOrientedManifold.componentSet M C := hx
  rw [← hz] at hx'
  simpa [SphericalTubeSystem.coreBoundarySphere] using hx'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.isInteriorPoint_of_mem_coreComponentSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.isInteriorPoint_of_mem_coreComponentSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.isInteriorPoint_of_mem_coreComponentSet ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.isInteriorPoint_of_mem_coreComponentSet

theorem isOpen_image_coreComponentSet (C : ConnectedComponents M.Carrier)
    (hC : E.cutIndices C = ∅) :
    IsOpen (E.capping.coreInclusion '' E.coreComponentSet C) := by
  classical
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨x, hx, rfl⟩
  have hsd : E.coreComponentSet C ∈ nhds x :=
    ((ClosedOrientedManifold.isOpen_componentSet M C).preimage
      continuous_subtype_val).mem_nhds hx
  exact immersion_image_mem_nhds (f := ⇑E.capping.coreInclusion) (x := x)
    (E.capping.core_embedding.isImmersion.isImmersionAt x)
    (by simp [EuclideanSpace])
    (E.isInteriorPoint_of_mem_coreComponentSet C hC hx) hsd

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.isOpen_image_coreComponentSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.isOpen_image_coreComponentSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.isOpen_image_coreComponentSet ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.isOpen_image_coreComponentSet

theorem isClosed_image_coreComponentSet (C : ConnectedComponents M.Carrier) :
    IsClosed (E.capping.coreInclusion '' E.coreComponentSet C) := by
  have hclosed : IsClosed (E.coreComponentSet C) :=
    (ClosedOrientedManifold.isClosed_componentSet M C).preimage continuous_subtype_val
  have : CompactSpace E.tubes.core := isCompact_iff_compactSpace.mp E.capping.core_compact
  exact (hclosed.isCompact.image E.capping.coreInclusion.continuous).isClosed

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.isClosed_image_coreComponentSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.isClosed_image_coreComponentSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.isClosed_image_coreComponentSet ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.isClosed_image_coreComponentSet

theorem isPreconnected_coreComponentSet (C : ConnectedComponents M.Carrier)
    (hC : E.cutIndices C = ∅) :
    IsPreconnected (E.coreComponentSet C) := by
  have hsub := E.componentSet_subset_core_of_cutIndices_eq_empty C hC
  have hcont : Continuous fun y : ↥(ClosedOrientedManifold.componentSet M C) =>
      (⟨(y : M.Carrier), hsub y.2⟩ : E.tubes.core) :=
    continuous_subtype_val.subtype_mk _
  have : PreconnectedSpace ↥(ClosedOrientedManifold.componentSet M C) :=
    isPreconnected_iff_preconnectedSpace.mp
      (ClosedOrientedManifold.isConnected_componentSet M C).isPreconnected
  have h := (_root_.PreconnectedSpace.isPreconnected_univ (α := ↥(ClosedOrientedManifold.componentSet M C))).image _
    hcont.continuousOn
  have himg : (fun y : ↥(ClosedOrientedManifold.componentSet M C) =>
      (⟨(y : M.Carrier), hsub y.2⟩ : E.tubes.core)) '' _root_.Set.univ = E.coreComponentSet C := by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨(x : M.Carrier), hx⟩, _root_.Set.mem_univ _, Subtype.ext rfl⟩
  rwa [himg] at h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.isPreconnected_coreComponentSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.isPreconnected_coreComponentSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.isPreconnected_coreComponentSet ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.isPreconnected_coreComponentSet

theorem image_coreComponentSet_eq_componentSet (C : ConnectedComponents M.Carrier)
    (hC : E.cutIndices C = ∅) {x : E.tubes.core} (hx : x ∈ E.coreComponentSet C) :
    E.capping.coreInclusion '' E.coreComponentSet C =
      ClosedOrientedManifold.componentSet E.capped
        (ConnectedComponents.mk (E.capping.coreInclusion x)) := by
  have hclop : IsClopen (E.capping.coreInclusion '' E.coreComponentSet C) :=
    ⟨E.isClosed_image_coreComponentSet C, E.isOpen_image_coreComponentSet C hC⟩
  have hxmem : E.capping.coreInclusion x ∈ E.capping.coreInclusion '' E.coreComponentSet C :=
    ⟨x, hx, rfl⟩
  have hpre : IsPreconnected (E.capping.coreInclusion '' E.coreComponentSet C) :=
    (E.isPreconnected_coreComponentSet C hC).image _
      E.capping.coreInclusion.continuous.continuousOn
  have hsub : E.capping.coreInclusion '' E.coreComponentSet C ⊆
      connectedComponent (E.capping.coreInclusion x) := fun y hy =>
    hpre.subset_connectedComponent hxmem hy
  have hsup : connectedComponent (E.capping.coreInclusion x) ⊆
      E.capping.coreInclusion '' E.coreComponentSet C :=
    isPreconnected_connectedComponent.subset_isClopen hclop
      ⟨_, mem_connectedComponent, hxmem⟩
  have hEq : E.capping.coreInclusion '' E.coreComponentSet C =
      connectedComponent (E.capping.coreInclusion x) := Set.Subset.antisymm hsub hsup
  rw [hEq, ClosedOrientedManifold.componentSet_mk]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.image_coreComponentSet_eq_componentSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.image_coreComponentSet_eq_componentSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.image_coreComponentSet_eq_componentSet ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.image_coreComponentSet_eq_componentSet

def UncutCappingRealization : Prop :=
  ∀ (C : ConnectedComponents M.Carrier), E.cutIndices C = ∅ →
    ∀ x : E.tubes.core, x ∈ E.coreComponentSet C →
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (M.component C).toClosedOrientedManifold
        (E.capped.component
          (ConnectedComponents.mk (E.capping.coreInclusion x))).toClosedOrientedManifold)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.UncutCappingRealization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.UncutCappingRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.UncutCappingRealization ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.UncutCappingRealization

def CappedPresentationRealization : Prop :=
  ∀ x : E.tubes.core,
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (E.capped.component
        (ConnectedComponents.mk (E.capping.coreInclusion x))).toClosedOrientedManifold
      (E.outgoingFactor (E.presentation (E.capping.coreInclusion x))).toClosedOrientedManifold)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.CappedPresentationRealization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.CappedPresentationRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.CappedPresentationRealization ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.CappedPresentationRealization

def CappedRetainedPresentationRealization : Prop :=
  ∀ (x : E.tubes.core) (q : Q.Carrier),
    E.presentation (E.capping.coreInclusion x) = Sum.inl q →
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (E.capped.component
          (ConnectedComponents.mk (E.capping.coreInclusion x))).toClosedOrientedManifold
        (Q.component (ConnectedComponents.mk q)).toClosedOrientedManifold)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.CappedRetainedPresentationRealization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.CappedRetainedPresentationRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.CappedRetainedPresentationRealization ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.CappedRetainedPresentationRealization

def CappedDiscardedPresentationRealization : Prop :=
  ∀ (x : E.tubes.core) (d : E.discarded.Carrier),
    E.presentation (E.capping.coreInclusion x) = Sum.inr d →
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (E.capped.component
          (ConnectedComponents.mk (E.capping.coreInclusion x))).toClosedOrientedManifold
        (E.discarded.component (ConnectedComponents.mk d)).toClosedOrientedManifold)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.CappedDiscardedPresentationRealization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.CappedDiscardedPresentationRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.CappedDiscardedPresentationRealization ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.CappedDiscardedPresentationRealization

theorem cappedPresentationRealization_of_retained_of_discarded
    (h₁ : E.CappedRetainedPresentationRealization)
    (h₂ : E.CappedDiscardedPresentationRealization) :
    E.CappedPresentationRealization := by
  intro x
  rcases hx : E.presentation (E.capping.coreInclusion x) with q | d
  · have := h₁ x q hx
    simpa only [SphericalCutCapTransition.outgoingFactor, hx] using this
  · have := h₂ x d hx
    simpa only [SphericalCutCapTransition.outgoingFactor, hx] using this

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cappedPresentationRealization_of_retained_of_discarded then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cappedPresentationRealization_of_retained_of_discarded"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cappedPresentationRealization_of_retained_of_discarded ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cappedPresentationRealization_of_retained_of_discarded

theorem noTubeRealization_of_uncutCappingRealization_of_cappedPresentationRealization
    (h₁ : E.UncutCappingRealization) (h₂ : E.CappedPresentationRealization) :
    E.NoTubeRealization := by
  intro C N hC hN
  obtain ⟨x, hx⟩ := E.exists_core_mem_componentSet C
  have hfac : E.outgoingFactor (E.presentation (E.capping.coreInclusion x)) = N := by
    have hmem : E.outgoingFactor (E.presentation (E.capping.coreInclusion x)) ∈
        E.associatedFactors C := ⟨x, hx, rfl⟩
    rw [hN] at hmem
    simpa using hmem
  obtain ⟨ρ₁⟩ := h₁ C hC x hx
  obtain ⟨ρ₂⟩ := h₂ x
  rw [hfac] at ρ₂
  exact ⟨ρ₁.trans ρ₂⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.noTubeRealization_of_uncutCappingRealization_of_cappedPresentationRealization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.noTubeRealization_of_uncutCappingRealization_of_cappedPresentationRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.noTubeRealization_of_uncutCappingRealization_of_cappedPresentationRealization ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.noTubeRealization_of_uncutCappingRealization_of_cappedPresentationRealization

theorem exists_cutIndices_eq_empty_of_isEmpty_index [IsEmpty E.tubes.Index]
    (C : ConnectedComponents M.Carrier) : E.cutIndices C = ∅ :=
  Finset.not_nonempty_iff_eq_empty.mp fun h => h.elim fun a _ => isEmptyElim a

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.exists_cutIndices_eq_empty_of_isEmpty_index then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.exists_cutIndices_eq_empty_of_isEmpty_index"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.exists_cutIndices_eq_empty_of_isEmpty_index ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.exists_cutIndices_eq_empty_of_isEmpty_index

theorem noTubeRealization_of_uncutCappingRealization_of_retained_of_discarded
    (h₀ : E.UncutCappingRealization) (h₁ : E.CappedRetainedPresentationRealization)
    (h₂ : E.CappedDiscardedPresentationRealization) : E.NoTubeRealization :=
  E.noTubeRealization_of_uncutCappingRealization_of_cappedPresentationRealization h₀
    (E.cappedPresentationRealization_of_retained_of_discarded h₁ h₂)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.noTubeRealization_of_uncutCappingRealization_of_retained_of_discarded then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.noTubeRealization_of_uncutCappingRealization_of_retained_of_discarded"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.noTubeRealization_of_uncutCappingRealization_of_retained_of_discarded ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.noTubeRealization_of_uncutCappingRealization_of_retained_of_discarded

theorem isPoincareStandard_of_capped_of_uncutCappingRealization
    (h : E.UncutCappingRealization) (C : ConnectedComponents M.Carrier)
    (hC : E.cutIndices C = ∅) (x : E.tubes.core) (hx : x ∈ E.coreComponentSet C)
    (hstd : isPoincareStandard
      ((E.capped.component
        (ConnectedComponents.mk (E.capping.coreInclusion x))).toClosedOrientedManifold).Carrier) :
    isPoincareStandard (M.component C).Carrier := by
  obtain ⟨ρ⟩ := h C hC x hx
  exact isPoincareStandard_of_diffeomorph ρ.1 hstd

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.isPoincareStandard_of_capped_of_uncutCappingRealization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.isPoincareStandard_of_capped_of_uncutCappingRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.isPoincareStandard_of_capped_of_uncutCappingRealization ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.isPoincareStandard_of_capped_of_uncutCappingRealization

end SphericalCutCapTransition

end DifferentialGeometry.Topology
