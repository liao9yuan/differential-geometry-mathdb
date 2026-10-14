import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticNeckChildCore
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalScalarCurvature

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Filter
open scoped _root_.Topology
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace GeometricCutoffRecord

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  (G : GeometricCutoffRecord H i parameters)

include G

theorem scalar_gt_protected_of_not_mem_retainedCore
    (x : (H.event i).incoming.terminalRegularOpen)
    (hx : x.1 ∈ (H.event i).transition.trace.tubes.core)
    (hdiscard : (⟨x.1, hx⟩ : (H.event i).transition.trace.tubes.core) ∉
      (H.event i).transition.trace.retainedCore) :
    ((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹ <
      metricScalarAt (H.event i).terminal.metric x := by
  apply lt_of_not_ge
  intro hscalar
  obtain ⟨y, hy, heq⟩ := interior_subset (G.protected_interior x hscalar)
  have hyx : y = (⟨x.1, hx⟩ : (H.event i).transition.trace.tubes.core) :=
    Subtype.ext heq
  exact hdiscard (hyx ▸ hy)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.scalar_gt_protected_of_not_mem_retainedCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.scalar_gt_protected_of_not_mem_retainedCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.scalar_gt_protected_of_not_mem_retainedCore ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.scalar_gt_protected_of_not_mem_retainedCore

theorem scalar_gt_protected_of_presentation_eq_inr
    (x : (H.event i).incoming.terminalRegularOpen)
    (hx : x.1 ∈ (H.event i).transition.trace.tubes.core)
    (d : (H.event i).discarded.Carrier)
    (hdiscard : (H.event i).transition.trace.presentation
      ((H.event i).transition.trace.capping.coreInclusion ⟨x.1, hx⟩) = Sum.inr d) :
    ((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹ <
      metricScalarAt (H.event i).terminal.metric x := by
  apply G.scalar_gt_protected_of_not_mem_retainedCore x hx
  rintro ⟨q, hq⟩
  exact Sum.inr_ne_inl (hdiscard.symm.trans hq)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.scalar_gt_protected_of_presentation_eq_inr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.scalar_gt_protected_of_presentation_eq_inr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.scalar_gt_protected_of_presentation_eq_inr ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.scalar_gt_protected_of_presentation_eq_inr

theorem scalar_gt_protected_on_discarded_core_component
    (z : (H.event i).transition.trace.tubes.core)
    (hz : z ∉ (H.event i).transition.trace.retainedCore)
    (x : (H.event i).incoming.terminalRegularOpen)
    (hx : x.1 ∈ (H.event i).transition.trace.tubes.core)
    (hcomponent : ConnectedComponents.mk (⟨x.1, hx⟩ : (H.event i).transition.trace.tubes.core) =
      ConnectedComponents.mk z) :
    ((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹ <
      metricScalarAt (H.event i).terminal.metric x := by
  apply G.scalar_gt_protected_of_not_mem_retainedCore x hx
  exact (H.event i).transition.trace.connectedComponent_subset_compl_retainedCore z hz
    (ConnectedComponents.coe_eq_coe'.mp hcomponent)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.scalar_gt_protected_on_discarded_core_component then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.scalar_gt_protected_on_discarded_core_component"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.scalar_gt_protected_on_discarded_core_component ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.scalar_gt_protected_on_discarded_core_component

section


theorem exists_late_retained_component_scalar_anchors
    {η : ℝ} (hη : 0 < η) :
    ∃ d ∈ _root_.Set.Ico (H.time i.castSucc) (H.time i.succ),
      ∀ z ∈ (H.event i).transition.trace.retainedCore,
        ∃ y : (H.event i).incoming.terminalRegularOpen,
          ∃ hy : y.val ∈ (H.event i).transition.trace.tubes.core,
            ConnectedComponents.mk (⟨y.val, hy⟩ : (H.event i).transition.trace.tubes.core) =
              ConnectedComponents.mk z ∧
            metricScalarAt (H.event i).terminal.metric y ≤
              ((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹ ∧
            ∀ t ∈ _root_.Set.Ioo d (H.time i.succ),
              (H.event i).incoming.flow.scalar t y.val <
                ((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹ + η := by
  classical
  let _ := (H.event i).transition.core_compact
  let _ := (H.event i).transition.core_locallyConnected
  let C := {c : ConnectedComponents (H.event i).transition.trace.tubes.core //
    ∃ z : (H.event i).transition.trace.tubes.core,
      ConnectedComponents.mk z = c ∧ z ∈ (H.event i).transition.trace.retainedCore}
  have hanchors (c : C) := G.retained_meets_protected c.val c.property
  choose y hy hcomponent hscalar using hanchors
  have hlate (c : C) : ∀ᶠ t in 𝓝[<] H.time i.succ,
      (H.event i).incoming.flow.scalar t (y c).val <
        ((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹ + η := by
    have hbound : metricScalarAt (H.event i).terminal.metric (y c) <
        ((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹ + η :=
      (hscalar c).trans_lt (lt_add_of_pos_right _ hη)
    exact ((H.event i).terminal.tendsto_metricScalarAt (y c)).eventually_lt_const hbound
  have hall : ∀ᶠ t in 𝓝[<] H.time i.succ, ∀ c : C,
      (H.event i).incoming.flow.scalar t (y c).val <
        ((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹ + η :=
    eventually_all.mpr hlate
  obtain ⟨d, hd, hall⟩ :=
    (mem_nhdsLT_iff_exists_mem_Ico_Ioo_subset (H.event i).incoming.lt).mp hall
  refine ⟨d, hd, ?_⟩
  intro z hz
  let c : C := ⟨ConnectedComponents.mk z, z, rfl, hz⟩
  exact ⟨y c, hy c, hcomponent c, hscalar c, fun t ht => hall ht c⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.exists_late_retained_component_scalar_anchors then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.exists_late_retained_component_scalar_anchors"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.exists_late_retained_component_scalar_anchors ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.exists_late_retained_component_scalar_anchors

theorem exists_late_retained_component_scalar_gap
    {η : ℝ} (hη : 0 < η) :
    ∃ d ∈ _root_.Set.Ico (H.time i.castSucc) (H.time i.succ),
      ∀ t ∈ _root_.Set.Ioo d (H.time i.succ), ∀ C : ℝ, 0 ≤ C →
        ∀ x : (H.stage i.castSucc).Carrier,
          C * (((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹ + η) <
            (H.event i).incoming.flow.scalar t x →
          ∀ z ∈ (H.event i).transition.trace.retainedCore,
            ∃ y : (H.event i).transition.trace.tubes.core,
              ConnectedComponents.mk y = ConnectedComponents.mk z ∧
              C * (H.event i).incoming.flow.scalar t y.val <
                (H.event i).incoming.flow.scalar t x := by
  obtain ⟨d, hd, hanchors⟩ := G.exists_late_retained_component_scalar_anchors hη
  refine ⟨d, hd, ?_⟩
  intro t ht C hC x hx z hz
  obtain ⟨y, hy, hcomponent, _, hscalar⟩ := hanchors z hz
  refine ⟨⟨y.val, hy⟩, hcomponent, ?_⟩
  exact (mul_le_mul_of_nonneg_left (hscalar t ht).le hC).trans_lt hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.exists_late_retained_component_scalar_gap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.exists_late_retained_component_scalar_gap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.exists_late_retained_component_scalar_gap ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.exists_late_retained_component_scalar_gap

end

end GeometricCutoffRecord

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
