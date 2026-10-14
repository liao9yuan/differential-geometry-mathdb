import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventRetainedMaps
import Submission.DifferentialGeometry.Topology.Embedding.Lift
import Submission.DifferentialGeometry.Topology.Embedding.Diffeomorph
import Submission.DifferentialGeometry.Topology.Manifold.OpenEmbedding
import Submission.DifferentialGeometry.Topology.Manifold.ImmersionDifferential
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventData
import Submission.DifferentialGeometry.Topology.Manifold.SmoothEmbeddingInteriorImage

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Submission.Set _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace MetricCutCapEvent

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)

theorem exists_oldTerminal_eq_of_mem_interior_old
    (x : E.incoming.terminalRegularOpen)
    (hx : x.1 ∈ interior (Subtype.val '' E.old)) :
    letI : ChartedSpace (EuclideanHalfSpace 3) E.old := E.oldCharts
    ∃ w : E.old, E.oldTerminal w = x ∧ (𝓡∂ 3).IsInteriorPoint w ∧
      E.RegularCrossing x.1 (E.oldOutput w) := by
  let : ChartedSpace (EuclideanHalfSpace 3) E.old := E.oldCharts
  obtain ⟨z, hz, hzx⟩ := interior_subset hx
  let w : E.old := ⟨z, hz⟩
  have hrange : Set.range (fun y : E.old => (y.1.1 : P.Carrier)) =
      Subtype.val '' E.old := by
    ext p
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y.1, y.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  have hw : (𝓡∂ 3).IsInteriorPoint w :=
    E.old_induced.isInteriorPoint_of_mem_interior_range rfl (by
      change z.1 ∈ interior _
      rw [hrange, hzx]
      exact hx) BoundarylessManifold.isInteriorPoint
  exact ⟨w, Subtype.ext ((E.oldTerminal_eq w).trans hzx), hw, w, hw, hzx, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.exists_oldTerminal_eq_of_mem_interior_old then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.exists_oldTerminal_eq_of_mem_interior_old"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.exists_oldTerminal_eq_of_mem_interior_old ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.exists_oldTerminal_eq_of_mem_interior_old

theorem exists_oldTerminal_eq_of_mem_interior_retained
    (hOld : E.old = E.transition.trace.retainedCore)
    (x : E.incoming.terminalRegularOpen)
    (hx : x.1 ∈ interior (Subtype.val '' E.transition.trace.retainedCore)) :
    ∃ z : E.old, E.oldTerminal z = x ∧ E.RegularCrossing x.val (E.oldOutput z) ∧
      E.transition.trace.presentation (E.transition.trace.capping.coreInclusion z.val) =
        Sum.inl (E.oldOutput z) := by
  rw [← hOld] at hx
  obtain ⟨z, hz, _, hcross⟩ := E.exists_oldTerminal_eq_of_mem_interior_old x hx
  exact ⟨z, hz, hcross, E.oldOutput_eq z⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.exists_oldTerminal_eq_of_mem_interior_retained then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.exists_oldTerminal_eq_of_mem_interior_retained"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.exists_oldTerminal_eq_of_mem_interior_retained ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.exists_oldTerminal_eq_of_mem_interior_retained

end MetricCutCapEvent

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.Manifold _root_.Submission.Manifold _root_.TopologicalSpace
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

universe u
variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)

theorem exists_regularCrossing_of_mem_interior_oldOutput
    (q : Q.Carrier) (hq : q ∈ interior (_root_.Set.range E.oldOutput)) :
    ∃ p : P.Carrier, E.RegularCrossing p q := by
  let : ChartedSpace (EuclideanHalfSpace 3) E.transition.trace.tubes.core := E.transition.coreCharts
  let : IsManifold (𝓡∂ 3) ∞ E.transition.trace.tubes.core := E.transition.coreSmooth
  let : ChartedSpace (EuclideanHalfSpace 3) E.old := E.oldCharts
  let : IsManifold (𝓡∂ 3) ∞ E.old := E.oldSmooth
  let V : _root_.TopologicalSpace.Opens Q.Carrier := ⟨interior (_root_.Set.range E.oldOutput), isOpen_interior⟩
  let i : V → Q.Carrier ⊕ E.discarded.Carrier := fun y => Sum.inl y.val
  have hi : _root_.Manifold.IsSmoothEmbedding ThreeModel ThreeModel ∞ i :=
    (IsSmoothEmbedding.sumInl (I := ThreeModel) (M := Q.Carrier)
      (M' := E.discarded.Carrier)).comp_of_boundarylessManifold_middle
        (IsSmoothEmbedding.of_opens V) (by simp)
  let z : V → E.capped.Carrier := E.transition.presentation.symm ∘ i
  have hz : _root_.Manifold.IsSmoothEmbedding ThreeModel ThreeModel ∞ z :=
    hi.diffeomorph_comp E.transition.presentation.symm
  have hsub : _root_.Set.range z ⊆ _root_.Set.range E.transition.trace.capping.coreInclusion := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨x, hx⟩ := interior_subset y.property
    refine ⟨x.val, ?_⟩
    apply E.transition.presentation.injective
    change E.transition.presentation (E.transition.trace.capping.coreInclusion x.val) =
      E.transition.presentation (E.transition.presentation.symm (i y))
    rw [E.transition.presentation.apply_symm_apply]
    exact (congrFun E.transition.presentation_eq (E.transition.trace.capping.coreInclusion x.val)).trans
      ((E.oldOutput_eq x).trans (congrArg Sum.inl hx))
  let k : V → E.transition.trace.tubes.core :=
    E.transition.core_inclusion_smooth.lift z hsub
  have hk : ContMDiff ThreeModel (𝓡∂ 3) ∞ k :=
    E.transition.core_inclusion_smooth.contMDiff_lift hz.contMDiff hsub
  have hkz : E.transition.trace.capping.coreInclusion ∘ k = z :=
    funext (E.transition.core_inclusion_smooth.comp_lift hsub)
  let f : V → P.Carrier := Subtype.val ∘ k
  have hf : ContMDiff ThreeModel ThreeModel ∞ f := E.transition.core_induced.contMDiff.comp hk
  have hkinj (y : V) : _root_.Function.Injective (mfderiv ThreeModel (𝓡∂ 3) k y) := by
    have hinj := (hz.isImmersion.isImmersionAt y).injective_mfderiv (by simp)
    rw [← hkz, mfderiv_comp y
      (E.transition.core_inclusion_smooth.contMDiff.mdifferentiableAt (by simp))
      (hk.mdifferentiableAt (by simp))] at hinj
    exact Function.Injective.of_comp hinj
  have hfinj (y : V) : _root_.Function.Injective (mfderiv ThreeModel ThreeModel f y) := by
    have hi := (E.transition.core_induced.isImmersion.isImmersionAt (k y)).injective_mfderiv (by simp)
    rw [show f = Subtype.val ∘ k from rfl,
      mfderiv_comp y (E.transition.core_induced.contMDiff.mdifferentiableAt (by simp))
        (hk.mdifferentiableAt (by simp))]
    exact hi.comp (hkinj y)
  have hlocal := DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv
    f hf hfinj rfl
  have hmem (y : V) : ∃ x : E.old, f y = x.val.val ∧ E.oldOutput x = y.val := by
    obtain ⟨x, hx⟩ := interior_subset y.property
    have hkx : k y = x.val := by
      apply E.transition.core_inclusion_smooth.isEmbedding.injective
      rw [E.transition.core_inclusion_smooth.comp_lift hsub y]
      apply E.transition.presentation.injective
      change E.transition.presentation (E.transition.presentation.symm (i y)) = _
      rw [E.transition.presentation.apply_symm_apply]
      exact ((congrFun E.transition.presentation_eq
        (E.transition.trace.capping.coreInclusion x.val)).trans
          ((E.oldOutput_eq x).trans (congrArg Sum.inl hx))).symm
    exact ⟨x, congrArg Subtype.val hkx, hx⟩
  have hsubold : _root_.Set.range f ⊆ Subtype.val '' E.old := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨x, hx, _⟩ := hmem y
    exact ⟨x.val, x.property, hx.symm⟩
  let y : V := ⟨q, hq⟩
  obtain ⟨x, hxy, hxq⟩ := hmem y
  have hpi : x.val.val ∈ interior (Subtype.val '' E.old) := by
    rw [← hxy]
    apply interior_mono hsubold
    rw [hlocal.isOpenMap.isOpen_range.interior_eq]
    exact _root_.Set.mem_range_self y
  obtain ⟨x', hx', _, hcross⟩ :=
    E.exists_oldTerminal_eq_of_mem_interior_old (E.oldTerminal x) (by
      rw [E.oldTerminal_eq]
      exact hpi)
  have heq : x' = x := E.oldTerminal_isSmoothEmbedding.isEmbedding.injective hx'
  refine ⟨x.val.val, ?_⟩
  simpa only [heq, hxq, E.oldTerminal_eq] using hcross

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.exists_regularCrossing_of_mem_interior_oldOutput then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.exists_regularCrossing_of_mem_interior_oldOutput"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.exists_regularCrossing_of_mem_interior_oldOutput ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.exists_regularCrossing_of_mem_interior_oldOutput

theorem exists_terminal_regularCrossing_of_mem_interior_oldOutput
    (q : Q.Carrier) (hq : q ∈ interior (_root_.Set.range E.oldOutput)) :
    ∃ p : E.incoming.terminalRegularOpen, E.RegularCrossing p.val q := by
  obtain ⟨p, x, hx, hxp, hxq⟩ := E.exists_regularCrossing_of_mem_interior_oldOutput q hq
  refine ⟨E.oldTerminal x, x, hx, ?_, hxq⟩
  exact (E.oldTerminal_eq x).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.exists_terminal_regularCrossing_of_mem_interior_oldOutput then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.exists_terminal_regularCrossing_of_mem_interior_oldOutput"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.exists_terminal_regularCrossing_of_mem_interior_oldOutput ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.exists_terminal_regularCrossing_of_mem_interior_oldOutput

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent
