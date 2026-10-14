import Submission.DifferentialGeometry.Topology.Manifold.HalfClosedInterval
import Submission.DifferentialGeometry.Topology.Manifold.Attachment.RadialCap
import Submission.DifferentialGeometry.Geometry.Metric.PolarCoordinates

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Manifold _root_.IsManifold _root_.TopologicalSpace _root_.Function
open scoped _root_.Manifold _root_.Topology _root_.ContDiff
open _root_.Submission.DifferentialGeometry.Topology.Manifold _root_.Submission.DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.Topology.Manifold.Attachment

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.E3 target :: scope.openDecls } }
private abbrev E2 := EuclideanSpace ℝ (Fin 2)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.E2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.E2 target :: scope.openDecls } }
private abbrev E1 := EuclideanSpace ℝ (Fin 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.E1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.E1 target :: scope.openDecls } }
private abbrev S2 := Metric.sphere (0 : E3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.S2 target :: scope.openDecls } }
private abbrev IR := (𝓡 2).prod (𝓡∂ 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.IR
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.IR target :: scope.openDecls } }
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.IC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.IC target :: scope.openDecls } }
private abbrev Retained (B : ℝ) := S2 × _root_.Set.Ico (0 : ℝ) B

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.Retained
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.Retained target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.Manifold.Attachment.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }
private def radialBall (L B : ℝ) : _root_.TopologicalSpace.Opens E3 :=
  ⟨{x | ‖x‖ < L + B}, isOpen_lt continuous_norm continuous_const⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.radialBall
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.radialBall target :: scope.openDecls } }

def retainedRadialMap {L B : ℝ} (hL : 0 < L) : Retained B → radialBall L B :=
  fun q => ⟨(L + q.2.val) • q.1.val, by
    change ‖(L + q.2.val) • q.1.val‖ < L + B
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (add_pos_of_pos_of_nonneg hL q.2.property.1),
      norm_eq_of_mem_sphere, mul_one]
    linarith [q.2.property.2]⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.Attachment.retainedRadialMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.Attachment.retainedRadialMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.Attachment.retainedRadialMap ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.retainedRadialMap

@[simp] theorem retainedRadialMap_apply {L B : ℝ} (hL : 0 < L) (q : Retained B) :
    (retainedRadialMap hL q : E3) = (L + q.2.val) • q.1.val := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.Attachment.retainedRadialMap_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.Attachment.retainedRadialMap_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.Attachment.retainedRadialMap_apply ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.retainedRadialMap_apply

theorem retainedRadialMap_norm {L B : ℝ} (hL : 0 < L) (q : Retained B) :
    ‖(retainedRadialMap hL q : E3)‖ = L + q.2.val := by
  rw [retainedRadialMap_apply, norm_smul, Real.norm_eq_abs,
    abs_of_pos (add_pos_of_pos_of_nonneg hL q.2.property.1), norm_eq_of_mem_sphere, mul_one]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.Attachment.retainedRadialMap_norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.Attachment.retainedRadialMap_norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.Attachment.retainedRadialMap_norm ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.retainedRadialMap_norm

theorem range_retainedRadialMap {L B : ℝ} (hL : 0 < L) :
    range (retainedRadialMap (B := B) hL) = {x : radialBall L B | L ≤ ‖x.val‖} := by
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    change L ≤ ‖(retainedRadialMap hL q : E3)‖
    rw [retainedRadialMap_norm hL q]
    linarith [q.2.property.1]
  · intro hx
    obtain ⟨q, hq⟩ := (retainedCylinderHomeomorphShell (B := B) hL).surjective ⟨x, hx⟩
    exact ⟨q, congrArg Subtype.val hq⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.Attachment.range_retainedRadialMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.Attachment.range_retainedRadialMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.Attachment.range_retainedRadialMap ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.range_retainedRadialMap

theorem retainedRadialMap_eq_attachment {L B : ℝ} (hL : 0 < L) (hB : 0 < B)
    (q : Retained B) :
    retainedRadialMap hL q = radialCapAttachmentHomeomorph hL hB
      (DifferentialGeometry.Topology.adjunctionLower
        (i := radialCapBoundary hL) (retainedBoundary hB) q) := by
  apply Subtype.ext
  exact (radialCapAttachmentHomeomorph_retained hL hB q).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.Attachment.retainedRadialMap_eq_attachment then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.Attachment.retainedRadialMap_eq_attachment"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.Attachment.retainedRadialMap_eq_attachment ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.retainedRadialMap_eq_attachment

theorem retainedCylinder_boundary_eq {B : ℝ} (hB : 0 < B) :
    letI := halfClosedIntervalChartedSpace hB
    IR.boundary (Retained B) = {q | q.2.val = 0} := by
  let : ChartedSpace (EuclideanHalfSpace 1) (_root_.Set.Ico (0 : ℝ) B) := halfClosedIntervalChartedSpace hB
  let : IsManifold (𝓡∂ 1) ∞ (_root_.Set.Ico (0 : ℝ) B) := halfClosedInterval_isManifold hB
  rw [ModelWithCorners.boundary_of_boundaryless_left, halfClosedInterval_boundary_eq hB]
  ext q
  change (True ∧ q.2.val = 0) ↔ q.2.val = 0
  exact ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.Attachment.retainedCylinder_boundary_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.Attachment.retainedCylinder_boundary_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.Attachment.retainedCylinder_boundary_eq ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.retainedCylinder_boundary_eq

private def modelEquiv : (E2 × ℝ) ≃L[ℝ] E3 :=
  ((ContinuousLinearEquiv.refl ℝ E2).prodCongr
    (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)).symm).trans
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)).symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.modelEquiv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.modelEquiv target :: scope.openDecls } }

private def sphereCylinderChart (L : ℝ) (y : S2) :
    OpenPartialHomeomorph (S2 × ℝ) (E2 × ℝ) :=
  (chartAt E2 y).prod (Homeomorph.addLeft (-L)).toOpenPartialHomeomorph

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.sphereCylinderChart
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.sphereCylinderChart target :: scope.openDecls } }

private theorem sphereCylinderChart_smooth (L : ℝ) (y : S2) :
    ContMDiffOn IC IC ∞ (sphereCylinderChart L y) (sphereCylinderChart L y).source := by
  exact (contMDiffOn_chart (I := 𝓡 2)).prodMap
    (show ContMDiffOn 𝓘(ℝ) 𝓘(ℝ) ∞ (Homeomorph.addLeft (-L)) _root_.Set.univ from
      (by fun_prop : ContDiff ℝ ∞ (fun t : ℝ => -L + t)).contMDiff.contMDiffOn)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.sphereCylinderChart_smooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.sphereCylinderChart_smooth target :: scope.openDecls } }

private theorem sphereCylinderChart_symm_smooth (L : ℝ) (y : S2) :
    ContMDiffOn IC IC ∞ (sphereCylinderChart L y).symm (sphereCylinderChart L y).target := by
  apply (contMDiffOn_chart_symm (I := 𝓡 2)).prodMap
  simpa [Homeomorph.addLeft] using
    (show ContMDiffOn 𝓘(ℝ) 𝓘(ℝ) ∞ (fun t : ℝ => L + t) _root_.Set.univ from
      (by fun_prop : ContDiff ℝ ∞ (fun t : ℝ => L + t)).contMDiff.contMDiffOn)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.sphereCylinderChart_symm_smooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.sphereCylinderChart_symm_smooth target :: scope.openDecls } }

private def ambientRadialChart (L : ℝ) (y : S2) : OpenPartialHomeomorph E3 E3 :=
  (euclideanPolarDiffeomorph (E := E3) (n := 2)).symm.toOpenPartialHomeomorph.trans
    ((sphereCylinderChart L y).trans modelEquiv.toHomeomorph.toOpenPartialHomeomorph)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.ambientRadialChart
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.ambientRadialChart target :: scope.openDecls } }

private theorem modelEquiv_smooth : ContMDiff IC (𝓡 3) ∞ modelEquiv := by
  dsimp only [IC]
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  exact modelEquiv.contDiff.contMDiff

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.modelEquiv_smooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.modelEquiv_smooth target :: scope.openDecls } }

private theorem modelEquiv_symm_smooth : ContMDiff (𝓡 3) IC ∞ modelEquiv.symm := by
  dsimp only [IC]
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  exact modelEquiv.symm.contDiff.contMDiff

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.modelEquiv_symm_smooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.modelEquiv_symm_smooth target :: scope.openDecls } }

private theorem ambientRadialChart_mem_maximalAtlas (L : ℝ) (y : S2) :
    ambientRadialChart L y ∈ _root_.IsManifold.maximalAtlas (𝓡 3) ∞ E3 := by
  apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
  · apply (modelEquiv_smooth.contMDiffOn (s := _root_.Set.univ)).comp
    · apply (sphereCylinderChart_smooth L y).comp
      · exact (euclideanPolarDiffeomorph (E := E3) (n := 2)).contMDiffOn_invFun.mono
          (fun _ hx => hx.1)
      · exact fun _ hx => hx.2.1
    · exact fun _ _ => _root_.Set.mem_univ _
  · apply (euclideanPolarDiffeomorph (E := E3) (n := 2)).contMDiffOn_toFun.comp
    · apply (sphereCylinderChart_symm_smooth L y).comp modelEquiv_symm_smooth.contMDiffOn
      exact fun _ hx => hx.1.2
    · exact fun _ hx => hx.2

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.ambientRadialChart_mem_maximalAtlas
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.ambientRadialChart_mem_maximalAtlas target :: scope.openDecls } }

private theorem polar_symm_retained {L B : ℝ} (hL : 0 < L) (q : Retained B) :
    (euclideanPolarDiffeomorph (E := E3) (n := 2)).symm
      (retainedRadialMap hL q : E3) = (q.1, L + q.2.val) := by
  change (euclideanPolarDiffeomorph (E := E3) (n := 2)).symm
    (euclideanPolarDiffeomorph (E := E3) (n := 2) (q.1, L + q.2.val)) = _
  exact (euclideanPolarDiffeomorph (E := E3) (n := 2)).left_inv
    (add_pos_of_pos_of_nonneg hL q.2.property.1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.polar_symm_retained
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.polar_symm_retained target :: scope.openDecls } }

private theorem ambientRadialChart_apply {L B : ℝ} (hL : 0 < L)
    (y : S2) (q : Retained B) :
    ambientRadialChart L y (retainedRadialMap hL q : E3) =
      modelEquiv ((chartAt E2 y) q.1, q.2.val) := by
  change modelEquiv (sphereCylinderChart L y
    ((euclideanPolarDiffeomorph (E := E3) (n := 2)).symm
      (retainedRadialMap hL q : E3))) = _
  rw [polar_symm_retained hL q]
  congr 1
  change ((chartAt E2 y) q.1, -L + (L + q.2.val)) = _
  rw [neg_add_cancel_left]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.ambientRadialChart_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.ambientRadialChart_apply target :: scope.openDecls } }

private theorem retained_mem_ambientRadialChart_source {L B : ℝ} (hL : 0 < L)
    (q : Retained B) :
    (retainedRadialMap hL q : E3) ∈ (ambientRadialChart L q.1).source := by
  change (retainedRadialMap hL q : E3) ≠ 0 ∧
    (euclideanPolarDiffeomorph (E := E3) (n := 2)).symm
      (retainedRadialMap hL q : E3) ∈
      ((sphereCylinderChart L q.1).trans modelEquiv.toHomeomorph.toOpenPartialHomeomorph).source
  refine ⟨?_, ?_⟩
  · exact euclideanPolarMap_ne_zero (q := (q.1, L + q.2.val))
      (add_pos_of_pos_of_nonneg hL q.2.property.1)
  · rw [polar_symm_retained hL q]
    exact ⟨⟨mem_chart_source E2 q.1, _root_.Set.mem_univ _⟩, _root_.Set.mem_univ _⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.retained_mem_ambientRadialChart_source
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.retained_mem_ambientRadialChart_source target :: scope.openDecls } }

private theorem restrictedChart_mem_maximalAtlas (U : _root_.TopologicalSpace.Opens E3) (hU : Nonempty U)
    (e : OpenPartialHomeomorph E3 E3) (he : e ∈ _root_.IsManifold.maximalAtlas (𝓡 3) ∞ E3) :
    e.subtypeRestr hU ∈ _root_.IsManifold.maximalAtlas (𝓡 3) ∞ U := by
  apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
  · change ContMDiffOn (𝓡 3) (𝓡 3) ∞ (e ∘ (Subtype.val : U → E3))
      (e.subtypeRestr hU).source
    exact (contMDiffOn_of_mem_maximalAtlas he).comp
      (contMDiff_subtype_val (U := U)).contMDiffOn
      (fun x hx => by simpa only [e.subtypeRestr_source hU] using hx)
  · intro z hz
    apply (ContMDiffWithinAt.subtypeVal_comp_iff U (e.subtypeRestr hU).symm
      (e.subtypeRestr hU).target z).mp
    apply ((contMDiffOn_symm_of_mem_maximalAtlas he).mono
      (e.subtypeRestr_target_subset hU)).congr
      (fun w hw => e.subtypeRestr_symm_apply hU hw) z hz

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.restrictedChart_mem_maximalAtlas
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.restrictedChart_mem_maximalAtlas target :: scope.openDecls } }

private def normalEquiv : ((E2 × E1) × Unit) ≃L[ℝ] E3 :=
  (ContinuousLinearEquiv.prodUnique ℝ (E2 × E1) Unit).trans
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)).symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.normalEquiv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.normalEquiv target :: scope.openDecls } }

theorem isSmoothEmbedding_retainedRadialMap {L B : ℝ} (hL : 0 < L) (hB : 0 < B) :
    letI := halfClosedIntervalChartedSpace hB
    IsSmoothEmbedding IR (𝓡 3) ∞ (retainedRadialMap (B := B) hL) := by
  let : ChartedSpace (EuclideanHalfSpace 1) (_root_.Set.Ico (0 : ℝ) B) := halfClosedIntervalChartedSpace hB
  let : IsManifold (𝓡∂ 1) ∞ (_root_.Set.Ico (0 : ℝ) B) := halfClosedInterval_isManifold hB
  refine ⟨?_, ?_⟩
  · suffices h : _root_.Manifold.IsImmersionOfComplement Unit IR (𝓡 3) ∞
        (retainedRadialMap (B := B) hL) from h.isImmersion
    intro q
    have hBall : Nonempty (radialBall L B) := ⟨⟨0, by simpa [radialBall] using add_pos hL hB⟩⟩
    let e := ambientRadialChart L q.1
    let c := e.subtypeRestr hBall
    refine IsImmersionAtOfComplement.mk_of_continuousAt
      (show ContinuousAt (retainedRadialMap (B := B) hL) q from by
        unfold retainedRadialMap
        fun_prop) normalEquiv
      (chartAt (ModelProd E2 (EuclideanHalfSpace 1)) q) c
      (mem_chart_source _ q) (by
        simpa only [c, e, OpenPartialHomeomorph.subtypeRestr_source, _root_.Set.mem_preimage] using
          retained_mem_ambientRadialChart_source hL q)
      (_root_.IsManifold.chart_mem_maximalAtlas _) (restrictedChart_mem_maximalAtlas _ hBall e
        (ambientRadialChart_mem_maximalAtlas L q.1)) ?_
    intro z hz
    let p : Retained B := ((chartAt (ModelProd E2 (EuclideanHalfSpace 1)) q).extend IR).symm z
    have heq := ((chartAt (ModelProd E2 (EuclideanHalfSpace 1)) q).extend IR).right_inv hz
    have hcoords : extChartAt IR q p =
        ((chartAt E2 q.1) p.1, (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)).symm p.2.val) := by
      apply Prod.ext
      · rfl
      · ext i
        fin_cases i
        change (extChartAt (𝓡∂ 1) q.2 p.2) 0 = p.2.val
        simpa using halfClosedInterval_extChartAt_apply hB q.2 p.2
    change ambientRadialChart L q.1 (retainedRadialMap hL p : E3) = normalEquiv (z, 0)
    rw [ambientRadialChart_apply hL q.1 p]
    have hzcoords : z =
        ((chartAt E2 q.1) p.1, (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)).symm p.2.val) :=
      heq.symm.trans hcoords
    rw [hzcoords]
    rfl
  · exact _root_.Topology.IsEmbedding.subtypeVal.comp
      (retainedCylinderHomeomorphShell (B := B) hL).isEmbedding

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.Attachment.isSmoothEmbedding_retainedRadialMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.Attachment.isSmoothEmbedding_retainedRadialMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.Attachment.isSmoothEmbedding_retainedRadialMap ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.isSmoothEmbedding_retainedRadialMap

end DifferentialGeometry.Topology.Manifold.Attachment
