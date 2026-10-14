import Submission.DifferentialGeometry.Topology.Manifold.Attachment.RadialEmbedding
import Submission.DifferentialGeometry.Topology.Manifold.ScaledClosedBall

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Manifold _root_.IsManifold _root_.TopologicalSpace _root_.Function
open scoped _root_.Manifold _root_.Topology _root_.ContDiff
open _root_.Submission.DifferentialGeometry.Topology _root_.Submission.DifferentialGeometry.Topology.Handle
open _root_.Submission.DifferentialGeometry.Topology.Manifold

namespace DifferentialGeometry.Topology.Manifold.Attachment

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.E3 target :: scope.openDecls } }
private abbrev S2 := Metric.sphere (0 : E3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.S2 target :: scope.openDecls } }
private abbrev Retained (B : ℝ) := S2 × _root_.Set.Ico (0 : ℝ) B

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.Retained
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.Retained target :: scope.openDecls } }
private abbrev IR := (𝓡 2).prod (𝓡∂ 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.IR
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.IR target :: scope.openDecls } }
private def radialBall (L B : ℝ) : _root_.TopologicalSpace.Opens E3 :=
  ⟨{x | ‖x‖ < L + B}, isOpen_lt continuous_norm continuous_const⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.radialBall
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.radialBall target :: scope.openDecls } }
private abbrev Attachment {L B : ℝ} (hL : 0 < L) (hB : 0 < B) :=
  AdjunctionSpace (radialCapBoundary hL) (retainedBoundary hB)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.Attachment
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.Attachment target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.Manifold.Attachment.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }

@[reducible] def radialCapAttachmentChartedSpace {L B : ℝ} (hL : 0 < L) (hB : 0 < B) :
    ChartedSpace E3 (Attachment hL hB) :=
  chartedSpaceOfHomeomorph (M := radialBall L B) (radialCapAttachmentHomeomorph hL hB : Attachment hL hB ≃ₜ radialBall L B)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachmentChartedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachmentChartedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachmentChartedSpace ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachmentChartedSpace

theorem radialCapAttachment_chartAt {L B : ℝ} (hL : 0 < L) (hB : 0 < B)
    (x : Attachment hL hB) :
    letI := radialCapAttachmentChartedSpace hL hB
    chartAt E3 x = (radialCapAttachmentHomeomorph hL hB).toOpenPartialHomeomorph.trans
      (chartAt (M := radialBall L B) E3 (radialCapAttachmentHomeomorph hL hB x)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachment_chartAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachment_chartAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachment_chartAt ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachment_chartAt

theorem radialCapAttachment_t2Space {L B : ℝ} (hL : 0 < L) (hB : 0 < B) :
    T2Space (Attachment hL hB) :=
  (radialCapAttachmentHomeomorph hL hB).isEmbedding.t2Space

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachment_t2Space then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachment_t2Space"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachment_t2Space ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachment_t2Space

theorem radialCapAttachment_secondCountableTopology {L B : ℝ} (hL : 0 < L) (hB : 0 < B) :
    SecondCountableTopology (Attachment hL hB) :=
  (radialCapAttachmentHomeomorph hL hB).secondCountableTopology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachment_secondCountableTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachment_secondCountableTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachment_secondCountableTopology ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachment_secondCountableTopology

theorem radialCapAttachment_isManifold {L B : ℝ} (hL : 0 < L) (hB : 0 < B) :
    letI := radialCapAttachmentChartedSpace hL hB
    IsManifold (𝓡 3) ∞ (Attachment hL hB) := by
  let := radialCapAttachmentChartedSpace hL hB
  exact @isManifoldOfHomeomorph ℝ _ E3 E3 _ _ _ (𝓡 3) (radialBall L B) _
    ((radialBall L B).instChartedSpace) ∞ (Attachment hL hB) _
    (radialCapAttachmentHomeomorph hL hB) inferInstance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachment_isManifold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachment_isManifold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachment_isManifold ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachment_isManifold

theorem radialCapAttachment_boundary_eq_empty {L B : ℝ} (hL : 0 < L) (hB : 0 < B) :
    letI := radialCapAttachmentChartedSpace hL hB
    (𝓡 3).boundary (Attachment hL hB) = ∅ := by
  let := radialCapAttachmentChartedSpace hL hB
  exact ModelWithCorners.Boundaryless.boundary_eq_empty

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachment_boundary_eq_empty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachment_boundary_eq_empty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachment_boundary_eq_empty ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachment_boundary_eq_empty

def radialCapAttachmentDiffeomorph {L B : ℝ} (hL : 0 < L) (hB : 0 < B) :
    letI := radialCapAttachmentChartedSpace hL hB
    Attachment hL hB ≃ₘ⟮𝓡 3, 𝓡 3⟯ radialBall L B := by
  let := radialCapAttachmentChartedSpace hL hB
  let e : Attachment hL hB ≃ₜ radialBall L B := radialCapAttachmentHomeomorph hL hB
  exact
    { toEquiv := e.toEquiv
      contMDiff_toFun := contMDiff_homeomorph_of_chartedSpaceOfHomeomorph e (𝓡 3) ∞
      contMDiff_invFun := contMDiff_homeomorph_symm_of_chartedSpaceOfHomeomorph e (𝓡 3) ∞ }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachmentDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachmentDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachmentDiffeomorph ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachmentDiffeomorph

@[simp] theorem radialCapAttachmentDiffeomorph_apply {L B : ℝ} (hL : 0 < L) (hB : 0 < B)
    (x : Attachment hL hB) :
    letI := radialCapAttachmentChartedSpace hL hB
    radialCapAttachmentDiffeomorph hL hB x = radialCapAttachmentHomeomorph hL hB x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachmentDiffeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachmentDiffeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachmentDiffeomorph_apply ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachmentDiffeomorph_apply

@[simp] theorem radialCapAttachmentDiffeomorph_symm_apply {L B : ℝ} (hL : 0 < L) (hB : 0 < B)
    (x : radialBall L B) :
    letI := radialCapAttachmentChartedSpace hL hB
    (radialCapAttachmentDiffeomorph hL hB).symm x =
      (radialCapAttachmentHomeomorph hL hB).symm x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachmentDiffeomorph_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachmentDiffeomorph_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachmentDiffeomorph_symm_apply ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachmentDiffeomorph_symm_apply

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

private theorem smoothEmbedding_into_open
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    (U : _root_.TopologicalSpace.Opens E3) (f : M → U)
    (hf : _root_.Manifold.IsSmoothEmbedding I (𝓡 3) ∞ (fun x => (f x : E3))) :
    IsSmoothEmbedding I (𝓡 3) ∞ f := by
  refine ⟨?_, (_root_.Topology.IsEmbedding.subtypeVal.of_comp_iff).mp hf.isEmbedding⟩
  obtain ⟨F, hF, hF', hfimm⟩ := hf.isImmersion
  let := hF
  let := hF'
  refine ⟨F, hF, hF', ?_⟩
  intro x
  let h := hfimm x
  have hU : Nonempty U := ⟨f x⟩
  let c := h.codChart.subtypeRestr hU
  refine IsImmersionAtOfComplement.mk_of_continuousAt
    (show ContinuousAt f x from (continuous_induced_rng.mpr hf.contMDiff.continuous).continuousAt)
    h.equiv h.domChart c h.mem_domChart_source ?_ h.domChart_mem_maximalAtlas
    (restrictedChart_mem_maximalAtlas U hU h.codChart h.codChart_mem_maximalAtlas) ?_
  · simpa only [c, OpenPartialHomeomorph.subtypeRestr_source, _root_.Set.mem_preimage] using h.mem_codChart_source
  · exact h.writtenInCharts

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.smoothEmbedding_into_open
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.smoothEmbedding_into_open target :: scope.openDecls } }

private theorem smoothEmbedding_into_attachment {L B : ℝ} (hL : 0 < L) (hB : 0 < B)
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    (f : M → Attachment hL hB)
    (hf : _root_.Manifold.IsSmoothEmbedding I (𝓡 3) ∞
      (radialCapAttachmentHomeomorph hL hB ∘ f : M → radialBall L B)) :
    letI := radialCapAttachmentChartedSpace hL hB
    IsSmoothEmbedding I (𝓡 3) ∞ f := by
  let := radialCapAttachmentChartedSpace hL hB
  let := radialCapAttachment_isManifold hL hB
  let d := radialCapAttachmentDiffeomorph hL hB
  refine ⟨?_, ((radialCapAttachmentHomeomorph hL hB).isEmbedding.of_comp_iff).mp hf.isEmbedding⟩
  obtain ⟨F, hF, hF', hfimm⟩ := hf.isImmersion
  let := hF
  let := hF'
  refine ⟨F, hF, hF', ?_⟩
  intro x
  let h := hfimm x
  let c := d.toHomeomorph.toOpenPartialHomeomorph.trans h.codChart
  have hc : c ∈ _root_.IsManifold.maximalAtlas (𝓡 3) ∞ (Attachment hL hB) := by
    apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
    · exact (contMDiffOn_of_mem_maximalAtlas h.codChart_mem_maximalAtlas).comp
        d.contMDiff.contMDiffOn (fun _ hy => hy.2)
    · change ContMDiffOn (𝓡 3) (𝓡 3) ∞ (d.symm ∘ h.codChart.symm) c.target
      have hd : ContMDiffOn (𝓡 3) (𝓡 3) ∞ d.symm univ := d.symm.contMDiff.contMDiffOn
      exact hd.comp
        ((contMDiffOn_symm_of_mem_maximalAtlas h.codChart_mem_maximalAtlas).mono
          (fun _ hy => hy.1)) (fun _ _ => _root_.Set.mem_univ _)
  refine IsImmersionAtOfComplement.mk_of_continuousAt
    (show ContinuousAt f x from
      ((radialCapAttachmentHomeomorph hL hB).isEmbedding.continuous_iff.mpr
        hf.contMDiff.continuous).continuousAt)
    h.equiv h.domChart c h.mem_domChart_source ⟨mem_univ _, h.mem_codChart_source⟩
    h.domChart_mem_maximalAtlas hc ?_
  exact h.writtenInCharts

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.smoothEmbedding_into_attachment
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.smoothEmbedding_into_attachment target :: scope.openDecls } }

theorem isSmoothEmbedding_radialCapAttachment_cap {L B : ℝ} (hL : 0 < L) (hB : 0 < B) :
    letI := closedBallChartedSpace hL
    letI := radialCapAttachmentChartedSpace hL hB
    _root_.Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞
      (adjunctionCell (radialCapBoundary hL) (retainedBoundary hB)) := by
  let := closedBallChartedSpace hL
  apply smoothEmbedding_into_attachment hL hB
  apply smoothEmbedding_into_open (radialBall L B)
  exact isSmoothEmbedding_closedBall_inclusion hL

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.Attachment.isSmoothEmbedding_radialCapAttachment_cap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.Attachment.isSmoothEmbedding_radialCapAttachment_cap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.Attachment.isSmoothEmbedding_radialCapAttachment_cap ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.isSmoothEmbedding_radialCapAttachment_cap

theorem isSmoothEmbedding_radialCapAttachment_retained {L B : ℝ} (hL : 0 < L) (hB : 0 < B) :
    letI := halfClosedIntervalChartedSpace hB
    letI := radialCapAttachmentChartedSpace hL hB
    _root_.Manifold.IsSmoothEmbedding IR (𝓡 3) ∞
      (adjunctionLower (i := radialCapBoundary hL) (retainedBoundary hB)) := by
  let := halfClosedIntervalChartedSpace hB
  apply smoothEmbedding_into_attachment hL hB
  have hmap : (radialCapAttachmentHomeomorph hL hB ∘
      adjunctionLower (i := radialCapBoundary hL) (retainedBoundary hB) :
      Retained B → radialBall L B) = retainedRadialMap hL := by
    apply funext
    intro q
    exact (retainedRadialMap_eq_attachment hL hB q).symm
  rw [hmap]
  exact isSmoothEmbedding_retainedRadialMap hL hB

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.Attachment.isSmoothEmbedding_radialCapAttachment_retained then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.Attachment.isSmoothEmbedding_radialCapAttachment_retained"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.Attachment.isSmoothEmbedding_radialCapAttachment_retained ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.isSmoothEmbedding_radialCapAttachment_retained

end DifferentialGeometry.Topology.Manifold.Attachment
