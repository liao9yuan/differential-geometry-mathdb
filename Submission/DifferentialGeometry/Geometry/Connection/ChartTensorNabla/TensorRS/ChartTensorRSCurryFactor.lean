import Submission.DifferentialGeometry.Geometry.Connection.ChartTensorNabla.TensorRS.ChartTensorRSCovariantDerivative
import Submission.DifferentialGeometry.Geometry.Connection.ChartTensorNabla.Tensor0S.Tensor0SChartParallelExtend
import Submission.DifferentialGeometry.Geometry.Connection.ChartTensorNabla.Tensor0S.Tensor0SIntrinsicChartCurryFactor

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section


open scoped _root_.Manifold _root_.ContDiff _root_.Topology
open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.Submission.DifferentialGeometry.Tensor0SBundle

namespace DifferentialGeometry
namespace Geometry
namespace Connection

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

noncomputable def tensorPartialEval (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b)
    (w : Π b : M, Tensor0SSpace r I b) :
    Π b : M, Tensor0SSpace s I b :=
  fun b => (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b) (w b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensorPartialEval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensorPartialEval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensorPartialEval ``Submission.DifferentialGeometry.Geometry.Connection.tensorPartialEval

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
@[simp] lemma tensorPartialEval_apply (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b)
    (w : Π b : M, Tensor0SSpace r I b) (b : M) :
    tensorPartialEval (I := I) (M := M) r s T w b =
      (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b) (w b) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensorPartialEval_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensorPartialEval_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensorPartialEval_apply ``Submission.DifferentialGeometry.Geometry.Connection.tensorPartialEval_apply

noncomputable def tensorRSEvalAtCLM (r s : ℕ) (D_α : Tensor0SModel r ℝ E) :
    TensorRSModel r s ℝ E →L[ℝ] Tensor0SModel s ℝ E :=
  ContinuousLinearMap.apply ℝ (Tensor0SModel s ℝ E) D_α

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensorRSEvalAtCLM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensorRSEvalAtCLM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensorRSEvalAtCLM ``Submission.DifferentialGeometry.Geometry.Connection.tensorRSEvalAtCLM

omit [CompleteSpace E] in
@[simp] lemma tensorRSEvalAtCLM_apply (r s : ℕ) (D_α : Tensor0SModel r ℝ E)
    (D : TensorRSModel r s ℝ E) :
    tensorRSEvalAtCLM (E := E) r s D_α D = D D_α := by
  classical
  unfold tensorRSEvalAtCLM
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensorRSEvalAtCLM_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensorRSEvalAtCLM_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensorRSEvalAtCLM_apply ``Submission.DifferentialGeometry.Geometry.Connection.tensorRSEvalAtCLM_apply

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem tensorRSChartE_section_repr_apply_model (r s : ℕ) (α : M)
    (T : Π b : M, TensorRSSpace r s I b) {b : M}
    (hb : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet)
    (D : Tensor0SModel r ℝ E) :
    (tensorRSChartESectionRepr (I := I) r s α T b) D =
      (_root_.FiberBundle.trivializationAt (Tensor0SModel s ℝ E)
          (fun y : M => Tensor0SSpace s I y) α).continuousLinearMapAt ℝ b
        ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b)
          ((_root_.FiberBundle.trivializationAt (Tensor0SModel r ℝ E)
            (fun y : M => Tensor0SSpace r I y) α).symmL ℝ b D)) := by
  classical
  set eRS := _root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
    (fun y : M => TensorRSSpace r s I y) α with heRS_def
  set er := _root_.FiberBundle.trivializationAt (Tensor0SModel r ℝ E)
    (fun y : M => Tensor0SSpace r I y) α with her_def
  set es := _root_.FiberBundle.trivializationAt (Tensor0SModel s ℝ E)
    (fun y : M => Tensor0SSpace s I y) α with hes_def
  have hbase_RS : b ∈ eRS.baseSet := by
    change b ∈ er.baseSet ∩ es.baseSet
    refine ⟨?_, ?_⟩
    · change b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet
      exact hb
    · change b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet
      exact hb
  have hcoeRS := eRS.coe_linearMapAt_of_mem (R := ℝ) hbase_RS
  unfold tensorRSChartESectionRepr
  change (eRS.linearMapAt ℝ b (T b)) D = _
  rw [show (eRS.linearMapAt ℝ b (T b)) = (eRS ⟨b, T b⟩).2 from
        congrFun hcoeRS (T b)]
  have hHom :
      eRS ⟨b, T b⟩
        = ⟨b, ((es.continuousLinearMapAt ℝ b
            : Tensor0SSpace s I b →L[ℝ] Tensor0SModel s ℝ E).comp
              ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b).comp
                ((er.symmL ℝ b)
                  : Tensor0SModel r ℝ E →L[ℝ] Tensor0SSpace r I b)))⟩ := rfl
  rw [hHom]
  change ((es.continuousLinearMapAt ℝ b
        : Tensor0SSpace s I b →L[ℝ] Tensor0SModel s ℝ E).comp
      ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b).comp
        ((er.symmL ℝ b)
          : Tensor0SModel r ℝ E →L[ℝ] Tensor0SSpace r I b))) D = _
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr_apply_model then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr_apply_model"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr_apply_model ``Submission.DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr_apply_model

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem tensorRSChartFiberFromModel_apply_at (r s : ℕ) (α : M) {b : M}
    (hb : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet)
    (D : TensorRSModel r s ℝ E) (α_input : Tensor0SSpace r I b) :
    (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from
      tensorRSChartFiberFromModel (I := I) r s α b D) α_input =
      (_root_.FiberBundle.trivializationAt (Tensor0SModel s ℝ E)
          (fun y : M => Tensor0SSpace s I y) α).symmL ℝ b
        (D ((_root_.FiberBundle.trivializationAt (Tensor0SModel r ℝ E)
          (fun y : M => Tensor0SSpace r I y) α).continuousLinearMapAt ℝ b α_input)) := by
  classical
  set eRS := _root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
    (fun y : M => TensorRSSpace r s I y) α with heRS_def
  set er := _root_.FiberBundle.trivializationAt (Tensor0SModel r ℝ E)
    (fun y : M => Tensor0SSpace r I y) α with her_def
  set es := _root_.FiberBundle.trivializationAt (Tensor0SModel s ℝ E)
    (fun y : M => Tensor0SSpace s I y) α with hes_def
  have hbase_RS : b ∈ eRS.baseSet := by
    change b ∈ er.baseSet ∩ es.baseSet
    refine ⟨?_, ?_⟩
    · change b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet
      exact hb
    · change b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet
      exact hb
  have hHomSymm : (eRS.symmL ℝ b D : Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b) =
      (es.symmL ℝ b).comp (D.comp (er.continuousLinearMapAt ℝ b)) := by
    have h := _root_.Bundle.Pretrivialization.continuousLinearMap_symm_apply'
      (σ := RingHom.id ℝ) (F₁ := Tensor0SModel r ℝ E)
      (E₁ := fun y : M => Tensor0SSpace r I y)
      (F₂ := Tensor0SModel s ℝ E)
      (E₂ := fun y : M => Tensor0SSpace s I y)
      (e₁ := er) (e₂ := es) (b := b) hbase_RS D
    rw [eRS.symmL_apply hbase_RS]
    change (eRS.symm b D : Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b) = _
    rw [show (eRS.symm b D : Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b) =
          ((_root_.Bundle.Pretrivialization.continuousLinearMap (𝕜₁ := ℝ) (𝕜₂ := ℝ)
            (σ := RingHom.id ℝ) (F₁ := Tensor0SModel r ℝ E)
            (E₁ := fun y : M => Tensor0SSpace r I y)
            (F₂ := Tensor0SModel s ℝ E)
            (E₂ := fun y : M => Tensor0SSpace s I y)
            er es).symm b D) from rfl]
    exact h
  unfold tensorRSChartFiberFromModel
  change (eRS.symmL ℝ b D : Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b) α_input = _
  rw [hHomSymm]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensorRSChartFiberFromModel_apply_at then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensorRSChartFiberFromModel_apply_at"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensorRSChartFiberFromModel_apply_at ``Submission.DifferentialGeometry.Geometry.Connection.tensorRSChartFiberFromModel_apply_at

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem tensor0SChartE_section_repr_tensorPartialEval_eq_tensorRS_repr_apply
    (r s : ℕ) (α : M) (T : Π b' : M, TensorRSSpace r s I b')
    {b : M}
    (α_input : Tensor0SSpace r I b)
    {b' : M} (hb' : b' ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet) :
    tensor0SChartESectionRepr (I := I) s α
        (tensorPartialEval (I := I) (M := M) r s T
          (chartTensor0SParallelExtend (I := I) r α b α_input)) b' =
      (tensorRSChartESectionRepr (I := I) r s α T b')
        ((_root_.FiberBundle.trivializationAt (Tensor0SModel r ℝ E)
          (fun y : M => Tensor0SSpace r I y) α).continuousLinearMapAt ℝ b α_input) := by
  classical
  set er := _root_.FiberBundle.trivializationAt (Tensor0SModel r ℝ E)
    (fun y : M => Tensor0SSpace r I y) α with her_def
  set es := _root_.FiberBundle.trivializationAt (Tensor0SModel s ℝ E)
    (fun y : M => Tensor0SSpace s I y) α with hes_def
  set D_α : Tensor0SModel r ℝ E := er.continuousLinearMapAt ℝ b α_input with hDα_def
  have hPE_at_b' :
      chartTensor0SParallelExtend (I := I) r α b α_input b' =
        er.symmL ℝ b' D_α := rfl
  have hLHS_unfold :
      tensor0SChartESectionRepr (I := I) s α
          (tensorPartialEval (I := I) (M := M) r s T
            (chartTensor0SParallelExtend (I := I) r α b α_input)) b' =
        es.continuousLinearMapAt ℝ b'
          ((show Tensor0SSpace r I b' →L[ℝ] Tensor0SSpace s I b' from T b')
            (chartTensor0SParallelExtend (I := I) r α b α_input b')) := by
    unfold tensor0SChartESectionRepr
    rw [tensorPartialEval_apply]
  rw [hLHS_unfold]
  rw [hPE_at_b']
  rw [tensorRSChartE_section_repr_apply_model (I := I) r s α T (b := b') hb' D_α]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensor0SChartE_section_repr_tensorPartialEval_eq_tensorRS_repr_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensor0SChartE_section_repr_tensorPartialEval_eq_tensorRS_repr_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensor0SChartE_section_repr_tensorPartialEval_eq_tensorRS_repr_apply ``Submission.DifferentialGeometry.Geometry.Connection.tensor0SChartE_section_repr_tensorPartialEval_eq_tensorRS_repr_apply

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem tensorPartialEval_chartPullback_eventually_eq_evalAt_chartPullback
    (r s : ℕ) (α : M) (T : Π b' : M, TensorRSSpace r s I b')
    {b : M} (α_input : Tensor0SSpace r I b)
    (hb_source : b ∈ (extChartAt I α).source)
    (hb_target : extChartAt I α b ∈ interior ((extChartAt I α).target : Set E))
    (hb_base : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet) :
    (tensor0SChartESectionRepr (I := I) s α
        (tensorPartialEval (I := I) (M := M) r s T
          (chartTensor0SParallelExtend (I := I) r α b α_input)) ∘
        (extChartAt I α).symm) =ᶠ[𝓝 (extChartAt I α b)]
      (fun y : E =>
        tensorRSEvalAtCLM (E := E) r s
            ((_root_.FiberBundle.trivializationAt (Tensor0SModel r ℝ E)
              (fun z : M => Tensor0SSpace r I z) α).continuousLinearMapAt ℝ b α_input)
          ((tensorRSChartESectionRepr (I := I) r s α T ∘ (extChartAt I α).symm) y)) := by
  classical
  set φ := extChartAt I α
  have hU_int : interior (φ.target : Set E) ∈ 𝓝 (φ b) :=
    isOpen_interior.mem_nhds hb_target
  have hBase_open : IsOpen (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet :=
    (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).open_baseSet
  have hb_inv : φ.symm (φ b) = b := φ.left_inv hb_source
  have hcont_symm : ContinuousAt φ.symm (φ b) :=
    continuousAt_extChartAt_symm' (I := I) (x := α) (x' := b) hb_source
  have hBase_pre : φ.symm ⁻¹' (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet ∈ 𝓝 (φ b) := by
    have hmem : (φ.symm (φ b)) ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
      rw [hb_inv]; exact hb_base
    exact hcont_symm.preimage_mem_nhds (hBase_open.mem_nhds hmem)
  filter_upwards [Filter.inter_mem hU_int hBase_pre] with y hy
  obtain ⟨_, hyBase⟩ := hy
  rw [Function.comp_apply, Function.comp_apply]
  rw [tensorRSEvalAtCLM_apply]
  exact tensor0SChartE_section_repr_tensorPartialEval_eq_tensorRS_repr_apply
    (I := I) r s α T (b := b) α_input (b' := φ.symm y) hyBase

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensorPartialEval_chartPullback_eventually_eq_evalAt_chartPullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensorPartialEval_chartPullback_eventually_eq_evalAt_chartPullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensorPartialEval_chartPullback_eventually_eq_evalAt_chartPullback ``Submission.DifferentialGeometry.Geometry.Connection.tensorPartialEval_chartPullback_eventually_eq_evalAt_chartPullback

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem fderiv_tensorPartialEval_chartPullback_eq_comp_evalAt
    (r s : ℕ) (α : M) (T : Π b' : M, TensorRSSpace r s I b')
    {b : M} (α_input : Tensor0SSpace r I b)
    (hb_source : b ∈ (extChartAt I α).source)
    (hb_target : extChartAt I α b ∈ interior ((extChartAt I α).target : Set E))
    (hb_base : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet)
    (hT : DifferentiableAt ℝ
      (tensorRSChartESectionRepr (I := I) r s α T ∘ (extChartAt I α).symm)
      (extChartAt I α b)) :
    fderiv ℝ
        (tensor0SChartESectionRepr (I := I) s α
            (tensorPartialEval (I := I) (M := M) r s T
              (chartTensor0SParallelExtend (I := I) r α b α_input)) ∘
          (extChartAt I α).symm)
        (extChartAt I α b) =
      (tensorRSEvalAtCLM (E := E) r s
            ((_root_.FiberBundle.trivializationAt (Tensor0SModel r ℝ E)
              (fun z : M => Tensor0SSpace r I z) α).continuousLinearMapAt ℝ b α_input)).comp
        (fderiv ℝ
          (tensorRSChartESectionRepr (I := I) r s α T ∘
            (extChartAt I α).symm)
          (extChartAt I α b)) := by
  classical
  have heq := tensorPartialEval_chartPullback_eventually_eq_evalAt_chartPullback
    (I := I) (M := M) r s α T (b := b) α_input hb_source hb_target hb_base
  rw [Filter.EventuallyEq.fderiv_eq heq]
  exact (((tensorRSEvalAtCLM (E := E) r s
      ((_root_.FiberBundle.trivializationAt (Tensor0SModel r ℝ E)
        (fun z : M => Tensor0SSpace r I z) α).continuousLinearMapAt ℝ b α_input)).hasFDerivAt
      (x := (tensorRSChartESectionRepr (I := I) r s α T ∘
        (extChartAt I α).symm) (extChartAt I α b))).comp
    (extChartAt I α b) hT.hasFDerivAt).fderiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.fderiv_tensorPartialEval_chartPullback_eq_comp_evalAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.fderiv_tensorPartialEval_chartPullback_eq_comp_evalAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.fderiv_tensorPartialEval_chartPullback_eq_comp_evalAt ``Submission.DifferentialGeometry.Geometry.Connection.fderiv_tensorPartialEval_chartPullback_eq_comp_evalAt

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem tensorRSIntrinsicChartCLM_factor
    (r s : ℕ) (α : M)
    (T : Π b : M, TensorRSSpace r s I b)
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α)
    (α_input : Tensor0SSpace r I b)
    (hT : DifferentiableAt ℝ
      (tensorRSChartESectionRepr (I := I) r s α T ∘ (extChartAt I α).symm)
      (extChartAt I α b))
    (X : Π b' : M, TangentSpace I b') :
    (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from
      tensorRSIntrinsicChartCLM (I := I) r s α T b (X b)) α_input =
      tensor0SIntrinsicChartCLM (I := I) s α
          (tensorPartialEval (I := I) (M := M) r s T
            (chartTensor0SParallelExtend (I := I) r α b α_input))
          b (X b) := by
  classical
  let _h_top_rs : TopologicalSpace
      (_root_.Bundle.TotalSpace (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y)) :=
    tensorRSBundleTopology r s
  let _h_top_s : TopologicalSpace (_root_.Bundle.TotalSpace (Tensor0SModel s ℝ E)
      (fun y : M => Tensor0SSpace s I y)) :=
    tensor0SBundleTopology s
  let _h_top_r : TopologicalSpace (_root_.Bundle.TotalSpace (Tensor0SModel r ℝ E)
      (fun y : M => Tensor0SSpace r I y)) :=
    tensor0SBundleTopology r
  have hb_source : b ∈ (extChartAt I α).source :=
    chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hb
  have hb_target : extChartAt I α b ∈ interior ((extChartAt I α).target : Set E) :=
    chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hb
  have hb_base : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hb
  set er := _root_.FiberBundle.trivializationAt (Tensor0SModel r ℝ E)
    (fun y : M => Tensor0SSpace r I y) α with her_def
  set es := _root_.FiberBundle.trivializationAt (Tensor0SModel s ℝ E)
    (fun y : M => Tensor0SSpace s I y) α with hes_def
  set D_α : Tensor0SModel r ℝ E := er.continuousLinearMapAt ℝ b α_input with hDα_def
  set w_E : E := trivToE (I := I) α b (X b) with hwE_def
  have hLHS_unfold :
      (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from
        tensorRSIntrinsicChartCLM (I := I) r s α T b (X b)) α_input =
        es.symmL ℝ b
          (fderiv ℝ
            (tensorRSChartESectionRepr (I := I) r s α T ∘ (extChartAt I α).symm)
            (extChartAt I α b) w_E D_α) := by
    rw [tensorRSIntrinsicChartCLM_apply (I := I) r s α T b (X b)]
    rw [tensorRSChartFiberFromModel_apply_at (I := I) r s α hb_base
      (fderiv ℝ
        (tensorRSChartESectionRepr (I := I) r s α T ∘ (extChartAt I α).symm)
        (extChartAt I α b) (trivToE (I := I) α b (X b))) α_input]
  rw [hLHS_unfold]
  have hRHS_unfold :
      tensor0SIntrinsicChartCLM (I := I) s α
          (tensorPartialEval (I := I) (M := M) r s T
            (chartTensor0SParallelExtend (I := I) r α b α_input))
          b (X b) =
        es.symmL ℝ b
          (fderiv ℝ
            (tensor0SChartESectionRepr (I := I) s α
                (tensorPartialEval (I := I) (M := M) r s T
                  (chartTensor0SParallelExtend (I := I) r α b α_input)) ∘
              (extChartAt I α).symm)
            (extChartAt I α b) w_E) := by
    rw [tensor0SIntrinsicChartCLM_apply (I := I) s α _ b (X b)]
    rfl
  rw [hRHS_unfold]
  have hfderivEq := fderiv_tensorPartialEval_chartPullback_eq_comp_evalAt
    (I := I) (M := M) r s α T (b := b) α_input hb_source hb_target hb_base hT
  have hfderiv_at_wE :
      fderiv ℝ
          (tensor0SChartESectionRepr (I := I) s α
              (tensorPartialEval (I := I) (M := M) r s T
                (chartTensor0SParallelExtend (I := I) r α b α_input)) ∘
            (extChartAt I α).symm)
          (extChartAt I α b) w_E =
        tensorRSEvalAtCLM (E := E) r s D_α
          (fderiv ℝ
            (tensorRSChartESectionRepr (I := I) r s α T ∘
              (extChartAt I α).symm)
            (extChartAt I α b) w_E) := by
    have := congrArg (fun L : E →L[ℝ] Tensor0SModel s ℝ E => L w_E) hfderivEq
    rw [hDα_def]
    simpa only [ContinuousLinearMap.comp_apply] using this
  rw [hfderiv_at_wE]
  rw [tensorRSEvalAtCLM_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensorRSIntrinsicChartCLM_factor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensorRSIntrinsicChartCLM_factor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensorRSIntrinsicChartCLM_factor ``Submission.DifferentialGeometry.Geometry.Connection.tensorRSIntrinsicChartCLM_factor

end Connection
end Geometry
end DifferentialGeometry

end
