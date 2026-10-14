import Submission.DifferentialGeometry.Geometry.Connection.ChartTensorNabla.Tensor0S.Tensor0SChartChristoffel
import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.Tensor0S.PartialEvaluation
import Submission.DifferentialGeometry.Geometry.Connection.ChartTensorNabla.Tensor0S.ChartTensor0SCovariantDerivative
import Submission.DifferentialGeometry.Tensor.Multilinear.Bundle.Evaluation

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

noncomputable def curryLeftEvalCLM (s : ℕ) (w : E) :
    Tensor0SModel (s + 1) ℝ E →L[ℝ] Tensor0SModel s ℝ E :=
  (ContinuousLinearMap.apply ℝ (Tensor0SModel s ℝ E) w).comp
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s + 1) => E)
        ℝ).toContinuousLinearEquiv.toContinuousLinearMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.curryLeftEvalCLM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.curryLeftEvalCLM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.curryLeftEvalCLM ``Submission.DifferentialGeometry.Geometry.Connection.curryLeftEvalCLM

omit [CompleteSpace E] in
@[simp] lemma curryLeftEvalCLM_apply (s : ℕ) (w : E)
    (F : Tensor0SModel (s + 1) ℝ E) (m : Fin s → E) :
    (curryLeftEvalCLM (E := E) s w F) m = F (Fin.cons w m) := by
  classical
  unfold curryLeftEvalCLM
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
    continuousMultilinearCurryLeftEquiv_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.curryLeftEvalCLM_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.curryLeftEvalCLM_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.curryLeftEvalCLM_apply ``Submission.DifferentialGeometry.Geometry.Connection.curryLeftEvalCLM_apply

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem tensor0SChartE_section_repr_apply_tuple {n : ℕ} (α : M)
    (T : Π b : M, Tensor0SSpace n I b) {b : M}
    (hb : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet)
    (v : Fin n → E) :
    (tensor0SChartESectionRepr (I := I) n α T b) v =
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin n => TangentSpace I b) ℝ from T b)
        (fun i => trivFromE (I := I) α b (v i)) := by
  classical
  have hbase : b ∈ (_root_.FiberBundle.trivializationAt (Tensor0SModel n ℝ E)
      (fun y : M => Tensor0SSpace n I y) α).baseSet := by
    change b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet
    exact hb
  have hcoe := (_root_.FiberBundle.trivializationAt (Tensor0SModel n ℝ E)
      (fun y : M => Tensor0SSpace n I y) α).coe_linearMapAt_of_mem (R := ℝ) hbase
  unfold tensor0SChartESectionRepr
  change ((_root_.FiberBundle.trivializationAt (Tensor0SModel n ℝ E)
      (fun y : M => Tensor0SSpace n I y) α).linearMapAt ℝ b (T b)) v = _
  rw [show ((_root_.FiberBundle.trivializationAt (Tensor0SModel n ℝ E)
      (fun y : M => Tensor0SSpace n I y) α).linearMapAt ℝ b) (T b) =
        ((_root_.FiberBundle.trivializationAt (Tensor0SModel n ℝ E)
          (fun y : M => Tensor0SSpace n I y) α) ⟨b, T b⟩).2 from
      congrFun hcoe (T b)]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensor0SChartE_section_repr_apply_tuple then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensor0SChartE_section_repr_apply_tuple"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensor0SChartE_section_repr_apply_tuple ``Submission.DifferentialGeometry.Geometry.Connection.tensor0SChartE_section_repr_apply_tuple

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem tensor0SBundle_symmL_apply_eq_compContinuousLinearMap {n : ℕ}
    (α : M) {b : M}
    (hb : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet)
    (D : Tensor0SModel n ℝ E) :
    letI _h_top : TopologicalSpace (_root_.Bundle.TotalSpace (Tensor0SModel n ℝ E)
        (fun y : M => Tensor0SSpace n I y)) :=
      tensor0SBundleTopology n
    ((_root_.FiberBundle.trivializationAt (Tensor0SModel n ℝ E)
        (fun y : M => Tensor0SSpace n I y) α).symmL ℝ b D :
        Tensor0SSpace n I b) =
      (tensor0SSpaceFiberContinuousLinearEquiv (I := I) n b).symm
        (D.compContinuousLinearMap (fun _ : Fin n => trivToE (I := I) α b)) := by
  let _h_top : TopologicalSpace (_root_.Bundle.TotalSpace (Tensor0SModel n ℝ E)
      (fun y : M => Tensor0SSpace n I y)) :=
    tensor0SBundleTopology n
  have h := _root_.Submission.Pretrivialization.continuousMultilinearMap_symm_apply_of_mem
    (𝕜 := ℝ) (s := n) (F := E) (E := (TangentSpace I : M → Type _))
    (e := _root_.FiberBundle.trivializationAt E (TangentSpace I) α) (b := b) hb D
  have hbTensor : b ∈ (_root_.FiberBundle.trivializationAt (Tensor0SModel n ℝ E)
      (fun y : M => Tensor0SSpace n I y) α).baseSet := by
    change b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet
    exact hb
  rw [(_root_.FiberBundle.trivializationAt (Tensor0SModel n ℝ E)
    (fun y : M => Tensor0SSpace n I y) α).symmL_apply hbTensor]
  change (_root_.FiberBundle.trivializationAt (Tensor0SModel n ℝ E)
    (fun y : M => Tensor0SSpace n I y) α).symm b D = _
  rw [show (_root_.FiberBundle.trivializationAt (Tensor0SModel n ℝ E)
      (fun y : M => Tensor0SSpace n I y) α).symm b D =
        ((Pretrivialization.continuousMultilinearMap (𝕜 := ℝ) (s := n)
          (F := E) (E := (TangentSpace I : M → Type _))
          (_root_.FiberBundle.trivializationAt E (TangentSpace I) α)).symm b D) from rfl]
  apply (tensor0SSpaceFiberContinuousLinearEquiv (I := I) n b).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensor0SBundle_symmL_apply_eq_compContinuousLinearMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensor0SBundle_symmL_apply_eq_compContinuousLinearMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensor0SBundle_symmL_apply_eq_compContinuousLinearMap ``Submission.DifferentialGeometry.Geometry.Connection.tensor0SBundle_symmL_apply_eq_compContinuousLinearMap

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem tensor0SChartE_section_repr_cons_eq_partialEval (s : ℕ) (α : M)
    (T : Π b : M, Tensor0SSpace (s + 1) I b) {b : M} (v : TangentSpace I b)
    {b' : M} (hb' : b' ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet)
    (m : Fin s → E) :
    (tensor0SChartESectionRepr (I := I) (s + 1) α T b')
        (Fin.cons (trivToE (I := I) α b v) m) =
      (tensor0SChartESectionRepr (I := I) s α
        (Tensor0SPartialEval.tensor0SPartialEval I M T
          (chartParallelExtend (I := I) α b v)) b') m := by
  classical
  rw [tensor0SChartE_section_repr_apply_tuple (I := I) (n := s + 1) α T hb']
  rw [tensor0SChartE_section_repr_apply_tuple (I := I) (n := s) α _ hb']
  have hRHS_eval :
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin s => TangentSpace I b') ℝ from
          Tensor0SPartialEval.tensor0SPartialEval I M T
            (chartParallelExtend (I := I) α b v) b')
          (fun i => trivFromE (I := I) α b' (m i)) =
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin (s + 1) => TangentSpace I b') ℝ from T b')
        (Fin.cons (chartParallelExtend (I := I) α b v b')
          (fun i => trivFromE (I := I) α b' (m i))) := by
    change (show ContinuousMultilinearMap ℝ
              (fun _ : Fin s => TangentSpace I b') ℝ from
            tensor0SCurry (I := I) (M := M) s b' (T b')
              (chartParallelExtend (I := I) α b v b'))
            (fun i => trivFromE (I := I) α b' (m i)) =
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin (s + 1) => TangentSpace I b') ℝ from T b')
        (Fin.cons (chartParallelExtend (I := I) α b v b')
          (fun i => trivFromE (I := I) α b' (m i)))
    exact TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := T b') (v0 := chartParallelExtend (I := I) α b v b')
      (vs := fun i => trivFromE (I := I) α b' (m i))
  rw [hRHS_eval]
  congr 1
  funext j
  refine Fin.cases ?_ ?_ j
  · simp only [Fin.cons_zero]; rfl
  · intro k; simp only [Fin.cons_succ]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensor0SChartE_section_repr_cons_eq_partialEval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensor0SChartE_section_repr_cons_eq_partialEval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensor0SChartE_section_repr_cons_eq_partialEval ``Submission.DifferentialGeometry.Geometry.Connection.tensor0SChartE_section_repr_cons_eq_partialEval

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem tensor0SChartE_section_repr_partialEval_eq_curryLeftEval (s : ℕ) (α : M)
    (T : Π b : M, Tensor0SSpace (s + 1) I b) {b : M} (v : TangentSpace I b)
    {b' : M} (hb' : b' ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet) :
    tensor0SChartESectionRepr (I := I) s α
        (Tensor0SPartialEval.tensor0SPartialEval I M T
          (chartParallelExtend (I := I) α b v)) b' =
      curryLeftEvalCLM (E := E) s (trivToE (I := I) α b v)
        (tensor0SChartESectionRepr (I := I) (s + 1) α T b') := by
  classical
  apply ContinuousMultilinearMap.ext
  intro m
  rw [curryLeftEvalCLM_apply]
  exact (tensor0SChartE_section_repr_cons_eq_partialEval (I := I) (M := M) s α T
    (b := b) v (b' := b') hb' m).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensor0SChartE_section_repr_partialEval_eq_curryLeftEval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensor0SChartE_section_repr_partialEval_eq_curryLeftEval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensor0SChartE_section_repr_partialEval_eq_curryLeftEval ``Submission.DifferentialGeometry.Geometry.Connection.tensor0SChartE_section_repr_partialEval_eq_curryLeftEval

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem partialEval_chartPullback_eventually_eq_curryLeftEval_chartPullback
    (s : ℕ) (α : M) (T : Π b : M, Tensor0SSpace (s + 1) I b)
    {b : M} (v : TangentSpace I b)
    (hb_source : b ∈ (extChartAt I α).source)
    (hb_target : extChartAt I α b ∈ interior ((extChartAt I α).target : Set E))
    (hb_base : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet) :
    (tensor0SChartESectionRepr (I := I) s α
        (Tensor0SPartialEval.tensor0SPartialEval I M T
          (chartParallelExtend (I := I) α b v)) ∘
        (extChartAt I α).symm) =ᶠ[𝓝 (extChartAt I α b)]
      (fun y : E =>
        curryLeftEvalCLM (E := E) s (trivToE (I := I) α b v)
          ((tensor0SChartESectionRepr (I := I) (s + 1) α T ∘
            (extChartAt I α).symm) y)) := by
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
  exact tensor0SChartE_section_repr_partialEval_eq_curryLeftEval
    (I := I) (M := M) s α T (b := b) v (b' := φ.symm y) hyBase

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.partialEval_chartPullback_eventually_eq_curryLeftEval_chartPullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.partialEval_chartPullback_eventually_eq_curryLeftEval_chartPullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.partialEval_chartPullback_eventually_eq_curryLeftEval_chartPullback ``Submission.DifferentialGeometry.Geometry.Connection.partialEval_chartPullback_eventually_eq_curryLeftEval_chartPullback

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem fderiv_partialEval_chartPullback_eq_comp_curryLeftEval (s : ℕ) (α : M)
    (T : Π b : M, Tensor0SSpace (s + 1) I b)
    {b : M} (v : TangentSpace I b)
    (hb_source : b ∈ (extChartAt I α).source)
    (hb_target : extChartAt I α b ∈ interior ((extChartAt I α).target : Set E))
    (hb_base : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet)
    (hT : DifferentiableAt ℝ
      (tensor0SChartESectionRepr (I := I) (s + 1) α T ∘ (extChartAt I α).symm)
      (extChartAt I α b)) :
    fderiv ℝ
        (tensor0SChartESectionRepr (I := I) s α
            (Tensor0SPartialEval.tensor0SPartialEval I M T
              (chartParallelExtend (I := I) α b v)) ∘
          (extChartAt I α).symm)
        (extChartAt I α b) =
      (curryLeftEvalCLM (E := E) s (trivToE (I := I) α b v)).comp
        (fderiv ℝ
          (tensor0SChartESectionRepr (I := I) (s + 1) α T ∘
            (extChartAt I α).symm)
          (extChartAt I α b)) := by
  classical
  have heq := partialEval_chartPullback_eventually_eq_curryLeftEval_chartPullback
    (I := I) (M := M) s α T (b := b) v hb_source hb_target hb_base
  rw [Filter.EventuallyEq.fderiv_eq heq]
  exact (((curryLeftEvalCLM (E := E) s (trivToE (I := I) α b v)).hasFDerivAt
      (x := (tensor0SChartESectionRepr (I := I) (s + 1) α T ∘
        (extChartAt I α).symm) (extChartAt I α b))).comp
    (extChartAt I α b) hT.hasFDerivAt).fderiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.fderiv_partialEval_chartPullback_eq_comp_curryLeftEval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.fderiv_partialEval_chartPullback_eq_comp_curryLeftEval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.fderiv_partialEval_chartPullback_eq_comp_curryLeftEval ``Submission.DifferentialGeometry.Geometry.Connection.fderiv_partialEval_chartPullback_eq_comp_curryLeftEval

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem tensor0SIntrinsicChartCLM_factor
    (s : ℕ) (α : M) (T : Π b : M, Tensor0SSpace (s + 1) I b)
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α)
    (v : TangentSpace I b)
    (hT : DifferentiableAt ℝ
      (tensor0SChartESectionRepr (I := I) (s + 1) α T ∘ (extChartAt I α).symm)
      (extChartAt I α b))
    (X : Π b' : M, TangentSpace I b')
    (m : Fin s → TangentSpace I b) :
    Tensor0SSpace.eval
        (tensor0SIntrinsicChartCLM (I := I) (s + 1) α T b (X b))
        (Fin.cons (chartParallelExtend (I := I) α b v b) m) =
      Tensor0SSpace.eval
        (tensor0SIntrinsicChartCLM (I := I) s α
          (Tensor0SPartialEval.tensor0SPartialEval I M T
            (chartParallelExtend (I := I) α b v))
          b (X b)) m := by
  classical
  let _h_top_succ : TopologicalSpace (_root_.Bundle.TotalSpace (Tensor0SModel (s + 1) ℝ E)
      (fun y : M => Tensor0SSpace (s + 1) I y)) :=
    tensor0SBundleTopology (s + 1)
  let _h_top_s : TopologicalSpace (_root_.Bundle.TotalSpace (Tensor0SModel s ℝ E)
      (fun y : M => Tensor0SSpace s I y)) :=
    tensor0SBundleTopology s
  have hb_source : b ∈ (extChartAt I α).source :=
    chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hb
  have hb_target : extChartAt I α b ∈ interior ((extChartAt I α).target : Set E) :=
    chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hb
  have hb_base : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hb
  set w : E := trivToE (I := I) α b (X b) with hw_def
  set mE : Fin s → E := fun i => trivToE (I := I) α b (m i) with hmt_def
  have hLHS_unfold :
      Tensor0SSpace.eval
        (tensor0SIntrinsicChartCLM (I := I) (s + 1) α T b (X b))
        (Fin.cons (chartParallelExtend (I := I) α b v b) m) =
      (fderiv ℝ
        (tensor0SChartESectionRepr (I := I) (s + 1) α T ∘ (extChartAt I α).symm)
        (extChartAt I α b) w)
        (Fin.cons (trivToE (I := I) α b v) mE) := by
    rw [tensor0SIntrinsicChartCLM_apply (I := I) (s + 1) α T b (X b)]
    unfold tensor0SChartFiberFromModel
    set D := fderiv ℝ
        (tensor0SChartESectionRepr (I := I) (s + 1) α T ∘ (extChartAt I α).symm)
        (extChartAt I α b) (trivToE (I := I) α b (X b))
    rw [tensor0SBundle_symmL_apply_eq_compContinuousLinearMap
      (I := I) (M := M) (n := s + 1) α hb_base D]
    rw [Tensor0SSpace.eval_fiber_equiv_symm]
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    congr 1
    funext j
    refine Fin.cases ?_ ?_ j
    · simp only [Fin.cons_zero]
      change trivToE (I := I) α b
          (trivFromE (I := I) α b (trivToE (I := I) α b v)) = trivToE (I := I) α b v
      exact trivToE_trivFromE (I := I) α hb_base _
    · intro k
      simp only [Fin.cons_succ]
      rfl
  rw [hLHS_unfold]
  have hRHS_unfold :
      Tensor0SSpace.eval
        (tensor0SIntrinsicChartCLM (I := I) s α
          (Tensor0SPartialEval.tensor0SPartialEval I M T
            (chartParallelExtend (I := I) α b v))
          b (X b)) m =
      (fderiv ℝ
        (tensor0SChartESectionRepr (I := I) s α
            (Tensor0SPartialEval.tensor0SPartialEval I M T
              (chartParallelExtend (I := I) α b v)) ∘
          (extChartAt I α).symm)
        (extChartAt I α b) w) mE := by
    rw [tensor0SIntrinsicChartCLM_apply (I := I) s α _ b (X b)]
    unfold tensor0SChartFiberFromModel
    set D' := fderiv ℝ
        (tensor0SChartESectionRepr (I := I) s α
          (Tensor0SPartialEval.tensor0SPartialEval I M T
            (chartParallelExtend (I := I) α b v)) ∘ (extChartAt I α).symm)
        (extChartAt I α b) (trivToE (I := I) α b (X b))
    rw [tensor0SBundle_symmL_apply_eq_compContinuousLinearMap
      (I := I) (M := M) (n := s) α hb_base D']
    rw [Tensor0SSpace.eval_fiber_equiv_symm]
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [hRHS_unfold]
  have hfderivEq := fderiv_partialEval_chartPullback_eq_comp_curryLeftEval
    (I := I) (M := M) s α T (b := b) v hb_source hb_target hb_base hT
  have hfderiv_at_w : fderiv ℝ
        (tensor0SChartESectionRepr (I := I) s α
            (Tensor0SPartialEval.tensor0SPartialEval I M T
              (chartParallelExtend (I := I) α b v)) ∘
          (extChartAt I α).symm)
        (extChartAt I α b) w =
      curryLeftEvalCLM (E := E) s (trivToE (I := I) α b v)
        (fderiv ℝ
          (tensor0SChartESectionRepr (I := I) (s + 1) α T ∘
            (extChartAt I α).symm)
          (extChartAt I α b) w) := by
    have := congrArg (fun L : E →L[ℝ] Tensor0SModel s ℝ E => L w) hfderivEq
    simpa [ContinuousLinearMap.comp_apply] using this
  rw [hfderiv_at_w, curryLeftEvalCLM_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensor0SIntrinsicChartCLM_factor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensor0SIntrinsicChartCLM_factor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensor0SIntrinsicChartCLM_factor ``Submission.DifferentialGeometry.Geometry.Connection.tensor0SIntrinsicChartCLM_factor

end Connection
end Geometry
end DifferentialGeometry

end
