import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.ChartGeometry.JinvContinuity
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.InnerBounds.InnerLowerBound
import Submission.DifferentialGeometry.Tensor.RSTensor.Defs
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Bundle.SectionRegularity
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Tangent.Riemannian
import Submission.DifferentialGeometry.Geometry.Metric.PointwiseInner.Defs
import Submission.DifferentialGeometry.Geometry.Metric.PointwiseInner.DualMetric
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.Algebra.Module.Multilinear.Topology
import Mathlib.Topology.FiberBundle.Trivialization
import Mathlib.Topology.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.IsManifold _root_.ContinuousLinearMap _root_.Submission.ContinuousLinearMap _root_.Bundle.ContinuousLinearMap
open scoped _root_.Manifold _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.ContDiff _root_.BigOperators _root_.Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Tensor
open _root_.Submission.DifferentialGeometry.Tensor.Tensor0SRiemannian
open _root_.Submission.DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem chartJ_apply_chartBasisVecFiber_continuousOn
    (α : M) (i : Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (fun b : M => chartTrivializationLinearMap (I := I) (M := M) α b
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i b))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
  have heq : ∀ b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet,
      chartTrivializationLinearMap (I := I) (M := M) α b
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i b) = (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i := by
    intro b hb
    unfold chartTrivializationLinearMap DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber
    exact (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).continuousLinearMapAt_symmL hb
      ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)
  refine ContinuousOn.congr ?_ (fun b hb => heq b hb)
  exact continuousOn_const

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartJ_apply_chartBasisVecFiber_continuousOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartJ_apply_chartBasisVecFiber_continuousOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartJ_apply_chartBasisVecFiber_continuousOn ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartJ_apply_chartBasisVecFiber_continuousOn

theorem metric_inner_chartBasisFibers_continuousOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (fun b : M =>
        g.inner b
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i b)
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j b))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
  have hsmooth : ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix g α b i j)
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet :=
    DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_entry_contMDiffOn (I := I) g α i j
  have hcont : ContinuousOn (fun b : M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix g α b i j)
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet :=
    hsmooth.continuousOn
  refine hcont.congr ?_
  intro b _
  exact (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_apply g α b i j).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metric_inner_chartBasisFibers_continuousOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metric_inner_chartBasisFibers_continuousOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metric_inner_chartBasisFibers_continuousOn ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metric_inner_chartBasisFibers_continuousOn

theorem separableFormAt_chartBasisFibers_eval_continuousOn
    (g : SmoothRiemannianMetric I M) (α : M) (r : ℕ)
    (Idx Jdx : Fin r → Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (fun b : M =>
        separableFormAt (I := I) (M := M) g b r
          (fun k : Fin r => tangentSpaceModelContinuousLinearEquiv (I := I) b
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α (Idx k) b))
          (fun k : Fin r => tangentSpaceModelContinuousLinearEquiv (I := I) b
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α (Jdx k) b)))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
  have heq : ∀ b : M,
      separableFormAt (I := I) (M := M) g b r
          (fun k : Fin r => tangentSpaceModelContinuousLinearEquiv (I := I) b
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α (Idx k) b))
          (fun k : Fin r => tangentSpaceModelContinuousLinearEquiv (I := I) b
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α (Jdx k) b)) =
        ∏ k : Fin r, g.inner b
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α (Idx k) b)
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α (Jdx k) b) := by
    intro b
    rw [separableFormAt_apply]
    apply Finset.prod_congr rfl
    intro k _
    simp
  refine ContinuousOn.congr ?_ (fun b _ => heq b)
  refine continuousOn_finsetProd _ (fun k _ => ?_)
  exact metric_inner_chartBasisFibers_continuousOn (I := I) (M := M) g α
    (Idx k) (Jdx k)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.separableFormAt_chartBasisFibers_eval_continuousOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.separableFormAt_chartBasisFibers_eval_continuousOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.separableFormAt_chartBasisFibers_eval_continuousOn ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.separableFormAt_chartBasisFibers_eval_continuousOn

omit [Module.Finite ℝ E] in
theorem triv_symm_apply_const_continuousOn_baseSet
    (α : M) (v : E) :
    ContinuousOn
      (fun b : M => TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) b
        ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).symm b v))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
  have hsymm :
      ContinuousOn
        (fun z : M × E => TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          z.1 ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).symm z.1 z.2))
        ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet ×ˢ Set.univ) :=
    (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).continuousOn_symm
  have hcomp : Continuous (fun b : M => (b, v)) :=
    continuous_id.prodMk continuous_const
  have hmaps :
      Set.MapsTo (fun b : M => (b, v))
        (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet
        ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet ×ˢ Set.univ) := by
    intro b hb
    exact ⟨hb, Set.mem_univ _⟩
  exact hsymm.comp hcomp.continuousOn hmaps

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.triv_symm_apply_const_continuousOn_baseSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.triv_symm_apply_const_continuousOn_baseSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.triv_symm_apply_const_continuousOn_baseSet ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.triv_symm_apply_const_continuousOn_baseSet

theorem chartBasisVec_continuousOn_baseSet
    (α : M) (k : Fin (Module.finrank ℝ E)) :
    ContinuousOn (DifferentialGeometry.Tensor.Coordinates.chartBasisVec (I := I) α k)
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
  unfold DifferentialGeometry.Tensor.Coordinates.chartBasisVec DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber
  refine ContinuousOn.congr
    (triv_symm_apply_const_continuousOn_baseSet (I := I) (M := M) α
      ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k)) ?_
  intro x hx
  change TotalSpace.mk' E x
      ((Trivialization.symmL ℝ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α) x)
        ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k)) =
    TotalSpace.mk' E x
      ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).symm x ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k))
  rw [Trivialization.symmL_apply _ hx]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartBasisVec_continuousOn_baseSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartBasisVec_continuousOn_baseSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartBasisVec_continuousOn_baseSet ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartBasisVec_continuousOn_baseSet

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [Module.Finite ℝ E] in
private lemma continuousOn_g_inner
    (g : SmoothRiemannianMetric I M)
    {v w : ∀ x : M, TangentSpace I x} {s : Set M}
    (hv : ContinuousOn (fun x : M => TotalSpace.mk' E
      (E := (TangentSpace I : M → Type _)) x (v x)) s)
    (hw : ContinuousOn (fun x : M => TotalSpace.mk' E
      (E := (TangentSpace I : M → Type _)) x (w x)) s) :
    ContinuousOn (fun b : M => g.inner b (v b) (w b)) s := by
  let cg : Bundle.ContinuousRiemannianMetric E (TangentSpace I : M → Type _) :=
    g.toContinuousRiemannianMetric
  let rb : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨cg.toRiemannianMetric⟩
  have h := ContinuousOn.inner_bundle (F := E) (B := M)
    (E := (TangentSpace I : M → Type _)) (b := fun x => x) (v := v) (w := w)
    (s := s) hv hw
  refine h.congr ?_
  intro b _
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.continuousOn_g_inner
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.continuousOn_g_inner target :: scope.openDecls } }

omit [Module.Finite ℝ E] in
theorem metric_inner_sections_continuousOn
    (g : SmoothRiemannianMetric I M)
    {v w : ∀ x : M, TangentSpace I x} {s : Set M}
    (hv : ContinuousOn (fun x : M => TotalSpace.mk' E
      (E := (TangentSpace I : M → Type _)) x (v x)) s)
    (hw : ContinuousOn (fun x : M => TotalSpace.mk' E
      (E := (TangentSpace I : M → Type _)) x (w x)) s) :
    ContinuousOn (fun b : M => g.inner b (v b) (w b)) s :=
  continuousOn_g_inner (I := I) (M := M) g hv hw

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metric_inner_sections_continuousOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metric_inner_sections_continuousOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metric_inner_sections_continuousOn ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metric_inner_sections_continuousOn

theorem metric_inner_chartBasisFiber_trivSymm_continuousOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (k : Fin (Module.finrank ℝ E)) (v : E) :
    ContinuousOn
      (fun b : M =>
        g.inner b
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k b)
          ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).symm b v))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
  have hX : ContinuousOn (DifferentialGeometry.Tensor.Coordinates.chartBasisVec (I := I) α k)
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet :=
    chartBasisVec_continuousOn_baseSet (I := I) (M := M) α k
  have hY : ContinuousOn
      (fun b : M => TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) b
        ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).symm b v))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet :=
    triv_symm_apply_const_continuousOn_baseSet (I := I) (M := M) α v
  have h := metric_inner_sections_continuousOn (I := I) (M := M) (E := E) g
    (v := fun b => DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k b)
    (w := fun b => (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).symm b v)
    (s := (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet) hX hY
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metric_inner_chartBasisFiber_trivSymm_continuousOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metric_inner_chartBasisFiber_trivSymm_continuousOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metric_inner_chartBasisFiber_trivSymm_continuousOn ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metric_inner_chartBasisFiber_trivSymm_continuousOn

omit [Module.Finite ℝ E] in
theorem metric_inner_trivSymm_trivSymm_continuousOn
    (g : SmoothRiemannianMetric I M) (α : M) (v w : E) :
    ContinuousOn
      (fun b : M =>
        g.inner b
          ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).symm b v)
          ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).symm b w))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
  have hX : ContinuousOn
      (fun b : M => TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) b
        ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).symm b v))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet :=
    triv_symm_apply_const_continuousOn_baseSet (I := I) (M := M) α v
  have hY : ContinuousOn
      (fun b : M => TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) b
        ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).symm b w))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet :=
    triv_symm_apply_const_continuousOn_baseSet (I := I) (M := M) α w
  exact metric_inner_sections_continuousOn (I := I) (M := M) (E := E) g
    (v := fun b => (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).symm b v)
    (w := fun b => (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).symm b w)
    (s := (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet) hX hY

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metric_inner_trivSymm_trivSymm_continuousOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metric_inner_trivSymm_trivSymm_continuousOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metric_inner_trivSymm_trivSymm_continuousOn ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metric_inner_trivSymm_trivSymm_continuousOn

section HeadlineNormComparison

variable [NeZero (Module.finrank ℝ E)]
variable [T2Space M] [CompactSpace M] [I.Boundaryless]

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M]
    [I.Boundaryless] in
lemma sq_norm_le_inv_eps_mul_chartTensorInnerPointwise_rs_model_on_compact
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    {K_M : Set M}
    (hK_M_sub_baseSet :
      K_M ⊆ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet)
    {ε : ℝ} (hε : 0 < ε)
    (h_lb : ∀ b : M, b ∈ K_M →
      ∀ T : TensorRSModel r s ℝ E, ‖T‖ = 1 →
        ε ≤ chartTensorInnerPointwiseRsModel (I := I) (M := M)
          g r s α b T T) :
    ∀ b : M, b ∈ K_M →
      ∀ T : TensorRSModel r s ℝ E,
        ‖T‖ ^ 2 ≤ ε⁻¹ *
          chartTensorInnerPointwiseRsModel (I := I) (M := M) g r s α b T T := by
  classical
  intro b hb T
  have hb_base : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet :=
    hK_M_sub_baseSet hb
  have hQ_nn : 0 ≤ chartTensorInnerPointwiseRsModel
      (I := I) (M := M) g r s α b T T :=
    chartTensorInnerPointwise_rs_model_nonneg
      (I := I) (M := M) g r s α hb_base T
  by_cases hT0 : T = 0
  · subst hT0
    have h_left : ‖(0 : TensorRSModel r s ℝ E)‖ ^ 2 = 0 := by
      simp
    have h_right : chartTensorInnerPointwiseRsModel
        (I := I) (M := M) g r s α b (0 : TensorRSModel r s ℝ E)
          (0 : TensorRSModel r s ℝ E) = 0 := by
      have h_zero_smul :
          chartTensorInnerPointwiseRsModel
            (I := I) (M := M) g r s α b
              ((0 : ℝ) • (0 : TensorRSModel r s ℝ E))
              (0 : TensorRSModel r s ℝ E) =
          (0 : ℝ) *
            chartTensorInnerPointwiseRsModel
              (I := I) (M := M) g r s α b
                (0 : TensorRSModel r s ℝ E) (0 : TensorRSModel r s ℝ E) :=
        chartTensorInnerPointwise_rs_model_smul_left
          (I := I) (M := M) g r s α b 0 (0 : TensorRSModel r s ℝ E)
          (0 : TensorRSModel r s ℝ E)
      have h_eq : (0 : TensorRSModel r s ℝ E) =
          ((0 : ℝ) • (0 : TensorRSModel r s ℝ E)) := by rw [zero_smul]
      calc chartTensorInnerPointwiseRsModel
            (I := I) (M := M) g r s α b
              (0 : TensorRSModel r s ℝ E) (0 : TensorRSModel r s ℝ E)
          = chartTensorInnerPointwiseRsModel
              (I := I) (M := M) g r s α b
                ((0 : ℝ) • (0 : TensorRSModel r s ℝ E))
                (0 : TensorRSModel r s ℝ E) := by rw [← h_eq]
        _ = (0 : ℝ) *
            chartTensorInnerPointwiseRsModel
              (I := I) (M := M) g r s α b
                (0 : TensorRSModel r s ℝ E) (0 : TensorRSModel r s ℝ E) :=
              h_zero_smul
        _ = 0 := by ring
    rw [h_left, h_right, _root_.MulZeroClass.mul_zero]
  · have hT_ne : ‖T‖ ≠ 0 := norm_ne_zero_iff.mpr hT0
    have hT_pos : 0 < ‖T‖ := (norm_pos_iff).mpr hT0
    let _ : NormSMulClass ℝ (TensorRSModel r s ℝ E) :=
      NormedSpace.toNormSMulClass
    set T' : TensorRSModel r s ℝ E := ‖T‖⁻¹ • T with hT'_def
    have hT'_norm : ‖T'‖ = 1 := by
      rw [hT'_def, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hT_pos]
      field_simp
    have h_T' : ε ≤ chartTensorInnerPointwiseRsModel
        (I := I) (M := M) g r s α b T' T' :=
      h_lb b hb T' hT'_norm
    have h_bilin :
        chartTensorInnerPointwiseRsModel (I := I) (M := M) g r s α b T' T' =
          (‖T‖⁻¹ * ‖T‖⁻¹) *
            chartTensorInnerPointwiseRsModel
              (I := I) (M := M) g r s α b T T := by
      rw [hT'_def]
      rw [chartTensorInnerPointwise_rs_model_smul_left
        (I := I) (M := M) g r s α b ‖T‖⁻¹ T (‖T‖⁻¹ • T)]
      rw [chartTensorInnerPointwise_rs_model_smul_right
        (I := I) (M := M) g r s α b ‖T‖⁻¹ T T]
      ring
    rw [h_bilin] at h_T'
    have h_sq_pos : 0 < ‖T‖ ^ 2 := by positivity
    have h_mul : ε * ‖T‖ ^ 2 ≤
        ((‖T‖⁻¹ * ‖T‖⁻¹) *
          chartTensorInnerPointwiseRsModel
            (I := I) (M := M) g r s α b T T) * ‖T‖ ^ 2 :=
      mul_le_mul_of_nonneg_right h_T' (le_of_lt h_sq_pos)
    have h_rhs :
        ((‖T‖⁻¹ * ‖T‖⁻¹) *
          chartTensorInnerPointwiseRsModel
            (I := I) (M := M) g r s α b T T) * ‖T‖ ^ 2 =
          chartTensorInnerPointwiseRsModel
            (I := I) (M := M) g r s α b T T := by
      have h_sq_eq : ‖T‖ ^ 2 = ‖T‖ * ‖T‖ := by ring
      rw [h_sq_eq]
      field_simp
    rw [h_rhs] at h_mul
    rw [show ε⁻¹ * chartTensorInnerPointwiseRsModel
        (I := I) (M := M) g r s α b T T =
        chartTensorInnerPointwiseRsModel
          (I := I) (M := M) g r s α b T T / ε by
      rw [div_eq_inv_mul]]
    exact (le_div_iff₀ hε).mpr (by linarith [h_mul])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sq_norm_le_inv_eps_mul_chartTensorInnerPointwise_rs_model_on_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sq_norm_le_inv_eps_mul_chartTensorInnerPointwise_rs_model_on_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sq_norm_le_inv_eps_mul_chartTensorInnerPointwise_rs_model_on_compact ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sq_norm_le_inv_eps_mul_chartTensorInnerPointwise_rs_model_on_compact

omit [T2Space M] [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartTrivializationNorm_le_const_mul_chartTensorInnerPointwise_rs_model_on_compact
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    {K_M : Set M} (hK_M_compact : IsCompact K_M)
    (hK_M_sub_baseSet :
      K_M ⊆ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ b : M, b ∈ K_M →
        ∀ T : TensorRSModel r s ℝ E,
          ‖T‖ ^ 2 ≤ K * chartTensorInnerPointwiseRsModel
            (I := I) (M := M) g r s α b T T := by
  classical
  obtain ⟨ε, hε_pos, h_lb⟩ :=
    exists_chartTensorInnerPointwise_rs_model_lower_bound_on_compact
      (I := I) (M := M) g r s α hK_M_compact hK_M_sub_baseSet
  refine ⟨ε⁻¹, le_of_lt (inv_pos.mpr hε_pos), ?_⟩
  exact sq_norm_le_inv_eps_mul_chartTensorInnerPointwise_rs_model_on_compact
    (I := I) (M := M) g r s α hK_M_sub_baseSet hε_pos h_lb

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartTrivializationNorm_le_const_mul_chartTensorInnerPointwise_rs_model_on_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartTrivializationNorm_le_const_mul_chartTensorInnerPointwise_rs_model_on_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartTrivializationNorm_le_const_mul_chartTensorInnerPointwise_rs_model_on_compact ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartTrivializationNorm_le_const_mul_chartTensorInnerPointwise_rs_model_on_compact

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartTrivializationNorm_le_const_mul_chartTensorInnerPointwise_rs_model_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ b : M, b ∈ tsupport (fun x : M =>
          ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ T : TensorRSModel r s ℝ E,
          ‖T‖ ^ 2 ≤ K * chartTensorInnerPointwiseRsModel
            (I := I) (M := M) g r s α b T T :=
  chartTrivializationNorm_le_const_mul_chartTensorInnerPointwise_rs_model_on_compact
    (I := I) (M := M) g r s α
    (pouTsupport_isCompact (I := I) (M := M) α)
    (pouTsupport_subset_baseSet (I := I) (M := M) α)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartTrivializationNorm_le_const_mul_chartTensorInnerPointwise_rs_model_on_pouTsupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartTrivializationNorm_le_const_mul_chartTensorInnerPointwise_rs_model_on_pouTsupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartTrivializationNorm_le_const_mul_chartTensorInnerPointwise_rs_model_on_pouTsupport ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartTrivializationNorm_le_const_mul_chartTensorInnerPointwise_rs_model_on_pouTsupport

omit [T2Space M] [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartTrivializationNorm_le_const_mul_tensorInnerPointwise_chartRSTwist_on_compact
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    {K_M : Set M} (hK_M_compact : IsCompact K_M)
    (hK_M_sub_baseSet :
      K_M ⊆ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ b : M, b ∈ K_M →
        ∀ T : TensorRSModel r s ℝ E,
          ‖T‖ ^ 2 ≤ K * tensorInnerPointwise (I := I) (M := M) g r s b
            (chartRSTwist (I := I) (M := M) α b r s T)
            (chartRSTwist (I := I) (M := M) α b r s T) := by
  classical
  obtain ⟨K, hK_nn, h_chart⟩ :=
    chartTrivializationNorm_le_const_mul_chartTensorInnerPointwise_rs_model_on_compact
      (I := I) (M := M) g r s α hK_M_compact hK_M_sub_baseSet
  refine ⟨K, hK_nn, ?_⟩
  intro b hb T
  have hb_base : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet :=
    hK_M_sub_baseSet hb
  have h := h_chart b hb T
  rw [chartTensorInnerPointwise_rs_model_eq_tensorInnerPointwise
      (I := I) (M := M) g r s α hb_base T T] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartTrivializationNorm_le_const_mul_tensorInnerPointwise_chartRSTwist_on_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartTrivializationNorm_le_const_mul_tensorInnerPointwise_chartRSTwist_on_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartTrivializationNorm_le_const_mul_tensorInnerPointwise_chartRSTwist_on_compact ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartTrivializationNorm_le_const_mul_tensorInnerPointwise_chartRSTwist_on_compact

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartTrivializationNorm_le_const_mul_tensorInnerPointwise_chartRSTwist_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ b : M, b ∈ tsupport (fun x : M =>
          ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ T : TensorRSModel r s ℝ E,
          ‖T‖ ^ 2 ≤ K * tensorInnerPointwise (I := I) (M := M) g r s b
            (chartRSTwist (I := I) (M := M) α b r s T)
            (chartRSTwist (I := I) (M := M) α b r s T) :=
  chartTrivializationNorm_le_const_mul_tensorInnerPointwise_chartRSTwist_on_compact
    (I := I) (M := M) g r s α
    (pouTsupport_isCompact (I := I) (M := M) α)
    (pouTsupport_subset_baseSet (I := I) (M := M) α)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartTrivializationNorm_le_const_mul_tensorInnerPointwise_chartRSTwist_on_pouTsupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartTrivializationNorm_le_const_mul_tensorInnerPointwise_chartRSTwist_on_pouTsupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartTrivializationNorm_le_const_mul_tensorInnerPointwise_chartRSTwist_on_pouTsupport ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartTrivializationNorm_le_const_mul_tensorInnerPointwise_chartRSTwist_on_pouTsupport

end HeadlineNormComparison

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
