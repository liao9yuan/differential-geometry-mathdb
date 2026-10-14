import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Bundle.SectionRegularity
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Invariance
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Separation.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.IsManifold _root_.ContinuousLinearMap _root_.Submission.ContinuousLinearMap _root_.Bundle.ContinuousLinearMap _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.ContDiff _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open _root_.Submission.DifferentialGeometry.Tensor
open _root_.Submission.DifferentialGeometry.Tensor.Tensor0SRiemannian
open _root_.Submission.DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [InnerProductSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

omit [T2Space M] in
private lemma achart_eq_of_chartAt_eq {b b₀ : M}
    (h_chart : chartAt H b = chartAt H b₀) :
    achart H b = achart H b₀ :=
  Subtype.ext h_chart

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.achart_eq_of_chartAt_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.achart_eq_of_chartAt_eq target :: scope.openDecls } }

omit [Module.Finite ℝ E] [InnerProductSpace ℝ E] [T2Space M] in
private lemma trivb₀_symmL_eq_id_of_chartAt_eq
    {b b₀ : M} (h_chart : chartAt H b = chartAt H b₀)
    (hb : b ∈ (chartAt H b₀).source) :
    (_root_.FiberBundle.trivializationAt E (TangentSpace I) b₀).symmL ℝ b = (1 : E →L[ℝ] E) := by
  rw [TangentBundle.symmL_trivializationAt_eq_core (𝕜 := ℝ) (I := I)
    (b₀ := b₀) (b := b) hb]
  rw [achart_eq_of_chartAt_eq (H := H) (M := M) h_chart]
  ext v
  apply (tangentBundleCore I M).coordChange_self (achart H b₀) b
  rw [tangentBundleCore_baseSet, coe_achart]
  exact hb

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.trivb₀_symmL_eq_id_of_chartAt_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.trivb₀_symmL_eq_id_of_chartAt_eq target :: scope.openDecls } }

omit [Module.Finite ℝ E] [InnerProductSpace ℝ E] [T2Space M] in
private lemma trivb₀_clmAt_eq_id_of_chartAt_eq
    {b b₀ : M} (h_chart : chartAt H b = chartAt H b₀)
    (hb : b ∈ (chartAt H b₀).source) :
    (_root_.FiberBundle.trivializationAt E (TangentSpace I) b₀).continuousLinearMapAt ℝ b =
      (1 : E →L[ℝ] E) := by
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core
    (𝕜 := ℝ) (I := I) (b₀ := b₀) (b := b) hb]
  rw [achart_eq_of_chartAt_eq (H := H) (M := M) h_chart]
  ext v
  apply (tangentBundleCore I M).coordChange_self (achart H b₀) b
  rw [tangentBundleCore_baseSet, coe_achart]
  exact hb

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.trivb₀_clmAt_eq_id_of_chartAt_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.trivb₀_clmAt_eq_id_of_chartAt_eq target :: scope.openDecls } }

omit [Module.Finite ℝ E] [InnerProductSpace ℝ E] [T2Space M] in
private lemma continuousOn_coordChangeL_b₀_α (b₀ α : M) :
    ContinuousOn
      (fun b : M => ((_root_.FiberBundle.trivializationAt E (TangentSpace I) b₀).coordChangeL ℝ
        (_root_.FiberBundle.trivializationAt E (TangentSpace I) α) b : E →L[ℝ] E))
      ((chartAt H b₀).source ∩ (chartAt H α).source) := by
  have h_smooth :
      ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) ∞
        (fun b : M => ((_root_.FiberBundle.trivializationAt E (TangentSpace I) b₀).coordChangeL ℝ
          (_root_.FiberBundle.trivializationAt E (TangentSpace I) α) b : E →L[ℝ] E))
        ((_root_.FiberBundle.trivializationAt E (TangentSpace I) b₀).baseSet ∩
          (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet) :=
    contMDiffOn_coordChangeL (n := (∞ : WithTop ℕ∞)) (IB := I) (F := E)
      (E := (TangentSpace I : M → Type _))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) b₀)
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α)
  have h_base_b₀ : (_root_.FiberBundle.trivializationAt E (TangentSpace I) b₀).baseSet =
      (chartAt H b₀).source :=
    TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) b₀
  have h_base_α : (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet =
      (chartAt H α).source :=
    TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) α
  rw [h_base_b₀, h_base_α] at h_smooth
  exact h_smooth.continuousOn

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.continuousOn_coordChangeL_b₀_α
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.continuousOn_coordChangeL_b₀_α target :: scope.openDecls } }

omit [Module.Finite ℝ E] [InnerProductSpace ℝ E] [T2Space M] in
private lemma coordChangeL_eq_chartJ_of_locality
    (α : M) {b b₀ : M}
    (hb_α : b ∈ (chartAt H α).source)
    (hb_b₀ : b ∈ (chartAt H b₀).source)
    (h_chart : chartAt H b = chartAt H b₀) :
    ((_root_.FiberBundle.trivializationAt E (TangentSpace I) b₀).coordChangeL ℝ
        (_root_.FiberBundle.trivializationAt E (TangentSpace I) α) b : E →L[ℝ] E) =
      chartTrivializationLinearMap (I := I) (M := M) α b := by
  ext v
  have hb_b₀' : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) b₀).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) b₀]
    exact hb_b₀
  have hb_α' : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) α]
    exact hb_α
  have h_apply :
      ((_root_.FiberBundle.trivializationAt E (TangentSpace I) b₀).coordChangeL ℝ
        (_root_.FiberBundle.trivializationAt E (TangentSpace I) α) b : E →L[ℝ] E) v =
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b
        ((_root_.FiberBundle.trivializationAt E (TangentSpace I) b₀).symmL ℝ b v) := by
    change ((_root_.FiberBundle.trivializationAt E (TangentSpace I) b₀).coordChangeL ℝ
        (_root_.FiberBundle.trivializationAt E (TangentSpace I) α) b) v =
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b
        ((_root_.FiberBundle.trivializationAt E (TangentSpace I) b₀).symmL ℝ b v)
    rw [Trivialization.coordChangeL_apply _ _ ⟨hb_b₀', hb_α'⟩]
    rw [Bundle.Trivialization.continuousLinearMapAt_apply,
        Bundle.Trivialization.coe_linearMapAt_of_mem _ hb_α',
        Bundle.Trivialization.symmL_apply _ hb_b₀']
  rw [h_apply]
  have h_symmL_id := trivb₀_symmL_eq_id_of_chartAt_eq (I := I) (M := M)
    h_chart hb_b₀
  have h_eq : (_root_.FiberBundle.trivializationAt E (TangentSpace I) b₀).symmL ℝ b v = v := by
    have := congrArg (fun (f : E →L[ℝ] E) => f v) h_symmL_id
    change ((_root_.FiberBundle.trivializationAt E (TangentSpace I) b₀).symmL ℝ b : E →L[ℝ] E) v = v
    exact this
  rw [h_eq]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.coordChangeL_eq_chartJ_of_locality
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.coordChangeL_eq_chartJ_of_locality target :: scope.openDecls } }

omit [Module.Finite ℝ E] [InnerProductSpace ℝ E] [T2Space M] in
private lemma coordChangeL_eq_chartJinv_of_locality
    (α : M) {b b₀ : M}
    (hb_α : b ∈ (chartAt H α).source)
    (hb_b₀ : b ∈ (chartAt H b₀).source)
    (h_chart : chartAt H b = chartAt H b₀) :
    ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).coordChangeL ℝ
        (_root_.FiberBundle.trivializationAt E (TangentSpace I) b₀) b : E →L[ℝ] E) =
      chartTrivializationLinearMapSymm (I := I) (M := M) α b := by
  ext v
  have hb_b₀' : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) b₀).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) b₀]
    exact hb_b₀
  have hb_α' : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) α]
    exact hb_α
  have h_apply :
      ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).coordChangeL ℝ
        (_root_.FiberBundle.trivializationAt E (TangentSpace I) b₀) b : E →L[ℝ] E) v =
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) b₀).continuousLinearMapAt ℝ b
        ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).symmL ℝ b v) := by
    change ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).coordChangeL ℝ
        (_root_.FiberBundle.trivializationAt E (TangentSpace I) b₀) b) v =
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) b₀).continuousLinearMapAt ℝ b
        ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).symmL ℝ b v)
    rw [Trivialization.coordChangeL_apply _ _ ⟨hb_α', hb_b₀'⟩]
    rw [Bundle.Trivialization.continuousLinearMapAt_apply,
        Bundle.Trivialization.coe_linearMapAt_of_mem _ hb_b₀',
        Bundle.Trivialization.symmL_apply _ hb_α']
  rw [h_apply]
  have h_clmAt_id := trivb₀_clmAt_eq_id_of_chartAt_eq (I := I) (M := M)
    h_chart hb_b₀
  have h_eq :
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) b₀).continuousLinearMapAt ℝ b
        ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).symmL ℝ b v) =
        (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).symmL ℝ b v := by
    have := congrArg
      (fun (f : E →L[ℝ] E) =>
        f ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).symmL ℝ b v)) h_clmAt_id
    change (_root_.FiberBundle.trivializationAt E (TangentSpace I) b₀).continuousLinearMapAt ℝ b
      ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).symmL ℝ b v) =
        (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).symmL ℝ b v
    exact this
  rw [h_eq]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.coordChangeL_eq_chartJinv_of_locality
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.coordChangeL_eq_chartJinv_of_locality target :: scope.openDecls } }

omit [Module.Finite ℝ E] [InnerProductSpace ℝ E] [T2Space M] in
private lemma chartJ_continuousOn_local
    (α b₀ : M)
    {U : Set M}
    (hU_sub_b₀ : U ⊆ (chartAt H b₀).source)
    (hU_sub_α : U ⊆ (chartAt H α).source)
    (hU_const : ∀ b ∈ U, chartAt H b = chartAt H b₀) :
    ContinuousOn (fun b : M => chartTrivializationLinearMap (I := I) (M := M) α b) U := by
  have h_coord_cont :
      ContinuousOn
        (fun b : M => ((_root_.FiberBundle.trivializationAt E (TangentSpace I) b₀).coordChangeL ℝ
          (_root_.FiberBundle.trivializationAt E (TangentSpace I) α) b : E →L[ℝ] E)) U := by
    refine (continuousOn_coordChangeL_b₀_α (I := I) b₀ α).mono ?_
    intro b hb
    exact ⟨hU_sub_b₀ hb, hU_sub_α hb⟩
  have h_eq : _root_.Set.EqOn
      (fun b : M => chartTrivializationLinearMap (I := I) (M := M) α b)
      (fun b : M => ((_root_.FiberBundle.trivializationAt E (TangentSpace I) b₀).coordChangeL ℝ
        (_root_.FiberBundle.trivializationAt E (TangentSpace I) α) b : E →L[ℝ] E)) U := by
    intro b hb
    exact (coordChangeL_eq_chartJ_of_locality (I := I) (M := M) α
      (hU_sub_α hb) (hU_sub_b₀ hb) (hU_const b hb)).symm
  exact h_coord_cont.congr h_eq

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartJ_continuousOn_local
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartJ_continuousOn_local target :: scope.openDecls } }

omit [Module.Finite ℝ E] [InnerProductSpace ℝ E] [T2Space M] in
private lemma chartJinv_continuousOn_local
    (α b₀ : M)
    {U : Set M}
    (hU_sub_b₀ : U ⊆ (chartAt H b₀).source)
    (hU_sub_α : U ⊆ (chartAt H α).source)
    (hU_const : ∀ b ∈ U, chartAt H b = chartAt H b₀) :
    ContinuousOn (fun b : M => chartTrivializationLinearMapSymm (I := I) (M := M) α b) U := by
  have h_coord_cont :
      ContinuousOn
        (fun b : M => ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).coordChangeL ℝ
          (_root_.FiberBundle.trivializationAt E (TangentSpace I) b₀) b : E →L[ℝ] E)) U := by
    have h := continuousOn_coordChangeL_b₀_α (I := I) α b₀
    refine h.mono ?_
    intro b hb
    exact ⟨hU_sub_α hb, hU_sub_b₀ hb⟩
  have h_eq : _root_.Set.EqOn
      (fun b : M => chartTrivializationLinearMapSymm (I := I) (M := M) α b)
      (fun b : M => ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).coordChangeL ℝ
        (_root_.FiberBundle.trivializationAt E (TangentSpace I) b₀) b : E →L[ℝ] E)) U := by
    intro b hb
    exact (coordChangeL_eq_chartJinv_of_locality (I := I) (M := M) α
      (hU_sub_α hb) (hU_sub_b₀ hb) (hU_const b hb)).symm
  exact h_coord_cont.congr h_eq

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartJinv_continuousOn_local
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartJinv_continuousOn_local target :: scope.openDecls } }

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
