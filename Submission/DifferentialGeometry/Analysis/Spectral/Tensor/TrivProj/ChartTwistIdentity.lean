import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Components.Defs
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Inner.InnerBridge
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.InnerBounds.InnerLowerBound
import Submission.DifferentialGeometry.Tensor.RSTensor.Defs
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Bundle.SectionRegularity
import Submission.DifferentialGeometry.Tensor.Multilinear.Bundle.Defs
import Mathlib.Topology.VectorBundle.Hom
import Mathlib.Topology.VectorBundle.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.IsManifold _root_.ContinuousLinearMap _root_.Submission.ContinuousLinearMap _root_.Bundle.ContinuousLinearMap
open scoped _root_.Manifold _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.ContDiff _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Tensor
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Tensor.Tensor0SRiemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma tensor0S_trivialization_continuousLinearMapAt_apply
    (α : M) {b : M} (r : ℕ)
    (hb : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet)
    (T : Tensor0SSpace r I b) :
    (_root_.FiberBundle.trivializationAt (Tensor0SModel r ℝ E)
        (fun y : M => Tensor0SSpace r I y) α).continuousLinearMapAt ℝ b T =
      (Tensor0SSpace.toModel T).compContinuousLinearMap
        (fun _ : Fin r => chartTrivializationLinearMapSymm (I := I) (M := M) α b) := by
  have hbase : b ∈ (_root_.FiberBundle.trivializationAt (Tensor0SModel r ℝ E)
      (fun y : M => Tensor0SSpace r I y) α).baseSet := by
    change b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet
    exact hb
  have hcoe := (_root_.FiberBundle.trivializationAt (Tensor0SModel r ℝ E)
      (fun y : M => Tensor0SSpace r I y) α).coe_linearMapAt_of_mem (R := ℝ) hbase
  change ((_root_.FiberBundle.trivializationAt (Tensor0SModel r ℝ E)
      (fun y : M => Tensor0SSpace r I y) α).linearMapAt ℝ b) T = _
  rw [show ((_root_.FiberBundle.trivializationAt (Tensor0SModel r ℝ E)
      (fun y : M => Tensor0SSpace r I y) α).linearMapAt ℝ b) T =
        ((_root_.FiberBundle.trivializationAt (Tensor0SModel r ℝ E)
          (fun y : M => Tensor0SSpace r I y) α) ⟨b, T⟩).2 from
      congrFun hcoe T]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensor0S_trivialization_continuousLinearMapAt_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensor0S_trivialization_continuousLinearMapAt_apply target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma tensor0S_trivialization_symmL_apply
    (α : M) {b : M} (r : ℕ)
    (hb : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet)
    (V : Tensor0SModel r ℝ E) :
    (_root_.FiberBundle.trivializationAt (Tensor0SModel r ℝ E)
        (fun y : M => Tensor0SSpace r I y) α).symmL ℝ b V =
      Tensor0SSpace.ofModel
        (V.compContinuousLinearMap
          (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b)) := by
  have hbase : b ∈ (_root_.FiberBundle.trivializationAt (Tensor0SModel r ℝ E)
      (fun y : M => Tensor0SSpace r I y) α).baseSet := by
    change b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet
    exact hb
  have h := _root_.Submission.Pretrivialization.continuousMultilinearMap_symm_apply_of_mem
    (𝕜 := ℝ) (s := r) (F := E) (E := (TangentSpace I : M → Type _))
    (e := _root_.FiberBundle.trivializationAt E (TangentSpace I) α) (b := b) hb V
  rw [(_root_.FiberBundle.trivializationAt (Tensor0SModel r ℝ E)
      (fun y : M => Tensor0SSpace r I y) α).symmL_apply
        (R := ℝ) hbase V]
  change (_root_.FiberBundle.trivializationAt (Tensor0SModel r ℝ E)
      (fun y : M => Tensor0SSpace r I y) α).symm b V = _
  rw [show (_root_.FiberBundle.trivializationAt (Tensor0SModel r ℝ E)
      (fun y : M => Tensor0SSpace r I y) α).symm b V =
        ((Pretrivialization.continuousMultilinearMap (𝕜 := ℝ) (s := r)
          (F := E) (E := (TangentSpace I : M → Type _))
          (_root_.FiberBundle.trivializationAt E (TangentSpace I) α)).symm b V) from rfl]
  rw [h]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensor0S_trivialization_symmL_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensor0S_trivialization_symmL_apply target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem tensorTrivProj_eq_chartRSTwistInv_toFun
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) {b : M}
    (hb : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet) :
    tensorTrivProj (I := I) (M := M) g r s S α b =
      chartRSTwistInv (I := I) (M := M) α b r s (S.toFun b) := by
  classical
  refine ContinuousLinearMap.ext ?_
  intro α'
  unfold tensorTrivProj
  have hbaseHom : b ∈ (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).baseSet := by
    change b ∈ (_root_.FiberBundle.trivializationAt (Tensor0SModel r ℝ E)
        (fun y : M => Tensor0SSpace r I y) α).baseSet ∩
      (_root_.FiberBundle.trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) α).baseSet
    refine ⟨?_, ?_⟩
    · change b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet
      exact hb
    · change b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet
      exact hb
  have hcoeRS := (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).coe_linearMapAt_of_mem
    (R := ℝ) hbaseHom
  change ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).linearMapAt ℝ b (S.toSection b)) α' = _
  have hval :
      ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).linearMapAt ℝ b (S.toSection b)) =
      ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α) ⟨b, S.toSection b⟩).2 :=
    congrFun hcoeRS (S.toSection b)
  rw [hval]
  have hHom :
      (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α) ⟨b, S.toSection b⟩
        = ⟨b, ((_root_.FiberBundle.trivializationAt (Tensor0SModel s ℝ E)
            (fun y : M => Tensor0SSpace s I y) α).continuousLinearMapAt ℝ b
            : Tensor0SSpace s I b →L[ℝ] Tensor0SModel s ℝ E).comp
              ((S.toSection b).comp
                ((_root_.FiberBundle.trivializationAt (Tensor0SModel r ℝ E)
                  (fun y : M => Tensor0SSpace r I y) α).symmL ℝ b
                  : Tensor0SModel r ℝ E →L[ℝ] Tensor0SSpace r I b))⟩ := rfl
  rw [hHom]
  change (((_root_.FiberBundle.trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) α).continuousLinearMapAt ℝ b
        : Tensor0SSpace s I b →L[ℝ] Tensor0SModel s ℝ E).comp
      ((S.toSection b).comp
        ((_root_.FiberBundle.trivializationAt (Tensor0SModel r ℝ E)
          (fun y : M => Tensor0SSpace r I y) α).symmL ℝ b
          : Tensor0SModel r ℝ E →L[ℝ] Tensor0SSpace r I b))) α' = _
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  rw [tensor0S_trivialization_symmL_apply (I := I) (M := M) α r hb α']
  rw [tensor0S_trivialization_continuousLinearMapAt_apply (I := I) (M := M) α s hb
    ((S.toSection b) (Tensor0SSpace.ofModel
      (α'.compContinuousLinearMap
        (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b))))]
  rw [chartRSTwistInv_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorTrivProj_eq_chartRSTwistInv_toFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorTrivProj_eq_chartRSTwistInv_toFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorTrivProj_eq_chartRSTwistInv_toFun ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorTrivProj_eq_chartRSTwistInv_toFun

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem chartRSTwist_tensorTrivProj_eq_toFun
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) {b : M}
    (hb : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet) :
    chartRSTwist (I := I) (M := M) α b r s
        (tensorTrivProj (I := I) (M := M) g r s S α b) =
      S.toFun b := by
  classical
  refine ContinuousLinearMap.ext ?_
  intro α'
  rw [tensorTrivProj_eq_chartRSTwistInv_toFun (I := I) (M := M) g r s α S hb]
  rw [chartRSTwist_apply, chartRSTwistInv_apply]
  have hinner :
      (α'.compContinuousLinearMap
          (fun _ : Fin r => chartTrivializationLinearMapSymm (I := I) (M := M) α
            b)).compContinuousLinearMap
        (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b) = α' := by
    refine ContinuousMultilinearMap.ext ?_
    intro v
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
        ContinuousMultilinearMap.compContinuousLinearMap_apply]
    congr 1
    funext k
    exact chartJinv_chartJ_self (I := I) (M := M) α hb (v k)
  rw [hinner]
  refine ContinuousMultilinearMap.ext ?_
  intro w
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  funext k
  exact chartJinv_chartJ_self (I := I) (M := M) α hb (w k)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartRSTwist_tensorTrivProj_eq_toFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartRSTwist_tensorTrivProj_eq_toFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartRSTwist_tensorTrivProj_eq_toFun ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartRSTwist_tensorTrivProj_eq_toFun

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel
    (r s : ℕ) (α : M) {b : M} (hb : b ∈ (chartAt H α).source)
    (T : TensorRSSpace r s I b) :
    (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b T =
      chartRSTwistInv (I := I) (M := M) α b r s (TensorRSSpace.toModel T) := by
  classical
  have hb' : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := hb
  refine ContinuousLinearMap.ext ?_
  intro α'
  have hbaseHom : b ∈ (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).baseSet := by
    change b ∈ (_root_.FiberBundle.trivializationAt (Tensor0SModel r ℝ E)
        (fun y : M => Tensor0SSpace r I y) α).baseSet ∩
      (_root_.FiberBundle.trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) α).baseSet
    refine ⟨?_, ?_⟩
    · change b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet
      exact hb'
    · change b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet
      exact hb'
  have hcoeRS := (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).coe_linearMapAt_of_mem
    (R := ℝ) hbaseHom
  change ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).linearMapAt ℝ b T) α' = _
  have hval :
      ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).linearMapAt ℝ b T) =
      ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α) ⟨b, T⟩).2 :=
    congrFun hcoeRS T
  rw [hval]
  have hHom :
      (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α) ⟨b, T⟩
        = ⟨b, ((_root_.FiberBundle.trivializationAt (Tensor0SModel s ℝ E)
            (fun y : M => Tensor0SSpace s I y) α).continuousLinearMapAt ℝ b
            : Tensor0SSpace s I b →L[ℝ] Tensor0SModel s ℝ E).comp
              (T.comp
                ((_root_.FiberBundle.trivializationAt (Tensor0SModel r ℝ E)
                  (fun y : M => Tensor0SSpace r I y) α).symmL ℝ b
                  : Tensor0SModel r ℝ E →L[ℝ] Tensor0SSpace r I b))⟩ := rfl
  rw [hHom]
  change (((_root_.FiberBundle.trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) α).continuousLinearMapAt ℝ b
        : Tensor0SSpace s I b →L[ℝ] Tensor0SModel s ℝ E).comp
      (T.comp
        ((_root_.FiberBundle.trivializationAt (Tensor0SModel r ℝ E)
          (fun y : M => Tensor0SSpace r I y) α).symmL ℝ b
          : Tensor0SModel r ℝ E →L[ℝ] Tensor0SSpace r I b))) α' = _
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  rw [tensor0S_trivialization_symmL_apply (I := I) (M := M) α r hb' α']
  rw [tensor0S_trivialization_continuousLinearMapAt_apply (I := I) (M := M) α s hb'
    (T (Tensor0SSpace.ofModel
      (α'.compContinuousLinearMap
        (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b))))]
  rw [chartRSTwistInv_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
