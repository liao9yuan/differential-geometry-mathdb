import Submission.DifferentialGeometry.Tensor.RSTensor.Defs
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Tangent.Riemannian
import Submission.DifferentialGeometry.Geometry.Metric.PointwiseInner.Defs
import Submission.DifferentialGeometry.Geometry.Metric.PointwiseInner.Algebra
import Submission.DifferentialGeometry.Geometry.Metric.PointwiseInner.DualMetric
import Submission.DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Bundle.InnerProduct
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Fiber.PositiveDefiniteBilinearBoundedUnitBall
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Chart.Inner
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Chart.ContinuousLinearMap
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.InnerBridge
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Topology.VectorBundle.Riemannian
import Mathlib.Analysis.LocallyConvex.Bounded
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.IsManifold _root_.ContinuousLinearMap _root_.Submission.ContinuousLinearMap _root_.Bundle.ContinuousLinearMap _root_.Bornology
open scoped _root_.Manifold _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.ContDiff _root_.BigOperators _root_.Matrix

namespace DifferentialGeometry
namespace Tensor
namespace Tensor0SRiemannian

open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable {n : ℕ}

private local instance tensor0SModelNormedSpace_local {s : ℕ} :
    NormedSpace ℝ (Tensor0SModel s ℝ E) :=
  Tensor0SBundle.tensor0SModelNormedSpace s

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor.Tensor0SRiemannian.tensor0SModelNormedSpace_local
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor.Tensor0SRiemannian.tensor0SModelNormedSpace_local target :: scope.openDecls } }

private local instance tensor0SModelNormedAddCommGroup_local {s : ℕ} :
    NormedAddCommGroup (Tensor0SModel s ℝ E) := inferInstance

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor.Tensor0SRiemannian.tensor0SModelNormedAddCommGroup_local
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor.Tensor0SRiemannian.tensor0SModelNormedAddCommGroup_local target :: scope.openDecls } }

lemma chartTensorInnerPointwise_0s_continuousOn_smooth_args
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∀ (s : ℕ)
    (T S : M → ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ)
    (_hT : ContinuousOn T (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet)
    (_hS : ContinuousOn S (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet),
      ContinuousOn (fun b : M =>
          chartTensorInnerPointwise0s (I := I) (M := M) s g α b (T b) (S b))
        (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
  intro s
  induction s with
  | zero =>
      intro T S hT hS
      have heval0 : Continuous
          (fun T : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => E) ℝ =>
            T (fun i => Fin.elim0 i)) :=
        continuous_id.eval_const _
      have heq : (fun b : M =>
          chartTensorInnerPointwise0s (I := I) (M := M) 0 g α b (T b) (S b)) =
          fun b : M =>
            ((T b) (fun i => Fin.elim0 i)) * ((S b) (fun i => Fin.elim0 i)) := by
        funext b
        rw [chartTensorInnerPointwise_0s_zero]
      rw [heq]
      exact (heval0.comp_continuousOn hT).mul (heval0.comp_continuousOn hS)
  | succ s ih =>
      intro T S hT hS
      have heq : (fun b : M =>
          chartTensorInnerPointwise0s (I := I) (M := M) (s + 1) g α b (T b) (S b)) =
          fun b : M =>
            ∑ i : Fin (Module.finrank ℝ E),
              ∑ j : Fin (Module.finrank ℝ E),
                (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix g α b)⁻¹ i j *
                  chartTensorInnerPointwise0s (I := I) (M := M) s g α b
                    ((T b).curryLeft ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i))
                    ((S b).curryLeft ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j)) := by
        funext b
        rw [chartTensorInnerPointwise_0s_succ]
      rw [heq]
      refine continuousOn_finsetSum _ (fun i _ => ?_)
      refine continuousOn_finsetSum _ (fun j _ => ?_)
      refine ContinuousOn.mul ?_ ?_
      · exact (chartGramMatrix_inv_entry_contMDiffOn (I := I) g α i j).continuousOn
      · have hT_curry : ContinuousOn
            (fun b : M => (T b).curryLeft ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i))
            (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
          have hheq : (fun b : M => (T b).curryLeft ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)) =
              fun b : M => curryLeftAtCLM (E := E) s ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) (T b) := by
            funext b
            rw [curryLeftAtCLM_apply]
          rw [hheq]
          exact (curryLeftAtCLM (E := E) s ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)).continuous.comp_continuousOn hT
        have hS_curry : ContinuousOn
            (fun b : M => (S b).curryLeft ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j))
            (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
          have hheq : (fun b : M => (S b).curryLeft ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j)) =
              fun b : M => curryLeftAtCLM (E := E) s ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j) (S b) := by
            funext b
            rw [curryLeftAtCLM_apply]
          rw [hheq]
          exact (curryLeftAtCLM (E := E) s ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j)).continuous.comp_continuousOn hS
        exact ih _ _ hT_curry hS_curry

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Tensor0SRiemannian.chartTensorInnerPointwise_0s_continuousOn_smooth_args then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Tensor0SRiemannian.chartTensorInnerPointwise_0s_continuousOn_smooth_args"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Tensor0SRiemannian.chartTensorInnerPointwise_0s_continuousOn_smooth_args ``Submission.DifferentialGeometry.Tensor.Tensor0SRiemannian.chartTensorInnerPointwise_0s_continuousOn_smooth_args

lemma chartTensorInnerPointwise_0s_contMDiffOn_smooth_args
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∀ (s : ℕ)
    (T S : M → ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ)
    (_hT : ∀ φ : Fin s → Fin (Module.finrank ℝ E),
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun b : M => (T b) (fun k : Fin s => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (φ k)))
        (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet)
    (_hS : ∀ φ : Fin s → Fin (Module.finrank ℝ E),
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun b : M => (S b) (fun k : Fin s => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (φ k)))
        (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet),
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun b : M =>
          chartTensorInnerPointwise0s (I := I) (M := M) s g α b (T b) (S b))
        (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
  intro s
  induction s with
  | zero =>
      intro T S hT hS
      have heq : (fun b : M =>
          chartTensorInnerPointwise0s (I := I) (M := M) 0 g α b (T b) (S b)) =
          fun b : M =>
            ((T b) (fun i => Fin.elim0 i)) * ((S b) (fun i => Fin.elim0 i)) := by
        funext b
        rw [chartTensorInnerPointwise_0s_zero]
      rw [heq]
      have hT0 := hT (fun i : Fin 0 => Fin.elim0 i)
      have hS0 := hS (fun i : Fin 0 => Fin.elim0 i)
      have hempty :
          (fun k : Fin 0 => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) ((fun i : Fin 0 => Fin.elim0 i) k))
            = (fun i : Fin 0 => (Fin.elim0 i : E)) := by
        funext i
        exact Fin.elim0 i
      have hT_smooth :
          ContMDiffOn I 𝓘(ℝ) ∞
            (fun b : M => (T b) (fun i => Fin.elim0 i))
            (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
        have : (fun b : M => (T b) (fun i : Fin 0 => Fin.elim0 i)) =
            (fun b : M => (T b)
              (fun k : Fin 0 =>
                (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) ((fun i : Fin 0 => Fin.elim0 i) k))) := by
          funext b
          congr 1
          rw [hempty]
        rw [this]
        exact hT0
      have hS_smooth :
          ContMDiffOn I 𝓘(ℝ) ∞
            (fun b : M => (S b) (fun i => Fin.elim0 i))
            (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
        have : (fun b : M => (S b) (fun i : Fin 0 => Fin.elim0 i)) =
            (fun b : M => (S b)
              (fun k : Fin 0 =>
                (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) ((fun i : Fin 0 => Fin.elim0 i) k))) := by
          funext b
          congr 1
          rw [hempty]
        rw [this]
        exact hS0
      exact hT_smooth.mul hS_smooth
  | succ s ih =>
      intro T S hT hS
      have heq : (fun b : M =>
          chartTensorInnerPointwise0s (I := I) (M := M) (s + 1) g α b (T b) (S b)) =
          fun b : M =>
            ∑ i : Fin (Module.finrank ℝ E),
              ∑ j : Fin (Module.finrank ℝ E),
                (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix g α b)⁻¹ i j *
                  chartTensorInnerPointwise0s (I := I) (M := M) s g α b
                    ((T b).curryLeft ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i))
                    ((S b).curryLeft ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j)) := by
        funext b
        rw [chartTensorInnerPointwise_0s_succ]
      rw [heq]
      refine contMDiffOn_finsetSum (fun i _ => ?_)
      refine contMDiffOn_finsetSum (fun j _ => ?_)
      refine ContMDiffOn.mul ?_ ?_
      · exact chartGramMatrix_inv_entry_contMDiffOn (I := I) g α i j
      · refine ih
            (fun b : M => (T b).curryLeft ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i))
            (fun b : M => (S b).curryLeft ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j))
            ?_ ?_
        · intro ψ
          set ψ' : Fin (s + 1) → Fin (Module.finrank ℝ E) :=
            Fin.cons (α := fun _ => Fin (Module.finrank ℝ E)) i ψ with hψ'
          have hψ'_zero : ψ' 0 = i := by
            simp [hψ']
          have hψ'_succ : ∀ k : Fin s, ψ' k.succ = ψ k := by
            intro k
            simp [hψ']
          have heq' :
              (fun b : M => ((T b).curryLeft ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i))
                  (fun k : Fin s => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (ψ k)))
                = fun b : M =>
                    (T b) (fun k : Fin (s + 1) =>
                      (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (ψ' k)) := by
            funext b
            rw [ContinuousMultilinearMap.curryLeft_apply]
            congr 1
            funext k
            refine Fin.cases ?_ ?_ k
            · rw [hψ'_zero]
              simp
            · intro k'
              rw [hψ'_succ k']
              simp
          rw [heq']
          exact hT ψ'
        · intro ψ
          set ψ' : Fin (s + 1) → Fin (Module.finrank ℝ E) :=
            Fin.cons (α := fun _ => Fin (Module.finrank ℝ E)) j ψ with hψ'
          have hψ'_zero : ψ' 0 = j := by
            simp [hψ']
          have hψ'_succ : ∀ k : Fin s, ψ' k.succ = ψ k := by
            intro k
            simp [hψ']
          have heq' :
              (fun b : M => ((S b).curryLeft ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j))
                  (fun k : Fin s => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (ψ k)))
                = fun b : M =>
                    (S b) (fun k : Fin (s + 1) =>
                      (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (ψ' k)) := by
            funext b
            rw [ContinuousMultilinearMap.curryLeft_apply]
            congr 1
            funext k
            refine Fin.cases ?_ ?_ k
            · rw [hψ'_zero]; simp
            · intro k'
              rw [hψ'_succ k']; simp
          rw [heq']
          exact hS ψ'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Tensor0SRiemannian.chartTensorInnerPointwise_0s_contMDiffOn_smooth_args then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Tensor0SRiemannian.chartTensorInnerPointwise_0s_contMDiffOn_smooth_args"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Tensor0SRiemannian.chartTensorInnerPointwise_0s_contMDiffOn_smooth_args ``Submission.DifferentialGeometry.Tensor.Tensor0SRiemannian.chartTensorInnerPointwise_0s_contMDiffOn_smooth_args

theorem chartLocal_continuous_inner_of_smooth_sections
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (T S : ∀ y : M, Tensor0SSpace s I y) (α : M)
    (hTα : ContinuousOn
      (fun b : M => (Tensor0SBundle.Tensor0SSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b)
          (T b)).compContinuousLinearMap
          (fun _ : Fin s => chartTrivializationLinearMapSymm (I := I) (M := M) α b))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet)
    (hSα : ContinuousOn
      (fun b : M => (Tensor0SBundle.Tensor0SSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b)
          (S b)).compContinuousLinearMap
          (fun _ : Fin s => chartTrivializationLinearMapSymm (I := I) (M := M) α b))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet) :
    ContinuousOn
      (fun b : M =>
        covariantTensorInnerPointwise (I := I) (M := M) s g b
          (Tensor0SBundle.Tensor0SSpace.toModel
            (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b) (T b))
          (Tensor0SBundle.Tensor0SSpace.toModel
            (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b) (S b)))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
  have hbridge : ∀ b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet,
      covariantTensorInnerPointwise (I := I) (M := M) s g b
        (Tensor0SBundle.Tensor0SSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b) (T b))
        (Tensor0SBundle.Tensor0SSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b) (S b)) =
      chartTensorInnerPointwise0s (I := I) (M := M) s g α b
        ((Tensor0SBundle.Tensor0SSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b)
          (T b)).compContinuousLinearMap
          (fun _ : Fin s => chartTrivializationLinearMapSymm (I := I) (M := M) α b))
        ((Tensor0SBundle.Tensor0SSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b)
          (S b)).compContinuousLinearMap
          (fun _ : Fin s => chartTrivializationLinearMapSymm (I := I) (M := M) α b)) := by
    intro b hb
    exact tensorInnerPointwise_0s_bridge_identity (I := I) (M := M) g α s hb _ _
  refine ContinuousOn.congr ?_ hbridge
  exact chartTensorInnerPointwise_0s_continuousOn_smooth_args
    (I := I) (M := M) g α s _ _ hTα hSα

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Tensor0SRiemannian.chartLocal_continuous_inner_of_smooth_sections then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Tensor0SRiemannian.chartLocal_continuous_inner_of_smooth_sections"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Tensor0SRiemannian.chartLocal_continuous_inner_of_smooth_sections ``Submission.DifferentialGeometry.Tensor.Tensor0SRiemannian.chartLocal_continuous_inner_of_smooth_sections

theorem _root_.Submission.Tensor0SBundle.continuous_inner_of_smooth_sections
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (T S : ∀ y : M, Tensor0SSpace s I y)
    (hT_charts : ∀ α : M, ContinuousOn
      (fun b : M => (Tensor0SBundle.Tensor0SSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b)
          (T b)).compContinuousLinearMap
          (fun _ : Fin s => chartTrivializationLinearMapSymm (I := I) (M := M) α b))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet)
    (hS_charts : ∀ α : M, ContinuousOn
      (fun b : M => (Tensor0SBundle.Tensor0SSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b)
          (S b)).compContinuousLinearMap
          (fun _ : Fin s => chartTrivializationLinearMapSymm (I := I) (M := M) α b))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet) :
    Continuous (fun b : M =>
      covariantTensorInnerPointwise (I := I) (M := M) s g b
        (Tensor0SBundle.Tensor0SSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b) (T b))
        (Tensor0SBundle.Tensor0SSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b) (S b))) := by
  rw [continuous_iff_continuousAt]
  intro b
  have hb_base : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) b).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt _ _ b
  have hOpen : IsOpen (_root_.FiberBundle.trivializationAt E (TangentSpace I) b).baseSet :=
    (_root_.FiberBundle.trivializationAt E (TangentSpace I) b).open_baseSet
  have hLocal := chartLocal_continuous_inner_of_smooth_sections
    (I := I) (M := M) g s T S b (hT_charts b) (hS_charts b)
  exact hLocal.continuousAt (hOpen.mem_nhds hb_base)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.Tensor0SBundle
  let env ← Lean.getEnv
  if env.contains `Tensor0SBundle.continuous_inner_of_smooth_sections then
    throwError "Refusing to shadow existing declaration Tensor0SBundle.continuous_inner_of_smooth_sections"
  Lean.modifyEnv fun env => Lean.addAlias env `Tensor0SBundle.continuous_inner_of_smooth_sections ``Submission.Tensor0SBundle.continuous_inner_of_smooth_sections

end Tensor0SRiemannian
end Tensor
end DifferentialGeometry

end
