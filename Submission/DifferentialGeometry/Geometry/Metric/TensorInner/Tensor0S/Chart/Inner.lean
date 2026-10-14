import Submission.DifferentialGeometry.Tensor.RSTensor.Defs
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Tangent.Riemannian
import Submission.DifferentialGeometry.Geometry.Metric.PointwiseInner.Defs
import Submission.DifferentialGeometry.Geometry.Metric.PointwiseInner.Algebra
import Submission.DifferentialGeometry.Geometry.Metric.PointwiseInner.DualMetric
import Submission.DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram
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
import Submission.DifferentialGeometry.Geometry.Operator.Gradient.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Operator


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.IsManifold _root_.ContinuousLinearMap _root_.Submission.ContinuousLinearMap _root_.Bundle.ContinuousLinearMap _root_.Bornology
open scoped _root_.Manifold _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.ContDiff _root_.BigOperators _root_.Matrix

namespace DifferentialGeometry
namespace Tensor
namespace Tensor0SRiemannian

open _root_.Submission.DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private lemma chartGramMatrix_adjugate_entry_contMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M => (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix g α b).adjugate i j)
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  have hexp :
      (fun b : M => (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix g α b).adjugate i j)
        = (fun b : M =>
            ((DifferentialGeometry.Tensor.Coordinates.chartGramMatrix g α b).updateRow j (Pi.single i 1)).det) := by
    funext b
    rw [Matrix.adjugate_apply]
  rw [hexp]
  have hexp2 :
      (fun b : M =>
          ((DifferentialGeometry.Tensor.Coordinates.chartGramMatrix g α b).updateRow j (Pi.single i 1)).det)
        = (fun b : M =>
            ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
              (Equiv.Perm.sign σ : ℝ) *
                ∏ k,
                  ((DifferentialGeometry.Tensor.Coordinates.chartGramMatrix g α b).updateRow j (Pi.single i 1))
                    (σ k) k) := by
    funext b
    rw [Matrix.det_apply]
    simp [Units.smul_def]
  rw [hexp2]
  refine contMDiffOn_finsetSum (fun σ _ => ?_)
  refine ContMDiffOn.mul (contMDiffOn_const) ?_
  refine contMDiffOn_finsetProd (fun k _ => ?_)
  by_cases hσkj : σ k = j
  · have heq :
        (fun b : M =>
            ((DifferentialGeometry.Tensor.Coordinates.chartGramMatrix g α b).updateRow j (Pi.single i 1)) (σ k) k)
          = (fun _ : M => (Pi.single i 1 : Fin (Module.finrank ℝ E) → ℝ) k) := by
      funext b
      rw [hσkj, Matrix.updateRow_self]
    rw [heq]
    exact contMDiffOn_const
  · have heq :
        (fun b : M =>
            ((DifferentialGeometry.Tensor.Coordinates.chartGramMatrix g α b).updateRow j (Pi.single i 1)) (σ k) k)
          = (fun b : M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix g α b (σ k) k) := by
      funext b
      rw [Matrix.updateRow_ne hσkj]
    rw [heq]
    exact DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_entry_contMDiffOn (I := I) g α (σ k) k

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor.Tensor0SRiemannian.chartGramMatrix_adjugate_entry_contMDiffOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor.Tensor0SRiemannian.chartGramMatrix_adjugate_entry_contMDiffOn target :: scope.openDecls } }

lemma chartGramMatrix_inv_entry_contMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M => (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix g α b)⁻¹ i j)
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
  have hexp :
      (fun b : M => (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix g α b)⁻¹ i j)
        = (fun b : M => (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix g α b).det⁻¹ *
              (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix g α b).adjugate i j) := by
    funext b
    rw [Matrix.inv_def]
    simp [Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  rw [hexp]
  intro b hb
  have hdet := DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_det_contMDiffOn (I := I) g α b hb
  have hadj := chartGramMatrix_adjugate_entry_contMDiffOn (I := I) g α i j b hb
  have hpos : 0 < (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix g α b).det :=
    DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_det_pos (I := I) g α hb
  have hpos_ne : (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix g α b).det ≠ 0 := ne_of_gt hpos
  have hinv : ContMDiffWithinAt I 𝓘(ℝ) ∞
      (fun b' : M => (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix g α b').det⁻¹)
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet b :=
    ContMDiffWithinAt.inv₀ hdet hpos_ne
  exact hinv.mul hadj

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Tensor0SRiemannian.chartGramMatrix_inv_entry_contMDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Tensor0SRiemannian.chartGramMatrix_inv_entry_contMDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Tensor0SRiemannian.chartGramMatrix_inv_entry_contMDiffOn ``Submission.DifferentialGeometry.Tensor.Tensor0SRiemannian.chartGramMatrix_inv_entry_contMDiffOn

noncomputable def chartTensorInnerPointwise0s :
    (s : ℕ) → SmoothRiemannianMetric I M → (α : M) → (b : M) →
      Tensor0SModel s ℝ E →
      Tensor0SModel s ℝ E → ℝ
  | 0, _g, _α, _b, S, T =>
      S (fun i => Fin.elim0 i) * T (fun i => Fin.elim0 i)
  | s + 1, g, α, b, S, T =>
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix g α b)⁻¹ i j *
          chartTensorInnerPointwise0s s g α b
            (S.curryLeft ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i))
            (T.curryLeft ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Tensor0SRiemannian.chartTensorInnerPointwise0s then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Tensor0SRiemannian.chartTensorInnerPointwise0s"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Tensor0SRiemannian.chartTensorInnerPointwise0s ``Submission.DifferentialGeometry.Tensor.Tensor0SRiemannian.chartTensorInnerPointwise0s

lemma chartTensorInnerPointwise_0s_zero
    (g : SmoothRiemannianMetric I M) (α b : M)
    (S T : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => E) ℝ) :
    chartTensorInnerPointwise0s (I := I) (M := M) 0 g α b S T =
      S (fun i => Fin.elim0 i) * T (fun i => Fin.elim0 i) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Tensor0SRiemannian.chartTensorInnerPointwise_0s_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Tensor0SRiemannian.chartTensorInnerPointwise_0s_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Tensor0SRiemannian.chartTensorInnerPointwise_0s_zero ``Submission.DifferentialGeometry.Tensor.Tensor0SRiemannian.chartTensorInnerPointwise_0s_zero

lemma chartTensorInnerPointwise_0s_succ
    (g : SmoothRiemannianMetric I M) (α b : M) (s : ℕ)
    (S T : ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => E) ℝ) :
    chartTensorInnerPointwise0s (I := I) (M := M) (s + 1) g α b S T =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix g α b)⁻¹ i j *
          chartTensorInnerPointwise0s (I := I) (M := M) s g α b
            (S.curryLeft ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i))
            (T.curryLeft ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Tensor0SRiemannian.chartTensorInnerPointwise_0s_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Tensor0SRiemannian.chartTensorInnerPointwise_0s_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Tensor0SRiemannian.chartTensorInnerPointwise_0s_succ ``Submission.DifferentialGeometry.Tensor.Tensor0SRiemannian.chartTensorInnerPointwise_0s_succ

lemma chartTensorInnerPointwise_0s_contMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∀ (s : ℕ) (S T : Tensor0SModel s ℝ E),
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun b : M =>
          chartTensorInnerPointwise0s (I := I) (M := M) s g α b S T)
        (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
  intro s
  induction s with
  | zero =>
      intro S T
      have heq :
          (fun b : M =>
              chartTensorInnerPointwise0s (I := I) (M := M) 0 g α b S T)
            = fun _ : M =>
              S (fun i => Fin.elim0 i) * T (fun i => Fin.elim0 i) := by
        funext b
        rw [chartTensorInnerPointwise_0s_zero]
      rw [heq]
      exact contMDiffOn_const
  | succ s ih =>
      intro S T
      have heq :
          (fun b : M =>
              chartTensorInnerPointwise0s (I := I) (M := M) (s + 1) g α b S T)
            = fun b : M =>
              ∑ i : Fin (Module.finrank ℝ E),
                ∑ j : Fin (Module.finrank ℝ E),
                  (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix g α b)⁻¹ i j *
                    chartTensorInnerPointwise0s (I := I) (M := M) s g α b
                      (S.curryLeft ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i))
                      (T.curryLeft ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j)) := by
        funext b
        rw [chartTensorInnerPointwise_0s_succ]
      rw [heq]
      refine contMDiffOn_finsetSum (fun i _ => ?_)
      refine contMDiffOn_finsetSum (fun j _ => ?_)
      refine ContMDiffOn.mul ?_ ?_
      · exact chartGramMatrix_inv_entry_contMDiffOn (I := I) g α i j
      · exact ih
          (S.curryLeft ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i))
          (T.curryLeft ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Tensor0SRiemannian.chartTensorInnerPointwise_0s_contMDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Tensor0SRiemannian.chartTensorInnerPointwise_0s_contMDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Tensor0SRiemannian.chartTensorInnerPointwise_0s_contMDiffOn ``Submission.DifferentialGeometry.Tensor.Tensor0SRiemannian.chartTensorInnerPointwise_0s_contMDiffOn

lemma chartTensorInnerPointwise_0s_add_left
    (g : SmoothRiemannianMetric I M) (α b : M) (s : ℕ)
    (S₁ S₂ T : Tensor0SModel s ℝ E) :
    chartTensorInnerPointwise0s (I := I) (M := M) s g α b (S₁ + S₂) T =
      chartTensorInnerPointwise0s (I := I) (M := M) s g α b S₁ T +
        chartTensorInnerPointwise0s (I := I) (M := M) s g α b S₂ T := by
  induction s with
  | zero =>
      change (S₁ + S₂) _ * T _ = S₁ _ * T _ + S₂ _ * T _
      rw [add_apply]; ring
  | succ s ih =>
      rw [chartTensorInnerPointwise_0s_succ,
          chartTensorInnerPointwise_0s_succ,
          chartTensorInnerPointwise_0s_succ]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro j _
      have hcurry :
          (S₁ + S₂).curryLeft ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) =
            S₁.curryLeft ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) +
              S₂.curryLeft ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) := by
        ext m
        simp [ContinuousMultilinearMap.curryLeft_apply,
              add_apply]
      rw [hcurry, ih]
      ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Tensor0SRiemannian.chartTensorInnerPointwise_0s_add_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Tensor0SRiemannian.chartTensorInnerPointwise_0s_add_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Tensor0SRiemannian.chartTensorInnerPointwise_0s_add_left ``Submission.DifferentialGeometry.Tensor.Tensor0SRiemannian.chartTensorInnerPointwise_0s_add_left

lemma chartTensorInnerPointwise_0s_smul_left
    (g : SmoothRiemannianMetric I M) (α b : M) (s : ℕ)
    (c : ℝ) (S T : Tensor0SModel s ℝ E) :
    chartTensorInnerPointwise0s (I := I) (M := M) s g α b (c • S) T =
      c * chartTensorInnerPointwise0s (I := I) (M := M) s g α b S T := by
  induction s with
  | zero =>
      change (c • S) _ * T _ = c * (S _ * T _)
      rw [smul_apply, smul_eq_mul]; ring
  | succ s ih =>
      rw [chartTensorInnerPointwise_0s_succ,
          chartTensorInnerPointwise_0s_succ,
          Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      have hcurry :
          (c • S).curryLeft ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) =
            c • S.curryLeft ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) := by
        ext m
        simp [ContinuousMultilinearMap.curryLeft_apply,
              smul_apply]
      rw [hcurry, ih]
      ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Tensor0SRiemannian.chartTensorInnerPointwise_0s_smul_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Tensor0SRiemannian.chartTensorInnerPointwise_0s_smul_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Tensor0SRiemannian.chartTensorInnerPointwise_0s_smul_left ``Submission.DifferentialGeometry.Tensor.Tensor0SRiemannian.chartTensorInnerPointwise_0s_smul_left

lemma chartTensorInnerPointwise_0s_add_right
    (g : SmoothRiemannianMetric I M) (α b : M) (s : ℕ)
    (S T₁ T₂ : Tensor0SModel s ℝ E) :
    chartTensorInnerPointwise0s (I := I) (M := M) s g α b S (T₁ + T₂) =
      chartTensorInnerPointwise0s (I := I) (M := M) s g α b S T₁ +
        chartTensorInnerPointwise0s (I := I) (M := M) s g α b S T₂ := by
  induction s with
  | zero =>
      change S _ * (T₁ + T₂) _ = S _ * T₁ _ + S _ * T₂ _
      rw [add_apply]; ring
  | succ s ih =>
      rw [chartTensorInnerPointwise_0s_succ,
          chartTensorInnerPointwise_0s_succ,
          chartTensorInnerPointwise_0s_succ]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro j _
      have hcurry :
          (T₁ + T₂).curryLeft ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j) =
            T₁.curryLeft ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j) +
              T₂.curryLeft ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j) := by
        ext m
        simp [ContinuousMultilinearMap.curryLeft_apply,
              add_apply]
      rw [hcurry, ih]
      ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Tensor0SRiemannian.chartTensorInnerPointwise_0s_add_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Tensor0SRiemannian.chartTensorInnerPointwise_0s_add_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Tensor0SRiemannian.chartTensorInnerPointwise_0s_add_right ``Submission.DifferentialGeometry.Tensor.Tensor0SRiemannian.chartTensorInnerPointwise_0s_add_right

lemma chartTensorInnerPointwise_0s_smul_right
    (g : SmoothRiemannianMetric I M) (α b : M) (s : ℕ)
    (c : ℝ) (S T : Tensor0SModel s ℝ E) :
    chartTensorInnerPointwise0s (I := I) (M := M) s g α b S (c • T) =
      c * chartTensorInnerPointwise0s (I := I) (M := M) s g α b S T := by
  induction s with
  | zero =>
      change S _ * (c • T) _ = c * (S _ * T _)
      rw [smul_apply, smul_eq_mul]; ring
  | succ s ih =>
      rw [chartTensorInnerPointwise_0s_succ,
          chartTensorInnerPointwise_0s_succ,
          Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      have hcurry :
          (c • T).curryLeft ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j) =
            c • T.curryLeft ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j) := by
        ext m
        simp [ContinuousMultilinearMap.curryLeft_apply,
              smul_apply]
      rw [hcurry, ih]
      ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Tensor0SRiemannian.chartTensorInnerPointwise_0s_smul_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Tensor0SRiemannian.chartTensorInnerPointwise_0s_smul_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Tensor0SRiemannian.chartTensorInnerPointwise_0s_smul_right ``Submission.DifferentialGeometry.Tensor.Tensor0SRiemannian.chartTensorInnerPointwise_0s_smul_right

end Tensor0SRiemannian
end Tensor
end DifferentialGeometry

end
