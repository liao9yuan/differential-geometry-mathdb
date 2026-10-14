import Submission.DifferentialGeometry.Tensor.Metric.TraceDerivativeBounds
import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.Tensor0S.Algebra.ContractionLeibniz
import Submission.DifferentialGeometry.Geometry.Connection.MetricCompatibility.Tensor.Metric
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Cotangent.Riemannian

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.TopologicalSpace _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Tensor0SBundle _root_.Submission.DifferentialGeometry.Tensor.RSTensor
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.Geometry.Tensor
open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators
namespace DifferentialGeometry.Geometry.Curvature

private def lowerPerm : Fin 6 ≃ Fin 6 where
  toFun := ![2, 3, 4, 0, 1, 5]
  invFun := ![3, 4, 0, 1, 2, 5]
  left_inv := by decide
  right_inv := by decide

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.lowerPerm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.lowerPerm target :: scope.openDecls } }

section Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

omit [CompleteSpace E] [T2Space M] in
private theorem trace_orthonormal (G : SmoothRiemannianMetric I M)
    (T : Tensor0SField (I := I) (M := M) ∞ 6) (x : M)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (TangentSpace I x))
    (hi : MetricInverseInBasis G x b (identityInvMetric (Idx := ι)))
    (w : Fin 4 → TangentSpace I x) :
    metricTraceFirstTwoField G T x w = ∑ i, T x (metricTraceInput (b i) (b i) w) := by
  erw [metricTraceFirstTwoField_apply, metricTraceFirstTwo0STensor_apply,
    metricTraceFirstTwo0SAt_eq_sum_basis G b (identityInvMetric (Idx := ι)) hi]
  simp only [metricTrace0S2InBasis, identityInvMetric, diagonalInvMetric,
    ite_mul, one_mul, _root_.MulZeroClass.zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.trace_orthonormal
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.trace_orthonormal target :: scope.openDecls } }

private theorem lower_product_eval (G g : SmoothRiemannianMetric I M)
    (x : M) (a b : TangentSpace I x) (w : Fin 4 → TangentSpace I x) :
    Tensor0SField.domDomCongr ∞ lowerPerm
      (tensor0SFieldProduct ∞
        (CovariantDerivative.rm04Section G (metricCov g) (metricCov_smooth g))
        (metricTensorField g)) x (metricTraceInput a b w) =
      G.inner x a
        (connectionRiemannCurvatureField (metricCov g)
          (CovariantDerivative.tangentConstAt (I := I) x (w 0)) (CovariantDerivative.tangentConstAt (I := I) x (w 1))
          (CovariantDerivative.tangentConstAt (I := I) x (w 2)) x) * g.inner x b (w 3) := by
  change tensor0SFieldProduct ∞
      (CovariantDerivative.rm04Section G (metricCov g) (metricCov_smooth g))
      (metricTensorField g) x (fun i => metricTraceInput a b w (lowerPerm i)) = _
  let S := CovariantDerivative.rm04Section G (metricCov g) (metricCov_smooth g)
  let V : Fin 6 → TangentSpace I x := fun i => metricTraceInput a b w (lowerPerm i)
  have he : V ∘ Fin.castAdd 2 = vec4 (w 0) (w 1) (w 2) a := by
    funext i
    fin_cases i <;> rfl
  have hs : S x (V ∘ Fin.castAdd 2) =
      G.inner x a
        (connectionRiemannCurvatureField (metricCov g)
          (CovariantDerivative.tangentConstAt (I := I) x (w 0))
          (CovariantDerivative.tangentConstAt (I := I) x (w 1))
          (CovariantDerivative.tangentConstAt (I := I) x (w 2)) x) := by
    rw [he]
    exact CovariantDerivative.rm04Section_apply_const G (metricCov g) (metricCov_smooth g) _ _ _ _
  have hm : metricTensorField g x (V ∘ Fin.natAdd 4) = g.inner x b (w 3) :=
    metricTensorField_apply g x (V ∘ Fin.natAdd 4)
  exact (tensor0SField_product_apply S (metricTensorField g) x V).trans
    (congrArg₂ (fun r s : ℝ => r * s) hs hm)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.lower_product_eval
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.lower_product_eval target :: scope.openDecls } }

theorem exists_metricRm04_relowering :
    ∃ e : Fin 6 ≃ Fin 6, ∀ G g : SmoothRiemannianMetric I M,
      metricRm04 g = metricTraceFirstTwoField G
        (Tensor0SField.domDomCongr ∞ e
          (tensor0SFieldProduct ∞
            (CovariantDerivative.rm04Section G (metricCov g) (metricCov_smooth g))
            (metricTensorField g))) := by
  refine ⟨lowerPerm, ?_⟩
  intro G g
  apply DFunLike.ext
  intro x
  apply tensor0SSpace_ext (I := I) 4 x
  intro w
  classical
  obtain ⟨b, hb⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis G x
  have hi : MetricInverseInBasis G x b (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))) :=
    metricInverseInBasis_identity_of_orthonormal G b hb
  erw [trace_orthonormal G _ x b hi w]
  simp_rw [lower_product_eval]
  let R := connectionRiemannCurvatureField (metricCov g)
    (CovariantDerivative.tangentConstAt (I := I) x (w 0)) (CovariantDerivative.tangentConstAt (I := I) x (w 1))
    (CovariantDerivative.tangentConstAt (I := I) x (w 2)) x
  have hw : w = vec4 (w 0) (w 1) (w 2) (w 3) := by
    funext i
    fin_cases i <;> rfl
  have hleft : metricRm04 g x w = g.inner x (w 3) R := by
    rw [hw]
    exact CovariantDerivative.rm04Section_apply_const g (metricCov g) (metricCov_smooth g) _ _ _ _
  rw [hleft]
  have hrepr (i) : b.repr R i = G.inner x (b i) R := by
    rw [basis_repr_eq_sum_inv_inner G x b (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))) hi R i]
    simp only [identityInvMetric, diagonalInvMetric, ite_mul, one_mul, _root_.MulZeroClass.zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [G.symm]
  calc
    g.inner x (w 3) R = g.inner x R (w 3) := g.symm x _ _
    _ = g.inner x (∑ i, b.repr R i • b i) (w 3) := by rw [b.sum_repr]
    _ = ∑ i, G.inner x (b i) R * g.inner x (b i) (w 3) := by
      rw [map_sum, sum_apply]
      simp only [map_smul, smul_apply, smul_eq_mul, hrepr]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.exists_metricRm04_relowering then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.exists_metricRm04_relowering"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.exists_metricRm04_relowering ``Submission.DifferentialGeometry.Geometry.Curvature.exists_metricRm04_relowering

end Manifold

section Euclidean
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
private local instance _root_.Submission.DifferentialGeometry.Geometry.Curvature.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

theorem exists_iterCov_metricRm04_relowering_bound_on_opens (k : ℕ) :
    ∃ C > 0, ∀ (U : _root_.TopologicalSpace.Opens E) (G g : SmoothRiemannianMetric 𝓘(ℝ, E) U) (x : U),
      let S := CovariantDerivative.rm04Section G (metricCov g) (metricCov_smooth g)
      Real.sqrt (normSq0S G x (4 + k) (iterCov G 4 (metricRm04 g) k x)) ≤
        C * ∑ c ∈ Finset.range (k + 1), (k.choose c : ℝ) *
          Real.sqrt (normSq0S G x (4 + c) (iterCov G 4 S c x)) *
          Real.sqrt (normSq0S G x (2 + (k - c))
            (iterCov G 2 (metricTensorField g) (k - c) x)) := by
  obtain ⟨C, hC, htrace⟩ := exists_iter_cov_metric_trace_first_two_bound_on_opens (E := E) 4 k
  refine ⟨C, hC, ?_⟩
  intro U G g x
  dsimp only
  obtain ⟨e, he⟩ := exists_metricRm04_relowering (I := 𝓘(ℝ, E)) (M := U)
  let S := CovariantDerivative.rm04Section G (metricCov g) (metricCov_smooth g)
  let P := tensor0SFieldProduct ∞ S (metricTensorField g)
  have ht := htrace U G (Tensor0SField.domDomCongr ∞ e P) x
  rw [← he G g] at ht
  obtain ⟨b, hb⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis G x
  have hi := metricInverseInBasis_identity_of_orthonormal G b hb
  rw [normSq0S_iterCov_domDomCongr G e P k x b hi] at ht
  exact ht.trans (mul_le_mul_of_nonneg_left
    (iterCov_product_sqrtNormSq_le G x b hi k S (metricTensorField g)) hC.le)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.exists_iterCov_metricRm04_relowering_bound_on_opens then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.exists_iterCov_metricRm04_relowering_bound_on_opens"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.exists_iterCov_metricRm04_relowering_bound_on_opens ``Submission.DifferentialGeometry.Geometry.Curvature.exists_iterCov_metricRm04_relowering_bound_on_opens
end Euclidean

end DifferentialGeometry.Geometry.Curvature
