import Submission.DifferentialGeometry.Geometry.Metric.Coordinates.ChartFrameBounds
import Submission.DifferentialGeometry.Geometry.Metric.PointwiseInner.Bounds

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set
open scoped _root_.ContDiff _root_.Manifold _root_.BigOperators

namespace DifferentialGeometry.Tensor.Coordinates

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] in
private theorem sqrt_inner_sum_le
    (g : SmoothRiemannianMetric I M) (q : M)
    {ι : Type*} (s : Finset ι) (v : ι → TangentSpace I q) :
    Real.sqrt (g.inner q (∑ i ∈ s, v i) (∑ i ∈ s, v i)) ≤
      ∑ i ∈ s, Real.sqrt (g.inner q (v i) (v i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (DifferentialGeometry.Analysis.Laplacian.gNorm_add_le g q _ _).trans
        (add_le_add le_rfl ih)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor.Coordinates.sqrt_inner_sum_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor.Coordinates.sqrt_inner_sum_le target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
private theorem sqrt_inner_smul
    (g : SmoothRiemannianMetric I M) (q : M) (r : ℝ) (v : TangentSpace I q) :
    Real.sqrt (g.inner q (r • v) (r • v)) =
      |r| * Real.sqrt (g.inner q v v) := by
  rw [DifferentialGeometry.Analysis.Laplacian.metric_inner_smul_self,
    Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq_eq_abs]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor.Coordinates.sqrt_inner_smul
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor.Coordinates.sqrt_inner_smul target :: scope.openDecls } }

theorem exists_pos_sqrt_inner_symmL_le_mul_norm_on_compact
    (g : SmoothRiemannianMetric I M) (p : M) {K : Set M}
    (hK : IsCompact K)
    (hchart : K ⊆ (_root_.FiberBundle.trivializationAt E (TangentSpace I) p).baseSet) :
    ∃ B : ℝ, 0 < B ∧ ∀ q ∈ K, ∀ w : E,
      Real.sqrt (g.inner q
        ((_root_.FiberBundle.trivializationAt E (TangentSpace I) p).symmL ℝ q w)
        ((_root_.FiberBundle.trivializationAt E (TangentSpace I) p).symmL ℝ q w)) ≤ B * ‖w‖ := by
  classical
  obtain ⟨R, hR, hframe⟩ := exists_pos_bound_chartBasisVec_on_compact g p hK hchart
  let A : ℝ := ∑ i, ‖((chartModelBasis E).coord i).toContinuousLinearMap‖
  have hA : 0 ≤ A := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨R * A + 1, by positivity, ?_⟩
  intro q hq w
  have hdecomp : (_root_.FiberBundle.trivializationAt E (TangentSpace I) p).symmL ℝ q w =
      ∑ i, (chartModelBasis E).repr w i • chartBasisVecFiber (I := I) p i q := by
    conv_lhs => rw [← (chartModelBasis E).sum_repr w]
    rw [map_sum]
    simp only [map_smul, chartBasisVecFiber]
  have hcoord (i : Fin (Module.finrank ℝ E)) :
      |(chartModelBasis E).repr w i| ≤
        ‖((chartModelBasis E).coord i).toContinuousLinearMap‖ * ‖w‖ :=
    (((chartModelBasis E).coord i).toContinuousLinearMap).le_opNorm w
  rw [hdecomp]
  calc
    _ ≤ ∑ i, Real.sqrt (g.inner q
        ((chartModelBasis E).repr w i • chartBasisVecFiber (I := I) p i q)
        ((chartModelBasis E).repr w i • chartBasisVecFiber (I := I) p i q)) :=
      sqrt_inner_sum_le g q Finset.univ _
    _ = ∑ i, |(chartModelBasis E).repr w i| *
        Real.sqrt (g.inner q (chartBasisVecFiber (I := I) p i q)
          (chartBasisVecFiber (I := I) p i q)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact sqrt_inner_smul g q _ _
    _ ≤ ∑ i, (‖((chartModelBasis E).coord i).toContinuousLinearMap‖ * ‖w‖) * R := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul (hcoord i) (hframe q hq i) (Real.sqrt_nonneg _)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = R * A * ‖w‖ := by
      simp only [A, ← Finset.sum_mul]
      ring
    _ ≤ (R * A + 1) * ‖w‖ := by nlinarith only [norm_nonneg w]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.exists_pos_sqrt_inner_symmL_le_mul_norm_on_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.exists_pos_sqrt_inner_symmL_le_mul_norm_on_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.exists_pos_sqrt_inner_symmL_le_mul_norm_on_compact ``Submission.DifferentialGeometry.Tensor.Coordinates.exists_pos_sqrt_inner_symmL_le_mul_norm_on_compact

end DifferentialGeometry.Tensor.Coordinates
