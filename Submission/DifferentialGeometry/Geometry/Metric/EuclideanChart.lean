import Submission.DifferentialGeometry.Geometry.Curvature.Bounds.RicciOperatorNorm
import Submission.DifferentialGeometry.Geometry.Metric.LocalChartDistance
import Submission.DifferentialGeometry.Topology.Manifold.ChartDifferential
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ContDiff _root_.BigOperators _root_.InnerProductSpace
namespace DifferentialGeometry.Geometry.Metric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private def metricBasis (g : SmoothRiemannianMetric I M) (p : M) :
    Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I p) := by
  exact (DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis g p).choose

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Metric.metricBasis
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Metric.metricBasis target :: scope.openDecls } }

private theorem metricBasis_inner (g : SmoothRiemannianMetric I M) (p : M)
    (i j : Fin (Module.finrank ℝ E)) :
    g.inner p (metricBasis g p i) (metricBasis g p j) = if i = j then 1 else 0 :=
  (DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis g p).choose_spec i j

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Metric.metricBasis_inner
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Metric.metricBasis_inner target :: scope.openDecls } }

def metricEuclideanFrame (g : SmoothRiemannianMetric I M) (p : M) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) ≃L[ℝ] TangentSpace I p :=
  ((WithLp.linearEquiv 2 ℝ (Fin (Module.finrank ℝ E) → ℝ)).trans
    (metricBasis g p).equivFun.symm).toContinuousLinearEquiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.metricEuclideanFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.metricEuclideanFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.metricEuclideanFrame ``Submission.DifferentialGeometry.Geometry.Metric.metricEuclideanFrame

private theorem metricEuclideanFrame_apply (g : SmoothRiemannianMetric I M) (p : M)
    (v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    metricEuclideanFrame g p v = ∑ i, v i • metricBasis g p i := by
  simp only [metricEuclideanFrame, LinearEquiv.coe_toContinuousLinearEquiv',
    LinearEquiv.trans_apply, Module.Basis.equivFun_symm_apply]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Metric.metricEuclideanFrame_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Metric.metricEuclideanFrame_apply target :: scope.openDecls } }

theorem metricEuclideanFrame_inner (g : SmoothRiemannianMetric I M) (p : M)
    (v w : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    g.inner p (metricEuclideanFrame g p v) (metricEuclideanFrame g p w) = ⟪v, w⟫_ℝ := by
  rw [metricEuclideanFrame_apply, metricEuclideanFrame_apply]
  simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply,
    smul_eq_mul, metricBasis_inner]
  simp only [mul_ite, mul_one, _root_.MulZeroClass.mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.metricEuclideanFrame_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.metricEuclideanFrame_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.metricEuclideanFrame_inner ``Submission.DifferentialGeometry.Geometry.Metric.metricEuclideanFrame_inner

theorem metricEuclideanFrame_sqrt (g : SmoothRiemannianMetric I M) (p : M)
    (v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    Real.sqrt (g.inner p (metricEuclideanFrame g p v) (metricEuclideanFrame g p v)) = ‖v‖ := by
  rw [metricEuclideanFrame_inner, real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg v)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.metricEuclideanFrame_sqrt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.metricEuclideanFrame_sqrt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.metricEuclideanFrame_sqrt ``Submission.DifferentialGeometry.Geometry.Metric.metricEuclideanFrame_sqrt

theorem metricEuclideanFrame_symm_norm (g : SmoothRiemannianMetric I M) (p : M)
    (v : TangentSpace I p) :
    ‖(metricEuclideanFrame g p).symm v‖ = Real.sqrt (g.inner p v v) := by
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using
    (metricEuclideanFrame_sqrt g p ((metricEuclideanFrame g p).symm v)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.metricEuclideanFrame_symm_norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.metricEuclideanFrame_symm_norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.metricEuclideanFrame_symm_norm ``Submission.DifferentialGeometry.Geometry.Metric.metricEuclideanFrame_symm_norm

def metricChartEuclideanEquiv (g : SmoothRiemannianMetric I M) (p : M) :
    E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
  ((_root_.FiberBundle.trivializationAt E (TangentSpace I) p).continuousLinearEquivAt ℝ p
    (FiberBundle.mem_baseSet_trivializationAt' p)).symm.trans (metricEuclideanFrame g p).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.metricChartEuclideanEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.metricChartEuclideanEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.metricChartEuclideanEquiv ``Submission.DifferentialGeometry.Geometry.Metric.metricChartEuclideanEquiv

theorem metricChartEuclideanEquiv_norm (g : SmoothRiemannianMetric I M) (p : M) (w : E) :
    ‖metricChartEuclideanEquiv g p w‖ =
      Real.sqrt (g.inner p
        ((_root_.FiberBundle.trivializationAt E (TangentSpace I) p).symmL ℝ p w)
        ((_root_.FiberBundle.trivializationAt E (TangentSpace I) p).symmL ℝ p w)) := by
  rw [metricChartEuclideanEquiv, ContinuousLinearEquiv.trans_apply,
    metricEuclideanFrame_symm_norm]
  rw [congrFun ((_root_.FiberBundle.trivializationAt E (TangentSpace I) p).symm_continuousLinearEquivAt_eq
    (R := ℝ) (FiberBundle.mem_baseSet_trivializationAt' p)) w]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.metricChartEuclideanEquiv_norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.metricChartEuclideanEquiv_norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.metricChartEuclideanEquiv_norm ``Submission.DifferentialGeometry.Geometry.Metric.metricChartEuclideanEquiv_norm

theorem metricChartEuclideanEquiv_symm_apply (g : SmoothRiemannianMetric I M) (p : M)
    (v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    (metricChartEuclideanEquiv g p).symm v =
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ p
        (metricEuclideanFrame g p v) := by
  simp only [metricChartEuclideanEquiv, ContinuousLinearEquiv.symm_trans_apply,
    ContinuousLinearEquiv.symm_symm]
  exact congrFun ((_root_.FiberBundle.trivializationAt E (TangentSpace I) p).coe_continuousLinearEquivAt_eq
    (R := ℝ) (FiberBundle.mem_baseSet_trivializationAt' p)) _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.metricChartEuclideanEquiv_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.metricChartEuclideanEquiv_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.metricChartEuclideanEquiv_symm_apply ``Submission.DifferentialGeometry.Geometry.Metric.metricChartEuclideanEquiv_symm_apply

variable {F H' N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

def euclideanChartExpression (g : SmoothRiemannianMetric I M)
    (h : SmoothRiemannianMetric J N) (f : M → N) (p : M) (q : N) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →
      EuclideanSpace ℝ (Fin (Module.finrank ℝ F)) :=
  (metricChartEuclideanEquiv h q) ∘
    (((extChartAt J q) ∘ f ∘ (extChartAt I p).symm) ∘ (metricChartEuclideanEquiv g p).symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.euclideanChartExpression then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.euclideanChartExpression"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.euclideanChartExpression ``Submission.DifferentialGeometry.Geometry.Metric.euclideanChartExpression

theorem fderiv_euclideanChartExpression_apply [I.Boundaryless] [J.Boundaryless]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (f : M → N) (p : M) (q : N) (x : M)
    (hx : x ∈ (extChartAt I p).source) (hfx : f x ∈ (extChartAt J q).source)
    (hc : ContinuousAt f x) (v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    fderiv ℝ (euclideanChartExpression g h f p q)
        (metricChartEuclideanEquiv g p (extChartAt I p x)) v =
      metricChartEuclideanEquiv h q
        ((_root_.FiberBundle.trivializationAt F (TangentSpace J) q).continuousLinearMapAt ℝ (f x)
          (mfderiv I J f x
            ((_root_.FiberBundle.trivializationAt E (TangentSpace I) p).symmL ℝ x
              ((_root_.FiberBundle.trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ p
                (metricEuclideanFrame g p v))))) := by
  rw [euclideanChartExpression, ContinuousLinearEquiv.comp_fderiv,
    ContinuousLinearEquiv.comp_right_fderiv, ContinuousLinearEquiv.symm_apply_apply,
    DifferentialGeometry.Topology.Manifold.fderiv_fixed_chart_eq_trivialization_comp_mfderiv
      f p q x hx hfx hc]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    metricChartEuclideanEquiv_symm_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.fderiv_euclideanChartExpression_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.fderiv_euclideanChartExpression_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.fderiv_euclideanChartExpression_apply ``Submission.DifferentialGeometry.Geometry.Metric.fderiv_euclideanChartExpression_apply

theorem eventually_norm_fderiv_euclideanChartExpression_le
    [I.Boundaryless] [J.Boundaryless]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (f : M → N) (hf : Continuous f) (p : M) {K : ℝ} (hK : 1 < K) :
    ∀ᶠ x in 𝓝 p, x ∈ (extChartAt I p).source ∧
      f x ∈ (extChartAt J (f p)).source ∧
      ((∀ v : TangentSpace I x,
        Real.sqrt (h.inner (f x) (mfderiv I J f x v) (mfderiv I J f x v)) ≤
          Real.sqrt (g.inner x v v)) →
        ‖fderiv ℝ (euclideanChartExpression g h f p (f p))
          (metricChartEuclideanEquiv g p (extChartAt I p x))‖ ≤ K ^ 2) := by
  have hK0 : 0 ≤ K := le_trans zero_le_one hK.le
  have htarget := (hf.continuousAt (x := p))
    (eventually_tangent_transport_le h (f p) hK)
  filter_upwards [eventually_tangent_transport_le g p hK, htarget] with x hgx hhx
  rcases hgx with ⟨hx, _, hgback⟩
  rcases hhx with ⟨hfx, hhforward, _⟩
  have hx' : x ∈ (extChartAt I p).source := by simpa only [extChartAt_source] using hx
  have hfx' : f x ∈ (extChartAt J (f p)).source := by simpa only [extChartAt_source] using hfx
  refine ⟨hx', hfx', fun hdf => ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _ (sq_nonneg K) fun v => ?_
  rw [fderiv_euclideanChartExpression_apply g h f p (f p) x hx' hfx' hf.continuousAt,
    metricChartEuclideanEquiv_norm]
  let u : TangentSpace I x := (_root_.FiberBundle.trivializationAt E (TangentSpace I) p).symmL ℝ x
    ((_root_.FiberBundle.trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ p
      (metricEuclideanFrame g p v))
  have h1 := hhforward (mfderiv I J f x u)
  have h2 := mul_le_mul_of_nonneg_left (hdf u) hK0
  have h3 := mul_le_mul_of_nonneg_left (hgback (metricEuclideanFrame g p v)) hK0
  have hlast : K * (K * Real.sqrt (g.inner p
      (metricEuclideanFrame g p v) (metricEuclideanFrame g p v))) = K ^ 2 * ‖v‖ := by
    rw [metricEuclideanFrame_sqrt]
    ring
  exact h1.trans (h2.trans (h3.trans_eq hlast))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.eventually_norm_fderiv_euclideanChartExpression_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.eventually_norm_fderiv_euclideanChartExpression_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.eventually_norm_fderiv_euclideanChartExpression_le ``Submission.DifferentialGeometry.Geometry.Metric.eventually_norm_fderiv_euclideanChartExpression_le

end DifferentialGeometry.Geometry.Metric

end

set_option autoImplicit false
noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Filter _root_.Set _root_.Submission.DifferentialGeometry
open scoped _root_.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry.Metric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem mfderiv_metricChartEuclideanEquiv_extChartAt
    (g : SmoothRiemannianMetric I M) (p y : M)
    (hy : y ∈ (chartAt H p).source) :
    mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
        (fun z => metricChartEuclideanEquiv g p (extChartAt I p z)) y =
      (metricChartEuclideanEquiv g p).toContinuousLinearMap.comp
        ((_root_.FiberBundle.trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ y) := by
  let A := metricChartEuclideanEquiv g p
  have hA : HasMFDerivAt 𝓘(ℝ, E)
      𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) A
      (extChartAt I p y) A.toContinuousLinearMap :=
    A.hasFDerivAt.hasMFDerivAt
  have hφ := (mdifferentiableAt_extChartAt (I := I) hy).hasMFDerivAt
  have hd := (hA.comp y hφ).mfderiv
  change mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
    (A ∘ extChartAt I p) y = _ at hd
  rw [← TangentBundle.continuousLinearMapAt_trivializationAt hy] at hd
  exact hd

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.mfderiv_metricChartEuclideanEquiv_extChartAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.mfderiv_metricChartEuclideanEquiv_extChartAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.mfderiv_metricChartEuclideanEquiv_extChartAt ``Submission.DifferentialGeometry.Geometry.Metric.mfderiv_metricChartEuclideanEquiv_extChartAt

theorem eventually_norm_mfderiv_metricChartEuclideanEquiv_extChartAt_le
    (g : SmoothRiemannianMetric I M) (p : M) {K : ℝ} (hK : 1 < K) :
    ∀ᶠ y in 𝓝 p, y ∈ (chartAt H p).source ∧
      ∀ v : TangentSpace I y,
        ‖mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
          (fun z => metricChartEuclideanEquiv g p (extChartAt I p z)) y v‖ ≤
            K * Real.sqrt (g.inner y v v) := by
  filter_upwards [eventually_tangent_transport_le g p hK] with y hy
  refine ⟨hy.1, fun v => ?_⟩
  rw [mfderiv_metricChartEuclideanEquiv_extChartAt g p y hy.1]
  let w : E := (_root_.FiberBundle.trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ y v
  change ‖metricChartEuclideanEquiv g p w‖ ≤ K * Real.sqrt (g.inner y v v)
  rw [metricChartEuclideanEquiv_norm]
  exact hy.2.1 v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.eventually_norm_mfderiv_metricChartEuclideanEquiv_extChartAt_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.eventually_norm_mfderiv_metricChartEuclideanEquiv_extChartAt_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.eventually_norm_mfderiv_metricChartEuclideanEquiv_extChartAt_le ``Submission.DifferentialGeometry.Geometry.Metric.eventually_norm_mfderiv_metricChartEuclideanEquiv_extChartAt_le

end DifferentialGeometry.Geometry.Metric

end
