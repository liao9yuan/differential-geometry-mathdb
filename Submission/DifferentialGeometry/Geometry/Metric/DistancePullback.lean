import Submission.DifferentialGeometry.Geometry.Metric.Pullback.Local
import Submission.DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal
namespace DifferentialGeometry.Geometry.Metric

variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]

omit [FiniteDimensional ℝ F] [T2Space N] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem edistOf_localPullMetric_le
    (g : SmoothRiemannianMetric J N) (f : M → N)
    (hf : IsLocalDiffeomorph I J ∞ f) (x y : M) :
    riemannianEDistOf g (f x) (f y) ≤ riemannianEDistOf (localPullMetric g f hf) x y := by
  let : _root_.Bundle.RiemannianBundle (TangentSpace J : N → Type _) := ⟨g.toRiemannianMetric⟩
  let : _root_.Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨(localPullMetric g f hf).toRiemannianMetric⟩
  have henorm : ∀ (p : N) (v : TangentSpace J p),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner p v v)) := by
    intro p v
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    rfl
  change _root_.Manifold.riemannianEDist J (f x) (f y) ≤ _root_.Manifold.riemannianEDist I x y
  by_contra hnot
  obtain ⟨γ, hγ0, hγ1, hγ, hlen⟩ :=
    _root_.Manifold.exists_lt_of_riemannianEDist_lt (lt_of_not_ge hnot)
  have hmap : ContMDiffOn 𝓘(ℝ) J 1 (f ∘ γ) (_root_.Set.Icc 0 1) :=
    (hf.contMDiff.of_le (by simp)).comp_contMDiffOn hγ
  have hbound := _root_.Manifold.riemannianEDist_le_pathELength (x := f x) (y := f y) hmap
    (by simp only [Function.comp_apply, hγ0])
    (by simp only [Function.comp_apply, hγ1]) zero_le_one
  rw [localPull_pathLen g henorm f hf hγ] at hbound
  exact (not_lt_of_ge hbound) hlen

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Metric.edistOf_localPullMetric_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Metric.edistOf_localPullMetric_le target :: scope.openDecls } }

omit [FiniteDimensional ℝ F] [T2Space N] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem edistOf_le_of_quad_of_localDiffeomorph
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (f : M → N) (hf : IsLocalDiffeomorph I J ∞ f) {c : ℝ} (hc : 0 < c)
    (hu : ∀ x v, h.inner (f x) (mfderiv I J f x v) (mfderiv I J f x v) ≤
      c * g.inner x v v)
    (x y : M) :
    riemannianEDistOf h (f x) (f y) ≤
      ENNReal.ofReal (Real.sqrt c) * riemannianEDistOf g x y := by
  refine (edistOf_localPullMetric_le h f hf x y).trans ?_
  refine edistOf_le_of_quad g (localPullMetric h f hf) hc ?_ x y
  intro z v
  rw [localPullMetric_inner]
  exact hu z v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.edistOf_le_of_quad_of_localDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.edistOf_le_of_quad_of_localDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.edistOf_le_of_quad_of_localDiffeomorph ``Submission.DifferentialGeometry.Geometry.Metric.edistOf_le_of_quad_of_localDiffeomorph

omit [FiniteDimensional ℝ F] [T2Space N] in
private theorem localPullMetric_eq_pullbackMetricCross
    (g : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N) :
    localPullMetric g Φ Φ.isLocalDiffeomorph = Diffeomorph.pullbackMetricCross g Φ := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [localPullMetric_inner, Diffeomorph.pullbackMetricCross_inner]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Metric.localPullMetric_eq_pullbackMetricCross
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Metric.localPullMetric_eq_pullbackMetricCross target :: scope.openDecls } }

private theorem localPullMetric_symm_pullbackMetricCross
    (g : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N) :
    localPullMetric (Diffeomorph.pullbackMetricCross g Φ) Φ.symm
      Φ.symm.isLocalDiffeomorph = g := by
  apply SmoothRiemannianMetric.ext_inner
  intro p v w
  have hd := (Φ.toOpenPartialHomeomorph_mdifferentiable (by decide)).comp_symm_deriv
    (show p ∈ (Φ.toHomeomorph.toOpenPartialHomeomorph).target from _root_.Set.mem_univ p)
  have hv : mfderiv I J Φ (Φ.symm p) (mfderiv J I Φ.symm p v) = v :=
    congrArg (fun D => D v) hd
  have hw : mfderiv I J Φ (Φ.symm p) (mfderiv J I Φ.symm p w) = w :=
    congrArg (fun D => D w) hd
  rw [localPullMetric_inner, Diffeomorph.pullbackMetricCross_inner, hv, hw,
    Φ.apply_symm_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Metric.localPullMetric_symm_pullbackMetricCross
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Metric.localPullMetric_symm_pullbackMetricCross target :: scope.openDecls } }

theorem edistOf_pullbackMetricCross
    (g : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N) (x y : M) :
    riemannianEDistOf (Diffeomorph.pullbackMetricCross g Φ) x y =
      riemannianEDistOf g (Φ x) (Φ y) := by
  apply le_antisymm
  · have h := edistOf_localPullMetric_le (Diffeomorph.pullbackMetricCross g Φ)
      Φ.symm Φ.symm.isLocalDiffeomorph (Φ x) (Φ y)
    rw [localPullMetric_symm_pullbackMetricCross, Φ.symm_apply_apply, Φ.symm_apply_apply] at h
    exact h
  · have h := edistOf_localPullMetric_le g Φ Φ.isLocalDiffeomorph x y
    rw [localPullMetric_eq_pullbackMetricCross] at h
    exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.edistOf_pullbackMetricCross then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.edistOf_pullbackMetricCross"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.edistOf_pullbackMetricCross ``Submission.DifferentialGeometry.Geometry.Metric.edistOf_pullbackMetricCross

end DifferentialGeometry.Geometry.Metric
