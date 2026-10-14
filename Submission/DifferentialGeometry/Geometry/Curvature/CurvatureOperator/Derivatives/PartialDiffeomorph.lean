import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.LocalPullback

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

variable {E H M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]

theorem curvDerivNorm_eq_of_partialDiffeomorph_restriction
    (Phi : PartialDiffeomorph I I M N ∞) (U : TopologicalSpace.Opens M)
    (hU : (U : Set M) ⊆ Phi.source)
    (g : SmoothRiemannianMetric I U) (h : SmoothRiemannianMetric I N)
    (hmet : ∀ x : U, ∀ v w : TangentSpace I x,
      g.inner x v w = h.inner (Phi x) (mfderiv I I (Phi : M → N) x v)
        (mfderiv I I (Phi : M → N) x w)) (q : ℕ) (x : U) :
    curvDerivNorm q g x = curvDerivNorm q h (Phi x) := by
  let V : TopologicalSpace.Opens N :=
    ⟨(Phi : M → N) '' (U : Set M), image_opens_isOpen Phi hU⟩
  let e : U ≃ₘ⟮I, I⟯ V := PartialDiffeomorph.toOpensDiffeo Phi hU
  have heq : g = Diffeomorph.pullbackMetricCross (h.restrictOpen V) e := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    rw [Diffeomorph.pullbackMetricCross_inner, SmoothRiemannianMetric.restrictOpen_inner]
    exact (hmet y v w).trans
      (congrArg₂ (fun v' w' => h.inner (Phi (y : M)) v' w')
        (PartialDiffeomorph.mfderiv_toOpensDiffeo Phi hU y v)
        (PartialDiffeomorph.mfderiv_toOpensDiffeo Phi hU y w)).symm
  rw [heq,
    DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.curvDerivNorm_pullbackMetricCross,
    curvDerivNorm_restrictOpen]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.curvDerivNorm_eq_of_partialDiffeomorph_restriction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.curvDerivNorm_eq_of_partialDiffeomorph_restriction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.curvDerivNorm_eq_of_partialDiffeomorph_restriction ``Submission.DifferentialGeometry.CheegerGromovCompactness.curvDerivNorm_eq_of_partialDiffeomorph_restriction

end DifferentialGeometry.CheegerGromovCompactness

end
