import Submission.DifferentialGeometry.Geometry.Comparison.Splitting.AffineZeroLevelCompleteness

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set
open scoped _root_.Topology _root_.ContDiff _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.Geometry.Topology

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

theorem affineFunction_splitting
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {b : M → ℝ} (hb : ContMDiff I 𝓘(ℝ, ℝ) ∞ b)
    (hunit : ∀ p, g.inner p (gradientFun (I := I) g b p) (gradientFun (I := I) g b p) = 1)
    (hH : ∀ p, hessFun (I := I) g b p = 0) :
    ∃ p₀ : {q : M // b q = 0},
      let _ := affineZeroLevelChartedSpace (I := I) g hEnorm hb hunit hH p₀
      let _ := affineZeroLevel_isManifold (I := I) g hEnorm hb hunit hH p₀
      let _ : SigmaCompactSpace {q : M // b q = 0} :=
        (isClosed_eq hb.continuous continuous_const).sigmaCompactSpace
      ConnectedSpace {q : M // b q = 0} ∧
      DifferentialGeometry.Geometry.IsEmbeddedSlice I (Module.finrank ℝ E - 1)
        {q : M | b q = 0} ∧
      Module.finrank ℝ (affineFunctionKernel (I := I) b p₀.1) + 1 = Module.finrank ℝ E ∧
      RiemannianMetricComplete (I := 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1))
        (affineZeroLevelMetric (I := I) g hEnorm hb hunit hH p₀) ∧
      ∃ Φ : ({q : M // b q = 0} × ℝ) ≃ₘ⟮
          𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1).prod 𝓘(ℝ, ℝ), I⟯ M,
        (∀ (p : {q : M // b q = 0}) (t : ℝ),
          Φ (p, t) = affineGradientFlow (I := I) g hEnorm b p.1 t) ∧
        (∀ x : M, Φ.symm x =
          (affineZeroLevelRetraction (I := I) g hEnorm hb hunit hH x, b x)) ∧
        (∀ (p : {q : M // b q = 0})
          (v w : TangentSpace 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1) p) (t a c : ℝ),
          g.inner (Φ (p, t))
            (mfderiv (𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1).prod 𝓘(ℝ, ℝ)) I
              Φ (p, t) (v, a))
            (mfderiv (𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1).prod 𝓘(ℝ, ℝ)) I
              Φ (p, t) (w, c)) =
            (affineZeroLevelMetric (I := I) g hEnorm hb hunit hH p₀).inner p v w + a * c) := by
  let x₀ : M := Classical.choice (inferInstance : Nonempty M)
  let p₀ := affineZeroLevelRetraction (I := I) g hEnorm hb hunit hH x₀
  refine ⟨p₀, ?_⟩
  let _ := affineZeroLevelChartedSpace (I := I) g hEnorm hb hunit hH p₀
  let _ := affineZeroLevel_isManifold (I := I) g hEnorm hb hunit hH p₀
  let _ : SigmaCompactSpace {q : M // b q = 0} :=
    (isClosed_eq hb.continuous continuous_const).sigmaCompactSpace
  refine ⟨affineFunctionZeroLevel_connectedSpace (I := I) g hEnorm hb hunit hH,
    affineZeroLevel_isEmbeddedSlice (I := I) g hEnorm hb hunit hH,
    affineFunction_kernel_finrank (I := I) g b hunit p₀.1,
    affineZeroLevelMetric_complete (I := I) g hEnorm hb hunit hH p₀,
    affineFunctionZeroLevelDiffeomorph (I := I) g hEnorm hb hunit hH p₀, ?_, ?_, ?_⟩
  · exact affineFunctionZeroLevelDiffeomorph_apply (I := I) g hEnorm hb hunit hH p₀
  · exact affineFunctionZeroLevelDiffeomorph_symm_apply (I := I) g hEnorm hb hunit hH p₀
  · exact affineFunctionZeroLevelDiffeomorph_preserves_product_metric
      (I := I) g hEnorm hb hunit hH p₀

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.affineFunction_splitting then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.affineFunction_splitting"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.affineFunction_splitting ``Submission.DifferentialGeometry.Geometry.Topology.affineFunction_splitting

end DifferentialGeometry.Geometry.Topology

end
