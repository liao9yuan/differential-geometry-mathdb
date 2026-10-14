import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Energy.RemainderLadder
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.Lifting.LowerScaleSecondOrderFibreBounds

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Filter _root_.Topology _root_.Submission.DifferentialGeometry.Tensor0SBundle _root_.ContinuousLinearMap _root_.Submission.ContinuousLinearMap _root_.Bundle.ContinuousLinearMap
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Tensor.RSTensor
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization
open _root_.Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization
open _root_.Submission.DifferentialGeometry.Integral.Connection
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

theorem secondOrderAction_ladder_affine_uniform
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ ρ K : ℝ, 0 < ρ ∧ 0 ≤ K ∧
      ∀ {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        {R : ℝ}, 0 ≤ R → R ≤ ρ →
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        (∀ a : ℕ, a ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
        ∃ Clower : ℕ → ℝ, (∀ m, 0 ≤ Clower m) ∧
          ∀ (T : SmoothCcTensor g 0 2)
            (hT : ∀ (x : M) (u v : TangentSpace I x),
              ccTensorBilin (I := I) g T x u v =
                ccTensorBilin (I := I) g T x v u)
            (hδ : gFibreOpBound (I := I) (M := M) g
              (ccTensorBilinSymm (I := I) g T) δ)
            (hδZ : gFibreOpBound (I := I) (M := M) g
              (ccTensorBilinSymm (I := I) g
                (0 : SmoothCcTensor g 0 2)) δ)
            (hT2 : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R)
            (m : ℕ),
              ‖smoothCcToTensorHs (I := I) (M := M) g (m : ℝ)
                  ((lowerScaleActionCoefficients (I := I) (M := M) g gBase T
                    (lt_of_le_of_lt hδ_le (by norm_num)) hδ hδZ).secondOrderAction
                      (I := I) (M := M) T)‖ ≤
                K * (δ / (1 - δ) ^ 2 + R) *
                    ‖smoothCcToTensorHs (I := I) (M := M) g ((m : ℝ) + 2) T‖ +
                  Clower m *
                    (1 + ‖smoothCcToTensorHs (I := I) (M := M) g (5 : ℝ) T‖) *
                    ‖smoothCcToTensorHs (I := I) (M := M) g ((m : ℝ) + 1) T‖ := by
  classical
  obtain ⟨ρ, K, hρ, hK, hcap⟩ :=
    secondOrderCoefficient_fibre_bound_uniform (I := I) (M := M) hDim gBase hΛ
  refine ⟨ρ, K, hρ, hK, ?_⟩
  intro δ hδ_le hδ0 R hR0 hRρ g hEq hjet
  obtain ⟨Kc, hKc_nn, htower⟩ := secondOrderCoefficient_jet_tower_quadratic (I := I) (M := M) g gBase
  have hε : 0 ≤ K * (δ / (1 - δ) ^ 2 + R) :=
    mul_nonneg hK (add_nonneg (div_nonneg hδ0 (sq_nonneg _)) hR0)
  obtain ⟨Cop, hCop, hop⟩ :=
    operatorFieldApplication_cap_hs_affine_le (I := I) (M := M) g 3 (by omega)
      (K * (δ / (1 - δ) ^ 2 + R)) hε Kc hKc_nn
  refine ⟨Cop, hCop, ?_⟩
  intro T hT hδ hδZ hT2 m
  let A := lowerScaleActionCoefficients (I := I) (M := M) g gBase T
    (lt_of_le_of_lt hδ_le (by norm_num)) hδ hδZ
  have hball : ‖smoothCcToTensorHs (I := I) (M := M) g (((3 : ℕ) : ℝ) + 2) T‖ ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g (5 : ℝ) T‖ :=
    le_of_eq (smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g
      (by push_cast; norm_num) T)
  have hc2pt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 4 2 x (A.secondOrderCoefficient.toSection x) ≤
        (K * (δ / (1 - δ) ^ 2 + R)) ^ 2 := by
    simpa only [A] using
      hcap hδ_le hδ0 hR0 hRρ g hEq hjet T hT hδ hδZ hT2
  have hc2jet : ∀ i : ℕ,
      ‖iteratedCovGrad (I := I) g 4 2 i A.secondOrderCoefficient‖ ^ 2 ≤
        Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) := by
    simpa only [A] using htower T hT hδ0 hδ_le hδ hδZ
  have hshape : A.secondOrderAction (I := I) (M := M) T =
      operatorFieldApply (I := I) (M := M) g (2 + 2) 2 A.secondOrderCoefficient
        (iteratedCovGrad (I := I) g 0 2 2 T) := rfl
  change ‖smoothCcToTensorHs (I := I) (M := M) g (m : ℝ)
      (A.secondOrderAction (I := I) (M := M) T)‖ ≤ _
  rw [hshape]
  exact le_trans (hop (norm_nonneg _) A.secondOrderCoefficient T hball hc2pt hc2jet m) (le_of_eq (by ring))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.secondOrderAction_ladder_affine_uniform then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.secondOrderAction_ladder_affine_uniform"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.secondOrderAction_ladder_affine_uniform ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.secondOrderAction_ladder_affine_uniform

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
