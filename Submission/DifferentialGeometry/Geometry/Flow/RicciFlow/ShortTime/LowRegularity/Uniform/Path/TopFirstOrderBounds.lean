import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.Coefficients.CurvatureBounds
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.Path.TopDeviationBounds
import Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.LinearMap

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section
set_option backward.isDefEq.respectTransparency false

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.DifferentialGeometry.Tensor0SBundle
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
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Integral.Connection
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

theorem top_path_h1_uniform
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ ρ Ctop Clow : ℝ, 0 < ρ ∧ 0 ≤ Ctop ∧ 0 ≤ Clow ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        (∀ a : ℕ, a ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
        ∀ (T T' : SmoothCcTensor g 0 2)
          {δ : ℝ} (hδ_lt : δ < 1)
          (hδ : gFibreOpBound g
            (ccTensorBilinSymm (I := I) g T) δ)
          {δ' : ℝ} (hδ'_lt : δ' < 1)
          (hδ' : gFibreOpBound g
            (ccTensorBilinSymm (I := I) g T') δ')
          {R : ℝ}, 0 ≤ R → R ≤ ρ →
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R →
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T'‖ ≤ R →
          ∀ U : SmoothCcTensor g 0 2,
            ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
              (operatorFieldApply (I := I) (M := M) g 4 2
                  (rhsTopPathIntegral (I := I) (M := M) g T T'
                    hδ_lt hδ hδ'_lt hδ')
                  (iteratedCovGrad (I := I) g 0 2 2 U) -
                DifferentialGeometry.Analysis.Elliptic.rawTensorConnLapSmooth
                  (I := I) g 0 2 U)‖ ≤
              Ctop * R *
                  ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ +
                Clow *
                  ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ := by
  obtain ⟨ρ, Cdev, hρ, hCdev, hdev⟩ :=
    top_path_dev_uniform (I := I) (M := M) hDim gBase hΛ
  obtain ⟨Capp, hCapp, happ⟩ :=
    operatorFieldApplication_h23_uniform (I := I) (M := M) hDim gBase hΛ
  obtain ⟨Clow, hClow, hlow⟩ :=
    fixed_curv_h1_uniform (I := I) (M := M) hDim gBase hΛ
  refine ⟨ρ, Capp * Cdev, Clow, hρ, mul_nonneg hCapp hCdev, hClow, ?_⟩
  intro g hEq hjet T T' δ hδ_lt hδ δ' hδ'_lt hδ' R hR hRρ hT hT' U
  obtain ⟨_, hdevJet⟩ :=
    hdev g hEq hjet T T' hδ_lt hδ hδ'_lt hδ' hR hRρ hT hT'
  have hA : 0 ≤ Cdev * R := mul_nonneg hCdev hR
  have htop := happ g hEq hjet
    (rhsTopPathIntegral (I := I) (M := M) g T T'
        hδ_lt hδ hδ'_lt hδ' -
      deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g)
    U (Cdev * R) hA hdevJet
  have hlow' := hlow g hEq hjet U
  rw [top_path_split (I := I) (M := M) g T T'
    hδ_lt hδ hδ'_lt hδ' U, ccTensorToHs_add]
  simpa only [mul_assoc, iteratedCovGrad_zero] using
    (norm_add_le _ _).trans (add_le_add htop hlow')

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.top_path_h1_uniform then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.top_path_h1_uniform"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.top_path_h1_uniform ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.top_path_h1_uniform

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
