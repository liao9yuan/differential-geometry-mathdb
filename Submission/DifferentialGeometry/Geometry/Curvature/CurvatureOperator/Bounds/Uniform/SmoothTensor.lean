import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Bounds.Tensor.Pointwise
import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Identities.TensorThirdOrder
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Defs
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.UniformChartBounds.FiberNorm.UniformBound

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Geometry.Curvature


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.FiberBundle _root_.NormedSpace _root_.Filter _root_.CovariantDerivative _root_.Submission.CovariantDerivative _root_.Submission.DifferentialGeometry.Geometry.Curvature.CovariantDerivative
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Elliptic

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M]
variable [CompleteSpace E]

def curvatureContraction
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Z : SmoothCcTensor g 0 s)
    {X Y : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    SmoothCcTensor g 0 s where
  toSection :=
    { toFun := fun b : M => riemannSec (tensorCov (I := I) g 0 s) X Y
        (fun y : M => Z.toSection y) b
      contMDiff_toFun :=
        riemannSec_contMDiff (cov := tensorCov (I := I) g 0 s) hX hY Z.toSection.contMDiff }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.curvatureContraction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.curvatureContraction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.curvatureContraction ``Submission.DifferentialGeometry.Analysis.Elliptic.curvatureContraction


omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma curvatureContraction_toSection_eq_riemannSec
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Z : SmoothCcTensor g 0 s)
    {X Y : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) (x : M) :
    (curvatureContraction (I := I) (M := M) g s Z hX hY).toSection x =
      riemannSec (tensorCov (I := I) g 0 s) X Y (fun y : M => Z.toSection y) x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.curvatureContraction_toSection_eq_riemannSec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.curvatureContraction_toSection_eq_riemannSec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.curvatureContraction_toSection_eq_riemannSec ``Submission.DifferentialGeometry.Analysis.Elliptic.curvatureContraction_toSection_eq_riemannSec


omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem curvatureContraction_toSection_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Z : SmoothCcTensor g 0 s)
    {X Y : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) (x : M) :
    (curvatureContraction (I := I) (M := M) g s Z hX hY).toSection x =
      riemannOp (tensorCov (I := I) g 0 s) x (X x) (Y x) (Z.toSection x) := by
  rw [curvatureContraction_toSection_eq_riemannSec]
  exact riemannSec_eq_riemannOp_smooth (cov := tensorCov (I := I) g 0 s) hX hY
    Z.toSection.contMDiff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.curvatureContraction_toSection_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.curvatureContraction_toSection_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.curvatureContraction_toSection_apply ``Submission.DifferentialGeometry.Analysis.Elliptic.curvatureContraction_toSection_apply


omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_uniform_riemannianFiberNormSq_riemannOp_bound
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Z : SmoothCcTensor g 0 s)
    {X Y : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    ∃ K_R : ℝ, 0 ≤ K_R ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 s x
        (riemannOp (tensorCov (I := I) g 0 s) x (X x) (Y x) (Z.toSection x)) ≤ K_R := by
  obtain ⟨K_R, hK_nonneg, hK⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor g 0 s
      (curvatureContraction (I := I) (M := M) g s Z hX hY)
  refine ⟨K_R, hK_nonneg, fun x => ?_⟩
  have hx := hK x
  rwa [curvatureContraction_toSection_apply (I := I) (M := M) g s Z hX hY x] at hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.exists_uniform_riemannianFiberNormSq_riemannOp_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.exists_uniform_riemannianFiberNormSq_riemannOp_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.exists_uniform_riemannianFiberNormSq_riemannOp_bound ``Submission.DifferentialGeometry.Analysis.Elliptic.exists_uniform_riemannianFiberNormSq_riemannOp_bound

def covGradCurvatureContraction
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Z : SmoothCcTensor g 0 s)
    {X Y : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    SmoothCcTensor g 0 (s + 1) :=
  covGrad g 0 s (curvatureContraction (I := I) (M := M) g s Z hX hY)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.covGradCurvatureContraction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.covGradCurvatureContraction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.covGradCurvatureContraction ``Submission.DifferentialGeometry.Analysis.Elliptic.covGradCurvatureContraction


omit [NeZero (Module.finrank ℝ E)] in
lemma covGradCurvatureContraction_toSection
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Z : SmoothCcTensor g 0 s)
    {X Y : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    (covGradCurvatureContraction (I := I) (M := M) g s Z hX hY).toSection =
      (covGrad g 0 s (curvatureContraction (I := I) (M := M) g s Z hX hY)).toSection := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.covGradCurvatureContraction_toSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.covGradCurvatureContraction_toSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.covGradCurvatureContraction_toSection ``Submission.DifferentialGeometry.Analysis.Elliptic.covGradCurvatureContraction_toSection


omit [NeZero (Module.finrank ℝ E)] in
theorem exists_uniform_riemannianFiberNormSq_covGrad_riemannOp_bound
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Z : SmoothCcTensor g 0 s)
    {X Y : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    ∃ KgradR : ℝ, 0 ≤ KgradR ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
        ((covGradCurvatureContraction (I := I) (M := M) g s Z hX hY).toSection x) ≤ KgradR :=
  exists_bound_riemannianFiberNormSq_smoothCcTensor g 0 (s + 1)
    (covGradCurvatureContraction (I := I) (M := M) g s Z hX hY)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.exists_uniform_riemannianFiberNormSq_covGrad_riemannOp_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.exists_uniform_riemannianFiberNormSq_covGrad_riemannOp_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.exists_uniform_riemannianFiberNormSq_covGrad_riemannOp_bound ``Submission.DifferentialGeometry.Analysis.Elliptic.exists_uniform_riemannianFiberNormSq_covGrad_riemannOp_bound

end Elliptic
end Analysis
end DifferentialGeometry

end
