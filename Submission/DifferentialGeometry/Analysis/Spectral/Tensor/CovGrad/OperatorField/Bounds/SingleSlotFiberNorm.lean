import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorField.Calculus.Covariant

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

private local instance tensorRSRiemannianNormedAddCommGroup_local
    (r s : ℕ) [h : Bundle.RiemannianBundle (fun b : M ↦ TensorRSSpace r s I b)] (b : M) :
    NormedAddCommGroup (TensorRSSpace r s I b) :=
  (h.g.toCore b).toNormedAddCommGroupOfTopology
    (h.g.continuousAt b) (h.g.isVonNBounded b)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.tensorRSRiemannianNormedAddCommGroup_local
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.tensorRSRiemannianNormedAddCommGroup_local target :: scope.openDecls } }

attribute [-instance] Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
omit [CompleteSpace E] in
lemma riemannianFiberNormSq_eq_bundle_norm_sq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) (z : TensorRSSpace r s I x) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g r s
    riemannianFiberNormSq (I := I) (M := M) g r s x z = ‖z‖ ^ 2 := by
  let : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g r s
  have h_inner :
      (DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM
          (I := I) (M := M) g r s x z z : ℝ) =
        riemannianFiberNormSq (I := I) (M := M) g r s x z := by
    rw [DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM_apply]
    exact (riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x z).symm
  have hself : (_root_.Inner.inner ℝ z z : ℝ) =
      riemannianFiberNormSq (I := I) (M := M) g r s x z := by
    rw [← h_inner]; rfl
  rw [← hself, real_inner_self_eq_norm_sq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.riemannianFiberNormSq_eq_bundle_norm_sq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.riemannianFiberNormSq_eq_bundle_norm_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.riemannianFiberNormSq_eq_bundle_norm_sq ``Submission.DifferentialGeometry.Analysis.Spectral.riemannianFiberNormSq_eq_bundle_norm_sq

attribute [-instance] Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] [CompleteSpace E] in
theorem riemannianFiberNormSq_clm_apply_le_of_sqrt_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (φ : TensorRSSpace 0 r I x →L[ℝ] TensorRSSpace 0 s I x) (μ : ℝ) (hμ : 0 ≤ μ)
    (hbound : ∀ v : TensorRSSpace 0 r I x,
      Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 s x (φ v)) ≤
        μ * Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 r x v)) :
    ∀ v : TensorRSSpace 0 r I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 s x (φ v) ≤
        μ ^ 2 * riemannianFiberNormSq (I := I) (M := M) g 0 r x v := by
  let instSource : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 r I b) :=
    Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g 0 r
  let instTarget : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 s I b) :=
    Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g 0 s
  intro v
  have hsrc_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g 0 r x v :=
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 r x v
  have htgt_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g 0 s x (φ v) :=
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 s x (φ v)
  have hb := hbound v
  have hrhs_nn : 0 ≤ μ * Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 r x v) :=
    mul_nonneg hμ (Real.sqrt_nonneg _)
  have hsq :
      (Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 s x (φ v))) ^ 2 ≤
        (μ * Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 r x v)) ^ 2 := by
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hb 2
  rw [Real.sq_sqrt htgt_nn] at hsq
  rw [mul_pow, Real.sq_sqrt hsrc_nn] at hsq
  exact hsq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.riemannianFiberNormSq_clm_apply_le_of_sqrt_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.riemannianFiberNormSq_clm_apply_le_of_sqrt_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.riemannianFiberNormSq_clm_apply_le_of_sqrt_le ``Submission.DifferentialGeometry.Analysis.Spectral.riemannianFiberNormSq_clm_apply_le_of_sqrt_le

end Spectral
end Analysis
end DifferentialGeometry

end
