import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Bounds.Tensor.FiberNorm
import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Bounds.Uniform.FrameEnergy
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Defs
import Mathlib.Topology.Order.Compact

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

variable {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]


omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M]
    [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma metric_inner_self_nonneg
    (g : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x) :
    0 ≤ g.inner x v v := by
  rcases eq_or_ne v 0 with hv0 | hv0
  · rw [hv0]; simp
  · exact (g.pos x v hv0).le

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.metric_inner_self_nonneg
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.metric_inner_self_nonneg target :: scope.openDecls } }

omit [SigmaCompactSpace M] in
theorem exists_continuous_riemannianFiberNormSq_riemannOp_tensorCov_proportional
    (g : SmoothRiemannianMetric I M) (t : ℕ) :
    ∃ Ccurv : M → ℝ, Continuous Ccurv ∧ (∀ x : M, 0 ≤ Ccurv x) ∧
      ∀ (x : M) (v w : TangentSpace I x) (T : TensorRSSpace 0 t I x),
        riemannianFiberNormSq (I := I) (M := M) g 0 t x
            (riemannOp (tensorCov (I := I) g 0 t) x v w T) ≤
          Ccurv x * g.inner x v v * g.inner x w w *
            riemannianFiberNormSq (I := I) (M := M) g 0 t x T := by
  classical
  obtain ⟨Ccurv, hCcurv_cont, hCcurv_nonneg, hCcurv_energy⟩ :=
    exists_continuous_riemannOp_tensorCovS_frameEnergy_bound (I := I) (M := M) g t
  refine ⟨Ccurv, hCcurv_cont, hCcurv_nonneg, ?_⟩
  intro x v w T
  obtain ⟨n, e, horth, hrepr, hvw⟩ :=
    riemannianFiberNormSq_riemannOp_tensorCovS_vw_factor_le (I := I) (M := M) g t x v w T
  have hvv_nonneg : 0 ≤ g.inner x v v := metric_inner_self_nonneg (I := I) (M := M) g x v
  have hww_nonneg : 0 ≤ g.inner x w w := metric_inner_self_nonneg (I := I) (M := M) g x w
  have hvw_nonneg : 0 ≤ g.inner x v v * g.inner x w w := mul_nonneg hvv_nonneg hww_nonneg
  have henergy :
      (∑ i : Fin n, ∑ j : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g 0 t x
            (riemannOp (tensorCov (I := I) g 0 t) x (e i) (e j) T)) ≤
        Ccurv x * riemannianFiberNormSq (I := I) (M := M) g 0 t x T :=
    hCcurv_energy x e horth hrepr T
  calc
    riemannianFiberNormSq (I := I) (M := M) g 0 t x
        (riemannOp (tensorCov (I := I) g 0 t) x v w T)
        ≤ g.inner x v v * g.inner x w w *
            ∑ i : Fin n, ∑ j : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g 0 t x
                (riemannOp (tensorCov (I := I) g 0 t) x (e i) (e j) T) := hvw
    _ ≤ g.inner x v v * g.inner x w w *
            (Ccurv x * riemannianFiberNormSq (I := I) (M := M) g 0 t x T) :=
          mul_le_mul_of_nonneg_left henergy hvw_nonneg
    _ = Ccurv x * g.inner x v v * g.inner x w w *
            riemannianFiberNormSq (I := I) (M := M) g 0 t x T := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.exists_continuous_riemannianFiberNormSq_riemannOp_tensorCov_proportional then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.exists_continuous_riemannianFiberNormSq_riemannOp_tensorCov_proportional"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.exists_continuous_riemannianFiberNormSq_riemannOp_tensorCov_proportional ``Submission.DifferentialGeometry.Analysis.Elliptic.exists_continuous_riemannianFiberNormSq_riemannOp_tensorCov_proportional

omit [SigmaCompactSpace M] in
theorem riemannianFiberNormSq_riemannOp_covGrad_uniform_proportional_bound
    (g : SmoothRiemannianMetric I M) (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (x : M) (v w : TangentSpace I x) (S : SmoothCcTensor g 0 s),
        riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
            (riemannOp (tensorCov (I := I) g 0 (s + 1)) x v w
              ((covGrad (I := I) (M := M) g 0 s S).toSection x)) ≤
          C * g.inner x v v * g.inner x w w *
            riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
              ((covGrad (I := I) (M := M) g 0 s S).toSection x) := by
  classical
  obtain ⟨Ccurv, hCcurv_cont, hCcurv_nonneg, hCcurv_bound⟩ :=
    exists_continuous_riemannianFiberNormSq_riemannOp_tensorCov_proportional
      (I := I) (M := M) g (s + 1)
  have hCpt := (isCompact_univ (X := M)).image hCcurv_cont
  obtain ⟨C₀, hC₀⟩ := hCpt.bddAbove
  refine ⟨max C₀ 0, le_max_right _ _, ?_⟩
  intro x v w S
  have hCcurv_le : Ccurv x ≤ _root_.Max.max C₀ 0 :=
    le_trans (hC₀ ⟨x, Set.mem_univ _, rfl⟩) (le_max_left _ _)
  have hfactor_nonneg :
      0 ≤ g.inner x v v * g.inner x w w *
        riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
          ((covGrad (I := I) (M := M) g 0 s S).toSection x) :=
    mul_nonneg
      (mul_nonneg (metric_inner_self_nonneg (I := I) (M := M) g x v)
        (metric_inner_self_nonneg (I := I) (M := M) g x w))
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1) x _)
  calc
    riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
        (riemannOp (tensorCov (I := I) g 0 (s + 1)) x v w
          ((covGrad (I := I) (M := M) g 0 s S).toSection x))
        ≤ Ccurv x * g.inner x v v * g.inner x w w *
            riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
              ((covGrad (I := I) (M := M) g 0 s S).toSection x) :=
          hCcurv_bound x v w ((covGrad (I := I) (M := M) g 0 s S).toSection x)
    _ = Ccurv x * (g.inner x v v * g.inner x w w *
            riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
              ((covGrad (I := I) (M := M) g 0 s S).toSection x)) := by ring
    _ ≤ _root_.Max.max C₀ 0 * (g.inner x v v * g.inner x w w *
            riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
              ((covGrad (I := I) (M := M) g 0 s S).toSection x)) :=
          mul_le_mul_of_nonneg_right hCcurv_le hfactor_nonneg
    _ = _root_.Max.max C₀ 0 * g.inner x v v * g.inner x w w *
            riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
              ((covGrad (I := I) (M := M) g 0 s S).toSection x) := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.riemannianFiberNormSq_riemannOp_covGrad_uniform_proportional_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.riemannianFiberNormSq_riemannOp_covGrad_uniform_proportional_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.riemannianFiberNormSq_riemannOp_covGrad_uniform_proportional_bound ``Submission.DifferentialGeometry.Analysis.Elliptic.riemannianFiberNormSq_riemannOp_covGrad_uniform_proportional_bound

end Elliptic
end Analysis
end DifferentialGeometry

end
