import Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert.OperatorField.Parametric.ScalarSmulJet
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Jet.Bounds.IteratedCovariantDerivative

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow _root_.Submission.DifferentialGeometry.Analysis.Sobolev
    DifferentialGeometry.Analysis.Spectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

theorem smul_hs_uniform (g : SmoothRiemannianMetric I M)
    (zeta : ℝ → C^∞⟮I, M; ℝ⟯) {S K : Set ℝ}
    (hK : IsCompact K) (hKS : K ⊆ S)
    (hzeta : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ ↦ (zeta p.2 : M → ℝ) p.1)
      ((Set.univ : Set M) ×ˢ S)) :
    ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ t, t ∈ K → ∀ U : SmoothCcTensor g 0 0,
        ‖ccTensorToHs (I := I) (M := M) g 0 (n : ℝ)
            (scalarSmul (I := I) (M := M) g 0 0 (zeta t) U)‖ ≤
          C * ‖ccTensorToHs (I := I) (M := M) g 0 (n : ℝ) U‖ := by
  classical
  obtain ⟨D, hD_nn, hD⟩ :=
    smul_jet_uniform (I := I) (M := M) g zeta hK hKS hzeta
  intro n
  obtain ⟨Cout, hCout_nn, hCout⟩ := hs_le_jet (I := I) (M := M) g 0 n
  obtain ⟨Cin, hCin_nn, hCin⟩ := hsJet_le (I := I) (M := M) g 0 n
  let Dsum : ℝ := ∑ j ∈ Finset.range (n + 1), D j
  have hDsum_nn : 0 ≤ Dsum := by
    exact Finset.sum_nonneg fun j _ ↦ hD_nn j
  refine ⟨Cout * Dsum * Cin, by positivity, ?_⟩
  intro t ht U
  let Jin : ℝ := ∑ j ∈ Finset.range (n + 1),
    ‖iteratedCovGrad (I := I) g 0 0 j U‖
  have hterm (j : ℕ) (hj : j ∈ Finset.range (n + 1)) :
      ‖iteratedCovGrad (I := I) g 0 0 j
          (scalarSmul (I := I) (M := M) g 0 0 (zeta t) U)‖ ≤
        D j * Jin := by
    have hjn : j + 1 ≤ n + 1 :=
      Nat.succ_le_succ (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
    have hsmall :
        (∑ l ∈ Finset.range (j + 1),
            ‖iteratedCovGrad (I := I) g 0 0 l U‖) ≤ Jin := by
      change
        (∑ l ∈ Finset.range (j + 1),
            ‖iteratedCovGrad (I := I) g 0 0 l U‖) ≤
          ∑ l ∈ Finset.range (n + 1),
            ‖iteratedCovGrad (I := I) g 0 0 l U‖
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono hjn) (fun l _ _ ↦ norm_nonneg _)
    exact (hD t ht U j).trans
      (mul_le_mul_of_nonneg_left hsmall (hD_nn j))
  have hsum :
      (∑ j ∈ Finset.range (n + 1),
          ‖iteratedCovGrad (I := I) g 0 0 j
            (scalarSmul (I := I) (M := M) g 0 0 (zeta t) U)‖) ≤
        Dsum * Jin := by
    calc
      (∑ j ∈ Finset.range (n + 1),
          ‖iteratedCovGrad (I := I) g 0 0 j
            (scalarSmul (I := I) (M := M) g 0 0 (zeta t) U)‖) ≤
          ∑ j ∈ Finset.range (n + 1), D j * Jin := by
            exact Finset.sum_le_sum fun j hj ↦ hterm j hj
      _ = Dsum * Jin := by simp only [Dsum, Finset.sum_mul]
  have hJin : Jin ≤ Cin * ‖ccTensorToHs (I := I) (M := M) g 0 (n : ℝ) U‖ := by
    simpa only [Jin] using hCin U
  calc
    ‖ccTensorToHs (I := I) (M := M) g 0 (n : ℝ)
        (scalarSmul (I := I) (M := M) g 0 0 (zeta t) U)‖ ≤
        Cout * (∑ j ∈ Finset.range (n + 1),
          ‖iteratedCovGrad (I := I) g 0 0 j
            (scalarSmul (I := I) (M := M) g 0 0 (zeta t) U)‖) :=
      hCout _
    _ ≤ Cout * (Dsum * Jin) :=
      mul_le_mul_of_nonneg_left hsum hCout_nn
    _ ≤ Cout *
        (Dsum * (Cin * ‖ccTensorToHs (I := I) (M := M) g 0 (n : ℝ) U‖)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hJin hDsum_nn) hCout_nn
    _ = (Cout * Dsum * Cin) *
        ‖ccTensorToHs (I := I) (M := M) g 0 (n : ℝ) U‖ := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.smul_hs_uniform then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.smul_hs_uniform"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.smul_hs_uniform ``Submission.DifferentialGeometry.Analysis.Spectral.smul_hs_uniform

end Spectral
end Analysis
end DifferentialGeometry

end
