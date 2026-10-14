import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.Pairing.Parametric
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Pairing.FiniteSpectral

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry.Analysis.Spectral

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert

open _root_.Submission.DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

theorem cc_a1_uniform
    (q : SmoothRiemannianMetric I M)
    (ζ : ℝ → C^∞⟮I, M; ℝ⟯) {R K : Set ℝ}
    (hK : IsCompact K) (hKR : K ⊆ R)
    (hζ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ => (ζ p.2 : M → ℝ) p.1)
      ((Set.univ : Set M) ×ˢ R)) (n : ℕ) :
    ∃ Cmid : ℝ, 0 ≤ Cmid ∧
      ∀ t, t ∈ K →
        ∀ (S : Finset
            (DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
              (I := I) (M := M) q 0 0))
          (T : TensorHs (I := I) (M := M) q 0 0 0)
          (hT : (Function.support T.coeff).Finite),
          hT.toFinset ⊆ S →
            2 * ∑ i ∈ S,
                tensorSobolevWeight (I := I) (M := M) i (n : ℝ) *
                  (T.coeff i *
                    tensorL2Coeff (I := I) (M := M)
                      (tensorResolventL2_isCompactOperator
                        (I := I) (M := M) q 0 0)
                      (SmoothCcTensor.toL2
                        (scalarSmul (I := I) (M := M) q 0 0 (ζ t)
                          (tensorHsSmoothRepr (I := I) (M := M) T hT))) i) ≤
              ((1 : ℝ) / 4) *
                  (∑ i ∈ S,
                    tensorSobolevWeight (I := I) (M := M) i
                        ((n + 1 : ℕ) : ℝ) *
                      (T.coeff i) ^ 2) +
                Cmid *
                  (∑ i ∈ S,
                    tensorSobolevWeight (I := I) (M := M) i (n : ℝ) *
                      (T.coeff i) ^ 2) := by
  classical
  obtain ⟨P, hP_nn, hpair⟩ :=
    iterL_smul_uniform (I := I) (M := M) q n ζ hK hKR hζ
  obtain ⟨Clo, hClo_nn, hlo⟩ := hsJet_le (I := I) (M := M) q 0 n
  obtain ⟨Chi, hChi_nn, hhi⟩ := hsJet_le (I := I) (M := M) q 0 (n + 1)
  let Q : ℝ := P * Chi * Clo
  have hQ_nn : 0 ≤ Q := by
    dsimp only [Q]
    positivity
  refine ⟨4 * Q ^ 2, by positivity, ?_⟩
  intro t ht S T hT hsub
  let U : SmoothCcTensor q 0 0 :=
    tensorHsSmoothRepr (I := I) (M := M) T hT
  let A : SmoothCcTensor q 0 0 :=
    scalarSmul (I := I) (M := M) q 0 0 (ζ t) U
  let Jhi : ℝ :=
    ∑ j ∈ Finset.range (n + 2),
      ‖iteratedCovGrad (I := I) q 0 0 j U‖
  let Jlo : ℝ :=
    ∑ j ∈ Finset.range (n + 1),
      ‖iteratedCovGrad (I := I) q 0 0 j U‖
  let Hhi : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) q 0 ((n + 1 : ℕ) : ℝ) U‖
  let Hlo : ℝ := ‖ccTensorToHs (I := I) (M := M) q 0 (n : ℝ) U‖
  have hpairU :
      |tensorL2Inner (I := I) (M := M) q 0 0
          (oneMinusConnLapSmoothIter (I := I) q 0 0 n U).toFun A.toFun| ≤
        P * (Jhi * Jlo) := by
    simpa only [A, Jhi, Jlo] using hpair t ht U
  have hhiU : Jhi ≤ Chi * Hhi := by
    have h := hhi U
    simpa only [Jhi, Hhi, show n + 1 + 1 = n + 2 by omega] using h
  have hloU : Jlo ≤ Clo * Hlo := by
    simpa only [Jlo, Hlo] using hlo U
  have hJhi_nn : 0 ≤ Jhi := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hJlo_nn : 0 ≤ Jlo := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hHhi_nn : 0 ≤ Hhi := norm_nonneg _
  have hHlo_nn : 0 ≤ Hlo := norm_nonneg _
  have hprod : Jhi * Jlo ≤ (Chi * Hhi) * (Clo * Hlo) :=
    mul_le_mul hhiU hloU hJlo_nn (mul_nonneg hChi_nn hHhi_nn)
  have hrem :
      |tensorL2Inner (I := I) (M := M) q 0 0
          (oneMinusConnLapSmoothIter (I := I) q 0 0 n U).toFun A.toFun| ≤
        Q * Hhi * Hlo := by
    calc
      |tensorL2Inner (I := I) (M := M) q 0 0
          (oneMinusConnLapSmoothIter (I := I) q 0 0 n U).toFun A.toFun| ≤
          P * (Jhi * Jlo) := hpairU
      _ ≤ P * ((Chi * Hhi) * (Clo * Hlo)) :=
        mul_le_mul_of_nonneg_left hprod hP_nn
      _ = Q * Hhi * Hlo := by simp only [Q]; ring
  have hsquare : 0 ≤ (Hhi - 4 * Q * Hlo) ^ 2 := sq_nonneg _
  have hsmooth :
      2 * tensorL2Inner (I := I) (M := M) q 0 0
          (oneMinusConnLapSmoothIter (I := I) q 0 0 n U).toFun A.toFun ≤
        ((1 : ℝ) / 4) * Hhi ^ 2 + (4 * Q ^ 2) * Hlo ^ 2 := by
    nlinarith [le_abs_self (tensorL2Inner (I := I) (M := M) q 0 0
      (oneMinusConnLapSmoothIter (I := I) q 0 0 n U).toFun A.toFun)]
  have hhiEnergy : Hhi ^ 2 =
      ∑ i ∈ hT.toFinset,
        tensorSobolevWeight (I := I) (M := M) i ((n + 1 : ℕ) : ℝ) *
          (T.coeff i) ^ 2 := by
    simpa only [Hhi, U] using
      finite_repr_norm (I := I) (M := M) q 0 (n + 1) T hT
  have hloEnergy : Hlo ^ 2 =
      ∑ i ∈ hT.toFinset,
        tensorSobolevWeight (I := I) (M := M) i (n : ℝ) *
          (T.coeff i) ^ 2 := by
    simpa only [Hlo, U] using
      finite_repr_norm (I := I) (M := M) q 0 n T hT
  have hcore :
      2 * ∑ i ∈ hT.toFinset,
          tensorSobolevWeight (I := I) (M := M) i (n : ℝ) *
            (T.coeff i * tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) q 0 0)
              (SmoothCcTensor.toL2 A) i) ≤
        ((1 : ℝ) / 4) *
            (∑ i ∈ hT.toFinset,
              tensorSobolevWeight (I := I) (M := M) i
                  ((n + 1 : ℕ) : ℝ) * (T.coeff i) ^ 2) +
          (4 * Q ^ 2) *
            (∑ i ∈ hT.toFinset,
              tensorSobolevWeight (I := I) (M := M) i (n : ℝ) *
                (T.coeff i) ^ 2) := by
    rw [finite_cc_pair (I := I) (M := M) q 0 n T hT A]
    rw [← hhiEnergy, ← hloEnergy]
    exact hsmooth
  have hcoeff {i} (hi : i ∉ hT.toFinset) : T.coeff i = 0 := by
    by_contra hne
    exact hi (hT.mem_toFinset.mpr (Function.mem_support.mpr hne))
  have hlhs :
      (∑ i ∈ hT.toFinset,
          tensorSobolevWeight (I := I) (M := M) i (n : ℝ) *
            (T.coeff i * tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) q 0 0)
              (SmoothCcTensor.toL2 A) i)) =
        ∑ i ∈ S,
          tensorSobolevWeight (I := I) (M := M) i (n : ℝ) *
            (T.coeff i * tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) q 0 0)
              (SmoothCcTensor.toL2 A) i) := by
    apply Finset.sum_subset hsub
    intro i _ hi
    rw [hcoeff hi, _root_.MulZeroClass.zero_mul, _root_.MulZeroClass.mul_zero]
  have hhigh :
      (∑ i ∈ hT.toFinset,
          tensorSobolevWeight (I := I) (M := M) i ((n + 1 : ℕ) : ℝ) *
            (T.coeff i) ^ 2) =
        ∑ i ∈ S,
          tensorSobolevWeight (I := I) (M := M) i ((n + 1 : ℕ) : ℝ) *
            (T.coeff i) ^ 2 := by
    apply Finset.sum_subset hsub
    intro i _ hi
    norm_num [hcoeff hi]
  have hlow :
      (∑ i ∈ hT.toFinset,
          tensorSobolevWeight (I := I) (M := M) i (n : ℝ) *
            (T.coeff i) ^ 2) =
        ∑ i ∈ S,
          tensorSobolevWeight (I := I) (M := M) i (n : ℝ) *
            (T.coeff i) ^ 2 := by
    apply Finset.sum_subset hsub
    intro i _ hi
    norm_num [hcoeff hi]
  rw [← hlhs, ← hhigh, ← hlow]
  simpa only [A, U] using hcore

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.cc_a1_uniform then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.cc_a1_uniform"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.cc_a1_uniform ``Submission.DifferentialGeometry.Analysis.Spectral.cc_a1_uniform

end DifferentialGeometry.Analysis.Spectral

end
