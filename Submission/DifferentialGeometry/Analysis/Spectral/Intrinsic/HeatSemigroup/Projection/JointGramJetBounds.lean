import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.Spectral.MassUniformBound
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.Regularity.InteriorTimeSmoothing
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.Spectral.SmoothRepresentativeRealization
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.Reconstruction.TensorHilbertSobolev
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.Spectrum.EigenCombination
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.Chart.MetricGramDifference
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.Chart.RawComponentIdentification
import Submission.DifferentialGeometry.Analysis.Sobolev.Embedding.CovariantDerivative.OrderDropping
import Submission.DifferentialGeometry.Analysis.Calculus.Smoothness.Tsum
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SmoothSection.CompactChartJetBound
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Spectrum.WeylSummability
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Spectrum.SobolevDecay
import Submission.DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.Regularity.JointChart
import Submission.DifferentialGeometry.Analysis.Elliptic.TensorRegularity.DirichletForm.RotatedTestSection
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SmoothSection.SmoothTensorAllOrderCompleteness
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.Representation.TensorReprFromFrame
import Submission.DifferentialGeometry.Analysis.Calculus.Smoothness.AnisotropicJoint

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter _root_.Topology
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Calculus

open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Integral.Measure

open _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Tensor
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Tensor
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private lemma norm_iteratedFDeriv_clm_le
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : F →L[ℝ] G) (i : ℕ) (hi : 1 ≤ i) (x : F) :
    ‖iteratedFDeriv ℝ i (fun p => L p) x‖ ≤ (‖L‖ + 1) ^ i := by
  have hD1 : (1 : ℝ) ≤ ‖L‖ + 1 := by have := norm_nonneg L; linarith
  rcases Nat.lt_or_ge i 2 with hlt | hge
  · interval_cases i
    rw [norm_iteratedFDeriv_one, ContinuousLinearMap.fderiv]
    simp only [pow_one]; linarith [norm_nonneg L]
  · obtain ⟨j, rfl⟩ : ∃ jj, i = (jj + 1) + 1 := ⟨i - 2, by omega⟩
    have hz : ‖iteratedFDeriv ℝ ((j + 1) + 1) (fun p => L p) x‖ = 0 := by
      rw [← norm_iteratedFDeriv_fderiv]
      have hfd : fderiv ℝ (fun p => L p) = fun _ : F => (L : F →L[ℝ] G) := by
        funext y; exact ContinuousLinearMap.fderiv L
      rw [hfd, iteratedFDeriv_const_of_ne (by omega) (L : F →L[ℝ] G)]
      simp
    rw [hz]; positivity

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Calculus.norm_iteratedFDeriv_clm_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Calculus.norm_iteratedFDeriv_clm_le target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma norm_iteratedFDerivWithin_compFst_le
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) {a bb : ℝ} {B : Set E}
    (hUD : UniqueDiffOn ℝ (Set.Icc a bb ×ˢ B)) (hab : a < bb)
    (n : ℕ) (q : ℝ × E) (hq : q ∈ Set.Icc a bb ×ˢ B)
    (C : ℝ) (hC : ∀ j ≤ n, ‖iteratedDeriv j f q.1‖ ≤ C) :
    ‖iteratedFDerivWithin ℝ n (fun p : ℝ × E => f p.1) (Set.Icc a bb ×ˢ B) q‖ ≤
      (n.factorial : ℝ) * C * (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ n := by
  classical
  set s := Set.Icc a bb ×ˢ B with hs_def
  set t := Set.Icc a bb with ht_def
  set L : (ℝ × E) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ E with hL_def
  have hUDt : UniqueDiffOn ℝ t := uniqueDiffOn_Icc hab
  have hmaps : Set.MapsTo (fun p : ℝ × E => p.1) s t := fun p hp => hp.1
  have hbound := norm_iteratedFDerivWithin_comp_le (𝕜 := ℝ) (g := f)
    (f := fun p : ℝ × E => p.1) (n := n) (s := s) (t := t) (x := q) (N := ∞)
    hf.contDiffOn contDiffOn_fst (by exact_mod_cast le_top) hUDt hUD hmaps hq
    (C := C) (D := ‖L‖ + 1)
    (fun i hi => by
      have heq : iteratedFDerivWithin ℝ i f t q.1 = iteratedFDeriv ℝ i f q.1 :=
        iteratedFDerivWithin_eq_iteratedFDeriv hUDt
          (hf.contDiffAt.of_le (by exact_mod_cast le_top)) (hmaps hq)
      rw [heq, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      exact hC i hi)
    (fun i hi1 hin => by
      have hwithin : iteratedFDerivWithin ℝ i (fun p : ℝ × E => p.1) s q =
          iteratedFDeriv ℝ i (fun p : ℝ × E => p.1) q :=
        iteratedFDerivWithin_eq_iteratedFDeriv hUD
          ((contDiff_fst (𝕜 := ℝ)).contDiffAt.of_le (by exact_mod_cast le_top)) hq
      rw [hwithin]
      exact norm_iteratedFDeriv_clm_le L i hi1 q)
  have hcomp : (f ∘ (fun p : ℝ × E => p.1)) = (fun p : ℝ × E => f p.1) := rfl
  rw [hcomp] at hbound
  exact hbound

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Calculus.norm_iteratedFDerivWithin_compFst_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Calculus.norm_iteratedFDerivWithin_compFst_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Calculus.norm_iteratedFDerivWithin_compFst_le ``Submission.DifferentialGeometry.Analysis.Calculus.norm_iteratedFDerivWithin_compFst_le

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma norm_iteratedFDerivWithin_compSnd_le
    (spatial : E → ℝ) {O : Set E} (hO_open : IsOpen O)
    (hspatial : ContDiffOn ℝ ∞ spatial O)
    {a bb : ℝ} {B : Set E} (hBO : B ⊆ O)
    (hUD : UniqueDiffOn ℝ (Set.Icc a bb ×ˢ B))
    (n : ℕ) (q : ℝ × E) (hq : q ∈ Set.Icc a bb ×ˢ B)
    (C : ℝ) (hC : ∀ j ≤ n, ‖iteratedFDerivWithin ℝ j spatial O q.2‖ ≤ C) :
    ‖iteratedFDerivWithin ℝ n (fun p : ℝ × E => spatial p.2) (Set.Icc a bb ×ˢ B) q‖ ≤
      (n.factorial : ℝ) * C * (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ n := by
  classical
  set s := Set.Icc a bb ×ˢ B with hs_def
  set L : (ℝ × E) →L[ℝ] E := ContinuousLinearMap.snd ℝ ℝ E with hL_def
  have hUDO : UniqueDiffOn ℝ O := hO_open.uniqueDiffOn
  have hmaps : Set.MapsTo (fun p : ℝ × E => p.2) s O := fun p hp => hBO hp.2
  have hbound := norm_iteratedFDerivWithin_comp_le (𝕜 := ℝ) (g := spatial)
    (f := fun p : ℝ × E => p.2) (n := n) (s := s) (t := O) (x := q) (N := ∞)
    hspatial contDiffOn_snd (by exact_mod_cast le_top) hUDO hUD hmaps hq
    (C := C) (D := ‖L‖ + 1)
    (fun i hi => hC i hi)
    (fun i hi1 hin => by
      have hwithin : iteratedFDerivWithin ℝ i (fun p : ℝ × E => p.2) s q =
          iteratedFDeriv ℝ i (fun p : ℝ × E => p.2) q :=
        iteratedFDerivWithin_eq_iteratedFDeriv hUD
          ((contDiff_snd (𝕜 := ℝ)).contDiffAt.of_le (by exact_mod_cast le_top)) hq
      rw [hwithin]
      exact norm_iteratedFDeriv_clm_le L i hi1 q)
  have hcomp : (spatial ∘ (fun p : ℝ × E => p.2)) = (fun p : ℝ × E => spatial p.2) := rfl
  rw [hcomp] at hbound
  exact hbound

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Calculus.norm_iteratedFDerivWithin_compSnd_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Calculus.norm_iteratedFDerivWithin_compSnd_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Calculus.norm_iteratedFDerivWithin_compSnd_le ``Submission.DifferentialGeometry.Analysis.Calculus.norm_iteratedFDerivWithin_compSnd_le

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma norm_iteratedFDerivWithin_compFst_le_ofOrder
    (kk : ℕ) (f : ℝ → ℝ) (hf : ContDiff ℝ (kk : ℕ) f) {a bb : ℝ} {B : Set E}
    (hUD : UniqueDiffOn ℝ (Set.Icc a bb ×ˢ B)) (hab : a < bb)
    (n : ℕ) (hn : n ≤ kk) (q : ℝ × E) (hq : q ∈ Set.Icc a bb ×ˢ B)
    (C : ℝ) (hC : ∀ j ≤ n, ‖iteratedDeriv j f q.1‖ ≤ C) :
    ‖iteratedFDerivWithin ℝ n (fun p : ℝ × E => f p.1) (Set.Icc a bb ×ˢ B) q‖ ≤
      (n.factorial : ℝ) * C * (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ n := by
  classical
  set s := Set.Icc a bb ×ˢ B with hs_def
  set t := Set.Icc a bb with ht_def
  set L : (ℝ × E) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ E with hL_def
  have hUDt : UniqueDiffOn ℝ t := uniqueDiffOn_Icc hab
  have hmaps : Set.MapsTo (fun p : ℝ × E => p.1) s t := fun p hp => hp.1
  have hbound := norm_iteratedFDerivWithin_comp_le (𝕜 := ℝ) (g := f)
    (f := fun p : ℝ × E => p.1) (n := n) (s := s) (t := t) (x := q)
    (N := ((kk : ℕ) : WithTop ℕ∞))
    hf.contDiffOn contDiffOn_fst (by exact_mod_cast hn) hUDt hUD hmaps hq
    (C := C) (D := ‖L‖ + 1)
    (fun i hi => by
      have heq : iteratedFDerivWithin ℝ i f t q.1 = iteratedFDeriv ℝ i f q.1 :=
        iteratedFDerivWithin_eq_iteratedFDeriv hUDt
          (hf.contDiffAt.of_le (by exact_mod_cast le_trans hi hn)) (hmaps hq)
      rw [heq, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      exact hC i hi)
    (fun i hi1 hin => by
      have hwithin : iteratedFDerivWithin ℝ i (fun p : ℝ × E => p.1) s q =
          iteratedFDeriv ℝ i (fun p : ℝ × E => p.1) q :=
        iteratedFDerivWithin_eq_iteratedFDeriv hUD
          ((contDiff_fst (𝕜 := ℝ)).contDiffAt.of_le (by exact_mod_cast le_top)) hq
      rw [hwithin]
      exact norm_iteratedFDeriv_clm_le L i hi1 q)
  have hcomp : (f ∘ (fun p : ℝ × E => p.1)) = (fun p : ℝ × E => f p.1) := rfl
  rw [hcomp] at hbound
  exact hbound

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Calculus.norm_iteratedFDerivWithin_compFst_le_ofOrder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Calculus.norm_iteratedFDerivWithin_compFst_le_ofOrder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Calculus.norm_iteratedFDerivWithin_compFst_le_ofOrder ``Submission.DifferentialGeometry.Analysis.Calculus.norm_iteratedFDerivWithin_compFst_le_ofOrder

end Calculus
end Analysis
end DifferentialGeometry

end
