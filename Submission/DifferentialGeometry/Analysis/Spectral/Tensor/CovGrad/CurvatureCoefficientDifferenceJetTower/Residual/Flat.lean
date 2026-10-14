import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower.Residual.Cells
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower.Residual.FlatSupremum
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower.Residual.FlatGagliardoNirenberg
import Submission.DifferentialGeometry.Analysis.Sobolev.BoundedFactorGridIntegral

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section


open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization
  (gFibreOpBound ccTensorBilinSymm ccTensorBilin ccTensorBilin_apply ccTensorModel
    ccTensorMultilinear ccTensorBilinSymm_contMDiff ccTensorBilinSymm_apply ccTensorBilinSymm_symm)
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.DeTurck

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

namespace CurvatureCoefficientDifferenceJetTower
end CurvatureCoefficientDifferenceJetTower

open _root_.Submission.DifferentialGeometry.Analysis.Spectral.CurvatureCoefficientDifferenceJetTower

section TopOrderSeparatedResidualIntegrator


theorem boundedFactorGrid_cappedTopLayer_integral_flat
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R) :
    ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (P : SmoothCcTensor g₀ 0 2),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ),
          MeasureTheory.Integrable
              (fun x => Combinatorics.boundedFactorGrid
                (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 2))
              (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
            (∫ x, Combinatorics.boundedFactorGrid
                  (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 2)
                ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
              Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  let : MeasurableSpace M := borel M
  have : BorelSpace M := ⟨rfl⟩
  have : _root_.MeasureTheory.IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  obtain ⟨Cemb, hCemb_nn, hCemb⟩ :=
    DifferentialGeometry.Analysis.Spectral.deTurckSmoothRemainderDiff_supercritical_pointwise_jet_le_fixedWindow
      (I := I) (M := M) g₀ a ha_super
  set Lam : ℝ := Cemb * Real.sqrt ((a + 1 + 1 : ℕ) : ℝ) * R with hLam
  have hLam_nn : 0 ≤ Lam := by rw [hLam]; positivity
  set Cgn : ℕ → ℝ := fun k =>
    if h : 1 ≤ k then
      (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g₀ 0 (2 + 2) k h).choose
    else 0 with hCgn
  have hCgn_nn : ∀ k, 0 ≤ Cgn k := by
    intro k
    simp only [hCgn]
    split_ifs with h
    · exact (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g₀ 0 (2 + 2) k h).choose_spec.1
    · exact le_refl 0
  have hCgn_ch : ∀ (k : ℕ) (hk : 1 ≤ k),
      (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g₀ 0 (2 + 2) k hk).choose = Cgn k := by
    intro k hk
    rw [hCgn]
    simp only [dif_pos hk]
  set vol : ℝ := ((riemannianVolumeMeasure (I := I) (M := M) g₀) Set.univ).toReal with hvol
  have hvol_nn : 0 ≤ vol := ENNReal.toReal_nonneg
  set MB : ℕ → ℝ := fun i => 1 + vol + Lam + ∑ k ∈ Finset.range (i + 1), Cgn k with hMBdef
  have hsumCgn_nn : ∀ i, 0 ≤ ∑ k ∈ Finset.range (i + 1), Cgn k :=
    fun i => Finset.sum_nonneg (fun k _ => hCgn_nn k)
  have hMB1 : ∀ i, 1 ≤ MB i := by
    intro i; rw [hMBdef]
    have := hsumCgn_nn i; linarith
  have hMB_nn : ∀ i, 0 ≤ MB i := fun i => le_trans zero_le_one (hMB1 i)
  have hMB_Lam : ∀ i, Lam ≤ MB i := by
    intro i; rw [hMBdef]; have := hsumCgn_nn i; linarith
  have hMB_vol : ∀ i, vol ≤ MB i := by
    intro i; rw [hMBdef]; have := hsumCgn_nn i; linarith
  have hMB_Cgn : ∀ i k, k ≤ i → Cgn k ≤ MB i := by
    intro i k hk
    rw [hMBdef]
    have hmem : k ∈ Finset.range (i + 1) := Finset.mem_range.mpr (by omega)
    have hle : Cgn k ≤ ∑ k' ∈ Finset.range (i + 1), Cgn k' :=
      Finset.single_le_sum (fun k' _ => hCgn_nn k') hmem
    linarith
  set gcount : ℕ → ℝ := fun i =>
    ∑ n ∈ Finset.range (i + 2 + 1), ((Finset.Nat.antidiagonalTuple n (i + 2)).card : ℝ)
    with hgcount
  have hgcount_nn : ∀ i, 0 ≤ gcount i :=
    fun i => Finset.sum_nonneg (fun n _ => Nat.cast_nonneg _)
  refine ⟨fun i => gcount i * (((i : ℝ) + 2) * MB i ^ (9 * (i + 2))),
    fun i => mul_nonneg (hgcount_nn i)
      (mul_nonneg (by positivity) (pow_nonneg (hMB_nn i) _)), ?_⟩
  intro P hPball i
  have hΛsup_low := fun (m : ℕ) (hm : m ≤ 2) (x : M) =>
    jetSupLow (I := I) (M := M) g₀ hR hCemb hLam P hPball m hm x
  have hΛsup_v2 : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 2) x
        ((iteratedCovGrad (I := I) g₀ 0 2 2 P).toSection x) ≤ Lam ^ 2 :=
    hΛsup_low 2 (le_refl 2)
  have hGNv := fun (i₀ : ℕ) (hi₀ : 1 ≤ i₀) (j : ℕ) (hj0 : 0 < j) (hji : j < i₀) =>
    jetGNInterp (I := I) (M := M) g₀ P hCgn_ch hLam_nn hΛsup_v2 i₀ hi₀ j hj0 hji
  set b : M → ℕ → ℝ := fun x l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
  have hcont : ∀ l : ℕ, Continuous (fun x => b x l) :=
    fun l => riemannianFiberNormSqIterCont (I := I) (M := M) g₀ P l
  have hcell_int : ∀ (n : ℕ) (e : Fin n → ℕ),
      MeasureTheory.Integrable (fun x => ∏ m : Fin n, b x (e m))
        (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    fun n e => Combinatorics.boundedFactorCell_integrable b hcont n e
  have hgrid_int : MeasureTheory.Integrable
      (fun x => Combinatorics.boundedFactorGrid (b x) (i + 1) (i + 2))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    Combinatorics.boundedFactorGrid_integrable b hcont (i + 1) (i + 2)
  refine ⟨hgrid_int, ?_⟩
  have hPT : ∀ n ∈ Finset.range (i + 2 + 1),
      ∀ e ∈ (Finset.Nat.antidiagonalTuple n (i + 2)).filter (fun e => ∀ m, e m ≤ i + 1),
      (∫ x, ∏ m : Fin n, b x (e m) ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
        (((i : ℝ) + 2) * MB i ^ (9 * (i + 2))) *
          (1 + ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
    intro n hn e he
    have hnle : n ≤ i + 2 := by have := Finset.mem_range.mp hn; omega
    have he_sum : ∑ m, e m = i + 2 :=
      Finset.Nat.mem_antidiagonalTuple.mp (Finset.mem_filter.mp he).1
    have he_cap : ∀ m, e m ≤ i + 1 := (Finset.mem_filter.mp he).2
    exact cappedTopLayerCell_integral_le (I := I) (M := M) g₀ P hLam_nn hΛsup_low
      Cgn hCgn_nn hGNv i n e hnle he_sum he_cap (MB i) (hMB1 i) (hMB_Lam i)
      (hMB_vol i) (fun k hk => hMB_Cgn i k hk)
  refine le_trans
    (le_of_eq (Combinatorics.integral_boundedFactorGrid b hcont (i + 1) (i + 2))) ?_
  have hKcell_nn : (0 : ℝ) ≤ ((i : ℝ) + 2) * MB i ^ (9 * (i + 2)) :=
    mul_nonneg (by positivity) (pow_nonneg (hMB_nn i) _)
  have hWsum_nn : (0 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 := by
    have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.range (i + 2)) =>
      sq_nonneg (‖iteratedCovGrad (I := I) g₀ 0 2 j P‖))
    linarith
  calc ∑ n ∈ Finset.range (i + 2 + 1),
        ∑ e ∈ (Finset.Nat.antidiagonalTuple n (i + 2)).filter (fun e => ∀ m, e m ≤ i + 1),
          ∫ x, ∏ m : Fin n, b x (e m) ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)
      ≤ ∑ n ∈ Finset.range (i + 2 + 1),
          ∑ e ∈ (Finset.Nat.antidiagonalTuple n (i + 2)).filter (fun e => ∀ m, e m ≤ i + 1),
            (((i : ℝ) + 2) * MB i ^ (9 * (i + 2))) *
              (1 + ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
        apply Finset.sum_le_sum; intro n hn
        apply Finset.sum_le_sum; intro e he
        exact hPT n hn e he
    _ = (∑ n ∈ Finset.range (i + 2 + 1),
          (((Finset.Nat.antidiagonalTuple n (i + 2)).filter (fun e => ∀ m, e m ≤ i + 1)).card : ℝ)) *
          ((((i : ℝ) + 2) * MB i ^ (9 * (i + 2))) *
            (1 + ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro n _; rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ gcount i *
          ((((i : ℝ) + 2) * MB i ^ (9 * (i + 2))) *
            (1 + ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)) := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg hKcell_nn hWsum_nn)
        rw [hgcount]
        apply Finset.sum_le_sum
        intro n _
        exact_mod_cast Finset.card_filter_le _ _
    _ = gcount i * (((i : ℝ) + 2) * MB i ^ (9 * (i + 2))) *
          (1 + ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) :=
        (mul_assoc _ _ _).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.boundedFactorGrid_cappedTopLayer_integral_flat then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.boundedFactorGrid_cappedTopLayer_integral_flat"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.boundedFactorGrid_cappedTopLayer_integral_flat ``Submission.DifferentialGeometry.Analysis.Spectral.boundedFactorGrid_cappedTopLayer_integral_flat

end TopOrderSeparatedResidualIntegrator

end Spectral
end Analysis
end DifferentialGeometry

end
