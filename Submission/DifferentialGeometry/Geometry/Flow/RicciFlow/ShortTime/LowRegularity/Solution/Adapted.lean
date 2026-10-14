import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Solution.SecondOrderExistence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Energy.Absorption

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.NNReal _root_.InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.Connection
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization
open _root_.Submission.DifferentialGeometry.Analysis.Spectral (ccTensorToHs)

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

def IsAdaptedLowRegularitySolution (g₀ : SmoothRiemannianMetric I M)
    {δ Ctop B0 B1 D ρ P T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (fLo : timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (Rcap Ctop₂ Kr2 Kr1 Kcap : ℝ) : Prop :=
  IsLowRegularitySolutionAt (I := I) (M := M) (δ := δ) (Ctop := Ctop) (B0 := B0)
      (B1 := B1) (D := D) (ρ := ρ) (P := P) g₀ hT hT1 fLo Rcap ∧
    HasGalerkinEnergyThreeBound (I := I) (M := M) g₀ Ctop₂ Kr2 Kr1 Kcap ∧
    ∃ A B : ℝ, HasEnergyLadderAbsorptionConstants (I := I) (M := M) g₀ A B ∧
      Ctop₂ * Kcap ≤ A ∧ Kr2 + Kr1 ≤ B ∧
      ∃ ε : ℝ, 0 < ε ∧
        A * (δ / (1 - δ) ^ 2) +
          B * lowRegularityStateRadius Ctop B1 ρ P + ε < 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsAdaptedLowRegularitySolution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsAdaptedLowRegularitySolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsAdaptedLowRegularitySolution ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsAdaptedLowRegularitySolution

theorem IsAdaptedLowRegularitySolution.toIsLowRegularitySolutionAt {g₀ : SmoothRiemannianMetric I M}
    {δ Ctop B0 B1 D ρ P T Rcap Ctop₂ Kr2 Kr1 Kcap : ℝ}
    {hT : 0 < T} {hT1 : T ≤ 1}
    {fLo : timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T}
    (h : IsAdaptedLowRegularitySolution (I := I) (M := M) (δ := δ) (Ctop := Ctop)
      (B0 := B0) (B1 := B1) (D := D) (ρ := ρ) (P := P)
      g₀ hT hT1 fLo Rcap Ctop₂ Kr2 Kr1 Kcap) :
    IsLowRegularitySolutionAt (I := I) (M := M) (δ := δ) (Ctop := Ctop) (B0 := B0)
      (B1 := B1) (D := D) (ρ := ρ) (P := P) g₀ hT hT1 fLo Rcap :=
  h.1

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsAdaptedLowRegularitySolution
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsAdaptedLowRegularitySolution.toIsLowRegularitySolutionAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsAdaptedLowRegularitySolution.toIsLowRegularitySolutionAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsAdaptedLowRegularitySolution.toIsLowRegularitySolutionAt ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsAdaptedLowRegularitySolution.toIsLowRegularitySolutionAt

theorem IsAdaptedLowRegularitySolution.toIsLowRegularitySolution {g₀ : SmoothRiemannianMetric I M}
    {δ Ctop B0 B1 D ρ P T Rcap Ctop₂ Kr2 Kr1 Kcap : ℝ}
    {hT : 0 < T} {hT1 : T ≤ 1}
    {fLo : timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T}
    (h : IsAdaptedLowRegularitySolution (I := I) (M := M) (δ := δ) (Ctop := Ctop)
      (B0 := B0) (B1 := B1) (D := D) (ρ := ρ) (P := P)
      g₀ hT hT1 fLo Rcap Ctop₂ Kr2 Kr1 Kcap) :
    IsLowRegularitySolution (I := I) (M := M) g₀ hT fLo :=
  h.toIsLowRegularitySolutionAt.toIsLowRegularitySolution

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsAdaptedLowRegularitySolution.toIsLowRegularitySolution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsAdaptedLowRegularitySolution.toIsLowRegularitySolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsAdaptedLowRegularitySolution.toIsLowRegularitySolution ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsAdaptedLowRegularitySolution.toIsLowRegularitySolution

theorem IsAdaptedLowRegularitySolution.toHasGalerkinEnergyThreeBound {g₀ : SmoothRiemannianMetric I M}
    {δ Ctop B0 B1 D ρ P T Rcap Ctop₂ Kr2 Kr1 Kcap : ℝ}
    {hT : 0 < T} {hT1 : T ≤ 1}
    {fLo : timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T}
    (h : IsAdaptedLowRegularitySolution (I := I) (M := M) (δ := δ) (Ctop := Ctop)
      (B0 := B0) (B1 := B1) (D := D) (ρ := ρ) (P := P)
      g₀ hT hT1 fLo Rcap Ctop₂ Kr2 Kr1 Kcap) :
    HasGalerkinEnergyThreeBound (I := I) (M := M) g₀ Ctop₂ Kr2 Kr1 Kcap :=
  h.2.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsAdaptedLowRegularitySolution.toHasGalerkinEnergyThreeBound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsAdaptedLowRegularitySolution.toHasGalerkinEnergyThreeBound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsAdaptedLowRegularitySolution.toHasGalerkinEnergyThreeBound ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsAdaptedLowRegularitySolution.toHasGalerkinEnergyThreeBound

theorem IsAdaptedLowRegularitySolution.exists_absorption_constants_and_margin {g₀ : SmoothRiemannianMetric I M}
    {δ Ctop B0 B1 D ρ P T Rcap Ctop₂ Kr2 Kr1 Kcap : ℝ}
    {hT : 0 < T} {hT1 : T ≤ 1}
    {fLo : timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T}
    (h : IsAdaptedLowRegularitySolution (I := I) (M := M) (δ := δ) (Ctop := Ctop)
      (B0 := B0) (B1 := B1) (D := D) (ρ := ρ) (P := P)
      g₀ hT hT1 fLo Rcap Ctop₂ Kr2 Kr1 Kcap) :
    ∃ A B : ℝ, HasEnergyLadderAbsorptionConstants (I := I) (M := M) g₀ A B ∧
      Ctop₂ * Kcap ≤ A ∧ Kr2 + Kr1 ≤ B ∧
      ∃ ε : ℝ, 0 < ε ∧
        A * (δ / (1 - δ) ^ 2) +
          B * lowRegularityStateRadius Ctop B1 ρ P + ε < 1 :=
  h.2.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsAdaptedLowRegularitySolution.exists_absorption_constants_and_margin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsAdaptedLowRegularitySolution.exists_absorption_constants_and_margin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsAdaptedLowRegularitySolution.exists_absorption_constants_and_margin ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsAdaptedLowRegularitySolution.exists_absorption_constants_and_margin

theorem IsAdaptedLowRegularitySolution.absorb {g₀ : SmoothRiemannianMetric I M}
    {δ Ctop B0 B1 D ρ P T Rcap Ctop₂ Kr2 Kr1 Kcap : ℝ}
    {hT : 0 < T} {hT1 : T ≤ 1}
    {fLo : timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T}
    (h : IsAdaptedLowRegularitySolution (I := I) (M := M) (δ := δ) (Ctop := Ctop)
      (B0 := B0) (B1 := B1) (D := D) (ρ := ρ) (P := P)
      g₀ hT hT1 fLo Rcap Ctop₂ Kr2 Kr1 Kcap) :
    ∃ ε : ℝ, 0 < ε ∧
      Ctop₂ * (Kcap * (δ / (1 - δ) ^ 2)) +
          Kr2 * lowRegularityStateRadius Ctop B1 ρ P +
          Kr1 * lowRegularityStateRadius Ctop B1 ρ P + ε < 1 :=
  by
    obtain ⟨A, B, _hgate, hA, hB, ε, hε, hbudget⟩ := h.exists_absorption_constants_and_margin
    have hR : 0 ≤ lowRegularityStateRadius Ctop B1 ρ P :=
      (lowRegularityStateRadius_pos h.1.top_nonneg h.1.slope_nonneg h.1.outer_pos h.1.realize_pos).le
    have hdom := energyLadder_absorption_coefficient_le hA hB h.1.threshold_nonneg hR
    exact ⟨ε, hε, by linarith only [hdom, hbudget]⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsAdaptedLowRegularitySolution.absorb then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsAdaptedLowRegularitySolution.absorb"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsAdaptedLowRegularitySolution.absorb ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsAdaptedLowRegularitySolution.absorb

theorem exists_absorption_radius_and_margin {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ δ Rcap ε : ℝ,
      0 < δ ∧ δ ≤ 1 / 3 ∧ 0 < Rcap ∧ 0 < ε ∧
      ∀ {R : ℝ}, R ≤ Rcap →
        A * (δ / (1 - δ) ^ 2) + B * R + ε < 1 := by
  let δ : ℝ := 1 / (16 * (A + 1))
  let Rcap : ℝ := 1 / (8 * (B + 1))
  have hδpos : 0 < δ := by
    dsimp [δ]
    positivity
  have hδ16 : δ ≤ 1 / 16 := by
    dsimp [δ]
    exact one_div_le_one_div_of_le (by norm_num) (by nlinarith [hA])
  have hδ3 : δ ≤ 1 / 3 := hδ16.trans (by norm_num)
  have hRpos : 0 < Rcap := by
    dsimp [Rcap]
    positivity
  refine ⟨δ, Rcap, 1 / 4, hδpos, hδ3, hRpos, by norm_num, ?_⟩
  intro R hR
  have h1δ : 0 < 1 - δ := by nlinarith
  have hden : 0 < (1 - δ) ^ 2 := pow_pos h1δ 2
  have hsq : (1 / 2 : ℝ) ≤ (1 - δ) ^ 2 := by
    nlinarith [sq_nonneg δ]
  have hrate : δ / (1 - δ) ^ 2 ≤ 2 * δ := by
    rw [div_le_iff₀ hden]
    have hm := mul_le_mul_of_nonneg_left hsq hδpos.le
    nlinarith [hm]
  have hAδ : A * δ ≤ 1 / 16 := by
    have hA1 : A + 1 ≠ 0 := by nlinarith [hA]
    dsimp [δ]
    calc
      A * (1 / (16 * (A + 1))) ≤
          (A + 1) * (1 / (16 * (A + 1))) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = 1 / 16 := by field_simp [hA1]
  have hgate : A * (δ / (1 - δ) ^ 2) ≤ 1 / 8 := by
    calc
      A * (δ / (1 - δ) ^ 2) ≤ A * (2 * δ) :=
        mul_le_mul_of_nonneg_left hrate hA
      _ ≤ 1 / 8 := by nlinarith [hAδ]
  have hBR : B * Rcap ≤ 1 / 8 := by
    have hB1 : B + 1 ≠ 0 := by nlinarith [hB]
    dsimp [Rcap]
    calc
      B * (1 / (8 * (B + 1))) ≤
          (B + 1) * (1 / (8 * (B + 1))) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = 1 / 8 := by field_simp [hB1]
  have hrad : B * R ≤ 1 / 8 :=
    (mul_le_mul_of_nonneg_left hR hB).trans hBR
  nlinarith [hgate, hrad]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_absorption_radius_and_margin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_absorption_radius_and_margin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_absorption_radius_and_margin ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_absorption_radius_and_margin

theorem exists_lowRegularity_absorption_radius_and_margin {Ctop₂ Kr2 Kr1 Kcap : ℝ}
    (hCtop₂ : 0 ≤ Ctop₂) (hKr2 : 0 ≤ Kr2)
    (hKr1 : 0 ≤ Kr1) (hKcap : 0 ≤ Kcap) :
    ∃ δ Rcap ε : ℝ,
      0 < δ ∧ δ ≤ 1 / 3 ∧ 0 < Rcap ∧ 0 < ε ∧
      ∀ {R : ℝ}, R ≤ Rcap →
        Ctop₂ * (Kcap * (δ / (1 - δ) ^ 2)) +
          Kr2 * R + Kr1 * R + ε < 1 := by
  obtain ⟨δ, Rcap, ε, hδ, hδ3, hRcap, hε, hbudget⟩ :=
    exists_absorption_radius_and_margin (A := Ctop₂ * Kcap) (B := Kr2 + Kr1)
      (mul_nonneg hCtop₂ hKcap) (add_nonneg hKr2 hKr1)
  refine ⟨δ, Rcap, ε, hδ, hδ3, hRcap, hε, ?_⟩
  intro R hR
  calc
    Ctop₂ * (Kcap * (δ / (1 - δ) ^ 2)) + Kr2 * R + Kr1 * R + ε =
        (Ctop₂ * Kcap) * (δ / (1 - δ) ^ 2) + (Kr2 + Kr1) * R + ε := by
          ring
    _ < 1 := hbudget hR

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_lowRegularity_absorption_radius_and_margin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_lowRegularity_absorption_radius_and_margin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_lowRegularity_absorption_radius_and_margin ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_lowRegularity_absorption_radius_and_margin

theorem exists_adapted_lowRegularity_solution_parameters_with_contraction_threshold
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) {Rmax : ℝ} (hRmax : 0 < Rmax) :
    ∃ (Ctop₂ Kr2 Kr1 Kcap δ Rcap ρ : ℝ)
      (hδ : 0 < δ) (hδ3 : δ ≤ 1 / 3)
      (_ : 0 < Rcap) (_ : Rcap ≤ Rmax) (hρ : 0 < ρ)
      (hreal' : ∀ S : SmoothCcTensor g 0 2,
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
          gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g S) δ)
      (B2 : ℝ), 0 ≤ B2 ∧ B2 < 1 ∧
      ∀ {c : ℝ}, B2 ≤ c → c < 1 →
        ∃ T₀ : ℝ, 0 < T₀ ∧
          ∀ {T : ℝ} (hT : 0 < T) (_ : T ≤ T₀) (hT1 : T ≤ 1),
            ∃ (f : timeL2 (TensorHs (I := I) (M := M) g 0 2 (1 : ℝ)) T)
              (fLo : timeL2 (TensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ)) T)
              (Ctop B0 B1 D ρout P : ℝ),
              HasCompatibleSecondOrderSolution (I := I) (M := M) g hρ hδ.le hδ3 hreal' hT hT1 f
                  Rcap ∧
                (∀ᵐ t ∂timeMeasure T, f t =
                  tensorHsCongr (I := I) (M := M) g 0 2
                    (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num) (fLo t)) ∧
                IsAdaptedLowRegularitySolution (I := I) (M := M) (δ := δ) (Ctop := Ctop)
                  (B0 := B0) (B1 := B1) (D := D) (ρ := ρout) (P := P)
                  g hT hT1 fLo Rcap Ctop₂ Kr2 Kr1 Kcap := by
  obtain ⟨A, B, hgate⟩ := exists_energy_ladder_absorption_constants (I := I) (M := M) hDim g
  obtain ⟨Ctop₂, Kr2, Kr1, Kcap, hord, hA, hB⟩ := hgate.2.2.1
  obtain ⟨δ, Rabs, ε, hδ, hδ3, hRabs, hε, hbudget⟩ :=
    exists_absorption_radius_and_margin hgate.1 hgate.2.1
  let Rcap : ℝ := _root_.Min.min Rmax Rabs
  have hRcap : 0 < Rcap := lt_min hRmax hRabs
  have hRcapMax : Rcap ≤ Rmax := min_le_left _ _
  have hRcapAbs : Rcap ≤ Rabs := min_le_right _ _
  obtain ⟨ρ, hρ, hreal', B2, hB2, hB2lt, hsolve⟩ :=
    exists_compatible_second_order_solution_with_contraction (I := I) (M := M) hDim g hRcap hδ hδ3
  refine ⟨Ctop₂, Kr2, Kr1, Kcap, δ, Rcap, ρ, hδ, hδ3, hRcap, hRcapMax,
    hρ, hreal', B2, hB2, hB2lt, ?_⟩
  intro c hB2c hc1
  obtain ⟨T₀, hT₀, hpack⟩ := hsolve hB2c hc1
  refine ⟨T₀, hT₀, ?_⟩
  intro T hT hTT₀ hT1
  obtain ⟨f, fLo, Ctop, B0, B1, D, ρout, P, hre, hfae, hlo⟩ :=
    hpack hT hTT₀ hT1
  refine ⟨f, fLo, Ctop, B0, B1, D, ρout, P, hre, hfae, hlo, hord,
    A, B, hgate, hA, hB, ε, hε, ?_⟩
  exact hbudget (hlo.stateRadius_le.trans hRcapAbs)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_adapted_lowRegularity_solution_parameters_with_contraction_threshold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_adapted_lowRegularity_solution_parameters_with_contraction_threshold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_adapted_lowRegularity_solution_parameters_with_contraction_threshold ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_adapted_lowRegularity_solution_parameters_with_contraction_threshold

theorem exists_adapted_lowRegularity_solution_parameters
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) {Rmax : ℝ} (hRmax : 0 < Rmax) :
    ∃ (Ctop₂ Kr2 Kr1 Kcap δ Rcap ρ : ℝ)
      (hδ : 0 < δ) (hδ3 : δ ≤ 1 / 3)
      (_ : 0 < Rcap) (_ : Rcap ≤ Rmax) (hρ : 0 < ρ)
      (hreal' : ∀ S : SmoothCcTensor g 0 2,
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
          gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g S) δ)
      (B2 : ℝ), 0 ≤ B2 ∧
      ∀ {c : ℝ}, B2 ≤ c → c < 1 →
        ∃ T₀ : ℝ, 0 < T₀ ∧
          ∀ {T : ℝ} (hT : 0 < T) (_ : T ≤ T₀) (hT1 : T ≤ 1),
            ∃ (f : timeL2 (TensorHs (I := I) (M := M) g 0 2 (1 : ℝ)) T)
              (fLo : timeL2 (TensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ)) T)
              (Ctop B0 B1 D ρout P : ℝ),
              HasCompatibleSecondOrderSolution (I := I) (M := M) g hρ hδ.le hδ3 hreal' hT hT1 f
                  Rcap ∧
                (∀ᵐ t ∂timeMeasure T, f t =
                  tensorHsCongr (I := I) (M := M) g 0 2
                    (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num) (fLo t)) ∧
                IsAdaptedLowRegularitySolution (I := I) (M := M) (δ := δ) (Ctop := Ctop)
                  (B0 := B0) (B1 := B1) (D := D) (ρ := ρout) (P := P)
                  g hT hT1 fLo Rcap Ctop₂ Kr2 Kr1 Kcap := by
  obtain ⟨Ctop₂, Kr2, Kr1, Kcap, δ, Rcap, ρ, hδ, hδ3, hRcap, hRcapMax,
      hρ, hreal', B2, hB2, -, hsolve⟩ :=
    exists_adapted_lowRegularity_solution_parameters_with_contraction_threshold (I := I) (M := M) hDim g hRmax
  exact ⟨Ctop₂, Kr2, Kr1, Kcap, δ, Rcap, ρ, hδ, hδ3, hRcap, hRcapMax,
    hρ, hreal', B2, hB2, hsolve⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_adapted_lowRegularity_solution_parameters then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_adapted_lowRegularity_solution_parameters"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_adapted_lowRegularity_solution_parameters ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_adapted_lowRegularity_solution_parameters

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
