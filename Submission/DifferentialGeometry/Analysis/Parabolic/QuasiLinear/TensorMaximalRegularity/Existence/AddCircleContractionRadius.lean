import Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.AddCircleDriftBounds

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal _root_.NNReal _root_.Topology

namespace AddCircle
open _root_.AddCircle

open _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev

open _root_.AddCircle in
private local instance _root_.Submission.AddCircle.instNeZeroNatFinrankReal_differentialGeometry : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.AddCircle.instNeZeroNatFinrankReal_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `AddCircle.instNeZeroNatFinrankReal_differentialGeometry target :: scope.openDecls } }

open _root_.AddCircle in
private theorem exists_pos_contraction_radius
    (A B C : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    {R : ℝ} (hR : 0 < R) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ R ∧ δ ≤ 1 ∧ ∀ {r T : ℝ},
      0 ≤ T → T ≤ r → r ≤ δ →
      A * r * (1 + T) + Real.sqrt (1 + T) *
        (B * (Real.sqrt T + (1 + T) * r / 4) + C * Real.sqrt T) < 1 := by
  let f : ℝ → ℝ := fun r => A * r * (1 + r) + Real.sqrt (1 + r) *
    (B * (Real.sqrt r + (1 + r) * r / 4) + C * Real.sqrt r)
  have hf : ContinuousAt f 0 := by fun_prop
  have hf0 : f 0 = 0 := by simp [f]
  have hevent : ∀ᶠ r in 𝓝 (0 : ℝ), f r < 1 :=
    hf.eventually_lt_const (by rw [hf0]; norm_num)
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp hevent
  let δ := _root_.Min.min R (_root_.Min.min 1 (ε / 2))
  have hδ : 0 < δ := lt_min hR (lt_min zero_lt_one (by positivity))
  refine ⟨δ, hδ, min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _), ?_⟩
  intro r T hT hTr hrδ
  have hr : 0 ≤ r := hT.trans hTr
  have hrε : r < ε := lt_of_le_of_lt
    (hrδ.trans ((min_le_right _ _).trans (min_le_right _ _))) (by linarith)
  have hfr : f r < 1 := he (by simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hr] using hrε)
  refine lt_of_le_of_lt ?_ hfr
  dsimp only [f]
  gcongr

run_cmd do
  let target := ``Submission.AddCircle.exists_pos_contraction_radius
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `AddCircle.exists_pos_contraction_radius target :: scope.openDecls } }

variable {ι : Type*} [Fintype ι]

open _root_.AddCircle in
private theorem drift_high_memLp
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (a : timeL2 (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) T) :
    MemLp (fun t => parameterDriftOperatorHsPi (ι := ι) g (a t)) 2 (timeMeasure T) :=
  memLp_parameterDriftOperatorHsPi (ι := ι) g (Lp.memLp a)

run_cmd do
  let target := ``Submission.AddCircle.drift_high_memLp
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `AddCircle.drift_high_memLp target :: scope.openDecls } }

open _root_.AddCircle in
private theorem drift_low_memLp
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (a : timeL2 (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) T) :
    MemLp (fun t => parameterDriftOperatorH0Pi (ι := ι) g (a t)) 2 (timeMeasure T) :=
  memLp_parameterDriftOperatorH0Pi (ι := ι) g (Lp.memLp a)

run_cmd do
  let target := ``Submission.AddCircle.drift_low_memLp
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `AddCircle.drift_low_memLp target :: scope.openDecls } }

open _root_.AddCircle in
theorem exists_pos_parameterDerivativeHsPi_contraction_radius
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (Cα C : ℝ≥0) {R : ℝ} (hR : 0 < R) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let q := ccTensorToHs g 0 ((1 : ℕ) : ℝ) (scalarCc g (laplacianPrincipalCoefficient g))
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ R ∧ δ ≤ 1 ∧ ∀ {r T : ℝ},
      0 < T → T ≤ r → r ≤ δ →
      ∀ a₂ : timeL2 (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) T,
      (∀ᵐ t ∂timeMeasure T, ‖J (a₂ t) - q‖ ≤ Cα * r) →
      ‖a₂‖ ≤ C * (Real.sqrt T + (1 + T) * r / 4) →
      let hh := drift_high_memLp (ι := ι) g a₂
      ∃ C2 : ℝ≥0,
        (∀ᵐ t ∂timeMeasure T, ‖parameterPrincipalOperatorHsPi (ι := ι) g (J (a₂ t))‖ ≤ C2) ∧
        (C2 : ℝ) * (1 + T) + Real.sqrt (1 + T) *
          ‖hh.toLp (fun t => parameterDriftOperatorHsPi (ι := ι) g (a₂ t))‖ < 1 := by
  intro J q
  let D : TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1) →L[ℝ] TensorHs g 0 0 ((1 : ℕ) : ℝ) := parameterDerivativeHs g 1
  let m : TensorHs g 0 0 ((1 : ℕ) : ℝ) →L[ℝ] TensorHs g 0 0 ((1 : ℕ) : ℝ) →L[ℝ] TensorHs g 0 0 ((1 : ℕ) : ℝ) := scalarHsMul g 1 (by norm_num)
  let d : TensorHs g 0 0 ((1 : ℕ) : ℝ) := ccTensorToHs g 0 ((1 : ℕ) : ℝ) (scalarCc g (laplacianDriftCoefficient g))
  let A : ℝ≥0 := ‖m‖₊ * ‖parameterSecondDerivativeHs g 1‖₊ * Cα
  let K := ‖m‖ * ‖D‖ ^ 2
  let B := ‖m‖ * ‖d‖ * ‖D‖
  obtain ⟨δ, hδ, hδR, hδ1, hsmall⟩ := exists_pos_contraction_radius
    A (K * C) B A.coe_nonneg (by positivity) (by positivity) hR
  refine ⟨δ, hδ, hδR, hδ1, ?_⟩
  intro r T hT hTr hrδ a₂ hclose hnorm hh
  have hr : 0 ≤ r := hT.le.trans hTr
  let C2 : ℝ≥0 := A * ⟨r, hr⟩
  have hbound : ∀ᵐ t ∂timeMeasure T,
      ‖parameterPrincipalOperatorHsPi (ι := ι) g (J (a₂ t))‖ ≤ C2 := by
    filter_upwards [hclose] with t ht
    calc
      _ ≤ ‖m‖ * ‖J (a₂ t) - q‖ * ‖parameterSecondDerivativeHs g 1‖ :=
        norm_parameterPrincipalOperatorHsPi_le g (J (a₂ t))
      _ ≤ ‖m‖ * (Cα * r) * ‖parameterSecondDerivativeHs g 1‖ := by gcongr
      _ = C2 := by
        change ‖m‖ * (Cα * r) * ‖parameterSecondDerivativeHs g 1‖ =
          (‖m‖ * ‖parameterSecondDerivativeHs g 1‖ * Cα) * r
        ring
  refine ⟨C2, hbound, ?_⟩
  have hn : ‖hh.toLp (fun t => parameterDriftOperatorHsPi (ι := ι) g (a₂ t))‖ ≤
      K * ‖a₂‖ + Real.sqrt T * B := norm_toLp_parameterDriftOperatorHsPi_le g a₂
  apply lt_of_le_of_lt _ (hsmall hT.le hTr hrδ)
  change (A : ℝ) * r * (1 + T) + _ ≤ _
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  calc
    _ ≤ K * ‖a₂‖ + Real.sqrt T * B := hn
    _ ≤ K * (C * (Real.sqrt T + (1 + T) * r / 4)) + Real.sqrt T * B := by gcongr
    _ = _ := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.exists_pos_parameterDerivativeHsPi_contraction_radius then
    throwError "Refusing to shadow existing declaration AddCircle.exists_pos_parameterDerivativeHsPi_contraction_radius"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.exists_pos_parameterDerivativeHsPi_contraction_radius ``Submission.AddCircle.exists_pos_parameterDerivativeHsPi_contraction_radius

open _root_.AddCircle in
theorem exists_pos_parameterDerivativeH0Pi_contraction_radius
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (Cα C : ℝ≥0) {R : ℝ} (hR : 0 < R) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let q := ccTensorToHs g 0 ((1 : ℕ) : ℝ) (scalarCc g (laplacianPrincipalCoefficient g))
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ R ∧ δ ≤ 1 ∧ ∀ {r T : ℝ},
      0 < T → T ≤ r → r ≤ δ →
      ∀ a₂ : timeL2 (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) T,
      (∀ᵐ t ∂timeMeasure T, ‖J (a₂ t) - q‖ ≤ Cα * r) →
      ‖a₂‖ ≤ C * (Real.sqrt T + (1 + T) * r / 4) →
      let hl := drift_low_memLp (ι := ι) g a₂
      ∃ C2 : ℝ≥0,
        (∀ᵐ t ∂timeMeasure T, ‖parameterPrincipalOperatorH0Pi (ι := ι) g (J (a₂ t))‖ ≤ C2) ∧
        (C2 : ℝ) * (1 + T) + Real.sqrt (1 + T) *
          ‖hl.toLp (fun t => parameterDriftOperatorH0Pi (ι := ι) g (a₂ t))‖ < 1 := by
  intro J q
  let D : TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1) →L[ℝ] TensorHs g 0 0 ((1 : ℕ) : ℝ) := parameterDerivativeHs g 1
  let d : TensorHs g 0 0 ((1 : ℕ) : ℝ) := ccTensorToHs g 0 ((1 : ℕ) : ℝ) (scalarCc g (laplacianDriftCoefficient g))
  let c : TensorHs g 0 0 ((1 : ℕ) : ℝ) →L[ℝ] C(AddCircle (1 : ℝ), ℝ) := (scalarH1ToContinuous g).comp (tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
  let Z : TensorHs g 0 0 ((0 : ℕ) : ℝ) →L[ℝ] TensorHs g 0 0 (0 : ℝ) := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))
  let D₀ : TensorHs g 0 0 (((0 : ℕ) : ℝ) + 1) →L[ℝ] TensorHs g 0 0 (0 : ℝ) := Z.comp (parameterDerivativeHs g 0)
  let M : C(AddCircle (1 : ℝ), ℝ) →L[ℝ] TensorHs g 0 0 (0 : ℝ) →L[ℝ] TensorHs g 0 0 (0 : ℝ) := scalarH0ContinuousMul g
  let A : ℝ≥0 := ‖M‖₊ * ‖c‖₊ * ‖Z.comp (parameterSecondDerivativeHs g 0)‖₊ * Cα
  let K := ‖M‖ * ‖c‖ * ‖D‖ * ‖D₀‖
  let B := ‖M‖ * ‖c‖ * ‖d‖ * ‖D₀‖
  obtain ⟨δ, hδ, hδR, hδ1, hsmall⟩ := exists_pos_contraction_radius
    A (K * C) B A.coe_nonneg (by positivity) (by positivity) hR
  refine ⟨δ, hδ, hδR, hδ1, ?_⟩
  intro r T hT hTr hrδ a₂ hclose hnorm hl
  have hr : 0 ≤ r := hT.le.trans hTr
  let C2 : ℝ≥0 := A * ⟨r, hr⟩
  have hbound : ∀ᵐ t ∂timeMeasure T,
      ‖parameterPrincipalOperatorH0Pi (ι := ι) g (J (a₂ t))‖ ≤ C2 := by
    filter_upwards [hclose] with t ht
    calc
      _ ≤ ‖M‖ * (‖c‖ * ‖J (a₂ t) - q‖) * ‖Z.comp (parameterSecondDerivativeHs g 0)‖ :=
        norm_parameterPrincipalOperatorH0Pi_le g (J (a₂ t))
      _ ≤ ‖M‖ * (‖c‖ * (Cα * r)) * ‖Z.comp (parameterSecondDerivativeHs g 0)‖ := by gcongr
      _ = C2 := by
        change ‖M‖ * (‖c‖ * (Cα * r)) * ‖Z.comp (parameterSecondDerivativeHs g 0)‖ =
          (‖M‖ * ‖c‖ * ‖Z.comp (parameterSecondDerivativeHs g 0)‖ * Cα) * r
        ring
  refine ⟨C2, hbound, ?_⟩
  have hn : ‖hl.toLp (fun t => parameterDriftOperatorH0Pi (ι := ι) g (a₂ t))‖ ≤
      K * ‖a₂‖ + Real.sqrt T * B := norm_toLp_parameterDriftOperatorH0Pi_le g a₂
  apply lt_of_le_of_lt _ (hsmall hT.le hTr hrδ)
  change (A : ℝ) * r * (1 + T) + _ ≤ _
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  calc
    _ ≤ K * ‖a₂‖ + Real.sqrt T * B := hn
    _ ≤ K * (C * (Real.sqrt T + (1 + T) * r / 4)) + Real.sqrt T * B := by gcongr
    _ = _ := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.exists_pos_parameterDerivativeH0Pi_contraction_radius then
    throwError "Refusing to shadow existing declaration AddCircle.exists_pos_parameterDerivativeH0Pi_contraction_radius"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.exists_pos_parameterDerivativeH0Pi_contraction_radius ``Submission.AddCircle.exists_pos_parameterDerivativeH0Pi_contraction_radius

end AddCircle
