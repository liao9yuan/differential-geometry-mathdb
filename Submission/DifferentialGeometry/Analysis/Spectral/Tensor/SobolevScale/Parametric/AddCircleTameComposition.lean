import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Parametric.AddCircleLocalComposition
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Embedding.ScalarContinuousInjective
import Submission.DifferentialGeometry.Analysis.Integration.Lp.Lifting
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Separable

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.BigOperators _root_.Topology _root_.Submission.Topology _root_.ENNReal

namespace AddCircle
open _root_.AddCircle

open _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {ι : Type*} [Fintype ι]

open _root_.AddCircle in
private local instance _root_.Submission.AddCircle.instNeZeroNatFinrankReal_differentialGeometry : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.AddCircle.instNeZeroNatFinrankReal_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `AddCircle.instNeZeroNatFinrankReal_differentialGeometry target :: scope.openDecls } }

open _root_.AddCircle in
private theorem exists_scalarHs_composition_on_ball_of_order
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ) {σ : ℝ} (hσ : σ = (k : ℝ) + 1)
    (F : (ι → ℝ) → ℝ) {U : Set (ι → ℝ)}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U)
    (u0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 σ))
    (hu0 : _root_.Set.range (scalarH1PiToContinuous g
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by rw [hσ]; norm_num : (1 : ℝ) ≤ σ)) u0)) ⊆ U) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by rw [hσ]; norm_num : (1 : ℝ) ≤ σ)
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : ι => J)
    ∃ r : ℝ, 0 < r ∧ ∃ C : NNReal,
      ∃ N : Metric.ball u0 r → TensorHs g 0 0 σ,
        LipschitzWith C N ∧
        (∀ u ∈ Metric.ball u0 r, _root_.Set.range (scalarH1PiToContinuous g (P u)) ⊆ U) ∧
        (∀ u x, scalarH1ToContinuous g (J (N u)) x =
          F (scalarH1PiToContinuous g (P u) x)) ∧
        ∀ (S : ι → SmoothCcTensor g 0 0)
          (hS : WithLp.toLp 2 (fun i => ccTensorToHs g 0 σ (S i)) ∈ Metric.ball u0 r)
          (hSU : ∀ x, (fun i => TensorRSField.scalar0 (S i).toSection x) ∈ U),
          N ⟨WithLp.toLp 2 (fun i => ccTensorToHs g 0 σ (S i)), hS⟩ =
            ccTensorToHs g 0 σ (SmoothCcTensor.scalarCompOn S F hF hSU) := by
  subst σ
  exact exists_scalarHs_composition_on_ball g k F hF hU u0 hu0

run_cmd do
  let target := ``Submission.AddCircle.exists_scalarHs_composition_on_ball_of_order
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `AddCircle.exists_scalarHs_composition_on_ball_of_order target :: scope.openDecls } }

open _root_.AddCircle in
theorem exists_scalarHs_composition_bound_of_lower_order_bound
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ)
    (F : (ι → ℝ) → ℝ) {U K : Set (ι → ℝ)}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (R : ℝ) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) n; linarith : (1 : ℝ) ≤ (n : ℝ) + 2)
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : ι => J)
    let L := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by linarith : (n : ℝ) + 1 ≤ (n : ℝ) + 2)
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n : ℝ) + 2)),
      _root_.Set.range (scalarH1PiToContinuous g (P u)) ⊆ K →
      (∑ i, ‖L (u i)‖) ≤ R →
      ∃ v : TensorHs g 0 0 ((n : ℝ) + 2),
        ‖v‖ ≤ C * (1 + ∑ i, ‖u i‖) ∧
        ∀ x, scalarH1ToContinuous g (J v) x =
          F (scalarH1PiToContinuous g (P u) x) := by
  classical
  intro J P L
  obtain ⟨K₁, hL, hKL, hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨C, hC, hc⟩ := exists_norm_ccTensorToHs_scalarCompOn_add_two_le_of_add_one_bound
    g n F hF hU hL hLU (R + 1)
  refine ⟨C, hC, ?_⟩
  intro u hu hnu
  let A := (scalarH1PiToContinuous g).comp P
  have huU : _root_.Set.range (A u) ⊆ U := hu.trans hKU
  obtain ⟨r, hr, Cn, N, hN, _, hEval, hSmooth⟩ :=
    exists_scalarHs_composition_on_ball_of_order g (n + 1)
      (by push_cast; ring : (n : ℝ) + 2 = ((n + 1 : ℕ) : ℝ) + 1) F hF hU u huU
  have hlow : Continuous (fun w : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n : ℝ) + 2)) =>
      ∑ i, ‖L (w i)‖) := by fun_prop
  have hnearNorm : ∀ᶠ w in 𝓝 u, (∑ i, ‖L (w i)‖) < R + 1 :=
    hlow.continuousAt.eventually (Iio_mem_nhds (by linarith))
  have hnearRange : ∀ᶠ w in 𝓝 u, _root_.Set.range (A w) ⊆ interior K₁ :=
    A.continuous.continuousAt.eventually
      (ContinuousMap.eventually_range_subset isOpen_interior (hu.trans hKL))
  obtain ⟨δ, hδ, hnear⟩ := Metric.eventually_nhds_iff.mp (hnearNorm.and hnearRange)
  let d := _root_.Min.min r δ
  have hd : 0 < d := lt_min hr hδ
  let D := Metric.ball u d
  let incl : D → Metric.ball u r := fun w =>
    ⟨w.1, Metric.ball_subset_ball (min_le_left r δ) w.2⟩
  have hIncl : Continuous incl := by fun_prop
  let e : (ι → SmoothCcTensor g 0 0) → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n : ℝ) + 2)) :=
    fun S => WithLp.toLp 2 (fun i => ccTensorToHs g 0 ((n : ℝ) + 2) (S i))
  have he : DenseRange e := denseRange_ccTensorToHs_piLp g 0 (by positivity) 2
  have heD : DenseRange (D.restrictPreimage e) :=
    he.restrictPreimage_of_isOpen Metric.isOpen_ball
  have heval (S : ι → SmoothCcTensor g 0 0) (x : AddCircle (1 : ℝ)) :
      A (e S) x = fun i => TensorRSField.scalar0 (S i).toSection x := by
    ext i
    change scalarH1ToContinuous g (J (ccTensorToHs g 0 ((n : ℝ) + 2) (S i))) x = _
    rw [tensorHsInclusion_ccTensorToHs, scalarH1ToContinuous_apply_ccTensorToHs]
  have hbound (w : D) : ‖N (incl w)‖ ≤ C * (1 + ∑ i, ‖w.1 i‖) := by
    refine heD.induction_on w (isClosed_le
      (hN.continuous.comp hIncl).norm (by fun_prop)) ?_
    intro S
    have hSδ : e S.1 ∈ Metric.ball u δ :=
      Metric.ball_subset_ball (min_le_right r δ) S.2
    have hSn := hnear hSδ
    have hSL : ∀ x, (fun i => TensorRSField.scalar0 (S.1 i).toSection x) ∈ K₁ := by
      intro x
      rw [← heval]
      exact interior_subset (hSn.2 (_root_.Set.mem_range_self x))
    have hSU : ∀ x, (fun i => TensorRSField.scalar0 (S.1 i).toSection x) ∈ U :=
      fun x => hLU (hSL x)
    have hlowS : (∑ i, ‖ccTensorToHs g 0 ((n : ℝ) + 1) (S.1 i)‖) ≤ R + 1 := by
      simpa only [e, L, WithLp.ofLp_toLp, tensorHsInclusion_ccTensorToHs] using hSn.1.le
    have hNS : N (incl (D.restrictPreimage e S)) =
        ccTensorToHs g 0 ((n : ℝ) + 2) (SmoothCcTensor.scalarCompOn S.1 F hF hSU) :=
      hSmooth S.1 _ hSU
    rw [hNS]
    exact hc S.1 hSL hlowS
  let uD : D := ⟨u, Metric.mem_ball_self hd⟩
  exact ⟨N (incl uD), hbound uD, fun x => hEval (incl uD) x⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.exists_scalarHs_composition_bound_of_lower_order_bound then
    throwError "Refusing to shadow existing declaration AddCircle.exists_scalarHs_composition_bound_of_lower_order_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.exists_scalarHs_composition_bound_of_lower_order_bound ``Submission.AddCircle.exists_scalarHs_composition_bound_of_lower_order_bound


open _root_.AddCircle in
theorem exists_scalarH2_composition_bound_of_h1_bound
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (F : (ι → ℝ) → ℝ) {U K : Set (ι → ℝ)}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (R : ℝ) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ 2)
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : ι => J)
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : PiLp 2 (fun _ : ι => TensorHs g 0 0 2),
      _root_.Set.range (scalarH1PiToContinuous g (P u)) ⊆ K →
      (∑ i, ‖J (u i)‖) ≤ R →
      ∃ v : TensorHs g 0 0 2,
        ‖v‖ ≤ C * (1 + ∑ i, ‖u i‖) ∧
        ∀ x, scalarH1ToContinuous g (J v) x =
          F (scalarH1PiToContinuous g (P u) x) := by
  classical
  intro J P
  obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨C, hC, hc⟩ := exists_norm_ccTensorToHs_scalarCompOn_h2_le_of_h1_bound
    g F hF hU hL hLU (R + 1)
  refine ⟨C, hC, ?_⟩
  intro u hu hnu
  let A := (scalarH1PiToContinuous g).comp P
  have huU : _root_.Set.range (A u) ⊆ U := hu.trans hKU
  obtain ⟨r, hr, Cn, N, hN, _, hEval, hSmooth⟩ :=
    exists_scalarH2_composition_on_ball g F hF hU u huU
  have hlow : Continuous (fun w : PiLp 2 (fun _ : ι => TensorHs g 0 0 2) =>
      ∑ i, ‖J (w i)‖) := by fun_prop
  have hnearNorm : ∀ᶠ w in 𝓝 u, (∑ i, ‖J (w i)‖) < R + 1 :=
    hlow.continuousAt.eventually (Iio_mem_nhds (by linarith))
  have hnearRange : ∀ᶠ w in 𝓝 u, _root_.Set.range (A w) ⊆ interior L :=
    A.continuous.continuousAt.eventually
      (ContinuousMap.eventually_range_subset isOpen_interior (hu.trans hKL))
  obtain ⟨δ, hδ, hnear⟩ := Metric.eventually_nhds_iff.mp (hnearNorm.and hnearRange)
  let d := _root_.Min.min r δ
  have hd : 0 < d := lt_min hr hδ
  let D := Metric.ball u d
  let incl : D → Metric.ball u r := fun w =>
    ⟨w.1, Metric.ball_subset_ball (min_le_left r δ) w.2⟩
  have hIncl : Continuous incl := by fun_prop
  let e : (ι → SmoothCcTensor g 0 0) → PiLp 2 (fun _ : ι => TensorHs g 0 0 2) :=
    fun S => WithLp.toLp 2 (fun i => ccTensorToHs g 0 2 (S i))
  have he : DenseRange e := denseRange_ccTensorToHs_piLp g 0 (by norm_num) 2
  have heD : DenseRange (D.restrictPreimage e) :=
    he.restrictPreimage_of_isOpen Metric.isOpen_ball
  have heval (S : ι → SmoothCcTensor g 0 0) (x : AddCircle (1 : ℝ)) :
      A (e S) x = fun i => TensorRSField.scalar0 (S i).toSection x := by
    ext i
    change scalarH1ToContinuous g (J (ccTensorToHs g 0 2 (S i))) x = _
    rw [tensorHsInclusion_ccTensorToHs, scalarH1ToContinuous_apply_ccTensorToHs]
  have hbound (w : D) : ‖N (incl w)‖ ≤ C * (1 + ∑ i, ‖w.1 i‖) := by
    refine heD.induction_on w (isClosed_le
      (hN.continuous.comp hIncl).norm (by fun_prop)) ?_
    intro S
    have hSδ : e S.1 ∈ Metric.ball u δ :=
      Metric.ball_subset_ball (min_le_right r δ) S.2
    have hSn := hnear hSδ
    have hSL : ∀ x, (fun i => TensorRSField.scalar0 (S.1 i).toSection x) ∈ L := by
      intro x
      rw [← heval]
      exact interior_subset (hSn.2 (_root_.Set.mem_range_self x))
    have hSU : ∀ x, (fun i => TensorRSField.scalar0 (S.1 i).toSection x) ∈ U :=
      fun x => hLU (hSL x)
    have hlowS : (∑ i, ‖ccTensorToHs g 0 1 (S.1 i)‖) ≤ R + 1 := by
      simpa only [e, J, WithLp.ofLp_toLp, tensorHsInclusion_ccTensorToHs] using hSn.1.le
    have hNS : N (incl (D.restrictPreimage e S)) =
        ccTensorToHs g 0 2 (SmoothCcTensor.scalarCompOn S.1 F hF hSU) :=
      hSmooth S.1 _ hSU
    rw [hNS]
    exact hc S.1 hSL hlowS
  let uD : D := ⟨u, Metric.mem_ball_self hd⟩
  exact ⟨N (incl uD), hbound uD, fun x => hEval (incl uD) x⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.exists_scalarH2_composition_bound_of_h1_bound then
    throwError "Refusing to shadow existing declaration AddCircle.exists_scalarH2_composition_bound_of_h1_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.exists_scalarH2_composition_bound_of_h1_bound ``Submission.AddCircle.exists_scalarH2_composition_bound_of_h1_bound

open _root_.AddCircle in
theorem exists_lp_scalarH2_composition_of_h1_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : _root_.MeasureTheory.Measure Ω) [_root_.MeasureTheory.IsFiniteMeasure μ]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (F : (ι → ℝ) → ℝ) {U K : Set (ι → ℝ)}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {p : ℝ≥0∞} {u : Ω → PiLp 2 (fun _ : ι => TensorHs g 0 0 2)}
    (hu : _root_.MeasureTheory.MemLp u p μ) {a : Ω → TensorHs g 0 0 1}
    (ha : _root_.MeasureTheory.AEStronglyMeasurable a μ) {R : ℝ} :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ 2)
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : ι => J)
    (∀ᵐ t ∂μ, _root_.Set.range (scalarH1PiToContinuous g (P (u t))) ⊆ K) →
    (∀ᵐ t ∂μ, (∑ i, ‖J (u t i)‖) ≤ R) →
    (∀ᵐ t ∂μ, ∀ x, scalarH1ToContinuous g (a t) x =
      F (scalarH1PiToContinuous g (P (u t)) x)) →
    ∃ v : _root_.MeasureTheory.Lp (TensorHs g 0 0 2) p μ, (fun t => J (v t)) =ᵐ[μ] a := by
  classical
  intro J P hRange hBound hEval
  obtain ⟨C, hC, hc⟩ := exists_scalarH2_composition_bound_of_h1_bound
    g F hF hU hK hKU R
  let b : Ω → ℝ := fun t => C * (1 + (Fintype.card ι : ℝ) * ‖u t‖)
  have hb : _root_.MeasureTheory.MemLp b p μ := by
    have h := ((_root_.MeasureTheory.memLp_const (1 : ℝ)).add
      (hu.norm.const_mul (Fintype.card ι : ℝ))).const_mul C
    exact h
  have hLift : ∀ᵐ t ∂μ, ∃ v : TensorHs g 0 0 2, J v = a t ∧ ‖v‖ ≤ b t := by
    filter_upwards [hRange, hBound, hEval] with t hRt hBt hEt
    obtain ⟨v, hv, hve⟩ := hc (u t) hRt hBt
    refine ⟨v, ?_, ?_⟩
    · apply scalarH1ToContinuous_injective g
      exact ContinuousMap.ext (fun x => (hve x).trans (hEt x).symm)
    · have hsum : (∑ i, ‖u t i‖) ≤ (Fintype.card ι : ℝ) * ‖u t‖ := by
        calc
          _ ≤ ∑ _i : ι, ‖u t‖ := Finset.sum_le_sum (fun i _ => PiLp.norm_apply_le _ i)
          _ = _ := by simp
      exact hv.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hsum) hC)
  obtain ⟨v, hv, _⟩ := exists_lp_lift_of_ae_exists_norm_le J.continuous
    (tensorHsInclusion_injective (by norm_num : (1 : ℝ) ≤ 2)) ha hb hLift
  exact ⟨v, hv⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.exists_lp_scalarH2_composition_of_h1_bound then
    throwError "Refusing to shadow existing declaration AddCircle.exists_lp_scalarH2_composition_of_h1_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.exists_lp_scalarH2_composition_of_h1_bound ``Submission.AddCircle.exists_lp_scalarH2_composition_of_h1_bound

open _root_.AddCircle in
theorem exists_lp_scalarH2_composition_bound_of_h1_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (F : (ι → ℝ) → ℝ) {U K : Set (ι → ℝ)}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (R : ℝ) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ 2)
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : ι => J)
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (μ : _root_.MeasureTheory.Measure Ω) [_root_.MeasureTheory.IsFiniteMeasure μ] {p : ℝ≥0∞}
      {u : Ω → PiLp 2 (fun _ : ι => TensorHs g 0 0 2)},
      _root_.MeasureTheory.MemLp u p μ → ∀ (a : Ω → TensorHs g 0 0 1), _root_.MeasureTheory.AEStronglyMeasurable a μ →
      (∀ᵐ t ∂μ, _root_.Set.range (scalarH1PiToContinuous g (P (u t))) ⊆ K) →
      (∀ᵐ t ∂μ, (∑ i, ‖J (u t i)‖) ≤ R) →
      (∀ᵐ t ∂μ, ∀ x, scalarH1ToContinuous g (a t) x =
        F (scalarH1PiToContinuous g (P (u t)) x)) →
      ∃ v : _root_.MeasureTheory.Lp (TensorHs g 0 0 2) p μ, (fun t => J (v t)) =ᵐ[μ] a ∧
        ∀ᵐ t ∂μ, ‖v t‖ ≤ C * (1 + ∑ i, ‖u t i‖) := by
  classical
  intro J P
  obtain ⟨C, hC, hc⟩ := exists_scalarH2_composition_bound_of_h1_bound
    g F hF hU hK hKU R
  refine ⟨C, hC, ?_⟩
  intro μ _ p u hu a ha hRange hBound hEval
  obtain ⟨v, hv⟩ := exists_lp_scalarH2_composition_of_h1_bound
    μ g F hF hU hK hKU hu ha hRange hBound hEval
  refine ⟨v, hv, ?_⟩
  filter_upwards [hRange, hBound, hEval, hv] with t hRt hBt hEt hvt
  obtain ⟨z, hz, hze⟩ := hc (u t) hRt hBt
  have hzj : J z = a t := by
    apply scalarH1ToContinuous_injective g
    exact ContinuousMap.ext (fun x => (hze x).trans (hEt x).symm)
  have heq : v t = z :=
    tensorHsInclusion_injective (by norm_num : (1 : ℝ) ≤ 2) (hvt.trans hzj.symm)
  rw [heq]
  exact hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.exists_lp_scalarH2_composition_bound_of_h1_bound then
    throwError "Refusing to shadow existing declaration AddCircle.exists_lp_scalarH2_composition_bound_of_h1_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.exists_lp_scalarH2_composition_bound_of_h1_bound ``Submission.AddCircle.exists_lp_scalarH2_composition_bound_of_h1_bound


open _root_.AddCircle in
theorem exists_lp_scalarHs_composition_of_lower_order_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : _root_.MeasureTheory.Measure Ω) [_root_.MeasureTheory.IsFiniteMeasure μ]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ)
    (F : (ι → ℝ) → ℝ) {U K : Set (ι → ℝ)}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {p : ℝ≥0∞} {u : Ω → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 2))}
    (hu : _root_.MeasureTheory.MemLp u p μ) {a : Ω → TensorHs g 0 0 ((k : ℝ) + 1)}
    (ha : _root_.MeasureTheory.AEStronglyMeasurable a μ) {R : ℝ} :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (1 : ℝ) ≤ (k : ℝ) + 2)
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : ι => J)
    let L := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by linarith : (k : ℝ) + 1 ≤ (k : ℝ) + 2)
    let K₁ := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (1 : ℝ) ≤ (k : ℝ) + 1)
    (∀ᵐ t ∂μ, _root_.Set.range (scalarH1PiToContinuous g (P (u t))) ⊆ K) →
    (∀ᵐ t ∂μ, (∑ i, ‖L (u t i)‖) ≤ R) →
    (∀ᵐ t ∂μ, ∀ x, scalarH1ToContinuous g (K₁ (a t)) x =
      F (scalarH1PiToContinuous g (P (u t)) x)) →
    ∃ v : _root_.MeasureTheory.Lp (TensorHs g 0 0 ((k : ℝ) + 2)) p μ,
      (fun t => L (v t)) =ᵐ[μ] a := by
  classical
  intro J P L K₁ hRange hBound hEval
  obtain ⟨C, hC, hc⟩ := exists_scalarHs_composition_bound_of_lower_order_bound
    g k F hF hU hK hKU R
  let b : Ω → ℝ := fun t => C * (1 + (Fintype.card ι : ℝ) * ‖u t‖)
  have hb : _root_.MeasureTheory.MemLp b p μ :=
    ((_root_.MeasureTheory.memLp_const (1 : ℝ)).add (hu.norm.const_mul (Fintype.card ι : ℝ))).const_mul C
  have hLift : ∀ᵐ t ∂μ, ∃ v : TensorHs g 0 0 ((k : ℝ) + 2),
      L v = a t ∧ ‖v‖ ≤ b t := by
    filter_upwards [hRange, hBound, hEval] with t hRt hBt hEt
    obtain ⟨v, hv, hve⟩ := hc (u t) hRt hBt
    refine ⟨v, ?_, ?_⟩
    · apply tensorHsInclusion_injective
        (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (1 : ℝ) ≤ (k : ℝ) + 1)
      apply scalarH1ToContinuous_injective g
      apply ContinuousMap.ext
      intro x
      simpa only [L, K₁, ← tensorHsInclusion_trans_apply] using
        (hve x).trans (hEt x).symm
    · have hsum : (∑ i, ‖u t i‖) ≤ (Fintype.card ι : ℝ) * ‖u t‖ := by
        calc
          _ ≤ ∑ _i : ι, ‖u t‖ := Finset.sum_le_sum (fun i _ => PiLp.norm_apply_le _ i)
          _ = _ := by simp
      exact hv.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hsum) hC)
  obtain ⟨v, hv, _⟩ := exists_lp_lift_of_ae_exists_norm_le L.continuous
    (tensorHsInclusion_injective (by linarith : (k : ℝ) + 1 ≤ (k : ℝ) + 2)) ha hb hLift
  exact ⟨v, hv⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.exists_lp_scalarHs_composition_of_lower_order_bound then
    throwError "Refusing to shadow existing declaration AddCircle.exists_lp_scalarHs_composition_of_lower_order_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.exists_lp_scalarHs_composition_of_lower_order_bound ``Submission.AddCircle.exists_lp_scalarHs_composition_of_lower_order_bound

open _root_.AddCircle in
theorem exists_lp_scalarHs_composition_bound_of_lower_order_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ)
    (F : (ι → ℝ) → ℝ) {U K : Set (ι → ℝ)}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (R : ℝ) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (1 : ℝ) ≤ (k : ℝ) + 2)
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : ι => J)
    let L := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by linarith : (k : ℝ) + 1 ≤ (k : ℝ) + 2)
    let K₁ := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (1 : ℝ) ≤ (k : ℝ) + 1)
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (μ : _root_.MeasureTheory.Measure Ω) [_root_.MeasureTheory.IsFiniteMeasure μ] {p : ℝ≥0∞}
      {u : Ω → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 2))},
      _root_.MeasureTheory.MemLp u p μ → ∀ (a : Ω → TensorHs g 0 0 ((k : ℝ) + 1)),
      _root_.MeasureTheory.AEStronglyMeasurable a μ →
      (∀ᵐ t ∂μ, _root_.Set.range (scalarH1PiToContinuous g (P (u t))) ⊆ K) →
      (∀ᵐ t ∂μ, (∑ i, ‖L (u t i)‖) ≤ R) →
      (∀ᵐ t ∂μ, ∀ x, scalarH1ToContinuous g (K₁ (a t)) x =
        F (scalarH1PiToContinuous g (P (u t)) x)) →
      ∃ v : _root_.MeasureTheory.Lp (TensorHs g 0 0 ((k : ℝ) + 2)) p μ,
        (fun t => L (v t)) =ᵐ[μ] a ∧
        ∀ᵐ t ∂μ, ‖v t‖ ≤ C * (1 + ∑ i, ‖u t i‖) := by
  classical
  intro J P L K₁
  obtain ⟨C, hC, hc⟩ := exists_scalarHs_composition_bound_of_lower_order_bound
    g k F hF hU hK hKU R
  refine ⟨C, hC, ?_⟩
  intro μ _ p u hu a ha hRange hBound hEval
  obtain ⟨v, hv⟩ := exists_lp_scalarHs_composition_of_lower_order_bound
    μ g k F hF hU hK hKU hu ha hRange hBound hEval
  refine ⟨v, hv, ?_⟩
  filter_upwards [hRange, hBound, hEval, hv] with t hRt hBt hEt hvt
  obtain ⟨z, hz, hze⟩ := hc (u t) hRt hBt
  have hzj : L z = a t := by
    apply tensorHsInclusion_injective
      (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (1 : ℝ) ≤ (k : ℝ) + 1)
    apply scalarH1ToContinuous_injective g
    apply ContinuousMap.ext
    intro x
    simpa only [L, K₁, ← tensorHsInclusion_trans_apply] using
      (hze x).trans (hEt x).symm
  have heq : v t = z := tensorHsInclusion_injective
    (by linarith : (k : ℝ) + 1 ≤ (k : ℝ) + 2) (hvt.trans hzj.symm)
  rw [heq]
  exact hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.exists_lp_scalarHs_composition_bound_of_lower_order_bound then
    throwError "Refusing to shadow existing declaration AddCircle.exists_lp_scalarHs_composition_bound_of_lower_order_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.exists_lp_scalarHs_composition_bound_of_lower_order_bound ``Submission.AddCircle.exists_lp_scalarHs_composition_bound_of_lower_order_bound

end AddCircle
