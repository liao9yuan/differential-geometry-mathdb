import Submission.DifferentialGeometry.Analysis.Integration.Lp.AffineDilation
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.ZeroBoundaryGraph
import Submission.DifferentialGeometry.External.DeGiorgi.SobolevSpace.Approximation
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Classical
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.ZeroTrace.Composition
import Submission.DifferentialGeometry.Analysis.Calculus.Cutoff.Ball
import Submission.DifferentialGeometry.External.DeGiorgi.PositivePart
import Submission.DifferentialGeometry.External.DeGiorgi.BallExtension.RoughInput

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section

open _root_.Set _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.Topology _root_.ENNReal _root_.NNReal

namespace DeGiorgi

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem memW01p_ball_of_global_memW1pWitness_of_zero_outside_closedBall_posdim
    {f : E → ℝ} (hf : MemW1pWitness 2 f Set.univ)
    (c : E) {R : ℝ} (hR : 0 < R)
    (hzero : ∀ x, x ∉ Metric.closedBall c R → f x = 0) :
    MemW01p 2 f (Metric.ball c R) := by
  let rn (n : ℕ) : ℝ := 1 + 1 / ((n : ℝ) + 1)
  have hrn (n : ℕ) : 1 < rn n := by
    dsimp only [rn]
    have h : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
    linarith
  have hrn0 (n : ℕ) : 0 < rn n := zero_lt_one.trans (hrn n)
  have hrn2 (n : ℕ) : rn n ≤ 2 := by
    have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by have h := Nat.cast_nonneg (α := ℝ) n; linarith
    have hinv := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hn
    dsimp only [rn]
    norm_num only [div_one] at hinv
    linarith
  have hrlim : _root_.Filter.Tendsto rn _root_.Filter.atTop (𝓝 1) := by
    simpa only [rn, add_zero] using tendsto_one_div_add_atTop_nhds_zero_nat.const_add (1 : ℝ)
  let S (n : ℕ) (x : E) := (1 - rn n) • c + rn n • x
  let fn (n : ℕ) (x : E) := f (S n x)
  let hnGlobal (n : ℕ) : MemW1pWitness 2 (fn n) Set.univ := by
    simpa only [_root_.Set.preimage_univ] using hf.compAddSmul ((1 - rn n) • c) (hrn0 n).ne'
  let hn (n : ℕ) : MemW1pWitness 2 (fn n) (Metric.ball c R) :=
    MemW1pWitness.restrict Metric.isOpen_ball (_root_.Set.subset_univ _) (hnGlobal n)
  have hSsub (n : ℕ) (x : E) : S n x - c = rn n • (x - c) := by
    dsimp only [S]
    module
  have hfnSupport (n : ℕ) : tsupport (fn n) ⊆ Metric.closedBall c (R / rn n) := by
    apply closure_minimal _ Metric.isClosed_closedBall
    intro x hx
    have hS : S n x ∈ Metric.closedBall c R := by
      by_contra h
      exact hx (hzero (S n x) h)
    rw [Metric.mem_closedBall, dist_eq_norm] at hS ⊢
    rw [hSsub n x, norm_smul, Real.norm_of_nonneg (hrn0 n).le] at hS
    exact (le_div_iff₀ (hrn0 n)).mpr (by simpa only [mul_comm] using hS)
  have hfnCompact (n : ℕ) : HasCompactSupport (fn n) :=
    (_root_.ProperSpace.isCompact_closedBall c (R / rn n)).of_isClosed_subset (isClosed_tsupport _) (hfnSupport n)
  have hfnInside (n : ℕ) : tsupport (fn n) ⊆ Metric.ball c R :=
    (hfnSupport n).trans (Metric.closedBall_subset_ball (div_lt_self hR (hrn n)))
  have hfnW0 (n : ℕ) : MemW01p 2 (fn n) (Metric.ball c R) := by
    simpa only [ENNReal.ofReal_ofNat] using memW01p_of_memW1p_of_tsupport_subset
      Metric.isOpen_ball (by norm_num : (1 : ℝ) < 2)
      (by simpa only [ENNReal.ofReal_ofNat] using (hn n).memW1p) (hfnCompact n) (hfnInside n)
  have hfLp : _root_.MeasureTheory.MemLp f 2 volume := by simpa only [Measure.restrict_univ] using hf.memLp
  have hGLp : _root_.MeasureTheory.MemLp hf.weakGrad 2 volume := by
    simpa only [Measure.restrict_univ] using hf.weakGrad_memLp
  have hgradBound (n : ℕ) : ‖gradLpOfWitness (hn n)‖ ≤
      2 * (_root_.MeasureTheory.eLpNorm hf.weakGrad 2 _root_.MeasureTheory.MeasureSpace.volume).toReal := by
    rw [gradLpOfWitness, Lp.norm_toLp]
    change (_root_.MeasureTheory.eLpNorm (fun x => rn n • hf.weakGrad (S n x)) 2
      (volume.restrict (Metric.ball c R))).toReal ≤ _
    have hb : _root_.MeasureTheory.eLpNorm (fun x => rn n • hf.weakGrad (S n x)) 2
        (volume.restrict (Metric.ball c R)) ≤
          ENNReal.ofReal 2 * _root_.MeasureTheory.eLpNorm hf.weakGrad 2 volume := by
      calc
        _ ≤ _root_.MeasureTheory.eLpNorm (fun x => rn n • hf.weakGrad (S n x)) 2 volume :=
          _root_.MeasureTheory.eLpNorm_mono_measure _ Measure.restrict_le_self
        _ ≤ ENNReal.ofReal (rn n) * _root_.MeasureTheory.eLpNorm (fun x => hf.weakGrad (S n x)) 2 volume := by
          simpa only [Pi.smul_def, Real.enorm_eq_ofReal (hrn0 n).le] using
            eLpNorm_const_smul_le (c := rn n)
              (f := fun x => hf.weakGrad (S n x)) (p := 2) (μ := _root_.MeasureTheory.MeasureSpace.volume)
        _ ≤ ENNReal.ofReal 2 * _root_.MeasureTheory.eLpNorm hf.weakGrad 2 volume :=
          mul_le_mul (ENNReal.ofReal_le_ofReal (hrn2 n))
            (eLpNorm_comp_add_smul_le_of_one_le hGLp ((1 - rn n) • c) (hrn n).le) zero_le zero_le
    have hfinite : ENNReal.ofReal 2 * _root_.MeasureTheory.eLpNorm hf.weakGrad 2 _root_.MeasureTheory.MeasureSpace.volume ≠ ∞ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hGLp.eLpNorm_lt_top.ne
    have h := ENNReal.toReal_mono hfinite hb
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2)] using h
  have hbound (n : ℕ) :
      ‖gradLpOfWitness (Classical.choose (hfnW0 n).2)‖ ≤
        2 * (_root_.MeasureTheory.eLpNorm hf.weakGrad 2 _root_.MeasureTheory.MeasureSpace.volume).toReal := by
    have hae := MemW1pWitness.ae_eq Metric.isOpen_ball (Classical.choose (hfnW0 n).2) (hn n)
    have heq : gradLpOfWitness (Classical.choose (hfnW0 n).2) = gradLpOfWitness (hn n) := by
      apply Lp.ext
      exact (Classical.choose (hfnW0 n).2).weakGrad_memLp.coeFn_toLp.trans
        (hae.trans (hn n).weakGrad_memLp.coeFn_toLp.symm)
    rw [heq]
    exact hgradBound n
  have hlim : _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x => fn n x - f x) 2
      (volume.restrict (Metric.ball c R))) _root_.Filter.atTop (𝓝 0) :=
    tendsto_eLpNorm_comp_add_smul_sub_on_ball hfLp c R (fun n => (hrn n).le) hrlim
  open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean in
  exact (exists_weakly_convergent_gradients_of_tendsto_L2
    Metric.isOpen_ball hfnW0 (hfLp.restrict _) hbound hlim).1

run_cmd do
  let target := ``Submission.DeGiorgi.memW01p_ball_of_global_memW1pWitness_of_zero_outside_closedBall_posdim
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DeGiorgi.memW01p_ball_of_global_memW1pWitness_of_zero_outside_closedBall_posdim target :: scope.openDecls } }

omit [NeZero d] in
theorem memW01p_ball_of_global_memW1pWitness_of_zero_outside_closedBall
    {f : E → ℝ} (hf : MemW1pWitness 2 f Set.univ)
    (c : E) {R : ℝ} (hR : 0 < R)
    (hzero : ∀ x, x ∉ Metric.closedBall c R → f x = 0) :
    MemW01p 2 f (Metric.ball c R) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have heq : f = fun _ => f 0 := funext fun x => congrArg f (Subsingleton.elim x 0)
    have hfc : ContDiff ℝ (⊤ : ℕ∞) f := by rw [heq]; exact contDiff_const
    have hcomp : HasCompactSupport f :=
      isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (_root_.Set.subset_univ _)
    have hsub : tsupport f ⊆ Metric.ball c R := by
      intro x _
      simpa only [Subsingleton.elim x c] using Metric.mem_ball_self hR
    let hfb : MemW1pWitness 2 f (Metric.ball c R) :=
      hf.restrict Metric.isOpen_ball (_root_.Set.subset_univ _)
    refine ⟨hfb.memW1p, hfb, fun _ => f, fun _ => hfc, fun _ => hcomp, fun _ => hsub, ?_, ?_⟩
    · simpa only [sub_self, _root_.MeasureTheory.eLpNorm_zero', Pi.zero_def] using
        (tendsto_const_nhds : _root_.Filter.Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) _root_.Filter.atTop (𝓝 0))
    · exact fun i => Fin.elim0 i
  · let _ : NeZero d := ⟨hd.ne'⟩
    exact memW01p_ball_of_global_memW1pWitness_of_zero_outside_closedBall_posdim hf c hR hzero

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.memW01p_ball_of_global_memW1pWitness_of_zero_outside_closedBall then
    throwError "Refusing to shadow existing declaration DeGiorgi.memW01p_ball_of_global_memW1pWitness_of_zero_outside_closedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.memW01p_ball_of_global_memW1pWitness_of_zero_outside_closedBall ``Submission.DeGiorgi.memW01p_ball_of_global_memW1pWitness_of_zero_outside_closedBall

end DeGiorgi

end

end

section

noncomputable section
open _root_.Set _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.ContDiff _root_.ENNReal

namespace DeGiorgi
open _root_.Submission.DifferentialGeometry.Analysis
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} [NeZero d]
local notation "V" => EuclideanSpace ℝ (Fin d)

theorem memW01p_pos_part_of_nonpos_outside_closedBall
    {f : V → ℝ} (hf : ContDiff ℝ 1 f) (c : V) {R : ℝ} (hR : 0 < R)
    (hzero : ∀ x, x ∉ Metric.closedBall c R → f x ≤ 0) :
    MemW01p 2 (fun x => _root_.Max.max (f x) 0) (Metric.ball c R) := by
  let χ := ballCutoff c R (R + 1)
  let F := fun x => χ x * f x
  have hFc : ContDiff ℝ 1 F := ((ballCutoff_contDiff c R (R + 1)).of_le (by norm_cast)).mul hf
  have hFs : HasCompactSupport F :=
    (ballCutoff_hasCompactSupport hR.le (by linarith : R < R + 1)).mul_right
  let Ω := Metric.ball c (R + 2)
  let : _root_.MeasureTheory.IsFiniteMeasure (volume.restrict Ω) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  obtain ⟨hw, hgrad⟩ := exists_memW1pWitness_of_contDiffOn_closedBall isOpen_univ hFc.contDiffOn
    (_root_.Set.subset_univ (Metric.closedBall c (R + 2))) 2
  let hpw := hw.posPart Metric.isOpen_ball ⟨fun _ => F, fun _ => hFc, fun _ => hFs,
    by simp, fun i => by simp [hgrad]⟩
  have hpz (x : V) (hx : x ∉ Metric.closedBall c R) : _root_.Max.max (F x) 0 = 0 := by
    apply max_eq_right
    exact mul_nonpos_of_nonneg_of_nonpos (ballCutoff_mem_Icc c R (R + 1) x).1 (hzero x hx)
  have hps : tsupport (fun x => _root_.Max.max (F x) 0) ⊆ Metric.closedBall c R :=
    closure_minimal (fun x hx => by by_contra h; exact hx (hpz x h)) Metric.isClosed_closedBall
  have hpc : HasCompactSupport (fun x => _root_.Max.max (F x) 0) :=
    (_root_.ProperSpace.isCompact_closedBall c R).of_isClosed_subset (isClosed_tsupport _) hps
  have hp0 : MemW01p 2 (fun x => _root_.Max.max (F x) 0) Ω := by
    have hh : MemW1p (ENNReal.ofReal 2) (fun x => _root_.Max.max (F x) 0) Ω := by
      simpa only [ENNReal.ofReal_ofNat] using hpw.memW1p
    simpa only [ENNReal.ofReal_ofNat] using memW01p_of_memW1p_of_tsupport_subset
      Metric.isOpen_ball (by norm_num : (1 : ℝ) < 2) hh hpc
      (hps.trans (Metric.closedBall_subset_ball (by linarith : R < R + 2)))
  have hglobal : MemW01p 2 (Ω.indicator (fun x => _root_.Max.max (F x) 0)) univ := by
    have hh : MemW01p (ENNReal.ofReal 2) (fun x => _root_.Max.max (F x) 0) Ω := by
      simpa only [ENNReal.ofReal_ofNat] using hp0
    simpa only [ENNReal.ofReal_ofNat] using zeroExtend_memW01p_p Metric.isOpen_ball
      (by norm_num : (1 : ℝ) < 2) hh
  have hbound := memW01p_ball_of_global_memW1pWitness_of_zero_outside_closedBall
    hglobal.memW1p.someWitness c hR (fun x hx => by
      by_cases hxm : x ∈ Ω
      · rw [_root_.Set.indicator_of_mem hxm, hpz x hx]
      · exact _root_.Set.indicator_of_notMem hxm _)
  apply hbound.congr
  filter_upwards [_root_.MeasureTheory.ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
  have hxΩ : x ∈ Ω := Metric.ball_subset_ball (by linarith : R ≤ R + 2) hx
  rw [_root_.Set.indicator_of_mem hxΩ]
  have hχx : χ x = 1 := ballCutoff_eq_one_of_mem_closedBall hR.le
    (by linarith : R < R + 1) (Metric.ball_subset_closedBall hx)
  simp only [F, hχx, one_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.memW01p_pos_part_of_nonpos_outside_closedBall then
    throwError "Refusing to shadow existing declaration DeGiorgi.memW01p_pos_part_of_nonpos_outside_closedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.memW01p_pos_part_of_nonpos_outside_closedBall ``Submission.DeGiorgi.memW01p_pos_part_of_nonpos_outside_closedBall

end DeGiorgi

end

end
