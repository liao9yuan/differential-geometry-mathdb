import Submission.DifferentialGeometry.Analysis.Sobolev.Approximation.WeakSolution.Construction
import Submission.DifferentialGeometry.Analysis.Sobolev.Solutions.WeakSolution
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.Density
import Submission.DifferentialGeometry.Analysis.Sobolev.Tools.Mollification.WeakDerivative

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory _root_.Metric _root_.Filter _root_.Topology _root_.Set _root_.Function
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergNonSmooth
open scoped _root_.ENNReal _root_.NNReal _root_.Convolution _root_.Pointwise _root_.BigOperators

namespace DifferentialGeometry.Analysis.Sobolev.H1WeakSolutionApprox

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

private structure H1WeakSolutionData
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω) (u f : E → ℝ) where
  hu_l2 : _root_.MeasureTheory.MemLp u 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)
  hf_l2 : _root_.MeasureTheory.MemLp f 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)
  weakPartial : Fin d → (E → ℝ)
  weakPartial_l2 : ∀ j, _root_.MeasureTheory.MemLp (weakPartial j) 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)
  weakPartial_isWeak : ∀ j,
    DeGiorgi.HasWeakPartialDeriv (d := d) j (weakPartial j) u Set.univ
  isWeakSolution : B.IsWeakSolution u f
  fseqL2Bound : ℝ
  fseq_l2_bound_nn : 0 ≤ fseqL2Bound
  fseq_l2_bounded : ∀ n : ℕ,
    _root_.MeasureTheory.eLpNorm (B.classicalApply
      (mollifyEps (d := d) (show (0 : ℝ) < 1 / ((n : ℝ) + 2) by positivity) u))
      2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) ≤ ENNReal.ofReal fseqL2Bound

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.H1WeakSolutionApprox.H1WeakSolutionData
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.H1WeakSolutionApprox.H1WeakSolutionData target :: scope.openDecls } }

omit [NeZero d] in
private lemma contDiff_mollifyEps_of_memLp_two
    {ε : ℝ} (hε : 0 < ε) {u : E → ℝ}
    (hu : _root_.MeasureTheory.MemLp u 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)) :
    ContDiff ℝ (⊤ : ℕ∞) (mollifyEps (d := d) hε u) :=
  mollifyEps_contDiff hε (hu.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.H1WeakSolutionApprox.contDiff_mollifyEps_of_memLp_two
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.H1WeakSolutionApprox.contDiff_mollifyEps_of_memLp_two target :: scope.openDecls } }

private lemma is_smooth_weak_solution_mollifyEps
    {Ω : Set E} (hΩ : IsOpen Ω) (B : SmoothEllipticBilinearForm d Ω)
    {u : E → ℝ} (hu : _root_.MeasureTheory.MemLp u 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E))
    {ε : ℝ} (hε : 0 < ε) :
    B.IsSmoothWeakSolution
      (mollifyEps (d := d) hε u)
      (B.classicalApply (mollifyEps (d := d) hε u)) :=
  SmoothEllipticBilinearForm.mollifyEps_isSmoothWeakSolution_classicalApply
    (d := d) hΩ B (hu.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)) hε

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.H1WeakSolutionApprox.is_smooth_weak_solution_mollifyEps
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.H1WeakSolutionApprox.is_smooth_weak_solution_mollifyEps target :: scope.openDecls } }

omit [NeZero d] in
private lemma memLp_two_restrict_of_memLp_two
    {f : E → ℝ} (hf : _root_.MeasureTheory.MemLp f 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)) (S : Set E) :
    MemLp f 2 (volume.restrict S) :=
  hf.restrict S

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.H1WeakSolutionApprox.memLp_two_restrict_of_memLp_two
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.H1WeakSolutionApprox.memLp_two_restrict_of_memLp_two target :: scope.openDecls } }

omit [NeZero d] in
private lemma integral_sq_le_eLpNorm_sq
    {f : E → ℝ} (hf : _root_.MeasureTheory.MemLp f 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E))
    {S : Set E} (_hS_open : IsOpen S) :
    ∫ x in S, (f x) ^ 2 ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) ≤
      ((_root_.MeasureTheory.eLpNorm f 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)).toReal) ^ 2 := by
  classical
  have hf_sq_int : _root_.MeasureTheory.Integrable (fun x => (f x) ^ 2) (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) := by
    have h_norm_eq : ∀ x : E, (f x) ^ 2 = ‖f x‖ ^ (2 : ℝ) := by
      intro x
      rw [Real.norm_eq_abs, ← sq_abs, ← Real.rpow_natCast, Nat.cast_ofNat]
    have h_funeq : (fun x : E => (f x) ^ 2) = (fun x : E => ‖f x‖ ^ (2 : ℝ)) := by
      funext x; exact h_norm_eq x
    rw [h_funeq]
    have := hf.integrable_norm_rpow (p := 2) (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
    simpa using this
  have h_int_le_E :
      ∫ x in S, (f x) ^ 2 ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) ≤
      ∫ x, (f x) ^ 2 ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) := by
    refine _root_.MeasureTheory.integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall (fun x => sq_nonneg _)) hf_sq_int
  have h_int_E : ∫ x, (f x) ^ 2 ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) =
      ((_root_.MeasureTheory.eLpNorm f 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)).toReal) ^ 2 := by
    have h_norm_eq : ∀ x : E, (f x) ^ 2 = ‖f x‖ ^ (2 : ℝ) := by
      intro x
      rw [Real.norm_eq_abs, ← sq_abs, ← Real.rpow_natCast, Nat.cast_ofNat]
    have h_funeq_int : ∫ x, (f x) ^ 2 ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) =
        ∫ x, ‖f x‖ ^ (2 : ℝ) ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) := by
      refine _root_.MeasureTheory.integral_congr_ae ?_
      filter_upwards with x using h_norm_eq x
    rw [h_funeq_int]
    have h_2_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
    have h_2_ne_top : (2 : ℝ≥0∞) ≠ ∞ := by norm_num
    have h_eLp := hf.eLpNorm_eq_integral_rpow_norm h_2_ne_zero h_2_ne_top
    have h_2_toReal : ((2 : ℝ≥0∞).toReal) = (2 : ℝ) := by norm_num
    rw [h_2_toReal] at h_eLp
    have h_int_nn : 0 ≤ ∫ x, ‖f x‖ ^ (2 : ℝ) ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) :=
      _root_.MeasureTheory.integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _
    have h_pow_nn : 0 ≤ (∫ x, ‖f x‖ ^ (2 : ℝ) ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)) ^ ((2 : ℝ)⁻¹) :=
      Real.rpow_nonneg h_int_nn _
    have hh : (_root_.MeasureTheory.eLpNorm f 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)).toReal =
        (∫ x, ‖f x‖ ^ (2 : ℝ) ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)) ^ ((2 : ℝ)⁻¹) := by
      rw [h_eLp]
      exact ENNReal.toReal_ofReal h_pow_nn
    rw [hh]
    rw [← Real.rpow_two]
    rw [← Real.rpow_mul h_int_nn]
    norm_num
  rw [h_int_E] at h_int_le_E
  exact h_int_le_E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.H1WeakSolutionApprox.integral_sq_le_eLpNorm_sq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.H1WeakSolutionApprox.integral_sq_le_eLpNorm_sq target :: scope.openDecls } }

private theorem exists_smoothApproximation_of_h1WeakSolutionData
    {Ω : Set E} (hΩ : IsOpen Ω) (B : SmoothEllipticBilinearForm d Ω)
    {u f : E → ℝ}
    (D : H1WeakSolutionData B u f) :
    Nonempty (SmoothApproximation B u f) := by
  classical
  set εFun : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 2) with hεFun_def
  have hε_pos : ∀ n, 0 < εFun n := fun n => by
    rw [hεFun_def]
    positivity
  set uSeq : ℕ → E → ℝ := fun n => mollifyEps (d := d) (hε_pos n) u with huSeq_def
  set fSeq : ℕ → E → ℝ := fun n => B.classicalApply (uSeq n) with hfSeq_def
  have huSeq_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (uSeq n) := fun n =>
    contDiff_mollifyEps_of_memLp_two (hε_pos n) D.hu_l2
  have huSeq_cont : ∀ n, Continuous (uSeq n) := fun n => (huSeq_smooth n).continuous
  have hfSeq_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (fSeq n) := fun n =>
    SmoothEllipticBilinearForm.contDiff_classicalApply (d := d) B (huSeq_smooth n)
  have hfSeq_cont : ∀ n, Continuous (fSeq n) := fun n => (hfSeq_smooth n).continuous
  have h_smooth_weak : ∀ n, B.IsSmoothWeakSolution (uSeq n) (fSeq n) := fun n =>
    is_smooth_weak_solution_mollifyEps hΩ B D.hu_l2 (hε_pos n)
  have hgrad_cont : ∀ n, ∀ j : Fin d,
      Continuous (fun x : E => (fderiv ℝ (uSeq n) x)
        (EuclideanSpace.single j 1)) := fun n j =>
    ((huSeq_smooth n).continuous_fderiv (by simp)).clm_apply continuous_const
  have huSeq_l2 : ∀ n, _root_.MeasureTheory.MemLp (uSeq n) 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) := fun n => by
    have h_eLp : _root_.MeasureTheory.eLpNorm (uSeq n) 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) ≤
        eLpNorm u 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) :=
      eLpNorm_mollifyEps_le (hε_pos n) D.hu_l2
    refine ⟨?_, ?_⟩
    · exact (huSeq_cont n).aestronglyMeasurable
    · exact lt_of_le_of_lt h_eLp D.hu_l2.eLpNorm_lt_top
  have hgrad_l2 : ∀ n, ∀ j : Fin d, _root_.MeasureTheory.MemLp
      (fun x : E => (fderiv ℝ (uSeq n) x) (EuclideanSpace.single j 1))
      2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) := fun n j => by
    have h_eLp : _root_.MeasureTheory.eLpNorm
        (fun x : E => (fderiv ℝ (uSeq n) x) (EuclideanSpace.single j 1)) 2
        (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) ≤
      eLpNorm (D.weakPartial j) 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) :=
      eLpNorm_partial_mollifyEps_le_of_weakPartial_univ (hε_pos n)
        (D.hu_l2.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))
        (D.weakPartial_l2 j) (D.weakPartial_isWeak j)
    refine ⟨?_, ?_⟩
    · exact (hgrad_cont n j).aestronglyMeasurable
    · exact lt_of_le_of_lt h_eLp (D.weakPartial_l2 j).eLpNorm_lt_top
  have hfSeq_l2 : ∀ n, _root_.MeasureTheory.MemLp (fSeq n) 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) := fun n => by
    refine ⟨?_, ?_⟩
    · exact (hfSeq_cont n).aestronglyMeasurable
    · have h_bound := D.fseq_l2_bounded n
      have hM_top : ENNReal.ofReal D.fseqL2Bound ≠ ∞ := ENNReal.ofReal_ne_top
      exact lt_of_le_of_lt h_bound (lt_of_le_of_ne le_top hM_top)
  set DB : ℝ :=
    ((_root_.MeasureTheory.eLpNorm u 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)).toReal) ^ 2 +
      ∑ j : Fin d, ((_root_.MeasureTheory.eLpNorm (D.weakPartial j) 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)).toReal) ^ 2 +
        ((_root_.MeasureTheory.eLpNorm f 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)).toReal) ^ 2 +
        D.fseqL2Bound ^ 2 with hDB_def
  have hDB_nn : 0 ≤ DB := by
    refine add_nonneg (add_nonneg (add_nonneg (sq_nonneg _) ?_) (sq_nonneg _))
      (sq_nonneg _)
    exact Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have hf_seq_l2_local : ∀ n, ∀ {S : Set E}, IsCompact (closure S) →
      MemLp (fSeq n) 2 (volume.restrict S) := fun n {S} _ =>
    memLp_two_restrict_of_memLp_two (hfSeq_l2 n) S
  have hu_seq_l2_local : ∀ n, ∀ {S : Set E}, IsCompact (closure S) →
      MemLp (uSeq n) 2 (volume.restrict S) := fun n {S} _ =>
    memLp_two_restrict_of_memLp_two (huSeq_l2 n) S
  have hgrad_seq_l2_local : ∀ n, ∀ {S : Set E}, IsCompact (closure S) →
      ∀ j : Fin d, _root_.MeasureTheory.MemLp
        (fun y : E => (fderiv ℝ (uSeq n) y) (EuclideanSpace.single j 1))
        2 (volume.restrict S) := fun n {S} _ j =>
    memLp_two_restrict_of_memLp_two (hgrad_l2 n j) S
  refine ⟨{
    uSeq := uSeq
    fSeq := fSeq
    u_seq_smooth := huSeq_smooth
    is_smooth_weak_solution := h_smooth_weak
    f_seq_l2_local := hf_seq_l2_local
    u_seq_l2_local := hu_seq_l2_local
    grad_seq_l2_local := hgrad_seq_l2_local
    dataBound := DB
    data_bound_nn := hDB_nn
    data_integrated_bound := ?_
  }⟩
  intro Ω' hΩ'_open _hΩ'_cc
  refine ⟨1, by norm_num, fun n => ?_⟩
  have h_grad_each : ∀ j : Fin d,
      ∫ y in Ω', ((fderiv ℝ (uSeq n) y) (EuclideanSpace.single j 1)) ^ 2
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) ≤
      ((_root_.MeasureTheory.eLpNorm (D.weakPartial j) 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)).toReal) ^ 2 := by
    intro j
    have h_partial_bound := integral_sq_le_eLpNorm_sq (hgrad_l2 n j) hΩ'_open
    refine h_partial_bound.trans ?_
    have h_eLp_bound :
        _root_.MeasureTheory.eLpNorm (fun x : E => (fderiv ℝ (uSeq n) x)
            (EuclideanSpace.single j 1)) 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) ≤
        eLpNorm (D.weakPartial j) 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) :=
      eLpNorm_partial_mollifyEps_le_of_weakPartial_univ (hε_pos n)
        (D.hu_l2.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))
        (D.weakPartial_l2 j) (D.weakPartial_isWeak j)
    have h_lhs_top : _root_.MeasureTheory.eLpNorm (fun x : E => (fderiv ℝ (uSeq n) x)
        (EuclideanSpace.single j 1)) 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) ≠ ∞ :=
      (hgrad_l2 n j).eLpNorm_ne_top
    have h_rhs_top : _root_.MeasureTheory.eLpNorm (D.weakPartial j) 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) ≠ ∞ :=
      (D.weakPartial_l2 j).eLpNorm_ne_top
    have h_toReal_le := (ENNReal.toReal_le_toReal h_lhs_top h_rhs_top).mpr h_eLp_bound
    have h_lhs_nn : 0 ≤ (_root_.MeasureTheory.eLpNorm (fun x : E => (fderiv ℝ (uSeq n) x)
        (EuclideanSpace.single j 1)) 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)).toReal :=
      ENNReal.toReal_nonneg
    have h_rhs_nn : 0 ≤ (_root_.MeasureTheory.eLpNorm (D.weakPartial j) 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)).toReal :=
      ENNReal.toReal_nonneg
    exact pow_le_pow_left₀ h_lhs_nn h_toReal_le 2
  have h_u_bound :
      ∫ y in Ω', (uSeq n y) ^ 2 ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) ≤
      ((_root_.MeasureTheory.eLpNorm u 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)).toReal) ^ 2 := by
    refine (integral_sq_le_eLpNorm_sq (huSeq_l2 n) hΩ'_open).trans ?_
    have h_eLp_bound : _root_.MeasureTheory.eLpNorm (uSeq n) 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) ≤
        eLpNorm u 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) :=
      eLpNorm_mollifyEps_le (hε_pos n) D.hu_l2
    have h_lhs_top : _root_.MeasureTheory.eLpNorm (uSeq n) 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) ≠ ∞ :=
      (huSeq_l2 n).eLpNorm_ne_top
    have h_rhs_top : _root_.MeasureTheory.eLpNorm u 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) ≠ ∞ :=
      D.hu_l2.eLpNorm_ne_top
    have h_toReal_le := (ENNReal.toReal_le_toReal h_lhs_top h_rhs_top).mpr h_eLp_bound
    have h_lhs_nn : 0 ≤ (_root_.MeasureTheory.eLpNorm (uSeq n) 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)).toReal :=
      ENNReal.toReal_nonneg
    exact pow_le_pow_left₀ h_lhs_nn h_toReal_le 2
  have h_f_bound :
      ∫ y in Ω', (fSeq n y) ^ 2 ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) ≤
      D.fseqL2Bound ^ 2 := by
    refine (integral_sq_le_eLpNorm_sq (hfSeq_l2 n) hΩ'_open).trans ?_
    have h_eLp_bound : _root_.MeasureTheory.eLpNorm (fSeq n) 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) ≤
        ENNReal.ofReal D.fseqL2Bound := D.fseq_l2_bounded n
    have h_lhs_top : _root_.MeasureTheory.eLpNorm (fSeq n) 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) ≠ ∞ :=
      (hfSeq_l2 n).eLpNorm_ne_top
    have h_rhs_top : ENNReal.ofReal D.fseqL2Bound ≠ ∞ := ENNReal.ofReal_ne_top
    have h_toReal_le :
        (_root_.MeasureTheory.eLpNorm (fSeq n) 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)).toReal ≤
          (ENNReal.ofReal D.fseqL2Bound).toReal :=
      (ENNReal.toReal_le_toReal h_lhs_top h_rhs_top).mpr h_eLp_bound
    rw [ENNReal.toReal_ofReal D.fseq_l2_bound_nn] at h_toReal_le
    have h_lhs_nn : 0 ≤ (_root_.MeasureTheory.eLpNorm (fSeq n) 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)).toReal :=
      ENNReal.toReal_nonneg
    exact pow_le_pow_left₀ h_lhs_nn h_toReal_le 2
  have h_grad_sum_int :
      ∫ y in Ω', ∑ j : Fin d,
          ((fderiv ℝ (uSeq n) y) (EuclideanSpace.single j 1)) ^ 2
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) =
      ∑ j : Fin d, ∫ y in Ω',
          ((fderiv ℝ (uSeq n) y) (EuclideanSpace.single j 1)) ^ 2
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) := by
    refine _root_.MeasureTheory.integral_finsetSum (μ := (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E).restrict Ω') Finset.univ ?_
    intro j _
    have h_norm_eq : ∀ y : E,
        ((fderiv ℝ (uSeq n) y) (EuclideanSpace.single j 1)) ^ 2 =
        ‖((fderiv ℝ (uSeq n) y) (EuclideanSpace.single j 1))‖ ^ (2 : ℝ) := by
      intro y
      rw [Real.norm_eq_abs, ← sq_abs, ← Real.rpow_natCast, Nat.cast_ofNat]
    have h_funeq : (fun y : E =>
        ((fderiv ℝ (uSeq n) y) (EuclideanSpace.single j 1)) ^ 2) =
        (fun y : E =>
        ‖((fderiv ℝ (uSeq n) y) (EuclideanSpace.single j 1))‖ ^ (2 : ℝ)) := by
      funext y; exact h_norm_eq y
    rw [h_funeq]
    have h_int_E : _root_.MeasureTheory.Integrable (fun y : E =>
        ‖((fderiv ℝ (uSeq n) y) (EuclideanSpace.single j 1))‖ ^ (2 : ℝ))
        (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) := by
      have := (hgrad_l2 n j).integrable_norm_rpow
        (p := 2) (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
      simpa using this
    exact h_int_E.restrict
  rw [h_grad_sum_int]
  have h_grad_sum_le :
      ∑ j : Fin d, ∫ y in Ω',
          ((fderiv ℝ (uSeq n) y) (EuclideanSpace.single j 1)) ^ 2
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) ≤
      ∑ j : Fin d, ((_root_.MeasureTheory.eLpNorm (D.weakPartial j) 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)).toReal) ^ 2 :=
    Finset.sum_le_sum (fun j _ => h_grad_each j)
  have h_combined :
      (∑ j : Fin d, ∫ y in Ω',
          ((fderiv ℝ (uSeq n) y) (EuclideanSpace.single j 1)) ^ 2
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)) +
      (∫ y in Ω', (uSeq n y) ^ 2 ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)) +
      (∫ y in Ω', (fSeq n y) ^ 2 ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)) ≤
      (∑ j : Fin d, ((_root_.MeasureTheory.eLpNorm (D.weakPartial j) 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)).toReal) ^ 2) +
      ((_root_.MeasureTheory.eLpNorm u 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)).toReal) ^ 2 +
      D.fseqL2Bound ^ 2 := by
    linarith
  refine h_combined.trans ?_
  rw [hDB_def]
  rw [one_mul]
  have h_f_nn : 0 ≤ ((_root_.MeasureTheory.eLpNorm f 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)).toReal) ^ 2 := sq_nonneg _
  linarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.H1WeakSolutionApprox.exists_smoothApproximation_of_h1WeakSolutionData
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.H1WeakSolutionApprox.exists_smoothApproximation_of_h1WeakSolutionData target :: scope.openDecls } }

theorem exists_smoothApproximation_of_h1_weak_solution
    {Ω : Set E} (hΩ : IsOpen Ω) (B : SmoothEllipticBilinearForm d Ω)
    {u f : E → ℝ}
    (hu_l2 : _root_.MeasureTheory.MemLp u 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E))
    (hu_grad_l2 : ∀ j : Fin d, ∃ g : E → ℝ,
      _root_.MeasureTheory.MemLp g 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) ∧
      DeGiorgi.HasWeakPartialDeriv (d := d) j g u Set.univ)
    (hf_l2 : _root_.MeasureTheory.MemLp f 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E))
    (h_weak : B.IsWeakSolution u f)
    {M_F : ℝ} (hMF_nn : 0 ≤ M_F)
    (hMF_bound : ∀ n : ℕ,
      _root_.MeasureTheory.eLpNorm
        (B.classicalApply (mollifyEps (d := d)
          (show (0 : ℝ) < 1 / ((n : ℝ) + 2) by positivity) u))
        2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) ≤ ENNReal.ofReal M_F) :
    Nonempty (SmoothApproximation B u f) := by
  classical
  set wp : Fin d → (E → ℝ) := fun j => Classical.choose (hu_grad_l2 j) with hwp_def
  have hwp_l2 : ∀ j, _root_.MeasureTheory.MemLp (wp j) 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) := fun j =>
    (Classical.choose_spec (hu_grad_l2 j)).1
  have hwp_isWeak : ∀ j,
      DeGiorgi.HasWeakPartialDeriv (d := d) j (wp j) u Set.univ := fun j =>
    (Classical.choose_spec (hu_grad_l2 j)).2
  let D : H1WeakSolutionData B u f :=
    { hu_l2 := hu_l2
      hf_l2 := hf_l2
      weakPartial := wp
      weakPartial_l2 := hwp_l2
      weakPartial_isWeak := hwp_isWeak
      isWeakSolution := h_weak
      fseqL2Bound := M_F
      fseq_l2_bound_nn := hMF_nn
      fseq_l2_bounded := hMF_bound }
  exact exists_smoothApproximation_of_h1WeakSolutionData hΩ B D

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.H1WeakSolutionApprox.exists_smoothApproximation_of_h1_weak_solution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.H1WeakSolutionApprox.exists_smoothApproximation_of_h1_weak_solution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.H1WeakSolutionApprox.exists_smoothApproximation_of_h1_weak_solution ``Submission.DifferentialGeometry.Analysis.Sobolev.H1WeakSolutionApprox.exists_smoothApproximation_of_h1_weak_solution

end DifferentialGeometry.Analysis.Sobolev.H1WeakSolutionApprox
