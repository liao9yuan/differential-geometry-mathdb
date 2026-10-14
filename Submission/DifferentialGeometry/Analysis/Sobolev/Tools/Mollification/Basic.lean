import Submission.DifferentialGeometry.Analysis.Sobolev.Tools.Mollification.Kernel
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.MeasureTheory _root_.Metric _root_.Filter _root_.Topology _root_.Set _root_.Function
open scoped _root_.ENNReal _root_.NNReal _root_.Convolution _root_.Pointwise _root_.BigOperators _root_.InnerProductSpace
  RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Sobolev

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

def mollifyEps {ε : ℝ} (hε : 0 < ε) (u : E → ℝ) : E → ℝ :=
  DifferentialGeometry.Analysis.Sobolev.mollifierEps (d := d) hε ⋆[
    ContinuousLinearMap.lsmul ℝ ℝ, (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)] u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.mollifyEps then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.mollifyEps"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.mollifyEps ``Submission.DifferentialGeometry.Analysis.Sobolev.mollifyEps

omit [NeZero d] in
theorem mollifyEps_contDiff {ε : ℝ} (hε : 0 < ε) {u : E → ℝ}
    (hu_local : _root_.MeasureTheory.LocallyIntegrable u (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)) :
    ContDiff ℝ (⊤ : ℕ∞) (mollifyEps (d := d) hε u) := by
  unfold mollifyEps
  exact HasCompactSupport.contDiff_convolution_left
    (L := ContinuousLinearMap.lsmul ℝ ℝ)
    (DifferentialGeometry.Analysis.Sobolev.mollifierEps_compactSupport hε)
    (DifferentialGeometry.Analysis.Sobolev.mollifierEps_smooth hε)
    hu_local

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.mollifyEps_contDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.mollifyEps_contDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.mollifyEps_contDiff ``Submission.DifferentialGeometry.Analysis.Sobolev.mollifyEps_contDiff

omit [NeZero d] in
theorem mollifyEps_continuous {ε : ℝ} (hε : 0 < ε) {u : E → ℝ}
    (hu_local : _root_.MeasureTheory.LocallyIntegrable u (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)) :
    Continuous (mollifyEps (d := d) hε u) :=
  (mollifyEps_contDiff (d := d) hε hu_local).continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.mollifyEps_continuous then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.mollifyEps_continuous"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.mollifyEps_continuous ``Submission.DifferentialGeometry.Analysis.Sobolev.mollifyEps_continuous

omit [NeZero d] in
lemma mollifyEps_apply {ε : ℝ} (hε : 0 < ε) (u : E → ℝ) (x : E) :
    mollifyEps (d := d) hε u x =
      ∫ t,
        DifferentialGeometry.Analysis.Sobolev.mollifierEps (d := d) hε t * u (x - t)
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) := by
  simp [mollifyEps, MeasureTheory.convolution_def,
    ContinuousLinearMap.lsmul_apply, smul_eq_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.mollifyEps_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.mollifyEps_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.mollifyEps_apply ``Submission.DifferentialGeometry.Analysis.Sobolev.mollifyEps_apply

omit [NeZero d] in
theorem mollifyEps_eq_convolution_swap
    {ε : ℝ} (hε : 0 < ε) (u : E → ℝ) (x : E) :
    mollifyEps (d := d) hε u x =
      (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)]
        mollifierEps (d := d) hε) x := by
  classical
  unfold mollifyEps
  rw [_root_.MeasureTheory.convolution_lsmul, _root_.MeasureTheory.convolution_lsmul_swap]
  refine _root_.MeasureTheory.integral_congr_ae ?_
  filter_upwards with t
  rw [smul_eq_mul, smul_eq_mul, mul_comm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.mollifyEps_eq_convolution_swap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.mollifyEps_eq_convolution_swap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.mollifyEps_eq_convolution_swap ``Submission.DifferentialGeometry.Analysis.Sobolev.mollifyEps_eq_convolution_swap

omit [NeZero d] in
theorem mollifyEps_hasCompactSupport {ε : ℝ} (hε : 0 < ε) {u : E → ℝ}
    (hu_support : HasCompactSupport u) :
    HasCompactSupport (mollifyEps (d := d) hε u) :=
  HasCompactSupport.convolution (L := ContinuousLinearMap.lsmul ℝ ℝ)
    (μ := (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E))
    (DifferentialGeometry.Analysis.Sobolev.mollifierEps_compactSupport hε)
    hu_support

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.mollifyEps_hasCompactSupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.mollifyEps_hasCompactSupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.mollifyEps_hasCompactSupport ``Submission.DifferentialGeometry.Analysis.Sobolev.mollifyEps_hasCompactSupport

omit [NeZero d] in
theorem mollifyEps_memLp_two_of_hasCompactSupport {ε : ℝ} (hε : 0 < ε)
    {u : E → ℝ} (hu_l2 : _root_.MeasureTheory.MemLp u 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E))
    (hu_support : HasCompactSupport u) :
    MemLp (mollifyEps (d := d) hε u) 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) := by
  have hu_local : _root_.MeasureTheory.LocallyIntegrable u (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) :=
    hu_l2.locallyIntegrable (by norm_num)
  have h_cont : Continuous (mollifyEps (d := d) hε u) :=
    mollifyEps_continuous (d := d) hε hu_local
  have h_support : HasCompactSupport (mollifyEps (d := d) hε u) :=
    mollifyEps_hasCompactSupport (d := d) hε hu_support
  exact h_cont.memLp_of_hasCompactSupport h_support

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.mollifyEps_memLp_two_of_hasCompactSupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.mollifyEps_memLp_two_of_hasCompactSupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.mollifyEps_memLp_two_of_hasCompactSupport ``Submission.DifferentialGeometry.Analysis.Sobolev.mollifyEps_memLp_two_of_hasCompactSupport

omit [NeZero d] in
theorem tendsto_mollifyEps_of_continuous {ι : Type*} {l : Filter ι}
    {ε : ι → ℝ} (hε : ∀ i, 0 < ε i) (hε_tendsto : _root_.Filter.Tendsto ε l (𝓝 0))
    {u : E → ℝ} (hu : Continuous u) (x₀ : E) :
    Tendsto (fun i => mollifyEps (d := d) (hε i) u x₀) l (𝓝 (u x₀)) := by
  have h_bump_rOut : ∀ i,
      (DifferentialGeometry.Analysis.Sobolev.mollifierBumpEps (d := d) (hε i)).rOut
        = ε i := by
    intro i
    show (DifferentialGeometry.Analysis.Sobolev.mollifierBumpEps (d := d) (hε i)).rOut
        = ε i
    rfl
  have h_rOut_tendsto :
      _root_.Filter.Tendsto
        (fun i => (DifferentialGeometry.Analysis.Sobolev.mollifierBumpEps
            (d := d) (hε i)).rOut)
        l (𝓝 0) := by
    have h_funeq : (fun i => (DifferentialGeometry.Analysis.Sobolev.mollifierBumpEps
        (d := d) (hε i)).rOut) = ε := by
      funext i; exact h_bump_rOut i
    rw [h_funeq]
    exact hε_tendsto
  have h_convergence_tendsto :
      _root_.Filter.Tendsto
        (fun i =>
          ((DifferentialGeometry.Analysis.Sobolev.mollifierBumpEps (d := d)
              (hε i)).normed (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) ⋆[
              ContinuousLinearMap.lsmul ℝ ℝ, (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)] u) x₀)
        l (𝓝 (u x₀)) :=
    ContDiffBump.convolution_tendsto_right_of_continuous (μ := (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E))
      h_rOut_tendsto hu x₀
  have h_fn_eq : ∀ i,
      ((DifferentialGeometry.Analysis.Sobolev.mollifierBumpEps (d := d)
            (hε i)).normed (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) ⋆[
            ContinuousLinearMap.lsmul ℝ ℝ, (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)] u) x₀
        = mollifyEps (d := d) (hε i) u x₀ := by
    intro i
    show ((DifferentialGeometry.Analysis.Sobolev.mollifierBumpEps (d := d)
            (hε i)).normed (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) ⋆[
            ContinuousLinearMap.lsmul ℝ ℝ, (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)] u) x₀
        = mollifyEps (d := d) (hε i) u x₀
    rfl
  refine h_convergence_tendsto.congr ?_
  intro i; exact h_fn_eq i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.tendsto_mollifyEps_of_continuous then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.tendsto_mollifyEps_of_continuous"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.tendsto_mollifyEps_of_continuous ``Submission.DifferentialGeometry.Analysis.Sobolev.tendsto_mollifyEps_of_continuous

omit [NeZero d] in
theorem ae_tendsto_mollifyEps_of_locallyIntegrable {ι : Type*} {l : Filter ι}
    {ε : ι → ℝ} (hε : ∀ i, 0 < ε i) (hε_tendsto : _root_.Filter.Tendsto ε l (𝓝 0))
    {u : E → ℝ} (hu_local : _root_.MeasureTheory.LocallyIntegrable u (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)) :
    ∀ᵐ x₀ ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E),
      Tendsto (fun i => mollifyEps (d := d) (hε i) u x₀) l (𝓝 (u x₀)) := by
  have h_bump_rOut : ∀ i,
      (DifferentialGeometry.Analysis.Sobolev.mollifierBumpEps (d := d) (hε i)).rOut
        = ε i := by
    intro i
    show (DifferentialGeometry.Analysis.Sobolev.mollifierBumpEps (d := d) (hε i)).rOut
        = ε i
    rfl
  have h_bump_rIn : ∀ i,
      (DifferentialGeometry.Analysis.Sobolev.mollifierBumpEps (d := d) (hε i)).rIn
        = ε i / 2 := by
    intro i
    show (DifferentialGeometry.Analysis.Sobolev.mollifierBumpEps (d := d) (hε i)).rIn
        = ε i / 2
    rfl
  have h_rOut_tendsto :
      _root_.Filter.Tendsto
        (fun i =>
          (DifferentialGeometry.Analysis.Sobolev.mollifierBumpEps (d := d) (hε i)).rOut)
        l (𝓝 0) := by
    have h_funeq : (fun i => (DifferentialGeometry.Analysis.Sobolev.mollifierBumpEps
        (d := d) (hε i)).rOut) = ε := by
      funext i; exact h_bump_rOut i
    rw [h_funeq]
    exact hε_tendsto
  have h_ratio :
      ∀ᶠ i in l,
        (DifferentialGeometry.Analysis.Sobolev.mollifierBumpEps (d := d) (hε i)).rOut
          ≤ 2 *
            (DifferentialGeometry.Analysis.Sobolev.mollifierBumpEps (d := d)
              (hε i)).rIn := by
    refine Filter.Eventually.of_forall fun i => ?_
    rw [h_bump_rOut, h_bump_rIn]
    have : ε i = 2 * (ε i / 2) := by ring
    linarith
  have h_ae :=
    ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      (μ := (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)) h_rOut_tendsto h_ratio hu_local
  filter_upwards [h_ae] with x₀ hx₀
  have h_eq : ∀ i,
      ((DifferentialGeometry.Analysis.Sobolev.mollifierBumpEps (d := d)
          (hε i)).normed (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) ⋆[
          ContinuousLinearMap.lsmul ℝ ℝ, (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)] u) x₀
        = mollifyEps (d := d) (hε i) u x₀ := by
    intro i
    show ((DifferentialGeometry.Analysis.Sobolev.mollifierBumpEps (d := d)
          (hε i)).normed (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) ⋆[
          ContinuousLinearMap.lsmul ℝ ℝ, (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)] u) x₀
        = mollifyEps (d := d) (hε i) u x₀
    rfl
  refine hx₀.congr ?_
  intro i; exact h_eq i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.ae_tendsto_mollifyEps_of_locallyIntegrable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.ae_tendsto_mollifyEps_of_locallyIntegrable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.ae_tendsto_mollifyEps_of_locallyIntegrable ``Submission.DifferentialGeometry.Analysis.Sobolev.ae_tendsto_mollifyEps_of_locallyIntegrable

end DifferentialGeometry.Analysis.Sobolev
