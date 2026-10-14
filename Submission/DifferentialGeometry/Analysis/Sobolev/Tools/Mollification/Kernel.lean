import Submission.DifferentialGeometry.Analysis.Sobolev.Tools.Translation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.MeasureTheory _root_.Metric _root_.Filter _root_.Topology _root_.Set _root_.Function
open scoped _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Analysis.Sobolev

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

def mollifierBump : ContDiffBump (0 : E) where
  rIn := 1 / 2
  rOut := 1
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.mollifierBump then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.mollifierBump"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.mollifierBump ``Submission.DifferentialGeometry.Analysis.Sobolev.mollifierBump

def mollifier : E → ℝ := mollifierBump.normed (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.mollifier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.mollifier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.mollifier ``Submission.DifferentialGeometry.Analysis.Sobolev.mollifier

omit [NeZero d] in
theorem mollifier_smooth :
    ContDiff ℝ (⊤ : ℕ∞) (mollifier (d := d)) :=
  (mollifierBump (d := d)).contDiff_normed

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.mollifier_smooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.mollifier_smooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.mollifier_smooth ``Submission.DifferentialGeometry.Analysis.Sobolev.mollifier_smooth

omit [NeZero d] in
theorem mollifier_continuous :
    Continuous (mollifier (d := d)) :=
  (mollifierBump (d := d)).continuous_normed

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.mollifier_continuous then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.mollifier_continuous"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.mollifier_continuous ``Submission.DifferentialGeometry.Analysis.Sobolev.mollifier_continuous

omit [NeZero d] in
theorem mollifier_nonneg (x : E) : 0 ≤ mollifier (d := d) x :=
  (mollifierBump (d := d)).nonneg_normed x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.mollifier_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.mollifier_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.mollifier_nonneg ``Submission.DifferentialGeometry.Analysis.Sobolev.mollifier_nonneg

omit [NeZero d] in
theorem mollifier_integral_eq_one :
    ∫ x, mollifier (d := d) x ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) = 1 :=
  (mollifierBump (d := d)).integral_normed

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.mollifier_integral_eq_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.mollifier_integral_eq_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.mollifier_integral_eq_one ``Submission.DifferentialGeometry.Analysis.Sobolev.mollifier_integral_eq_one

omit [NeZero d] in
theorem mollifier_integrable :
    Integrable (mollifier (d := d)) (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) :=
  (mollifierBump (d := d)).integrable_normed

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.mollifier_integrable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.mollifier_integrable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.mollifier_integrable ``Submission.DifferentialGeometry.Analysis.Sobolev.mollifier_integrable

omit [NeZero d] in
theorem mollifier_compactSupport : HasCompactSupport (mollifier (d := d)) :=
  (mollifierBump (d := d)).hasCompactSupport_normed

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.mollifier_compactSupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.mollifier_compactSupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.mollifier_compactSupport ``Submission.DifferentialGeometry.Analysis.Sobolev.mollifier_compactSupport

omit [NeZero d] in
theorem mollifier_support_eq :
    Function.support (mollifier (d := d)) = Metric.ball (0 : E) 1 := by
  unfold mollifier
  simpa [mollifierBump] using (mollifierBump (d := d)).support_normed_eq (μ := _root_.MeasureTheory.MeasureSpace.volume)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.mollifier_support_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.mollifier_support_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.mollifier_support_eq ``Submission.DifferentialGeometry.Analysis.Sobolev.mollifier_support_eq

omit [NeZero d] in
theorem mollifier_tsupport_eq :
    tsupport (mollifier (d := d)) = Metric.closedBall (0 : E) 1 := by
  unfold mollifier
  simpa [mollifierBump] using (mollifierBump (d := d)).tsupport_normed_eq (μ := _root_.MeasureTheory.MeasureSpace.volume)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.mollifier_tsupport_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.mollifier_tsupport_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.mollifier_tsupport_eq ``Submission.DifferentialGeometry.Analysis.Sobolev.mollifier_tsupport_eq

omit [NeZero d] in
theorem mollifier_support_subset_closedBall_one :
    Function.support (mollifier (d := d)) ⊆ Metric.closedBall (0 : E) 1 := by
  rw [mollifier_support_eq]
  exact Metric.ball_subset_closedBall

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.mollifier_support_subset_closedBall_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.mollifier_support_subset_closedBall_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.mollifier_support_subset_closedBall_one ``Submission.DifferentialGeometry.Analysis.Sobolev.mollifier_support_subset_closedBall_one

def mollifierBumpEps {ε : ℝ} (hε : 0 < ε) : ContDiffBump (0 : E) where
  rIn := ε / 2
  rOut := ε
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.mollifierBumpEps then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.mollifierBumpEps"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.mollifierBumpEps ``Submission.DifferentialGeometry.Analysis.Sobolev.mollifierBumpEps

def mollifierEps {ε : ℝ} (hε : 0 < ε) : E → ℝ :=
  (mollifierBumpEps (d := d) hε).normed (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.mollifierEps then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.mollifierEps"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.mollifierEps ``Submission.DifferentialGeometry.Analysis.Sobolev.mollifierEps

omit [NeZero d] in
theorem mollifierEps_smooth {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (mollifierEps (d := d) hε) :=
  (mollifierBumpEps (d := d) hε).contDiff_normed

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.mollifierEps_smooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.mollifierEps_smooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.mollifierEps_smooth ``Submission.DifferentialGeometry.Analysis.Sobolev.mollifierEps_smooth

omit [NeZero d] in
theorem mollifierEps_continuous {ε : ℝ} (hε : 0 < ε) :
    Continuous (mollifierEps (d := d) hε) :=
  (mollifierBumpEps (d := d) hε).continuous_normed

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.mollifierEps_continuous then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.mollifierEps_continuous"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.mollifierEps_continuous ``Submission.DifferentialGeometry.Analysis.Sobolev.mollifierEps_continuous

omit [NeZero d] in
theorem mollifierEps_nonneg {ε : ℝ} (hε : 0 < ε) (x : E) :
    0 ≤ mollifierEps (d := d) hε x :=
  (mollifierBumpEps (d := d) hε).nonneg_normed x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.mollifierEps_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.mollifierEps_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.mollifierEps_nonneg ``Submission.DifferentialGeometry.Analysis.Sobolev.mollifierEps_nonneg

omit [NeZero d] in
theorem mollifierEps_integral_eq_one {ε : ℝ} (hε : 0 < ε) :
    ∫ x, mollifierEps (d := d) hε x ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) = 1 :=
  (mollifierBumpEps (d := d) hε).integral_normed

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.mollifierEps_integral_eq_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.mollifierEps_integral_eq_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.mollifierEps_integral_eq_one ``Submission.DifferentialGeometry.Analysis.Sobolev.mollifierEps_integral_eq_one

omit [NeZero d] in
theorem mollifierEps_integrable {ε : ℝ} (hε : 0 < ε) :
    Integrable (mollifierEps (d := d) hε) (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) :=
  (mollifierBumpEps (d := d) hε).integrable_normed

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.mollifierEps_integrable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.mollifierEps_integrable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.mollifierEps_integrable ``Submission.DifferentialGeometry.Analysis.Sobolev.mollifierEps_integrable

omit [NeZero d] in
theorem mollifierEps_compactSupport {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (mollifierEps (d := d) hε) :=
  (mollifierBumpEps (d := d) hε).hasCompactSupport_normed

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.mollifierEps_compactSupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.mollifierEps_compactSupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.mollifierEps_compactSupport ``Submission.DifferentialGeometry.Analysis.Sobolev.mollifierEps_compactSupport

omit [NeZero d] in
theorem mollifierEps_support_eq {ε : ℝ} (hε : 0 < ε) :
    Function.support (mollifierEps (d := d) hε) = Metric.ball (0 : E) ε := by
  unfold mollifierEps
  simpa [mollifierBumpEps] using
    (mollifierBumpEps (d := d) hε).support_normed_eq (μ := _root_.MeasureTheory.MeasureSpace.volume)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.mollifierEps_support_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.mollifierEps_support_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.mollifierEps_support_eq ``Submission.DifferentialGeometry.Analysis.Sobolev.mollifierEps_support_eq

omit [NeZero d] in
theorem mollifierEps_tsupport_eq {ε : ℝ} (hε : 0 < ε) :
    tsupport (mollifierEps (d := d) hε) = Metric.closedBall (0 : E) ε := by
  unfold mollifierEps
  simpa [mollifierBumpEps] using
    (mollifierBumpEps (d := d) hε).tsupport_normed_eq (μ := _root_.MeasureTheory.MeasureSpace.volume)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.mollifierEps_tsupport_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.mollifierEps_tsupport_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.mollifierEps_tsupport_eq ``Submission.DifferentialGeometry.Analysis.Sobolev.mollifierEps_tsupport_eq

omit [NeZero d] in
theorem mollifierEps_support_subset_closedBall_eps
    {ε : ℝ} (hε : 0 < ε) :
    Function.support (mollifierEps (d := d) hε) ⊆ Metric.closedBall (0 : E) ε := by
  rw [mollifierEps_support_eq]
  exact Metric.ball_subset_closedBall

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.mollifierEps_support_subset_closedBall_eps then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.mollifierEps_support_subset_closedBall_eps"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.mollifierEps_support_subset_closedBall_eps ``Submission.DifferentialGeometry.Analysis.Sobolev.mollifierEps_support_subset_closedBall_eps

omit [NeZero d] in
theorem mollifierEps_tsupport_subset_closedBall_eps
    {ε : ℝ} (hε : 0 < ε) :
    tsupport (mollifierEps (d := d) hε) ⊆ Metric.closedBall (0 : E) ε := by
  rw [mollifierEps_tsupport_eq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.mollifierEps_tsupport_subset_closedBall_eps then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.mollifierEps_tsupport_subset_closedBall_eps"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.mollifierEps_tsupport_subset_closedBall_eps ``Submission.DifferentialGeometry.Analysis.Sobolev.mollifierEps_tsupport_subset_closedBall_eps

end DifferentialGeometry.Analysis.Sobolev
