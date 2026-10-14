import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Embedding.Inclusion

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral

private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}
variable {a : ℝ}

omit [NeZero (Module.finrank ℝ E)] in
lemma tensorSobolevWeight_mid_eq_sqrt_mul_sqrt
    (i : TensorEigenIdx (I := I) (M := M) g r s) (a : ℝ) :
    tensorSobolevWeight (I := I) (M := M) i (a + 1) =
      Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (a + 2)) *
        Real.sqrt (tensorSobolevWeight (I := I) (M := M) i a) := by
  have hbase : (0 : ℝ) < 1 + TensorEigenIdx.lambda (I := I) (M := M) i :=
    lt_of_lt_of_le one_pos (one_le_one_add_lambda (I := I) (M := M) i)
  set x := 1 + TensorEigenIdx.lambda (I := I) (M := M) i with hx
  unfold tensorSobolevWeight
  rw [← hx]
  have hsqrt_u : Real.sqrt (x ^ (a + 2)) = x ^ ((a + 2) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hbase.le]
    congr 1
    ring
  have hsqrt_l : Real.sqrt (x ^ (a : ℝ)) = x ^ (a / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hbase.le]
    congr 1
    ring
  rw [hsqrt_u, hsqrt_l, ← Real.rpow_add hbase]
  congr 1
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorSobolevWeight_mid_eq_sqrt_mul_sqrt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorSobolevWeight_mid_eq_sqrt_mul_sqrt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorSobolevWeight_mid_eq_sqrt_mul_sqrt ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorSobolevWeight_mid_eq_sqrt_mul_sqrt

omit [NeZero (Module.finrank ℝ E)] in
lemma crossPairing_summable
    (v : TensorHs (I := I) (M := M) g r s (a + 2))
    (w : TensorHs (I := I) (M := M) g r s a) :
    Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
      tensorSobolevWeight (I := I) (M := M) i (a + 1) * (v.coeff i * w.coeff i)) := by
  have hv := v.weighted_summable
  have hw := w.weighted_summable
  have h_dom : Summable
      (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
        (1 / 2) * (tensorSobolevWeight (I := I) (M := M) i (a + 2) * (v.coeff i) ^ 2) +
          (1 / 2) * (tensorSobolevWeight (I := I) (M := M) i a * (w.coeff i) ^ 2)) :=
    (hv.mul_left _).add (hw.mul_left _)
  refine Summable.of_norm_bounded h_dom ?_
  intro i
  set wu := tensorSobolevWeight (I := I) (M := M) i (a + 2) with hwu
  set wl := tensorSobolevWeight (I := I) (M := M) i a with hwl
  have hwu0 : 0 ≤ wu := tensorSobolevWeight_nonneg (I := I) (M := M) i (a + 2)
  have hwl0 : 0 ≤ wl := tensorSobolevWeight_nonneg (I := I) (M := M) i a
  have hsplit : tensorSobolevWeight (I := I) (M := M) i (a + 1) =
      Real.sqrt wu * Real.sqrt wl :=
    tensorSobolevWeight_mid_eq_sqrt_mul_sqrt (I := I) (M := M) i a
  rw [Real.norm_eq_abs, hsplit, abs_mul, abs_mul, abs_mul,
    abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _)]
  have hsqu : Real.sqrt wu ^ 2 = wu := Real.sq_sqrt hwu0
  have hsql : Real.sqrt wl ^ 2 = wl := Real.sq_sqrt hwl0
  nlinarith [sq_nonneg (Real.sqrt wu * |v.coeff i| - Real.sqrt wl * |w.coeff i|),
    Real.sqrt_nonneg wu, Real.sqrt_nonneg wl, abs_nonneg (v.coeff i),
    abs_nonneg (w.coeff i), sq_abs (v.coeff i), sq_abs (w.coeff i), hsqu, hsql]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.crossPairing_summable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.crossPairing_summable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.crossPairing_summable ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.crossPairing_summable

def crossPairing
    (v : TensorHs (I := I) (M := M) g r s (a + 2))
    (w : TensorHs (I := I) (M := M) g r s a) : ℝ :=
  ∑' i, tensorSobolevWeight (I := I) (M := M) i (a + 1) * (v.coeff i * w.coeff i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.crossPairing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.crossPairing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.crossPairing ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.crossPairing

omit [NeZero (Module.finrank ℝ E)] in
lemma crossPairing_add_left
    (v v' : TensorHs (I := I) (M := M) g r s (a + 2))
    (w : TensorHs (I := I) (M := M) g r s a) :
    crossPairing (I := I) (M := M) (v + v') w =
      crossPairing (I := I) (M := M) v w + crossPairing (I := I) (M := M) v' w := by
  unfold crossPairing
  rw [← Summable.tsum_add (crossPairing_summable (I := I) (M := M) v w)
    (crossPairing_summable (I := I) (M := M) v' w)]
  refine tsum_congr (fun i => ?_)
  simp only [TensorHs.add_coeff]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.crossPairing_add_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.crossPairing_add_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.crossPairing_add_left ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.crossPairing_add_left

omit [NeZero (Module.finrank ℝ E)] in
lemma crossPairing_add_right
    (v : TensorHs (I := I) (M := M) g r s (a + 2))
    (w w' : TensorHs (I := I) (M := M) g r s a) :
    crossPairing (I := I) (M := M) v (w + w') =
      crossPairing (I := I) (M := M) v w + crossPairing (I := I) (M := M) v w' := by
  unfold crossPairing
  rw [← Summable.tsum_add (crossPairing_summable (I := I) (M := M) v w)
    (crossPairing_summable (I := I) (M := M) v w')]
  refine tsum_congr (fun i => ?_)
  simp only [TensorHs.add_coeff]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.crossPairing_add_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.crossPairing_add_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.crossPairing_add_right ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.crossPairing_add_right

omit [NeZero (Module.finrank ℝ E)] in
lemma crossPairing_smul_left (c : ℝ)
    (v : TensorHs (I := I) (M := M) g r s (a + 2))
    (w : TensorHs (I := I) (M := M) g r s a) :
    crossPairing (I := I) (M := M) (c • v) w =
      c * crossPairing (I := I) (M := M) v w := by
  unfold crossPairing
  rw [← tsum_mul_left]
  refine tsum_congr (fun i => ?_)
  simp only [TensorHs.smul_coeff]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.crossPairing_smul_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.crossPairing_smul_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.crossPairing_smul_left ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.crossPairing_smul_left

omit [NeZero (Module.finrank ℝ E)] in
lemma crossPairing_smul_right (c : ℝ)
    (v : TensorHs (I := I) (M := M) g r s (a + 2))
    (w : TensorHs (I := I) (M := M) g r s a) :
    crossPairing (I := I) (M := M) v (c • w) =
      c * crossPairing (I := I) (M := M) v w := by
  unfold crossPairing
  rw [← tsum_mul_left]
  refine tsum_congr (fun i => ?_)
  simp only [TensorHs.smul_coeff]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.crossPairing_smul_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.crossPairing_smul_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.crossPairing_smul_right ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.crossPairing_smul_right

omit [NeZero (Module.finrank ℝ E)] in
lemma crossPairing_eq_inner_rescale
    (v : TensorHs (I := I) (M := M) g r s (a + 2))
    (w : TensorHs (I := I) (M := M) g r s a) :
    crossPairing (I := I) (M := M) v w =
      (_root_.Inner.inner ℝ (TensorHs.rescaleToL2 (I := I) (M := M) v)
        (TensorHs.rescaleToL2 (I := I) (M := M) w) : ℝ) := by
  rw [lp.inner_eq_tsum]
  unfold crossPairing
  refine tsum_congr (fun i => ?_)
  rw [show (_root_.Inner.inner ℝ ((TensorHs.rescaleToL2 (I := I) (M := M) v : _ → ℝ) i)
          ((TensorHs.rescaleToL2 (I := I) (M := M) w : _ → ℝ) i) : ℝ) =
        (TensorHs.rescaleToL2 (I := I) (M := M) v : _ → ℝ) i *
          (TensorHs.rescaleToL2 (I := I) (M := M) w : _ → ℝ) i by
      simp [RCLike.inner_apply, mul_comm]]
  rw [TensorHs.rescaleToL2_apply, TensorHs.rescaleToL2_apply,
    tensorSobolevWeight_mid_eq_sqrt_mul_sqrt (I := I) (M := M) i a]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.crossPairing_eq_inner_rescale then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.crossPairing_eq_inner_rescale"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.crossPairing_eq_inner_rescale ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.crossPairing_eq_inner_rescale

omit [NeZero (Module.finrank ℝ E)] in
theorem abs_crossPairing_le
    (v : TensorHs (I := I) (M := M) g r s (a + 2))
    (w : TensorHs (I := I) (M := M) g r s a) :
    |crossPairing (I := I) (M := M) v w| ≤ ‖v‖ * ‖w‖ := by
  rw [crossPairing_eq_inner_rescale]
  refine le_trans (abs_real_inner_le_norm _ _) ?_
  have hv : ‖TensorHs.rescaleToL2 (I := I) (M := M) v‖ = ‖v‖ :=
    (TensorHs.rescaleEquivL2 (I := I) (M := M)).norm_map v
  have hw : ‖TensorHs.rescaleToL2 (I := I) (M := M) w‖ = ‖w‖ :=
    (TensorHs.rescaleEquivL2 (I := I) (M := M)).norm_map w
  rw [hv, hw]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.abs_crossPairing_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.abs_crossPairing_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.abs_crossPairing_le ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.abs_crossPairing_le

omit [NeZero (Module.finrank ℝ E)] in
theorem crossPairing_self_eq_normSq
    (v : TensorHs (I := I) (M := M) g r s (a + 2)) :
    crossPairing (I := I) (M := M) v
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          (show a ≤ a + 2 by linarith) v) =
      ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          (show a + 1 ≤ a + 2 by linarith) v‖ ^ 2 := by
  rw [TensorHs.norm_sq_eq_tsum]
  unfold crossPairing
  refine tsum_congr (fun i => ?_)
  rw [tensorHsInclusion_coeff_apply, tensorHsInclusion_coeff_apply, sq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.crossPairing_self_eq_normSq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.crossPairing_self_eq_normSq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.crossPairing_self_eq_normSq ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.crossPairing_self_eq_normSq

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHsInclusion_norm_sq_le
    (v : TensorHs (I := I) (M := M) g r s (a + 2)) :
    ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show a + 1 ≤ a + 2 by linarith) v‖ ^ 2 ≤
      ‖v‖ *
        ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          (show a ≤ a + 2 by linarith) v‖ := by
  rw [← crossPairing_self_eq_normSq (I := I) (M := M) v]
  refine le_trans (le_abs_self _) ?_
  exact abs_crossPairing_le (I := I) (M := M) v
    (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
      (show a ≤ a + 2 by linarith) v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsInclusion_norm_sq_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsInclusion_norm_sq_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsInclusion_norm_sq_le ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsInclusion_norm_sq_le

end DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

end
