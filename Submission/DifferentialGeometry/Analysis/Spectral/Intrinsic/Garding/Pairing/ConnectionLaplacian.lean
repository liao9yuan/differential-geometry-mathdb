import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.Spectrum.SobolevScaleSummability
import Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.Commutation.CovariantDivergence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private noncomputable def pointInnerLeft
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (T : TensorRSModel r s ℝ E) : TensorRSModel r s ℝ E →+ ℝ where
  toFun := fun S => tensorInnerPointwise (I := I) (M := M) g r s x S T
  map_zero' := tensorInnerPointwise_zero_left (I := I) (M := M) g r s x T
  map_add' := fun S₁ S₂ => tensorInnerPointwise_add_left
    (I := I) (M := M) g r s x S₁ S₂ T

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.pointInnerLeft
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.pointInnerLeft target :: scope.openDecls } }

private noncomputable def pointInnerRight
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (S : TensorRSModel r s ℝ E) : TensorRSModel r s ℝ E →+ ℝ where
  toFun := fun T => tensorInnerPointwise (I := I) (M := M) g r s x S T
  map_zero' := tensorInnerPointwise_zero_right (I := I) (M := M) g r s x S
  map_add' := tensorInnerPointwise_add_right (I := I) (M := M) g r s x S

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.pointInnerRight
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.pointInnerRight target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] in
private theorem l2_sub_left_cc (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S₁ S₂ T : SmoothCcTensor g r s) :
    tensorL2Inner (I := I) (M := M) g r s (S₁.toFun - S₂.toFun) T.toFun =
      tensorL2Inner (I := I) (M := M) g r s S₁.toFun T.toFun -
        tensorL2Inner (I := I) (M := M) g r s S₂.toFun T.toFun := by
  unfold tensorL2Inner
  rw [← MeasureTheory.integral_sub
    (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) S₁ T)
    (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) S₂ T)]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  change tensorInnerPointwise (I := I) (M := M) g r s x
      (S₁.toFun x - S₂.toFun x) (T.toFun x) = _
  exact map_sub (pointInnerLeft (I := I) (M := M) g r s x (T.toFun x))
    (S₁.toFun x) (S₂.toFun x)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.l2_sub_left_cc
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.l2_sub_left_cc target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] in
private theorem l2_sub_right_cc (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T₁ T₂ : SmoothCcTensor g r s) :
    tensorL2Inner (I := I) (M := M) g r s S.toFun (T₁.toFun - T₂.toFun) =
      tensorL2Inner (I := I) (M := M) g r s S.toFun T₁.toFun -
        tensorL2Inner (I := I) (M := M) g r s S.toFun T₂.toFun := by
  unfold tensorL2Inner
  rw [← MeasureTheory.integral_sub
    (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) S T₁)
    (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) S T₂)]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  change tensorInnerPointwise (I := I) (M := M) g r s x
      (S.toFun x) (T₁.toFun x - T₂.toFun x) = _
  exact map_sub (pointInnerRight (I := I) (M := M) g r s x (S.toFun x))
    (T₁.toFun x) (T₂.toFun x)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.l2_sub_right_cc
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.l2_sub_right_cc target :: scope.openDecls } }


omit [CompactSpace M] in
theorem oneMinusConnLapSmooth_l2Inner_selfAdjoint
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T v : SmoothCcTensor g r s) :
    tensorL2Inner (I := I) (M := M) g r s
        (oneMinusConnLapSmooth (I := I) g r s T).toFun v.toFun =
      tensorL2Inner (I := I) (M := M) g r s T.toFun
        (oneMinusConnLapSmooth (I := I) g r s v).toFun := by
  have hTfun : (oneMinusConnLapSmooth (I := I) g r s T).toFun =
      T.toFun - (rawTensorConnLapSmooth (I := I) g r s T).toFun := by
    unfold oneMinusConnLapSmooth
    rw [SmoothCcTensor.toFun_sub]
  have hvfun : (oneMinusConnLapSmooth (I := I) g r s v).toFun =
      v.toFun - (rawTensorConnLapSmooth (I := I) g r s v).toFun := by
    unfold oneMinusConnLapSmooth
    rw [SmoothCcTensor.toFun_sub]
  rw [hTfun, hvfun,
    l2_sub_left_cc (I := I) (M := M) g r s T
      (rawTensorConnLapSmooth (I := I) g r s T) v,
    l2_sub_right_cc (I := I) (M := M) g r s T v
      (rawTensorConnLapSmooth (I := I) g r s v)]
  rw [rawTensorConnLapSmooth_l2Inner_selfAdjoint (I := I) (M := M) g r s T v]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.oneMinusConnLapSmooth_l2Inner_selfAdjoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.oneMinusConnLapSmooth_l2Inner_selfAdjoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.oneMinusConnLapSmooth_l2Inner_selfAdjoint ``Submission.DifferentialGeometry.Analysis.Spectral.oneMinusConnLapSmooth_l2Inner_selfAdjoint

omit [CompactSpace M] in
theorem oneMinusConnLapSmooth_l2Inner_eq_add_covGrad
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (A B : SmoothCcTensor g r s) :
    tensorL2Inner (I := I) (M := M) g r s
        (oneMinusConnLapSmooth (I := I) g r s A).toFun B.toFun =
      tensorL2Inner (I := I) (M := M) g r s A.toFun B.toFun +
        tensorL2Inner (I := I) (M := M) g r (s + 1)
          (covGrad (I := I) (M := M) g r s A).toFun
          (covGrad (I := I) (M := M) g r s B).toFun := by
  have hAfun : (oneMinusConnLapSmooth (I := I) g r s A).toFun =
      A.toFun - (rawTensorConnLapSmooth (I := I) g r s A).toFun := by
    unfold oneMinusConnLapSmooth
    rw [SmoothCcTensor.toFun_sub]
  have hgreen := tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawTensorConnLapSmooth_rs
    (I := I) (M := M) g r s A B
  rw [hAfun,
    l2_sub_left_cc (I := I) (M := M) g r s A
      (rawTensorConnLapSmooth (I := I) g r s A) B,
    hgreen]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.oneMinusConnLapSmooth_l2Inner_eq_add_covGrad then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.oneMinusConnLapSmooth_l2Inner_eq_add_covGrad"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.oneMinusConnLapSmooth_l2Inner_eq_add_covGrad ``Submission.DifferentialGeometry.Analysis.Spectral.oneMinusConnLapSmooth_l2Inner_eq_add_covGrad


omit [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
theorem oneMinusConnLapSmoothIter_oneMinusConnLapSmooth_comm
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (k : ℕ) (v : SmoothCcTensor g r s) :
    oneMinusConnLapSmoothIter (I := I) g r s k
        (oneMinusConnLapSmooth (I := I) g r s v) =
      oneMinusConnLapSmooth (I := I) g r s
        (oneMinusConnLapSmoothIter (I := I) g r s k v) := by
  induction k with
  | zero => simp only [oneMinusConnLapSmoothIter_zero]
  | succ p ih =>
    rw [oneMinusConnLapSmoothIter_succ, ih, oneMinusConnLapSmoothIter_succ]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.oneMinusConnLapSmoothIter_oneMinusConnLapSmooth_comm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.oneMinusConnLapSmoothIter_oneMinusConnLapSmooth_comm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.oneMinusConnLapSmoothIter_oneMinusConnLapSmooth_comm ``Submission.DifferentialGeometry.Analysis.Spectral.oneMinusConnLapSmoothIter_oneMinusConnLapSmooth_comm


omit [CompactSpace M] in
theorem oneMinusConnLapSmoothIter_l2Inner_selfAdjoint
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (n : ℕ)
    (T v : SmoothCcTensor g r s) :
    tensorL2Inner (I := I) (M := M) g r s
        (oneMinusConnLapSmoothIter (I := I) g r s n T).toFun v.toFun =
      tensorL2Inner (I := I) (M := M) g r s T.toFun
        (oneMinusConnLapSmoothIter (I := I) g r s n v).toFun := by
  induction n generalizing v with
  | zero => simp only [oneMinusConnLapSmoothIter_zero]
  | succ k ih =>
    rw [oneMinusConnLapSmoothIter_succ, oneMinusConnLapSmoothIter_succ]
    rw [oneMinusConnLapSmooth_l2Inner_selfAdjoint (I := I) (M := M) g r s
      (oneMinusConnLapSmoothIter (I := I) g r s k T) v]
    rw [ih (oneMinusConnLapSmooth (I := I) g r s v),
      oneMinusConnLapSmoothIter_oneMinusConnLapSmooth_comm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.oneMinusConnLapSmoothIter_l2Inner_selfAdjoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.oneMinusConnLapSmoothIter_l2Inner_selfAdjoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.oneMinusConnLapSmoothIter_l2Inner_selfAdjoint ``Submission.DifferentialGeometry.Analysis.Spectral.oneMinusConnLapSmoothIter_l2Inner_selfAdjoint


omit [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
theorem oneMinusConnLapSmoothIter_add
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (a b : ℕ)
    (T : SmoothCcTensor g r s) :
    oneMinusConnLapSmoothIter (I := I) g r s (a + b) T =
      oneMinusConnLapSmoothIter (I := I) g r s a
        (oneMinusConnLapSmoothIter (I := I) g r s b T) := by
  induction a with
  | zero => simp only [Nat.zero_add, oneMinusConnLapSmoothIter_zero]
  | succ k ih =>
    rw [show k + 1 + b = (k + b) + 1 from by omega, oneMinusConnLapSmoothIter_succ,
      oneMinusConnLapSmoothIter_succ, ih]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.oneMinusConnLapSmoothIter_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.oneMinusConnLapSmoothIter_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.oneMinusConnLapSmoothIter_add ``Submission.DifferentialGeometry.Analysis.Spectral.oneMinusConnLapSmoothIter_add


omit [CompactSpace M] in
theorem oneMinusConnLapSmoothIter_l2Inner_sym_split
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (a b : ℕ)
    (A B : SmoothCcTensor g r s) :
    tensorL2Inner (I := I) (M := M) g r s
        (oneMinusConnLapSmoothIter (I := I) g r s (a + b) A).toFun B.toFun =
      tensorL2Inner (I := I) (M := M) g r s
        (oneMinusConnLapSmoothIter (I := I) g r s b A).toFun
        (oneMinusConnLapSmoothIter (I := I) g r s a B).toFun := by
  rw [oneMinusConnLapSmoothIter_add (I := I) (M := M) g r s a b A]
  rw [oneMinusConnLapSmoothIter_l2Inner_selfAdjoint (I := I) (M := M) g r s a
    (oneMinusConnLapSmoothIter (I := I) g r s b A) B]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.oneMinusConnLapSmoothIter_l2Inner_sym_split then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.oneMinusConnLapSmoothIter_l2Inner_sym_split"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.oneMinusConnLapSmoothIter_l2Inner_sym_split ``Submission.DifferentialGeometry.Analysis.Spectral.oneMinusConnLapSmoothIter_l2Inner_sym_split

omit [CompactSpace M] in
theorem oneMinusConnLapSmoothIter_l2Inner_eq_add_sum_covGrad
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (n : ℕ)
    (A B : SmoothCcTensor g r s) :
    tensorL2Inner (I := I) (M := M) g r s
        (oneMinusConnLapSmoothIter (I := I) g r s n A).toFun B.toFun =
      tensorL2Inner (I := I) (M := M) g r s A.toFun B.toFun +
        ∑ m ∈ Finset.range n,
          tensorL2Inner (I := I) (M := M) g r (s + 1)
            (covGrad (I := I) (M := M) g r s
              (oneMinusConnLapSmoothIter (I := I) g r s m A)).toFun
            (covGrad (I := I) (M := M) g r s B).toFun := by
  induction n with
  | zero =>
    simp only [oneMinusConnLapSmoothIter_zero, Finset.range_zero, Finset.sum_empty, add_zero]
  | succ k ih =>
    rw [oneMinusConnLapSmoothIter_succ,
      oneMinusConnLapSmooth_l2Inner_eq_add_covGrad (I := I) (M := M) g r s
        (oneMinusConnLapSmoothIter (I := I) g r s k A) B,
      ih, Finset.sum_range_succ]
    ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.oneMinusConnLapSmoothIter_l2Inner_eq_add_sum_covGrad then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.oneMinusConnLapSmoothIter_l2Inner_eq_add_sum_covGrad"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.oneMinusConnLapSmoothIter_l2Inner_eq_add_sum_covGrad ``Submission.DifferentialGeometry.Analysis.Spectral.oneMinusConnLapSmoothIter_l2Inner_eq_add_sum_covGrad


omit [SigmaCompactSpace M] in
omit [CompactSpace M] [I.Boundaryless] in
theorem rawConnLap_add (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (A B : SmoothCcTensor g r s) :
    rawTensorConnLapSmooth (I := I) g r s (A + B) =
      rawTensorConnLapSmooth (I := I) g r s A +
        rawTensorConnLapSmooth (I := I) g r s B := by
  have h0 : rawTensorConnLapSmooth (I := I) g r s (0 : SmoothCcTensor g r s) = 0 := by
    have h := rawTensorConnLapSmooth_sub (I := I) (M := M) g r s A A
    rw [sub_self, sub_self] at h
    exact h
  have hAB : A + B = A - (0 - B) := by abel
  rw [hAB, rawTensorConnLapSmooth_sub (I := I) (M := M) g r s A (0 - B),
    rawTensorConnLapSmooth_sub (I := I) (M := M) g r s 0 B, h0]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.rawConnLap_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.rawConnLap_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.rawConnLap_add ``Submission.DifferentialGeometry.Analysis.Spectral.rawConnLap_add


omit [SigmaCompactSpace M] in
omit [CompactSpace M] [I.Boundaryless] in
theorem oneMinusConn_add (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (A B : SmoothCcTensor g r s) :
    oneMinusConnLapSmooth (I := I) g r s (A + B) =
      oneMinusConnLapSmooth (I := I) g r s A +
        oneMinusConnLapSmooth (I := I) g r s B := by
  unfold oneMinusConnLapSmooth
  rw [rawConnLap_add (I := I) (M := M) g r s A B]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.oneMinusConn_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.oneMinusConn_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.oneMinusConn_add ``Submission.DifferentialGeometry.Analysis.Spectral.oneMinusConn_add


omit [SigmaCompactSpace M] in
omit [CompactSpace M] [I.Boundaryless] in
theorem connLapIter_map_add (g : SmoothRiemannianMetric I M) (r s j : ℕ)
    (A B : SmoothCcTensor g r s) :
    oneMinusConnLapSmoothIter (I := I) g r s j (A + B) =
      oneMinusConnLapSmoothIter (I := I) g r s j A +
        oneMinusConnLapSmoothIter (I := I) g r s j B := by
  induction j with
  | zero => simp only [oneMinusConnLapSmoothIter_zero]
  | succ k ih =>
    rw [oneMinusConnLapSmoothIter_succ, oneMinusConnLapSmoothIter_succ,
      oneMinusConnLapSmoothIter_succ, ih, oneMinusConn_add (I := I) (M := M) g r s]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.connLapIter_map_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.connLapIter_map_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.connLapIter_map_add ``Submission.DifferentialGeometry.Analysis.Spectral.connLapIter_map_add

omit [CompactSpace M] [SigmaCompactSpace M] in
theorem covGrad_oneMinus (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S : SmoothCcTensor g 0 s) :
    covGrad (I := I) (M := M) g 0 s
        (oneMinusConnLapSmooth (I := I) g 0 s S) =
      oneMinusConnLapSmooth (I := I) g 0 (s + 1)
          (covGrad (I := I) (M := M) g 0 s S) +
        pointwiseTensorCurv (I := I) (M := M) g s S := by
  have hcomm := pointwiseTensorCurv_commutator_eq (I := I) (M := M) g s S
  unfold oneMinusConnLapSmooth
  rw [covGrad_sub (I := I) (M := M) g 0 s S
    (rawTensorConnLapSmooth (I := I) g 0 s S)]
  rw [hcomm]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.covGrad_oneMinus then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.covGrad_oneMinus"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.covGrad_oneMinus ``Submission.DifferentialGeometry.Analysis.Spectral.covGrad_oneMinus


omit [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
theorem connLapIter_one (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) :
    oneMinusConnLapSmoothIter (I := I) g r s 1 S =
      oneMinusConnLapSmooth (I := I) g r s S := by
  rw [oneMinusConnLapSmoothIter_succ, oneMinusConnLapSmoothIter_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.connLapIter_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.connLapIter_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.connLapIter_one ``Submission.DifferentialGeometry.Analysis.Spectral.connLapIter_one

omit [SigmaCompactSpace M] in
omit [CompactSpace M] in
theorem covGrad_iterL (g : SmoothRiemannianMetric I M) (s j : ℕ) :
    ∀ S : SmoothCcTensor g 0 s,
      covGrad (I := I) (M := M) g 0 s
          (oneMinusConnLapSmoothIter (I := I) g 0 s j S) =
        oneMinusConnLapSmoothIter (I := I) g 0 (s + 1) j
            (covGrad (I := I) (M := M) g 0 s S) +
          ∑ i ∈ Finset.range j,
            oneMinusConnLapSmoothIter (I := I) g 0 (s + 1) i
              (pointwiseTensorCurv (I := I) (M := M) g s
                (oneMinusConnLapSmoothIter (I := I) g 0 s (j - 1 - i) S)) := by
  induction j with
  | zero =>
    intro S
    simp only [oneMinusConnLapSmoothIter_zero, Finset.range_zero, Finset.sum_empty, add_zero]
  | succ k ih =>
    intro S
    have hsplit : oneMinusConnLapSmoothIter (I := I) g 0 s (k + 1) S =
        oneMinusConnLapSmoothIter (I := I) g 0 s k
          (oneMinusConnLapSmooth (I := I) g 0 s S) := by
      rw [oneMinusConnLapSmoothIter_add (I := I) (M := M) g 0 s k 1 S,
        connLapIter_one (I := I) (M := M) g 0 s S]
    rw [hsplit, ih (oneMinusConnLapSmooth (I := I) g 0 s S)]
    rw [covGrad_oneMinus (I := I) (M := M) g s S]
    rw [connLapIter_map_add (I := I) (M := M) g 0 (s + 1) k
      (oneMinusConnLapSmooth (I := I) g 0 (s + 1)
        (covGrad (I := I) (M := M) g 0 s S))
      (pointwiseTensorCurv (I := I) (M := M) g s S)]
    have hL : oneMinusConnLapSmoothIter (I := I) g 0 (s + 1) k
        (oneMinusConnLapSmooth (I := I) g 0 (s + 1)
          (covGrad (I := I) (M := M) g 0 s S)) =
        oneMinusConnLapSmoothIter (I := I) g 0 (s + 1) (k + 1)
          (covGrad (I := I) (M := M) g 0 s S) := by
      rw [oneMinusConnLapSmoothIter_add (I := I) (M := M) g 0 (s + 1) k 1,
        connLapIter_one (I := I) (M := M) g 0 (s + 1)]
    rw [hL]
    have hsum : ∑ i ∈ Finset.range k,
        oneMinusConnLapSmoothIter (I := I) g 0 (s + 1) i
          (pointwiseTensorCurv (I := I) (M := M) g s
            (oneMinusConnLapSmoothIter (I := I) g 0 s (k - 1 - i)
              (oneMinusConnLapSmooth (I := I) g 0 s S))) =
        ∑ i ∈ Finset.range k,
          oneMinusConnLapSmoothIter (I := I) g 0 (s + 1) i
            (pointwiseTensorCurv (I := I) (M := M) g s
              (oneMinusConnLapSmoothIter (I := I) g 0 s (k + 1 - 1 - i) S)) := by
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [Finset.mem_range] at hi
      have hidx : k + 1 - 1 - i = (k - 1 - i) + 1 := by omega
      rw [hidx, oneMinusConnLapSmoothIter_add (I := I) (M := M) g 0 s
        (k - 1 - i) 1 S, connLapIter_one (I := I) (M := M) g 0 s S]
    rw [hsum]
    rw [Finset.sum_range_succ
      (fun i => oneMinusConnLapSmoothIter (I := I) g 0 (s + 1) i
        (pointwiseTensorCurv (I := I) (M := M) g s
          (oneMinusConnLapSmoothIter (I := I) g 0 s (k + 1 - 1 - i) S))) k]
    rw [show k + 1 - 1 - k = 0 from by omega, oneMinusConnLapSmoothIter_zero]
    abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.covGrad_iterL then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.covGrad_iterL"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.covGrad_iterL ``Submission.DifferentialGeometry.Analysis.Spectral.covGrad_iterL

end Spectral
end Analysis
end DifferentialGeometry
