import Submission.DifferentialGeometry.Analysis.Spectral.Scalar.EigenIdx
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Hs

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.Spectral

private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Hs.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Hs.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Hs.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Hs.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Hs.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Hs.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Hs.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Hs.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Hs.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Hs.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Hs.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Hs.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

def scalarSobolevWeight {g : SmoothRiemannianMetric I M}
    (i : EigenIdx (I := I) (M := M) g) (σ : ℝ) : ℝ :=
  (1 + EigenIdx.lambda (I := I) (M := M) i) ^ σ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Hs.scalarSobolevWeight then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Hs.scalarSobolevWeight"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Hs.scalarSobolevWeight ``Submission.DifferentialGeometry.Analysis.Sobolev.Hs.scalarSobolevWeight

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma one_le_one_add_lambda {g : SmoothRiemannianMetric I M}
    (i : EigenIdx (I := I) (M := M) g) :
    (1 : ℝ) ≤ 1 + EigenIdx.lambda (I := I) (M := M) i := by
  have h := EigenIdx.lambda_nonneg (I := I) (M := M) i
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Hs.one_le_one_add_lambda then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Hs.one_le_one_add_lambda"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Hs.one_le_one_add_lambda ``Submission.DifferentialGeometry.Analysis.Sobolev.Hs.one_le_one_add_lambda

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma scalarSobolevWeight_pos {g : SmoothRiemannianMetric I M}
    (i : EigenIdx (I := I) (M := M) g) (σ : ℝ) :
    0 < scalarSobolevWeight (I := I) (M := M) i σ := by
  unfold scalarSobolevWeight
  have h : (1 : ℝ) ≤ 1 + EigenIdx.lambda (I := I) (M := M) i :=
    one_le_one_add_lambda (I := I) (M := M) i
  exact Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos h) σ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Hs.scalarSobolevWeight_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Hs.scalarSobolevWeight_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Hs.scalarSobolevWeight_pos ``Submission.DifferentialGeometry.Analysis.Sobolev.Hs.scalarSobolevWeight_pos

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma scalarSobolevWeight_nonneg {g : SmoothRiemannianMetric I M}
    (i : EigenIdx (I := I) (M := M) g) (σ : ℝ) :
    0 ≤ scalarSobolevWeight (I := I) (M := M) i σ :=
  (scalarSobolevWeight_pos (I := I) (M := M) i σ).le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Hs.scalarSobolevWeight_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Hs.scalarSobolevWeight_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Hs.scalarSobolevWeight_nonneg ``Submission.DifferentialGeometry.Analysis.Sobolev.Hs.scalarSobolevWeight_nonneg

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma one_le_scalarSobolevWeight {g : SmoothRiemannianMetric I M}
    (i : EigenIdx (I := I) (M := M) g) {σ : ℝ} (hσ : 0 ≤ σ) :
    1 ≤ scalarSobolevWeight (I := I) (M := M) i σ := by
  unfold scalarSobolevWeight
  exact Real.one_le_rpow (one_le_one_add_lambda (I := I) (M := M) i) hσ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Hs.one_le_scalarSobolevWeight then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Hs.one_le_scalarSobolevWeight"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Hs.one_le_scalarSobolevWeight ``Submission.DifferentialGeometry.Analysis.Sobolev.Hs.one_le_scalarSobolevWeight

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma scalarSobolevWeight_zero {g : SmoothRiemannianMetric I M}
    (i : EigenIdx (I := I) (M := M) g) :
    scalarSobolevWeight (I := I) (M := M) i (0 : ℝ) = 1 := by
  unfold scalarSobolevWeight
  exact Real.rpow_zero _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Hs.scalarSobolevWeight_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Hs.scalarSobolevWeight_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Hs.scalarSobolevWeight_zero ``Submission.DifferentialGeometry.Analysis.Sobolev.Hs.scalarSobolevWeight_zero

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma sq_sqrt_scalarSobolevWeight {g : SmoothRiemannianMetric I M}
    (i : EigenIdx (I := I) (M := M) g) (σ : ℝ) :
    Real.sqrt (scalarSobolevWeight (I := I) (M := M) i σ) ^ 2 =
      scalarSobolevWeight (I := I) (M := M) i σ :=
  Real.sq_sqrt (scalarSobolevWeight_nonneg (I := I) (M := M) i σ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Hs.sq_sqrt_scalarSobolevWeight then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Hs.sq_sqrt_scalarSobolevWeight"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Hs.sq_sqrt_scalarSobolevWeight ``Submission.DifferentialGeometry.Analysis.Sobolev.Hs.sq_sqrt_scalarSobolevWeight

def scalarL2Coeff {g : SmoothRiemannianMetric I M}
    (u : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (i : EigenIdx (I := I) (M := M) g) : ℝ :=
  (resolventHilbertEigenbasisSigma (I := I) (M := M) g).repr u i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Hs.scalarL2Coeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Hs.scalarL2Coeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Hs.scalarL2Coeff ``Submission.DifferentialGeometry.Analysis.Sobolev.Hs.scalarL2Coeff

structure ScalarHs (g : SmoothRiemannianMetric I M) (σ : ℝ) where
  coeff : EigenIdx (I := I) (M := M) g → ℝ
  weighted_summable :
    Summable (fun i => scalarSobolevWeight (I := I) (M := M) i σ *
      (coeff i) ^ 2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs ``Submission.DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs

namespace ScalarHs

variable {g : SmoothRiemannianMetric I M} {σ : ℝ}

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[ext] lemma ext {S T : ScalarHs (I := I) (M := M) g σ}
    (h : S.coeff = T.coeff) : S = T := by
  cases S; cases T; cases h; rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.ext then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.ext"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.ext ``Submission.DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.ext

instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.instZero : Zero (ScalarHs (I := I) (M := M) g σ) where
  zero := ⟨fun _ => 0, by simp⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.instZero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.instZero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.instZero ``Submission.DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.instZero

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma zero_coeff :
    (0 : ScalarHs (I := I) (M := M) g σ).coeff =
      (fun _ => 0) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.zero_coeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.zero_coeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.zero_coeff ``Submission.DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.zero_coeff

instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.instAdd : Add (ScalarHs (I := I) (M := M) g σ) where
  add S T :=
    { coeff := fun i => S.coeff i + T.coeff i
      weighted_summable := by
        have hS := S.weighted_summable
        have hT := T.weighted_summable
        have h_dom : Summable
            (fun i : EigenIdx (I := I) (M := M) g =>
              2 * (scalarSobolevWeight (I := I) (M := M) i σ *
                  (S.coeff i) ^ 2) +
                2 * (scalarSobolevWeight (I := I) (M := M) i σ *
                  (T.coeff i) ^ 2)) :=
          (hS.mul_left 2).add (hT.mul_left 2)
        refine Summable.of_nonneg_of_le ?_ ?_ h_dom
        · intro i
          have hw : 0 ≤ scalarSobolevWeight (I := I) (M := M) i σ :=
            scalarSobolevWeight_nonneg (I := I) (M := M) i σ
          positivity
        · intro i
          have hw : 0 ≤ scalarSobolevWeight (I := I) (M := M) i σ :=
            scalarSobolevWeight_nonneg (I := I) (M := M) i σ
          have h_sq : (S.coeff i + T.coeff i) ^ 2 ≤
              2 * (S.coeff i) ^ 2 + 2 * (T.coeff i) ^ 2 := by
            nlinarith [sq_nonneg (S.coeff i - T.coeff i)]
          calc
            scalarSobolevWeight (I := I) (M := M) i σ *
                  (S.coeff i + T.coeff i) ^ 2
                ≤ scalarSobolevWeight (I := I) (M := M) i σ *
                  (2 * (S.coeff i) ^ 2 + 2 * (T.coeff i) ^ 2) :=
                  mul_le_mul_of_nonneg_left h_sq hw
            _ = 2 * (scalarSobolevWeight (I := I) (M := M) i σ *
                    (S.coeff i) ^ 2) +
                  2 * (scalarSobolevWeight (I := I) (M := M) i σ *
                    (T.coeff i) ^ 2) := by ring }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.instAdd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.instAdd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.instAdd ``Submission.DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.instAdd

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma add_coeff
    (S T : ScalarHs (I := I) (M := M) g σ) :
    (S + T).coeff = (fun i => S.coeff i + T.coeff i) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.add_coeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.add_coeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.add_coeff ``Submission.DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.add_coeff

instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.instNeg : Neg (ScalarHs (I := I) (M := M) g σ) where
  neg S :=
    { coeff := fun i => -S.coeff i
      weighted_summable := by
        have hS := S.weighted_summable
        have h_eq :
            (fun i : EigenIdx (I := I) (M := M) g =>
              scalarSobolevWeight (I := I) (M := M) i σ *
                (-S.coeff i) ^ 2) =
            (fun i => scalarSobolevWeight (I := I) (M := M) i σ *
                (S.coeff i) ^ 2) := by
          funext i; ring
        rwa [h_eq] }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.instNeg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.instNeg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.instNeg ``Submission.DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.instNeg

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma neg_coeff (S : ScalarHs (I := I) (M := M) g σ) :
    (-S).coeff = (fun i => -S.coeff i) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.neg_coeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.neg_coeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.neg_coeff ``Submission.DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.neg_coeff

instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.instSub : Sub (ScalarHs (I := I) (M := M) g σ) where
  sub S T :=
    { coeff := fun i => S.coeff i - T.coeff i
      weighted_summable := by
        have hS := S.weighted_summable
        have hT := T.weighted_summable
        have h_dom : Summable
            (fun i : EigenIdx (I := I) (M := M) g =>
              2 * (scalarSobolevWeight (I := I) (M := M) i σ *
                  (S.coeff i) ^ 2) +
                2 * (scalarSobolevWeight (I := I) (M := M) i σ *
                  (T.coeff i) ^ 2)) :=
          (hS.mul_left 2).add (hT.mul_left 2)
        refine Summable.of_nonneg_of_le ?_ ?_ h_dom
        · intro i
          have hw : 0 ≤ scalarSobolevWeight (I := I) (M := M) i σ :=
            scalarSobolevWeight_nonneg (I := I) (M := M) i σ
          positivity
        · intro i
          have hw : 0 ≤ scalarSobolevWeight (I := I) (M := M) i σ :=
            scalarSobolevWeight_nonneg (I := I) (M := M) i σ
          have h_sq : (S.coeff i - T.coeff i) ^ 2 ≤
              2 * (S.coeff i) ^ 2 + 2 * (T.coeff i) ^ 2 := by
            nlinarith [sq_nonneg (S.coeff i + T.coeff i)]
          calc
            scalarSobolevWeight (I := I) (M := M) i σ *
                  (S.coeff i - T.coeff i) ^ 2
                ≤ scalarSobolevWeight (I := I) (M := M) i σ *
                  (2 * (S.coeff i) ^ 2 + 2 * (T.coeff i) ^ 2) :=
                  mul_le_mul_of_nonneg_left h_sq hw
            _ = 2 * (scalarSobolevWeight (I := I) (M := M) i σ *
                    (S.coeff i) ^ 2) +
                  2 * (scalarSobolevWeight (I := I) (M := M) i σ *
                    (T.coeff i) ^ 2) := by ring }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.instSub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.instSub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.instSub ``Submission.DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.instSub

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma sub_coeff
    (S T : ScalarHs (I := I) (M := M) g σ) :
    (S - T).coeff = (fun i => S.coeff i - T.coeff i) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.sub_coeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.sub_coeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.sub_coeff ``Submission.DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.sub_coeff

instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.instSMulReal : SMul ℝ (ScalarHs (I := I) (M := M) g σ) where
  smul c S :=
    { coeff := fun i => c * S.coeff i
      weighted_summable := by
        have hS := S.weighted_summable
        have h_eq :
            (fun i : EigenIdx (I := I) (M := M) g =>
              scalarSobolevWeight (I := I) (M := M) i σ *
                (c * S.coeff i) ^ 2) =
            (fun i => c ^ 2 * (scalarSobolevWeight (I := I) (M := M) i σ *
                (S.coeff i) ^ 2)) := by
          funext i; ring
        rw [h_eq]
        exact hS.mul_left _ }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.instSMulReal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.instSMulReal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.instSMulReal ``Submission.DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.instSMulReal

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma smul_coeff (c : ℝ)
    (S : ScalarHs (I := I) (M := M) g σ) :
    (c • S).coeff = (fun i => c * S.coeff i) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.smul_coeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.smul_coeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.smul_coeff ``Submission.DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.smul_coeff

instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.instAddCommGroup : AddCommGroup (ScalarHs (I := I) (M := M) g σ) where
  add_assoc S T U := by ext i; simp [add_assoc]
  zero_add S := by ext i; simp
  add_zero S := by ext i; simp
  add_comm S T := by ext i; simp [add_comm]
  neg_add_cancel S := by ext i; simp
  sub_eq_add_neg S T := by ext i; simp [sub_eq_add_neg]
  nsmul := nsmulRec
  zsmul := zsmulRec

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.instAddCommGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.instAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.instAddCommGroup ``Submission.DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.instAddCommGroup

instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.instModuleReal : Module ℝ (ScalarHs (I := I) (M := M) g σ) where
  one_smul S := by ext i; simp
  mul_smul a b S := by ext i; simp [mul_assoc]
  smul_zero c := by ext i; simp
  smul_add c S T := by ext i; simp [mul_add]
  add_smul a b S := by ext i; simp [add_mul]
  zero_smul S := by ext i; simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.instModuleReal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.instModuleReal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.instModuleReal ``Submission.DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.instModuleReal

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma weightedProd_summable
    (S T : ScalarHs (I := I) (M := M) g σ) :
    Summable (fun i : EigenIdx (I := I) (M := M) g =>
      scalarSobolevWeight (I := I) (M := M) i σ *
        (S.coeff i * T.coeff i)) := by
  have hS := S.weighted_summable
  have hT := T.weighted_summable
  have h_dom : Summable
      (fun i : EigenIdx (I := I) (M := M) g =>
        (1 / 2) * (scalarSobolevWeight (I := I) (M := M) i σ *
            (S.coeff i) ^ 2) +
          (1 / 2) * (scalarSobolevWeight (I := I) (M := M) i σ *
            (T.coeff i) ^ 2)) :=
    (hS.mul_left _).add (hT.mul_left _)
  refine Summable.of_norm_bounded h_dom ?_
  intro i
  have hw : 0 ≤ scalarSobolevWeight (I := I) (M := M) i σ :=
    scalarSobolevWeight_nonneg (I := I) (M := M) i σ
  have h_amgm :
      |scalarSobolevWeight (I := I) (M := M) i σ *
          (S.coeff i * T.coeff i)| ≤
        (1 / 2) * (scalarSobolevWeight (I := I) (M := M) i σ *
            (S.coeff i) ^ 2) +
          (1 / 2) * (scalarSobolevWeight (I := I) (M := M) i σ *
            (T.coeff i) ^ 2) := by
    rw [abs_mul, abs_of_nonneg hw]
    have h_prod : |S.coeff i * T.coeff i| ≤
        (1 / 2) * (S.coeff i) ^ 2 + (1 / 2) * (T.coeff i) ^ 2 := by
      rw [abs_mul]
      nlinarith [sq_nonneg (|S.coeff i| - |T.coeff i|),
        abs_nonneg (S.coeff i), abs_nonneg (T.coeff i),
        sq_abs (S.coeff i), sq_abs (T.coeff i)]
    calc
      scalarSobolevWeight (I := I) (M := M) i σ *
            |S.coeff i * T.coeff i|
          ≤ scalarSobolevWeight (I := I) (M := M) i σ *
            ((1 / 2) * (S.coeff i) ^ 2 + (1 / 2) * (T.coeff i) ^ 2) :=
            mul_le_mul_of_nonneg_left h_prod hw
      _ = (1 / 2) * (scalarSobolevWeight (I := I) (M := M) i σ *
              (S.coeff i) ^ 2) +
            (1 / 2) * (scalarSobolevWeight (I := I) (M := M) i σ *
              (T.coeff i) ^ 2) := by ring
  simpa using h_amgm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.weightedProd_summable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.weightedProd_summable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.weightedProd_summable ``Submission.DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.weightedProd_summable

def innerFun (S T : ScalarHs (I := I) (M := M) g σ) : ℝ :=
  ∑' i, scalarSobolevWeight (I := I) (M := M) i σ *
    (S.coeff i * T.coeff i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.innerFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.innerFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.innerFun ``Submission.DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.innerFun

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma innerFun_self (T : ScalarHs (I := I) (M := M) g σ) :
    innerFun (I := I) (M := M) T T =
      ∑' i, scalarSobolevWeight (I := I) (M := M) i σ *
        (T.coeff i) ^ 2 := by
  unfold innerFun
  refine tsum_congr (fun i => ?_)
  rw [sq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.innerFun_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.innerFun_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.innerFun_self ``Submission.DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.innerFun_self

@[reducible] def innerCore :
    InnerProductSpace.Core ℝ
      (ScalarHs (I := I) (M := M) g σ) where
  inner S T := innerFun (I := I) (M := M) S T
  conj_inner_symm S T := by
    simp only [conj_trivial]
    unfold innerFun
    refine tsum_congr (fun i => ?_)
    ring
  re_inner_nonneg T := by
    simp only [RCLike.re_to_real]
    rw [show (innerFun (I := I) (M := M) T T) =
      ∑' i, scalarSobolevWeight (I := I) (M := M) i σ *
        (T.coeff i) ^ 2 from innerFun_self (I := I) (M := M) T]
    refine tsum_nonneg (fun i => ?_)
    have hw : 0 ≤ scalarSobolevWeight (I := I) (M := M) i σ :=
      scalarSobolevWeight_nonneg (I := I) (M := M) i σ
    positivity
  add_left S T U := by
    change innerFun (I := I) (M := M) (S + T) U =
      innerFun (I := I) (M := M) S U + innerFun (I := I) (M := M) T U
    unfold innerFun
    rw [← Summable.tsum_add
      (weightedProd_summable (I := I) (M := M) S U)
      (weightedProd_summable (I := I) (M := M) T U)]
    refine tsum_congr (fun i => ?_)
    simp only [add_coeff]
    ring
  smul_left S T c := by
    simp only [conj_trivial]
    change innerFun (I := I) (M := M) (c • S) T =
      c * innerFun (I := I) (M := M) S T
    unfold innerFun
    rw [← tsum_mul_left]
    refine tsum_congr (fun i => ?_)
    simp only [smul_coeff]
    ring
  definite T hT := by
    rw [show (innerFun (I := I) (M := M) T T) =
      ∑' i, scalarSobolevWeight (I := I) (M := M) i σ *
        (T.coeff i) ^ 2 from innerFun_self (I := I) (M := M) T] at hT
    have h_nonneg : ∀ i : EigenIdx (I := I) (M := M) g,
        0 ≤ scalarSobolevWeight (I := I) (M := M) i σ * (T.coeff i) ^ 2 := by
      intro i
      have hw : 0 ≤ scalarSobolevWeight (I := I) (M := M) i σ :=
        scalarSobolevWeight_nonneg (I := I) (M := M) i σ
      positivity
    have h_zero : ∀ i : EigenIdx (I := I) (M := M) g,
        scalarSobolevWeight (I := I) (M := M) i σ * (T.coeff i) ^ 2 = 0 := by
      intro i
      have h_le := Summable.le_tsum T.weighted_summable i
        (fun j _ => h_nonneg j)
      rw [hT] at h_le
      exact le_antisymm h_le (h_nonneg i)
    ext i
    have hwi : scalarSobolevWeight (I := I) (M := M) i σ * (T.coeff i) ^ 2
        = 0 := h_zero i
    have hw_ne : scalarSobolevWeight (I := I) (M := M) i σ ≠ 0 :=
      (scalarSobolevWeight_pos (I := I) (M := M) i σ).ne'
    have h_sq : (T.coeff i) ^ 2 = 0 := by
      rcases mul_eq_zero.mp hwi with h | h
      · exact absurd h hw_ne
      · exact h
    have : T.coeff i = 0 := by nlinarith [h_sq]
    simpa using this

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.innerCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.innerCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.innerCore ``Submission.DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.innerCore

instance instNormedAddCommGroup :
    NormedAddCommGroup (ScalarHs (I := I) (M := M) g σ) :=
  InnerProductSpace.Core.toNormedAddCommGroup
    (cd := innerCore (I := I) (M := M) (g := g) (σ := σ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.instNormedAddCommGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.instNormedAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.instNormedAddCommGroup ``Submission.DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.instNormedAddCommGroup

instance instInnerProductSpace :
    InnerProductSpace ℝ (ScalarHs (I := I) (M := M) g σ) :=
  InnerProductSpace.ofCore
    (innerCore (I := I) (M := M) (g := g) (σ := σ)).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.instInnerProductSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.instInnerProductSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.instInnerProductSpace ``Submission.DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.instInnerProductSpace

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma inner_def (S T : ScalarHs (I := I) (M := M) g σ) :
    (_root_.Inner.inner ℝ S T : ℝ) =
      ∑' i, scalarSobolevWeight (I := I) (M := M) i σ *
        (S.coeff i * T.coeff i) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.inner_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.inner_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.inner_def ``Submission.DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.inner_def

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma inner_self_eq (T : ScalarHs (I := I) (M := M) g σ) :
    (_root_.Inner.inner ℝ T T : ℝ) =
      ∑' i, scalarSobolevWeight (I := I) (M := M) i σ *
        (T.coeff i) ^ 2 :=
  innerFun_self (I := I) (M := M) T

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.inner_self_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.inner_self_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.inner_self_eq ``Submission.DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.inner_self_eq

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem norm_sq_eq_tsum
    (T : ScalarHs (I := I) (M := M) g σ) :
    ‖T‖ ^ 2 =
      ∑' i, scalarSobolevWeight (I := I) (M := M) i σ *
        (T.coeff i) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_self_eq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.norm_sq_eq_tsum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.norm_sq_eq_tsum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.norm_sq_eq_tsum ``Submission.DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.norm_sq_eq_tsum

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem norm_eq_sqrt_tsum
    (T : ScalarHs (I := I) (M := M) g σ) :
    ‖T‖ =
      Real.sqrt (∑' i, scalarSobolevWeight (I := I) (M := M) i σ *
        (T.coeff i) ^ 2) := by
  rw [← norm_sq_eq_tsum]
  exact (Real.sqrt_sq (norm_nonneg T)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.norm_eq_sqrt_tsum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.norm_eq_sqrt_tsum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.norm_eq_sqrt_tsum ``Submission.DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.norm_eq_sqrt_tsum

end ScalarHs

namespace ScalarHs

variable {g : SmoothRiemannianMetric I M} {σ : ℝ}

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma rescale_memℓp (T : ScalarHs (I := I) (M := M) g σ) :
    Memℓp (fun i : EigenIdx (I := I) (M := M) g =>
      Real.sqrt (scalarSobolevWeight (I := I) (M := M) i σ) *
        T.coeff i) 2 := by
  apply memℓp_gen
  have h_eq :
      (fun i : EigenIdx (I := I) (M := M) g =>
        ‖Real.sqrt (scalarSobolevWeight (I := I) (M := M) i σ) *
            T.coeff i‖ ^ (2 : ℝ≥0∞).toReal) =
      (fun i => scalarSobolevWeight (I := I) (M := M) i σ *
          (T.coeff i) ^ 2) := by
    funext i
    have hpr : ‖Real.sqrt (scalarSobolevWeight (I := I) (M := M) i σ) *
          T.coeff i‖ ^ (2 : ℝ≥0∞).toReal =
        ‖Real.sqrt (scalarSobolevWeight (I := I) (M := M) i σ) *
          T.coeff i‖ ^ (2 : ℕ) := by
      rw [show (2 : ℝ≥0∞).toReal = ((2 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast]
    have hsq : Real.sqrt (scalarSobolevWeight (I := I) (M := M) i σ) ^ 2 =
        scalarSobolevWeight (I := I) (M := M) i σ :=
      sq_sqrt_scalarSobolevWeight (I := I) (M := M) i σ
    rw [hpr, Real.norm_eq_abs, sq_abs, mul_pow, hsq]
  rw [h_eq]
  exact T.weighted_summable

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.rescale_memℓp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.rescale_memℓp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.rescale_memℓp ``Submission.DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.rescale_memℓp

def rescaleToL2 (T : ScalarHs (I := I) (M := M) g σ) :
    lp (fun _ : EigenIdx (I := I) (M := M) g => ℝ) 2 :=
  ⟨fun i => Real.sqrt (scalarSobolevWeight (I := I) (M := M) i σ) *
      T.coeff i, rescale_memℓp (I := I) (M := M) T⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.rescaleToL2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.rescaleToL2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.rescaleToL2 ``Submission.DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.rescaleToL2

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma rescaleToL2_apply
    (T : ScalarHs (I := I) (M := M) g σ)
    (i : EigenIdx (I := I) (M := M) g) :
    (rescaleToL2 (I := I) (M := M) T : _ → ℝ) i =
      Real.sqrt (scalarSobolevWeight (I := I) (M := M) i σ) *
        T.coeff i := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.rescaleToL2_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.rescaleToL2_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.rescaleToL2_apply ``Submission.DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.rescaleToL2_apply

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma rescaleFromL2_weighted_summable
    (f : lp (fun _ : EigenIdx (I := I) (M := M) g => ℝ) 2) :
    Summable (fun i : EigenIdx (I := I) (M := M) g =>
      scalarSobolevWeight (I := I) (M := M) i σ *
        ((Real.sqrt (scalarSobolevWeight (I := I) (M := M) i σ))⁻¹ *
          (f : _ → ℝ) i) ^ 2) := by
  have hf : Summable (fun i : EigenIdx (I := I) (M := M) g =>
      ((f : _ → ℝ) i) ^ 2) := by
    have hmem := lp.memℓp f
    have h := hmem.summable (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
    have hpr : (2 : ℝ≥0∞).toReal = 2 := by norm_num
    have h_eq :
        (fun i : EigenIdx (I := I) (M := M) g =>
          ‖(f : _ → ℝ) i‖ ^ (2 : ℝ≥0∞).toReal) =
        (fun i => ((f : _ → ℝ) i) ^ 2) := by
      funext i
      rw [hpr, Real.norm_eq_abs, ← sq_abs]
      norm_num
    rwa [h_eq] at h
  have h_eq :
      (fun i : EigenIdx (I := I) (M := M) g =>
        scalarSobolevWeight (I := I) (M := M) i σ *
          ((Real.sqrt (scalarSobolevWeight (I := I) (M := M) i σ))⁻¹ *
            (f : _ → ℝ) i) ^ 2) =
      (fun i => ((f : _ → ℝ) i) ^ 2) := by
    funext i
    have hw_pos : 0 < scalarSobolevWeight (I := I) (M := M) i σ :=
      scalarSobolevWeight_pos (I := I) (M := M) i σ
    have hsq : Real.sqrt (scalarSobolevWeight (I := I) (M := M) i σ) ^ 2 =
        scalarSobolevWeight (I := I) (M := M) i σ :=
      sq_sqrt_scalarSobolevWeight (I := I) (M := M) i σ
    rw [mul_pow, inv_pow, hsq]
    rw [← mul_assoc, mul_inv_cancel₀ hw_pos.ne', one_mul]
  rw [h_eq]
  exact hf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.rescaleFromL2_weighted_summable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.rescaleFromL2_weighted_summable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.rescaleFromL2_weighted_summable ``Submission.DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.rescaleFromL2_weighted_summable

def rescaleFromL2
    (f : lp (fun _ : EigenIdx (I := I) (M := M) g => ℝ) 2) :
    ScalarHs (I := I) (M := M) g σ where
  coeff i := (Real.sqrt (scalarSobolevWeight (I := I) (M := M) i σ))⁻¹ *
    (f : _ → ℝ) i
  weighted_summable := rescaleFromL2_weighted_summable (I := I) (M := M) f

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.rescaleFromL2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.rescaleFromL2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.rescaleFromL2 ``Submission.DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.rescaleFromL2

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma rescaleFromL2_coeff
    (f : lp (fun _ : EigenIdx (I := I) (M := M) g => ℝ) 2)
    (i : EigenIdx (I := I) (M := M) g) :
    (rescaleFromL2 (I := I) (M := M) (g := g) (σ := σ) f).coeff i =
      (Real.sqrt (scalarSobolevWeight (I := I) (M := M) i σ))⁻¹ *
        (f : _ → ℝ) i := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.rescaleFromL2_coeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.rescaleFromL2_coeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.rescaleFromL2_coeff ``Submission.DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.rescaleFromL2_coeff

def rescaleEquivL2 :
    ScalarHs (I := I) (M := M) g σ ≃ₗᵢ[ℝ]
      lp (fun _ : EigenIdx (I := I) (M := M) g => ℝ) 2 where
  toFun := rescaleToL2 (I := I) (M := M)
  invFun := rescaleFromL2 (I := I) (M := M)
  map_add' S T := by
    apply lp.ext
    funext i
    simp only [rescaleToL2, lp.coeFn_add, Pi.add_apply, add_coeff]
    ring
  map_smul' c T := by
    apply lp.ext
    funext i
    simp only [rescaleToL2, lp.coeFn_smul, Pi.smul_apply, smul_coeff,
      smul_eq_mul, RingHom.id_apply]
    ring
  left_inv T := by
    ext i
    simp only [rescaleFromL2_coeff, rescaleToL2_apply]
    have hsqrt_pos :
        0 < Real.sqrt (scalarSobolevWeight (I := I) (M := M) i σ) :=
      Real.sqrt_pos.mpr (scalarSobolevWeight_pos (I := I) (M := M) i σ)
    rw [← mul_assoc, inv_mul_cancel₀ hsqrt_pos.ne', one_mul]
  right_inv f := by
    apply lp.ext
    funext i
    simp only [rescaleToL2_apply, rescaleFromL2_coeff]
    have hsqrt_pos :
        0 < Real.sqrt (scalarSobolevWeight (I := I) (M := M) i σ) :=
      Real.sqrt_pos.mpr (scalarSobolevWeight_pos (I := I) (M := M) i σ)
    rw [← mul_assoc, mul_inv_cancel₀ hsqrt_pos.ne', one_mul]
  norm_map' T := by
    have hpr : (2 : ℝ≥0∞).toReal = 2 := by norm_num
    have h_lp_sq :
        ‖rescaleToL2 (I := I) (M := M) T‖ ^ 2 =
          ∑' i, scalarSobolevWeight (I := I) (M := M) i σ *
            (T.coeff i) ^ 2 := by
      have h := lp.norm_rpow_eq_tsum
        (p := 2)
        (E := fun _ : EigenIdx (I := I) (M := M) g => ℝ)
        (by norm_num) (rescaleToL2 (I := I) (M := M) T)
      rw [hpr] at h
      have h_lhs : ‖rescaleToL2 (I := I) (M := M) T‖ ^ (2 : ℝ) =
          ‖rescaleToL2 (I := I) (M := M) T‖ ^ 2 := by norm_cast
      rw [h_lhs] at h
      rw [h]
      refine tsum_congr (fun i => ?_)
      have hsq :
          Real.sqrt (scalarSobolevWeight (I := I) (M := M) i σ) ^ 2 =
            scalarSobolevWeight (I := I) (M := M) i σ :=
        sq_sqrt_scalarSobolevWeight (I := I) (M := M) i σ
      have hcast :
          ‖(rescaleToL2 (I := I) (M := M) T : _ → ℝ) i‖ ^ (2 : ℝ) =
            ‖(rescaleToL2 (I := I) (M := M) T : _ → ℝ) i‖ ^ (2 : ℕ) := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rw [hcast, rescaleToL2_apply, Real.norm_eq_abs, sq_abs, mul_pow, hsq]
    have h_norm_sq : ‖T‖ ^ 2 =
        ∑' i, scalarSobolevWeight (I := I) (M := M) i σ *
          (T.coeff i) ^ 2 :=
      norm_sq_eq_tsum (I := I) (M := M) T
    have h_eq_sq :
        ‖rescaleToL2 (I := I) (M := M) T‖ ^ 2 = ‖T‖ ^ 2 := by
      rw [h_lp_sq, h_norm_sq]
    have h1 : 0 ≤ ‖rescaleToL2 (I := I) (M := M) T‖ := norm_nonneg _
    have h2 : 0 ≤ ‖T‖ := norm_nonneg T
    have := congrArg Real.sqrt h_eq_sq
    rwa [Real.sqrt_sq h1, Real.sqrt_sq h2] at this

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.rescaleEquivL2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.rescaleEquivL2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.rescaleEquivL2 ``Submission.DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.rescaleEquivL2

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma rescaleEquivL2_apply
    (T : ScalarHs (I := I) (M := M) g σ) :
    (rescaleEquivL2 (I := I) (M := M) (g := g) (σ := σ) T : _ → ℝ) =
      (fun i => Real.sqrt (scalarSobolevWeight (I := I) (M := M) i σ) *
        T.coeff i) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.rescaleEquivL2_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.rescaleEquivL2_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.rescaleEquivL2_apply ``Submission.DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.rescaleEquivL2_apply

instance instCompleteSpace :
    CompleteSpace (ScalarHs (I := I) (M := M) g σ) :=
  (rescaleEquivL2 (I := I) (M := M)
    (g := g) (σ := σ)).toIsometryEquiv.completeSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.instCompleteSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.instCompleteSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.instCompleteSpace ``Submission.DifferentialGeometry.Analysis.Sobolev.Hs.ScalarHs.instCompleteSpace

end ScalarHs

abbrev HkScalar (g : SmoothRiemannianMetric I M) (k : ℕ) : Type _ :=
  ScalarHs (I := I) (M := M) g (k : ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Hs.HkScalar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Hs.HkScalar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Hs.HkScalar ``Submission.DifferentialGeometry.Analysis.Sobolev.Hs.HkScalar

end Hs
end Sobolev
end Analysis
end DifferentialGeometry

end
