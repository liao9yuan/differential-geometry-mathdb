import Submission.DifferentialGeometry.Analysis.Sobolev.Embedding.Tensor.Cm
import Submission.DifferentialGeometry.Analysis.Sobolev.Embedding.CovariantDerivative.OrderDropping
import Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert.Hilbert.Density
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Module.Completion

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
    DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev
    DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev.SmoothCcTensorHs
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section
set_option backward.isDefEq.respectTransparency false

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle _root_.Topology _root_.Metric
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators

namespace DifferentialGeometry.Analysis.Sobolev

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev

section NormedSpaceModel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
lemma smoothCcTensor_toSection_add_apply
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (S T : SmoothCcTensor g r s) (x : M) :
    (S + T).toSection x = S.toSection x + T.toSection x := by
  rw [SmoothCcTensor.toSection_add]; rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.smoothCcTensor_toSection_add_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.smoothCcTensor_toSection_add_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.smoothCcTensor_toSection_add_apply ``Submission.DifferentialGeometry.Analysis.Sobolev.smoothCcTensor_toSection_add_apply

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
lemma smoothCcTensor_toSection_sub_apply
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (S T : SmoothCcTensor g r s) (x : M) :
    (S - T).toSection x = S.toSection x - T.toSection x := by
  rw [SmoothCcTensor.toSection_sub]; rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.smoothCcTensor_toSection_sub_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.smoothCcTensor_toSection_sub_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.smoothCcTensor_toSection_sub_apply ``Submission.DifferentialGeometry.Analysis.Sobolev.smoothCcTensor_toSection_sub_apply

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
lemma smoothCcTensor_toSection_smul_apply
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (c : ℝ) (T : SmoothCcTensor g r s) (x : M) :
    (c • T).toSection x = c • (T.toSection x) := by
  rw [SmoothCcTensor.toSection_smul]; rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.smoothCcTensor_toSection_smul_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.smoothCcTensor_toSection_smul_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.smoothCcTensor_toSection_smul_apply ``Submission.DifferentialGeometry.Analysis.Sobolev.smoothCcTensor_toSection_smul_apply

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
lemma smoothCcTensor_toSection_neg_apply
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (T : SmoothCcTensor g r s) (x : M) :
    (-T).toSection x = -(T.toSection x) := by
  rw [SmoothCcTensor.toSection_neg]; rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.smoothCcTensor_toSection_neg_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.smoothCcTensor_toSection_neg_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.smoothCcTensor_toSection_neg_apply ``Submission.DifferentialGeometry.Analysis.Sobolev.smoothCcTensor_toSection_neg_apply

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
lemma smoothCcTensor_toSection_zero_apply
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (x : M) :
    (0 : SmoothCcTensor g r s).toSection x = 0 := by
  rw [SmoothCcTensor.toSection_zero]; rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.smoothCcTensor_toSection_zero_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.smoothCcTensor_toSection_zero_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.smoothCcTensor_toSection_zero_apply ``Submission.DifferentialGeometry.Analysis.Sobolev.smoothCcTensor_toSection_zero_apply

end NormedSpaceModel

section InnerProductSpaceModel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance tensorRSRiemannianNormedAddCommGroup_local
    (r s : ℕ) [h : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b)] (b : M) :
    NormedAddCommGroup (TensorRSSpace r s I b) :=
  (h.g.toCore b).toNormedAddCommGroupOfTopology
    (h.g.continuousAt b) (h.g.isVonNBounded b)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.tensorRSRiemannianNormedAddCommGroup_local
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.tensorRSRiemannianNormedAddCommGroup_local target :: scope.openDecls } }

set_option backward.isDefEq.respectTransparency true in
attribute [-instance] Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace in
def gSupVal (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) : ℝ :=
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g r s
  ⨆ x : M, ‖T.toSection x‖

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.gSupVal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.gSupVal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.gSupVal ``Submission.DifferentialGeometry.Analysis.Sobolev.gSupVal

set_option backward.isDefEq.respectTransparency true in
attribute [-instance] Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace in
omit [BoundarylessManifold I M] in
lemma bddAbove_section_norm_range
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (hk : 2 * k > Module.finrank ℝ E) (T : SmoothCcTensor g r s) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g r s
    BddAbove (Set.range (fun x : M => ‖T.toSection x‖)) := by
  let : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g r s
  obtain ⟨C, _, hC⟩ := tensorPouSobolevHilbert_embedding_Ck (I := I) (M := M)
    (g := g) (r := r) (s := s) (k := k) (m := 0) (by omega)
  exact ⟨C * ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) T‖,
    by rintro _ ⟨x, rfl⟩; exact hC T x⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.bddAbove_section_norm_range then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.bddAbove_section_norm_range"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.bddAbove_section_norm_range ``Submission.DifferentialGeometry.Analysis.Sobolev.bddAbove_section_norm_range

attribute [-instance] Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
set_option backward.isDefEq.respectTransparency true in
lemma gSupVal_nonneg (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) : 0 ≤ gSupVal (I := I) (M := M) g r s T := by
  let : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g r s
  rcases isEmpty_or_nonempty M with hM | hM
  · rw [gSupVal, Real.iSup_of_isEmpty]
  · rw [gSupVal]; exact Real.iSup_nonneg (fun x => norm_nonneg _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.gSupVal_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.gSupVal_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.gSupVal_nonneg ``Submission.DifferentialGeometry.Analysis.Sobolev.gSupVal_nonneg

attribute [-instance] Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
set_option backward.isDefEq.respectTransparency true in
lemma gSupVal_zero (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    gSupVal (I := I) (M := M) g r s 0 = 0 := by
  let : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g r s
  rw [gSupVal]
  have hz : (fun x : M => ‖(0 : SmoothCcTensor g r s).toSection x‖)
      = fun _ => (0 : ℝ) := by
    funext x; rw [smoothCcTensor_toSection_zero_apply, norm_zero]
  rw [hz]
  rcases isEmpty_or_nonempty M with hM | hM
  · rw [Real.iSup_of_isEmpty]
  · rw [ciSup_const]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.gSupVal_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.gSupVal_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.gSupVal_zero ``Submission.DifferentialGeometry.Analysis.Sobolev.gSupVal_zero

attribute [-instance] Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
set_option backward.isDefEq.respectTransparency true in
lemma gSupVal_neg (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) :
    gSupVal (I := I) (M := M) g r s (-T) = gSupVal (I := I) (M := M) g r s T := by
  let : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g r s
  rw [gSupVal, gSupVal]
  congr 1; funext x
  rw [smoothCcTensor_toSection_neg_apply, norm_neg]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.gSupVal_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.gSupVal_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.gSupVal_neg ``Submission.DifferentialGeometry.Analysis.Sobolev.gSupVal_neg

attribute [-instance] Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace in
omit [BoundarylessManifold I M] in
set_option backward.isDefEq.respectTransparency true in
lemma gSupVal_add_le (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (hk : 2 * k > Module.finrank ℝ E) (S T : SmoothCcTensor g r s) :
    gSupVal (I := I) (M := M) g r s (S + T) ≤
      gSupVal (I := I) (M := M) g r s S + gSupVal (I := I) (M := M) g r s T := by
  let : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g r s
  rcases isEmpty_or_nonempty M with hM | hM
  · simp only [gSupVal]
    rw [Real.iSup_of_isEmpty, Real.iSup_of_isEmpty, Real.iSup_of_isEmpty]; norm_num
  · have hbS := bddAbove_section_norm_range (I := I) (M := M) g r s k hk S
    have hbT := bddAbove_section_norm_range (I := I) (M := M) g r s k hk T
    rw [gSupVal, gSupVal, gSupVal]
    refine Real.iSup_le (fun x => ?_)
      (add_nonneg (gSupVal_nonneg (I := I) (M := M) g r s S)
        (gSupVal_nonneg (I := I) (M := M) g r s T))
    have hpt : ‖(S + T).toSection x‖ ≤ ‖S.toSection x‖ + ‖T.toSection x‖ := by
      rw [smoothCcTensor_toSection_add_apply]; exact norm_add_le _ _
    exact le_trans hpt (add_le_add (le_ciSup hbS x) (le_ciSup hbT x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.gSupVal_add_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.gSupVal_add_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.gSupVal_add_le ``Submission.DifferentialGeometry.Analysis.Sobolev.gSupVal_add_le

attribute [-instance] Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace in
omit [BoundarylessManifold I M] in
set_option backward.isDefEq.respectTransparency true in
lemma gSupVal_smul_le (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (hk : 2 * k > Module.finrank ℝ E) (c : ℝ) (T : SmoothCcTensor g r s) :
    gSupVal (I := I) (M := M) g r s (c • T) ≤
      |c| * gSupVal (I := I) (M := M) g r s T := by
  let : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g r s
  rcases isEmpty_or_nonempty M with hM | hM
  · simp only [gSupVal]
    rw [Real.iSup_of_isEmpty, Real.iSup_of_isEmpty, _root_.MulZeroClass.mul_zero]
  · have hbT := bddAbove_section_norm_range (I := I) (M := M) g r s k hk T
    rw [gSupVal, gSupVal]
    refine Real.iSup_le (fun x => ?_)
      (mul_nonneg (abs_nonneg c) (gSupVal_nonneg (I := I) (M := M) g r s T))
    have hpt : ‖(c • T).toSection x‖ = |c| * ‖T.toSection x‖ := by
      rw [smoothCcTensor_toSection_smul_apply, norm_smul, Real.norm_eq_abs]
    rw [hpt]
    exact mul_le_mul_of_nonneg_left (le_ciSup hbT x) (abs_nonneg c)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.gSupVal_smul_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.gSupVal_smul_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.gSupVal_smul_le ``Submission.DifferentialGeometry.Analysis.Sobolev.gSupVal_smul_le

attribute [-instance] Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace in
omit [BoundarylessManifold I M] in
lemma gSupVal_smul (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (hk : 2 * k > Module.finrank ℝ E) (c : ℝ) (T : SmoothCcTensor g r s) :
    gSupVal (I := I) (M := M) g r s (c • T) =
      |c| * gSupVal (I := I) (M := M) g r s T := by
  rcases eq_or_ne c 0 with hc | hc
  · subst hc
    rw [zero_smul, gSupVal_zero, abs_zero, _root_.MulZeroClass.zero_mul]
  · refine le_antisymm (gSupVal_smul_le (I := I) (M := M) g r s k hk c T) ?_
    have hstep := gSupVal_smul_le (I := I) (M := M) g r s k hk c⁻¹ (c • T)
    rw [smul_smul, inv_mul_cancel₀ hc, one_smul] at hstep
    have hcpos : 0 < |c| := abs_pos.mpr hc
    rw [abs_inv] at hstep
    have h2 : |c| * gSupVal (I := I) (M := M) g r s T ≤
        |c| * (|c|⁻¹ * gSupVal (I := I) (M := M) g r s (c • T)) :=
      mul_le_mul_of_nonneg_left hstep (le_of_lt hcpos)
    rwa [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hcpos), one_mul] at h2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.gSupVal_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.gSupVal_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.gSupVal_smul ``Submission.DifferentialGeometry.Analysis.Sobolev.gSupVal_smul

structure CSupTensor (g : SmoothRiemannianMetric I M) (r s k : ℕ) where
  toHsTensor : DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev.SmoothCcTensorHs g r s (2 * k)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.CSupTensor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.CSupTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.CSupTensor ``Submission.DifferentialGeometry.Analysis.Sobolev.CSupTensor

namespace CSupTensor

variable {g : SmoothRiemannianMetric I M} {r s k : ℕ}

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
@[ext] theorem ext {S T : CSupTensor g r s k}
    (h : S.toHsTensor = T.toHsTensor) : S = T := by
  cases S; cases T; congr

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.CSupTensor.ext then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.CSupTensor.ext"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.CSupTensor.ext ``Submission.DifferentialGeometry.Analysis.Sobolev.CSupTensor.ext

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
lemma toHsTensor_injective :
    Function.Injective
      (fun S : CSupTensor g r s k => S.toHsTensor) := by
  intro S T h; exact ext h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.CSupTensor.toHsTensor_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.CSupTensor.toHsTensor_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.CSupTensor.toHsTensor_injective ``Submission.DifferentialGeometry.Analysis.Sobolev.CSupTensor.toHsTensor_injective

instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.CSupTensor.instZero : Zero (CSupTensor g r s k) := ⟨⟨0⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.CSupTensor.instZero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.CSupTensor.instZero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.CSupTensor.instZero ``Submission.DifferentialGeometry.Analysis.Sobolev.CSupTensor.instZero
instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.CSupTensor.instAdd : Add (CSupTensor g r s k) :=
  ⟨fun S T => ⟨S.toHsTensor + T.toHsTensor⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.CSupTensor.instAdd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.CSupTensor.instAdd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.CSupTensor.instAdd ``Submission.DifferentialGeometry.Analysis.Sobolev.CSupTensor.instAdd
instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.CSupTensor.instNeg : Neg (CSupTensor g r s k) := ⟨fun S => ⟨-S.toHsTensor⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.CSupTensor.instNeg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.CSupTensor.instNeg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.CSupTensor.instNeg ``Submission.DifferentialGeometry.Analysis.Sobolev.CSupTensor.instNeg
instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.CSupTensor.instSub : Sub (CSupTensor g r s k) :=
  ⟨fun S T => ⟨S.toHsTensor - T.toHsTensor⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.CSupTensor.instSub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.CSupTensor.instSub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.CSupTensor.instSub ``Submission.DifferentialGeometry.Analysis.Sobolev.CSupTensor.instSub
instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.CSupTensor.instSMulReal : SMul ℝ (CSupTensor g r s k) :=
  ⟨fun c S => ⟨c • S.toHsTensor⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.CSupTensor.instSMulReal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.CSupTensor.instSMulReal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.CSupTensor.instSMulReal ``Submission.DifferentialGeometry.Analysis.Sobolev.CSupTensor.instSMulReal

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma toHsTensor_zero :
    (0 : CSupTensor g r s k).toHsTensor = 0 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.CSupTensor.toHsTensor_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.CSupTensor.toHsTensor_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.CSupTensor.toHsTensor_zero ``Submission.DifferentialGeometry.Analysis.Sobolev.CSupTensor.toHsTensor_zero
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma toHsTensor_add (S T : CSupTensor g r s k) :
    (S + T).toHsTensor = S.toHsTensor + T.toHsTensor := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.CSupTensor.toHsTensor_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.CSupTensor.toHsTensor_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.CSupTensor.toHsTensor_add ``Submission.DifferentialGeometry.Analysis.Sobolev.CSupTensor.toHsTensor_add
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma toHsTensor_neg (S : CSupTensor g r s k) :
    (-S).toHsTensor = -S.toHsTensor := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.CSupTensor.toHsTensor_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.CSupTensor.toHsTensor_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.CSupTensor.toHsTensor_neg ``Submission.DifferentialGeometry.Analysis.Sobolev.CSupTensor.toHsTensor_neg
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma toHsTensor_sub (S T : CSupTensor g r s k) :
    (S - T).toHsTensor = S.toHsTensor - T.toHsTensor := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.CSupTensor.toHsTensor_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.CSupTensor.toHsTensor_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.CSupTensor.toHsTensor_sub ``Submission.DifferentialGeometry.Analysis.Sobolev.CSupTensor.toHsTensor_sub
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma toHsTensor_smul (c : ℝ) (S : CSupTensor g r s k) :
    (c • S).toHsTensor = c • S.toHsTensor := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.CSupTensor.toHsTensor_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.CSupTensor.toHsTensor_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.CSupTensor.toHsTensor_smul ``Submission.DifferentialGeometry.Analysis.Sobolev.CSupTensor.toHsTensor_smul

instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.CSupTensor.instSMulNat : SMul ℕ (CSupTensor g r s k) := ⟨nsmulRec⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.CSupTensor.instSMulNat then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.CSupTensor.instSMulNat"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.CSupTensor.instSMulNat ``Submission.DifferentialGeometry.Analysis.Sobolev.CSupTensor.instSMulNat
instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.CSupTensor.instSMulInt : SMul ℤ (CSupTensor g r s k) := ⟨zsmulRec⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.CSupTensor.instSMulInt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.CSupTensor.instSMulInt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.CSupTensor.instSMulInt ``Submission.DifferentialGeometry.Analysis.Sobolev.CSupTensor.instSMulInt

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma toHsTensor_nsmul (S : CSupTensor g r s k) (n : ℕ) :
    (n • S).toHsTensor = n • S.toHsTensor := by
  induction n with
  | zero =>
      change (nsmulRec 0 S).toHsTensor = (0 : ℕ) • S.toHsTensor
      simp [nsmulRec]
  | succ n ih =>
      change (nsmulRec (n + 1) S).toHsTensor = (n + 1) • S.toHsTensor
      change (nsmulRec n S + S).toHsTensor = (n + 1) • S.toHsTensor
      have hn : (nsmulRec n S).toHsTensor = n • S.toHsTensor := ih
      rw [toHsTensor_add, hn, succ_nsmul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.CSupTensor.toHsTensor_nsmul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.CSupTensor.toHsTensor_nsmul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.CSupTensor.toHsTensor_nsmul ``Submission.DifferentialGeometry.Analysis.Sobolev.CSupTensor.toHsTensor_nsmul

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma toHsTensor_zsmul (S : CSupTensor g r s k) (z : ℤ) :
    (z • S).toHsTensor = z • S.toHsTensor := by
  rcases z with n | n
  · change (n • S).toHsTensor = (Int.ofNat n) • S.toHsTensor
    rw [toHsTensor_nsmul]; simp
  · change (-((n + 1) • S)).toHsTensor = (Int.negSucc n) • S.toHsTensor
    rw [toHsTensor_neg, toHsTensor_nsmul]
    show -((n + 1) • S.toHsTensor) = Int.negSucc n • S.toHsTensor
    rw [show (Int.negSucc n : ℤ) = -((n + 1 : ℕ) : ℤ) from rfl,
      neg_zsmul, natCast_zsmul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.CSupTensor.toHsTensor_zsmul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.CSupTensor.toHsTensor_zsmul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.CSupTensor.toHsTensor_zsmul ``Submission.DifferentialGeometry.Analysis.Sobolev.CSupTensor.toHsTensor_zsmul

instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.CSupTensor.instAddCommGroup : AddCommGroup (CSupTensor g r s k) :=
  toHsTensor_injective.addCommGroup
    (fun S => S.toHsTensor)
    toHsTensor_zero
    toHsTensor_add
    toHsTensor_neg
    toHsTensor_sub
    toHsTensor_nsmul
    toHsTensor_zsmul

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.CSupTensor.instAddCommGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.CSupTensor.instAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.CSupTensor.instAddCommGroup ``Submission.DifferentialGeometry.Analysis.Sobolev.CSupTensor.instAddCommGroup

def toHsTensorAddHom :
    CSupTensor g r s k →+
      DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev.SmoothCcTensorHs g r s (2 * k) where
  toFun := fun S => S.toHsTensor
  map_zero' := toHsTensor_zero
  map_add' := toHsTensor_add

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.CSupTensor.toHsTensorAddHom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.CSupTensor.toHsTensorAddHom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.CSupTensor.toHsTensorAddHom ``Submission.DifferentialGeometry.Analysis.Sobolev.CSupTensor.toHsTensorAddHom

instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.CSupTensor.instModuleReal : Module ℝ (CSupTensor g r s k) :=
  toHsTensor_injective.module ℝ toHsTensorAddHom toHsTensor_smul

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.CSupTensor.instModuleReal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.CSupTensor.instModuleReal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.CSupTensor.instModuleReal ``Submission.DifferentialGeometry.Analysis.Sobolev.CSupTensor.instModuleReal

def ofHs :
    DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev.SmoothCcTensorHs g r s
      (2 * k) →ₗ[ℝ] CSupTensor g r s k where
  toFun := fun S => ⟨S⟩
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.CSupTensor.ofHs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.CSupTensor.ofHs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.CSupTensor.ofHs ``Submission.DifferentialGeometry.Analysis.Sobolev.CSupTensor.ofHs

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma ofHs_apply
    (S : DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev.SmoothCcTensorHs g r s (2 * k)) :
    (ofHs (g := g) (r := r) (s := s) (k := k) S).toHsTensor = S := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.CSupTensor.ofHs_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.CSupTensor.ofHs_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.CSupTensor.ofHs_apply ``Submission.DifferentialGeometry.Analysis.Sobolev.CSupTensor.ofHs_apply

def toCc (S : CSupTensor g r s k) : SmoothCcTensor g r s :=
  S.toHsTensor.toCcTensor

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.CSupTensor.toCc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.CSupTensor.toCc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.CSupTensor.toCc ``Submission.DifferentialGeometry.Analysis.Sobolev.CSupTensor.toCc

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma toCc_zero : (0 : CSupTensor g r s k).toCc = 0 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.CSupTensor.toCc_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.CSupTensor.toCc_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.CSupTensor.toCc_zero ``Submission.DifferentialGeometry.Analysis.Sobolev.CSupTensor.toCc_zero
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma toCc_add (S T : CSupTensor g r s k) :
    (S + T).toCc = S.toCc + T.toCc := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.CSupTensor.toCc_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.CSupTensor.toCc_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.CSupTensor.toCc_add ``Submission.DifferentialGeometry.Analysis.Sobolev.CSupTensor.toCc_add
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma toCc_neg (S : CSupTensor g r s k) : (-S).toCc = -S.toCc := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.CSupTensor.toCc_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.CSupTensor.toCc_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.CSupTensor.toCc_neg ``Submission.DifferentialGeometry.Analysis.Sobolev.CSupTensor.toCc_neg
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma toCc_smul (c : ℝ) (S : CSupTensor g r s k) :
    (c • S).toCc = c • S.toCc := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.CSupTensor.toCc_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.CSupTensor.toCc_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.CSupTensor.toCc_smul ``Submission.DifferentialGeometry.Analysis.Sobolev.CSupTensor.toCc_smul

end CSupTensor

attribute [-instance] Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace in
def gSupAddGroupSeminorm (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (hk : 2 * k > Module.finrank ℝ E) :
    AddGroupSeminorm (CSupTensor g r s k) where
  toFun := fun S => gSupVal (I := I) (M := M) g r s S.toCc
  map_zero' := by
    change gSupVal (I := I) (M := M) g r s (0 : CSupTensor g r s k).toCc = 0
    rw [CSupTensor.toCc_zero, gSupVal_zero]
  add_le' := fun S T => by
    change gSupVal (I := I) (M := M) g r s (S + T).toCc ≤
      gSupVal (I := I) (M := M) g r s S.toCc +
        gSupVal (I := I) (M := M) g r s T.toCc
    rw [CSupTensor.toCc_add]
    exact gSupVal_add_le (I := I) (M := M) g r s k hk S.toCc T.toCc
  neg' := fun S => by
    change gSupVal (I := I) (M := M) g r s (-S).toCc =
      gSupVal (I := I) (M := M) g r s S.toCc
    rw [CSupTensor.toCc_neg, gSupVal_neg]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.gSupAddGroupSeminorm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.gSupAddGroupSeminorm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.gSupAddGroupSeminorm ``Submission.DifferentialGeometry.Analysis.Sobolev.gSupAddGroupSeminorm

attribute [-instance] Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace in
@[reducible] noncomputable def csupSeminormedAddCommGroup
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (hk : 2 * k > Module.finrank ℝ E) :
    SeminormedAddCommGroup (CSupTensor g r s k) :=
  AddGroupSeminorm.toSeminormedAddCommGroup
    (gSupAddGroupSeminorm (I := I) (M := M) g r s k hk)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.csupSeminormedAddCommGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.csupSeminormedAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.csupSeminormedAddCommGroup ``Submission.DifferentialGeometry.Analysis.Sobolev.csupSeminormedAddCommGroup

attribute [-instance] Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace in
omit [BoundarylessManifold I M] in
lemma csupSeminormedAddCommGroup_norm
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (hk : 2 * k > Module.finrank ℝ E) (S : CSupTensor g r s k) :
    @_root_.Norm.norm _ (csupSeminormedAddCommGroup (I := I) (M := M) g r s k hk).toNorm S =
      gSupVal (I := I) (M := M) g r s S.toCc := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.csupSeminormedAddCommGroup_norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.csupSeminormedAddCommGroup_norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.csupSeminormedAddCommGroup_norm ``Submission.DifferentialGeometry.Analysis.Sobolev.csupSeminormedAddCommGroup_norm

attribute [-instance] Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace in
@[reducible] noncomputable def csupNormedSpace
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (hk : 2 * k > Module.finrank ℝ E) :
    letI := csupSeminormedAddCommGroup (I := I) (M := M) g r s k hk
    NormedSpace ℝ (CSupTensor g r s k) :=
  letI := csupSeminormedAddCommGroup (I := I) (M := M) g r s k hk
  NormedSpace.mk (𝕜 := ℝ) (E := CSupTensor g r s k) fun c S => by
    have h1 : ‖c • S‖ = gSupVal (I := I) (M := M) g r s (c • S).toCc :=
      csupSeminormedAddCommGroup_norm (I := I) (M := M) g r s k hk (c • S)
    have h2 : ‖S‖ = gSupVal (I := I) (M := M) g r s S.toCc :=
      csupSeminormedAddCommGroup_norm (I := I) (M := M) g r s k hk S
    rw [h1, h2, CSupTensor.toCc_smul,
      gSupVal_smul (I := I) (M := M) g r s k hk c S.toCc, Real.norm_eq_abs]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.csupNormedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.csupNormedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.csupNormedSpace ``Submission.DifferentialGeometry.Analysis.Sobolev.csupNormedSpace

noncomputable def CSupBanach (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (hk : 2 * k > Module.finrank ℝ E) : Type _ :=
  letI := csupSeminormedAddCommGroup (I := I) (M := M) g r s k hk
  UniformSpace.Completion (CSupTensor g r s k)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.CSupBanach then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.CSupBanach"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.CSupBanach ``Submission.DifferentialGeometry.Analysis.Sobolev.CSupBanach

noncomputable instance instCSupBanachNormedAddCommGroup
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (hk : 2 * k > Module.finrank ℝ E) :
    NormedAddCommGroup (CSupBanach (I := I) (M := M) g r s k hk) :=
  letI := csupSeminormedAddCommGroup (I := I) (M := M) g r s k hk
  (inferInstance :
    NormedAddCommGroup (UniformSpace.Completion (CSupTensor g r s k)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.instCSupBanachNormedAddCommGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.instCSupBanachNormedAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.instCSupBanachNormedAddCommGroup ``Submission.DifferentialGeometry.Analysis.Sobolev.instCSupBanachNormedAddCommGroup

noncomputable instance instCSupBanachNormedSpace
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (hk : 2 * k > Module.finrank ℝ E) :
    NormedSpace ℝ (CSupBanach (I := I) (M := M) g r s k hk) :=
  letI := csupSeminormedAddCommGroup (I := I) (M := M) g r s k hk
  letI := csupNormedSpace (I := I) (M := M) g r s k hk
  (inferInstance :
    NormedSpace ℝ (UniformSpace.Completion (CSupTensor g r s k)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.instCSupBanachNormedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.instCSupBanachNormedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.instCSupBanachNormedSpace ``Submission.DifferentialGeometry.Analysis.Sobolev.instCSupBanachNormedSpace

instance instCSupBanachCompleteSpace
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (hk : 2 * k > Module.finrank ℝ E) :
    CompleteSpace (CSupBanach (I := I) (M := M) g r s k hk) :=
  letI := csupSeminormedAddCommGroup (I := I) (M := M) g r s k hk
  (inferInstance :
    CompleteSpace (UniformSpace.Completion (CSupTensor g r s k)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.instCSupBanachCompleteSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.instCSupBanachCompleteSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.instCSupBanachCompleteSpace ``Submission.DifferentialGeometry.Analysis.Sobolev.instCSupBanachCompleteSpace

attribute [-instance] Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace in
noncomputable def smoothToC0Lin
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (hk : 2 * k > Module.finrank ℝ E) :
    DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev.SmoothCcTensorHs g r s (2 * k) →ₗ[ℝ]
      CSupBanach (I := I) (M := M) g r s k hk :=
  letI := csupSeminormedAddCommGroup (I := I) (M := M) g r s k hk
  letI := csupNormedSpace (I := I) (M := M) g r s k hk
  (UniformSpace.Completion.toComplL :
    CSupTensor g r s k →L[ℝ]
      UniformSpace.Completion (CSupTensor g r s k)).toLinearMap.comp
    (CSupTensor.ofHs (g := g) (r := r) (s := s) (k := k))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.smoothToC0Lin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.smoothToC0Lin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.smoothToC0Lin ``Submission.DifferentialGeometry.Analysis.Sobolev.smoothToC0Lin

attribute [-instance] Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace in
omit [BoundarylessManifold I M] in
lemma norm_smoothToC0Lin
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (hk : 2 * k > Module.finrank ℝ E)
    (S : DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev.SmoothCcTensorHs g r s (2 * k)) :
    ‖smoothToC0Lin (I := I) (M := M) g r s k hk S‖ =
      gSupVal (I := I) (M := M) g r s S.toCcTensor := by
  let := csupSeminormedAddCommGroup (I := I) (M := M) g r s k hk
  let := csupNormedSpace (I := I) (M := M) g r s k hk
  have hiso :=
    (UniformSpace.Completion.toComplₗᵢ :
        CSupTensor g r s k →ₗᵢ[ℝ]
          UniformSpace.Completion (CSupTensor g r s k)).norm_map
      (CSupTensor.ofHs (g := g) (r := r) (s := s) (k := k) S)
  have hval : ‖smoothToC0Lin (I := I) (M := M) g r s k hk S‖ =
      ‖(CSupTensor.ofHs (g := g) (r := r) (s := s) (k := k) S :
        CSupTensor g r s k)‖ := hiso
  rw [hval, csupSeminormedAddCommGroup_norm (I := I) (M := M) g r s k hk]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.norm_smoothToC0Lin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.norm_smoothToC0Lin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.norm_smoothToC0Lin ``Submission.DifferentialGeometry.Analysis.Sobolev.norm_smoothToC0Lin

attribute [-instance] Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
lemma norm_coe_toCompl_eq_toHs
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (S : DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev.SmoothCcTensorHs g r s (2 * k)) :
    ‖(S : TensorPouSobolevHilbert g r s (2 * k))‖ =
      ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) S.toCcTensor‖ := by
  have hrhs : SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) S.toCcTensor =
      ((⟨S.toCcTensor⟩ : DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev.SmoothCcTensorHs
        g r s (2 * k)) :
        TensorPouSobolevHilbert g r s (2 * k)) := rfl
  have hS : (⟨S.toCcTensor⟩ :
    DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev.SmoothCcTensorHs g r s (2 * k)) = S := by
    cases S; rfl
  rw [hrhs, hS]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.norm_coe_toCompl_eq_toHs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.norm_coe_toCompl_eq_toHs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.norm_coe_toCompl_eq_toHs ``Submission.DifferentialGeometry.Analysis.Sobolev.norm_coe_toCompl_eq_toHs

attribute [-instance] Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace in
omit [BoundarylessManifold I M] in
set_option backward.isDefEq.respectTransparency true in
lemma exists_smoothToC0Lin_norm_le
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (hk : 2 * k > Module.finrank ℝ E) :
    ∃ C : ℝ, 0 < C ∧
      ∀ S : DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev.SmoothCcTensorHs g r s (2 * k),
        ‖smoothToC0Lin (I := I) (M := M) g r s k hk S‖ ≤
          C * ‖(S : TensorPouSobolevHilbert g r s (2 * k))‖ := by
  let : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g r s
  obtain ⟨C, hCpos, hC⟩ := tensorPouSobolevHilbert_embedding_Ck (I := I) (M := M)
    (g := g) (r := r) (s := s) (k := k) (m := 0) (by omega)
  refine ⟨C, hCpos, fun S => ?_⟩
  rw [norm_smoothToC0Lin (I := I) (M := M) g r s k hk S,
    norm_coe_toCompl_eq_toHs (I := I) (M := M) g r s k S]
  rcases isEmpty_or_nonempty M with hM | hM
  · rw [gSupVal, Real.iSup_of_isEmpty]
    exact mul_nonneg (le_of_lt hCpos) (norm_nonneg _)
  · rw [gSupVal]
    refine Real.iSup_le (fun x => ?_)
      (mul_nonneg (le_of_lt hCpos) (norm_nonneg _))
    exact hC S.toCcTensor x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.exists_smoothToC0Lin_norm_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.exists_smoothToC0Lin_norm_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.exists_smoothToC0Lin_norm_le ``Submission.DifferentialGeometry.Analysis.Sobolev.exists_smoothToC0Lin_norm_le

attribute [-instance] Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace in
noncomputable def tensorHsToC0
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (hk : 2 * k > Module.finrank ℝ E) :
    TensorPouSobolevHilbert g r s (2 * k) →L[ℝ]
      CSupBanach (I := I) (M := M) g r s k hk :=
  (smoothToC0Lin (I := I) (M := M) g r s k hk).extendOfNorm
    (UniformSpace.Completion.toComplL :
      DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev.SmoothCcTensorHs g r s (2 * k) →L[ℝ]
        TensorPouSobolevHilbert g r s (2 * k)).toLinearMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.tensorHsToC0 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.tensorHsToC0"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.tensorHsToC0 ``Submission.DifferentialGeometry.Analysis.Sobolev.tensorHsToC0

attribute [-instance] Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
lemma denseRange_toComplL_toLinearMap
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) :
    DenseRange
      ⇑(UniformSpace.Completion.toComplL :
        DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev.SmoothCcTensorHs g r s (2 * k) →L[ℝ]
          TensorPouSobolevHilbert g r s (2 * k)).toLinearMap := by
  have hcoe : ⇑(UniformSpace.Completion.toComplL :
        DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev.SmoothCcTensorHs g r s (2 * k) →L[ℝ]
          TensorPouSobolevHilbert g r s (2 * k)).toLinearMap =
      ((↑) : DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev.SmoothCcTensorHs g r s (2 * k) →
        UniformSpace.Completion
          (DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev.SmoothCcTensorHs g r s
          (2 * k))) := by
    funext S; rfl
  rw [hcoe]
  exact UniformSpace.Completion.denseRange_coe

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.denseRange_toComplL_toLinearMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.denseRange_toComplL_toLinearMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.denseRange_toComplL_toLinearMap ``Submission.DifferentialGeometry.Analysis.Sobolev.denseRange_toComplL_toLinearMap

attribute [-instance] Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace in
omit [BoundarylessManifold I M] in
theorem tensorHsToC0_coe
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (hk : 2 * k > Module.finrank ℝ E)
    (S : DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev.SmoothCcTensorHs g r s (2 * k)) :
    tensorHsToC0 (I := I) (M := M) g r s k hk
        (S : TensorPouSobolevHilbert g r s (2 * k)) =
      smoothToC0Lin (I := I) (M := M) g r s k hk S := by
  obtain ⟨C, _, hC⟩ := exists_smoothToC0Lin_norm_le (I := I) (M := M) g r s k hk
  have h := LinearMap.extendOfNorm_eq
    (f := smoothToC0Lin (I := I) (M := M) g r s k hk)
    (e := (UniformSpace.Completion.toComplL :
      DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev.SmoothCcTensorHs g r s (2 * k) →L[ℝ]
        TensorPouSobolevHilbert g r s (2 * k)).toLinearMap)
    (denseRange_toComplL_toLinearMap (I := I) (M := M) g r s k)
    ⟨C, hC⟩ S
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.tensorHsToC0_coe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.tensorHsToC0_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.tensorHsToC0_coe ``Submission.DifferentialGeometry.Analysis.Sobolev.tensorHsToC0_coe

attribute [-instance] Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace in
omit [BoundarylessManifold I M] in
theorem tensorHsToC0_norm_apply_le
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (hk : 2 * k > Module.finrank ℝ E) :
    ∃ C : ℝ, 0 < C ∧
      ∀ u : TensorPouSobolevHilbert g r s (2 * k),
        ‖tensorHsToC0 (I := I) (M := M) g r s k hk u‖ ≤ C * ‖u‖ := by
  obtain ⟨C, hCpos, hC⟩ := exists_smoothToC0Lin_norm_le (I := I) (M := M) g r s k hk
  refine ⟨C, hCpos, fun u => ?_⟩
  exact LinearMap.norm_extendOfNorm_apply_le
    (denseRange_toComplL_toLinearMap (I := I) (M := M) g r s k) C hC u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.tensorHsToC0_norm_apply_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.tensorHsToC0_norm_apply_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.tensorHsToC0_norm_apply_le ``Submission.DifferentialGeometry.Analysis.Sobolev.tensorHsToC0_norm_apply_le

attribute [-instance] Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace in
omit [BoundarylessManifold I M] in
theorem tensorHsToC0_opNorm_le
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (hk : 2 * k > Module.finrank ℝ E) :
    ∃ C : ℝ, 0 < C ∧ ‖tensorHsToC0 (I := I) (M := M) g r s k hk‖ ≤ C := by
  obtain ⟨C, hCpos, hC⟩ := exists_smoothToC0Lin_norm_le (I := I) (M := M) g r s k hk
  refine ⟨C, hCpos, ?_⟩
  exact LinearMap.opNorm_extendOfNorm_le
    (denseRange_toComplL_toLinearMap (I := I) (M := M) g r s k)
    (le_of_lt hCpos) hC

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.tensorHsToC0_opNorm_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.tensorHsToC0_opNorm_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.tensorHsToC0_opNorm_le ``Submission.DifferentialGeometry.Analysis.Sobolev.tensorHsToC0_opNorm_le

attribute [-instance] Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace in
omit [BoundarylessManifold I M] in
theorem tensorHsToC0_norm_le_of_norm_le
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (hk : 2 * k > Module.finrank ℝ E) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (u : TensorPouSobolevHilbert g r s (2 * k)) (B : ℝ), ‖u‖ ≤ B →
        ‖tensorHsToC0 (I := I) (M := M) g r s k hk u‖ ≤ C * B := by
  obtain ⟨C, hCpos, hC⟩ := tensorHsToC0_norm_apply_le (I := I) (M := M) g r s k hk
  refine ⟨C, hCpos, fun u B hB => ?_⟩
  calc ‖tensorHsToC0 (I := I) (M := M) g r s k hk u‖ ≤ C * ‖u‖ := hC u
    _ ≤ C * B := mul_le_mul_of_nonneg_left hB (le_of_lt hCpos)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.tensorHsToC0_norm_le_of_norm_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.tensorHsToC0_norm_le_of_norm_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.tensorHsToC0_norm_le_of_norm_le ``Submission.DifferentialGeometry.Analysis.Sobolev.tensorHsToC0_norm_le_of_norm_le

end InnerProductSpaceModel

end DifferentialGeometry.Analysis.Sobolev

end
