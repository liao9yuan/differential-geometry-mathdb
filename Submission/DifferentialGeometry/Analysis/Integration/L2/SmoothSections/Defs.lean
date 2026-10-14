import Submission.DifferentialGeometry.Analysis.Integration.L2.CompactSupport
import Submission.DifferentialGeometry.Analysis.Integration.L2.Pairing.CauchySchwarz
import Submission.DifferentialGeometry.Tensor.RSTensor.Defs
import Mathlib.Topology.Algebra.Support
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section


open _root_.Manifold _root_.Set _root_.Filter _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators _root_.Matrix

namespace DifferentialGeometry
namespace Integral
namespace L2

open _root_.Submission.DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def compactlySupportedSmoothTensorSections
    (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (r s : ℕ) :
    Submodule ℝ (Cₛ^∞⟮I; TensorRSModel r s ℝ E,
      (fun x : M => TensorRSSpace r s I x)⟯) where
  carrier :=
    { S : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
        (fun x : M => TensorRSSpace r s I x)⟯ |
        HasCompactSupport
          (fun x : M => TensorRSSpace.toModel (S x)) }
  zero_mem' := by
    change HasCompactSupport
      (fun x : M => TensorRSSpace.toModel
        ((0 : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
          (fun x : M => TensorRSSpace r s I x)⟯) x))
    have h : (fun x : M => TensorRSSpace.toModel
        ((0 : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
          (fun x : M => TensorRSSpace r s I x)⟯) x)) =
        (fun _ : M => (0 : TensorRSModel r s ℝ E)) := by
      funext x
      simp [ContMDiffSection.coe_zero,
        TensorRSSpace.toModel_zero]
    rw [h]
    exact HasCompactSupport.zero
  add_mem' := by
    intro S T hS hT
    change HasCompactSupport
      (fun x : M => TensorRSSpace.toModel
        ((S + T : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
          (fun x : M => TensorRSSpace r s I x)⟯) x))
    have h : (fun x : M => TensorRSSpace.toModel
        ((S + T : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
          (fun x : M => TensorRSSpace r s I x)⟯) x)) =
        (fun x : M => TensorRSSpace.toModel (S x)) +
          (fun x : M => TensorRSSpace.toModel (T x)) := by
      funext x
      simp [ContMDiffSection.coe_add, Pi.add_apply,
        TensorRSSpace.toModel_add]
    rw [h]
    exact hS.add hT
  smul_mem' := by
    intro c S hS
    change HasCompactSupport
      (fun x : M => TensorRSSpace.toModel
        ((c • S : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
          (fun x : M => TensorRSSpace r s I x)⟯) x))
    have h : (fun x : M => TensorRSSpace.toModel
        ((c • S : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
          (fun x : M => TensorRSSpace r s I x)⟯) x)) =
        (fun _ : M => c) •
          (fun x : M => TensorRSSpace.toModel (S x)) := by
      funext x
      simp [ContMDiffSection.coe_smul, Pi.smul_apply,
        TensorRSSpace.toModel_smul]
    rw [h]
    exact hS.smul_left

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.compactlySupportedSmoothTensorSections then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.compactlySupportedSmoothTensorSections"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.compactlySupportedSmoothTensorSections ``Submission.DifferentialGeometry.Integral.L2.compactlySupportedSmoothTensorSections

@[simp]
lemma mem_compactlySupportedSmoothTensorSections {r s : ℕ}
    {S : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
      (fun x : M => TensorRSSpace r s I x)⟯} :
    S ∈ compactlySupportedSmoothTensorSections I M r s ↔
      HasCompactSupport
        (fun x : M => TensorRSSpace.toModel (S x)) := Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.mem_compactlySupportedSmoothTensorSections then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.mem_compactlySupportedSmoothTensorSections"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.mem_compactlySupportedSmoothTensorSections ``Submission.DifferentialGeometry.Integral.L2.mem_compactlySupportedSmoothTensorSections

structure SmoothCcTensor (g : SmoothRiemannianMetric I M) (r s : ℕ) where
  toSection : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
    (fun x : M => TensorRSSpace r s I x)⟯
  hasCompactSupport :
    HasCompactSupport (fun x : M => TensorRSSpace.toModel (toSection x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.SmoothCcTensor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.SmoothCcTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.SmoothCcTensor ``Submission.DifferentialGeometry.Integral.L2.SmoothCcTensor

namespace SmoothCcTensor


def toFun {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S : SmoothCcTensor g r s) : M → TensorRSModel r s ℝ E :=
  fun x => TensorRSSpace.toModel (S.toSection x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.SmoothCcTensor.toFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.SmoothCcTensor.toFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.SmoothCcTensor.toFun ``Submission.DifferentialGeometry.Integral.L2.SmoothCcTensor.toFun

@[simp] lemma toFun_apply
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S : SmoothCcTensor g r s) (x : M) :
    S.toFun x = TensorRSSpace.toModel (S.toSection x) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.SmoothCcTensor.toFun_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.SmoothCcTensor.toFun_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.SmoothCcTensor.toFun_apply ``Submission.DifferentialGeometry.Integral.L2.SmoothCcTensor.toFun_apply

@[ext] lemma ext
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {S T : SmoothCcTensor g r s} (h : S.toSection = T.toSection) :
    S = T := by
  cases S; cases T; congr

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.SmoothCcTensor.ext then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.SmoothCcTensor.ext"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.SmoothCcTensor.ext ``Submission.DifferentialGeometry.Integral.L2.SmoothCcTensor.ext

end SmoothCcTensor

section Algebra

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}

instance _root_.Submission.DifferentialGeometry.Integral.L2.instZeroSmoothCcTensor : Zero (SmoothCcTensor g r s) where
  zero :=
    { toSection := 0
      hasCompactSupport := by
        have h : (fun x : M => TensorRSSpace.toModel
            ((0 : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
              (fun x : M => TensorRSSpace r s I x)⟯) x)) =
            (fun _ : M => (0 : TensorRSModel r s ℝ E)) := by
          funext x
          simp [ContMDiffSection.coe_zero,
            TensorRSSpace.toModel_zero]
        rw [h]
        exact HasCompactSupport.zero }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.instZeroSmoothCcTensor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.instZeroSmoothCcTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.instZeroSmoothCcTensor ``Submission.DifferentialGeometry.Integral.L2.instZeroSmoothCcTensor

instance _root_.Submission.DifferentialGeometry.Integral.L2.instAddSmoothCcTensor : Add (SmoothCcTensor g r s) where
  add S T :=
    { toSection := S.toSection + T.toSection
      hasCompactSupport := by
        have h : (fun x : M => TensorRSSpace.toModel
            ((S.toSection + T.toSection :
              Cₛ^∞⟮I; TensorRSModel r s ℝ E,
              (fun x : M => TensorRSSpace r s I x)⟯) x)) =
            (fun x : M => TensorRSSpace.toModel (S.toSection x)) +
              (fun x : M => TensorRSSpace.toModel (T.toSection x)) := by
          funext x
          simp [ContMDiffSection.coe_add, Pi.add_apply,
            TensorRSSpace.toModel_add]
        rw [h]
        exact S.hasCompactSupport.add T.hasCompactSupport }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.instAddSmoothCcTensor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.instAddSmoothCcTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.instAddSmoothCcTensor ``Submission.DifferentialGeometry.Integral.L2.instAddSmoothCcTensor

instance _root_.Submission.DifferentialGeometry.Integral.L2.instNegSmoothCcTensor : Neg (SmoothCcTensor g r s) where
  neg S :=
    { toSection := -S.toSection
      hasCompactSupport := by
        have h : (fun x : M => TensorRSSpace.toModel
            ((-S.toSection : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
              (fun x : M => TensorRSSpace r s I x)⟯) x)) =
            -(fun x : M => TensorRSSpace.toModel (S.toSection x)) := by
          funext x
          simp [ContMDiffSection.coe_neg, Pi.neg_apply,
            TensorRSSpace.toModel_neg]
        rw [h]
        exact S.hasCompactSupport.neg }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.instNegSmoothCcTensor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.instNegSmoothCcTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.instNegSmoothCcTensor ``Submission.DifferentialGeometry.Integral.L2.instNegSmoothCcTensor

instance _root_.Submission.DifferentialGeometry.Integral.L2.instSubSmoothCcTensor : Sub (SmoothCcTensor g r s) where
  sub S T :=
    { toSection := S.toSection - T.toSection
      hasCompactSupport := by
        have h : (fun x : M => TensorRSSpace.toModel
            ((S.toSection - T.toSection :
              Cₛ^∞⟮I; TensorRSModel r s ℝ E,
              (fun x : M => TensorRSSpace r s I x)⟯) x)) =
            (fun x : M => TensorRSSpace.toModel (S.toSection x)) -
              (fun x : M => TensorRSSpace.toModel (T.toSection x)) := by
          funext x
          simp [ContMDiffSection.coe_sub, Pi.sub_apply,
            TensorRSSpace.toModel_sub]
        rw [h]
        exact S.hasCompactSupport.sub T.hasCompactSupport }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.instSubSmoothCcTensor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.instSubSmoothCcTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.instSubSmoothCcTensor ``Submission.DifferentialGeometry.Integral.L2.instSubSmoothCcTensor

instance _root_.Submission.DifferentialGeometry.Integral.L2.instSMulRealSmoothCcTensor : SMul ℝ (SmoothCcTensor g r s) where
  smul c S :=
    { toSection := c • S.toSection
      hasCompactSupport := by
        have h : (fun x : M => TensorRSSpace.toModel
            ((c • S.toSection :
              Cₛ^∞⟮I; TensorRSModel r s ℝ E,
              (fun x : M => TensorRSSpace r s I x)⟯) x)) =
            (fun _ : M => c) •
              (fun x : M => TensorRSSpace.toModel (S.toSection x)) := by
          funext x
          simp [ContMDiffSection.coe_smul, Pi.smul_apply,
            TensorRSSpace.toModel_smul]
        rw [h]
        exact S.hasCompactSupport.smul_left }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.instSMulRealSmoothCcTensor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.instSMulRealSmoothCcTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.instSMulRealSmoothCcTensor ``Submission.DifferentialGeometry.Integral.L2.instSMulRealSmoothCcTensor


lemma SmoothCcTensor.toSection_injective :
    Function.Injective (fun S : SmoothCcTensor g r s => S.toSection) := by
  intro S T h
  exact SmoothCcTensor.ext h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.SmoothCcTensor.toSection_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.SmoothCcTensor.toSection_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.SmoothCcTensor.toSection_injective ``Submission.DifferentialGeometry.Integral.L2.SmoothCcTensor.toSection_injective

@[simp] lemma SmoothCcTensor.toSection_zero :
    (0 : SmoothCcTensor g r s).toSection = 0 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.SmoothCcTensor.toSection_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.SmoothCcTensor.toSection_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.SmoothCcTensor.toSection_zero ``Submission.DifferentialGeometry.Integral.L2.SmoothCcTensor.toSection_zero

@[simp] lemma SmoothCcTensor.toSection_add (S T : SmoothCcTensor g r s) :
    (S + T).toSection = S.toSection + T.toSection := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.SmoothCcTensor.toSection_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.SmoothCcTensor.toSection_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.SmoothCcTensor.toSection_add ``Submission.DifferentialGeometry.Integral.L2.SmoothCcTensor.toSection_add

@[simp] lemma SmoothCcTensor.toSection_neg (S : SmoothCcTensor g r s) :
    (-S).toSection = -S.toSection := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.SmoothCcTensor.toSection_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.SmoothCcTensor.toSection_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.SmoothCcTensor.toSection_neg ``Submission.DifferentialGeometry.Integral.L2.SmoothCcTensor.toSection_neg

@[simp] lemma SmoothCcTensor.toSection_sub (S T : SmoothCcTensor g r s) :
    (S - T).toSection = S.toSection - T.toSection := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.SmoothCcTensor.toSection_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.SmoothCcTensor.toSection_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.SmoothCcTensor.toSection_sub ``Submission.DifferentialGeometry.Integral.L2.SmoothCcTensor.toSection_sub

@[simp] lemma SmoothCcTensor.toSection_smul (c : ℝ) (S : SmoothCcTensor g r s) :
    (c • S).toSection = c • S.toSection := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.SmoothCcTensor.toSection_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.SmoothCcTensor.toSection_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.SmoothCcTensor.toSection_smul ``Submission.DifferentialGeometry.Integral.L2.SmoothCcTensor.toSection_smul

instance _root_.Submission.DifferentialGeometry.Integral.L2.instSMulNatSmoothCcTensor : SMul ℕ (SmoothCcTensor g r s) := ⟨nsmulRec⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.instSMulNatSmoothCcTensor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.instSMulNatSmoothCcTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.instSMulNatSmoothCcTensor ``Submission.DifferentialGeometry.Integral.L2.instSMulNatSmoothCcTensor

instance _root_.Submission.DifferentialGeometry.Integral.L2.instSMulIntSmoothCcTensor : SMul ℤ (SmoothCcTensor g r s) := ⟨zsmulRec⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.instSMulIntSmoothCcTensor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.instSMulIntSmoothCcTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.instSMulIntSmoothCcTensor ``Submission.DifferentialGeometry.Integral.L2.instSMulIntSmoothCcTensor

@[simp] lemma SmoothCcTensor.toSection_nsmul (S : SmoothCcTensor g r s) (n : ℕ) :
    (n • S).toSection = n • S.toSection := by
  induction n with
  | zero =>
    change (nsmulRec 0 S).toSection = (0 : ℕ) • S.toSection
    simp [nsmulRec]
  | succ n ih =>
    change (nsmulRec (n + 1) S).toSection = (n + 1) • S.toSection
    change (nsmulRec n S + S).toSection = (n + 1) • S.toSection
    have hn : (nsmulRec n S).toSection = n • S.toSection := ih
    rw [SmoothCcTensor.toSection_add, hn, succ_nsmul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.SmoothCcTensor.toSection_nsmul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.SmoothCcTensor.toSection_nsmul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.SmoothCcTensor.toSection_nsmul ``Submission.DifferentialGeometry.Integral.L2.SmoothCcTensor.toSection_nsmul

@[simp] lemma SmoothCcTensor.toSection_zsmul (S : SmoothCcTensor g r s) (z : ℤ) :
    (z • S).toSection = z • S.toSection := by
  rcases z with n | n
  · change (n • S).toSection = (Int.ofNat n) • S.toSection
    rw [SmoothCcTensor.toSection_nsmul]
    simp
  · change (-((n + 1) • S)).toSection = (Int.negSucc n) • S.toSection
    rw [SmoothCcTensor.toSection_neg, SmoothCcTensor.toSection_nsmul]
    show -((n + 1) • S.toSection) =
      Int.negSucc n • S.toSection
    rw [show (Int.negSucc n : ℤ) = -((n + 1 : ℕ) : ℤ) from rfl,
      neg_zsmul, natCast_zsmul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.SmoothCcTensor.toSection_zsmul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.SmoothCcTensor.toSection_zsmul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.SmoothCcTensor.toSection_zsmul ``Submission.DifferentialGeometry.Integral.L2.SmoothCcTensor.toSection_zsmul

instance _root_.Submission.DifferentialGeometry.Integral.L2.instAddCommGroupSmoothCcTensor : AddCommGroup (SmoothCcTensor g r s) :=
  SmoothCcTensor.toSection_injective.addCommGroup
    (fun S => S.toSection)
    SmoothCcTensor.toSection_zero
    SmoothCcTensor.toSection_add
    SmoothCcTensor.toSection_neg
    SmoothCcTensor.toSection_sub
    SmoothCcTensor.toSection_nsmul
    SmoothCcTensor.toSection_zsmul

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.instAddCommGroupSmoothCcTensor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.instAddCommGroupSmoothCcTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.instAddCommGroupSmoothCcTensor ``Submission.DifferentialGeometry.Integral.L2.instAddCommGroupSmoothCcTensor


def SmoothCcTensor.toSectionAddHom :
    SmoothCcTensor g r s →+ Cₛ^∞⟮I; TensorRSModel r s ℝ E,
      (fun x : M => TensorRSSpace r s I x)⟯ where
  toFun := fun S => S.toSection
  map_zero' := SmoothCcTensor.toSection_zero
  map_add' := SmoothCcTensor.toSection_add

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.SmoothCcTensor.toSectionAddHom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.SmoothCcTensor.toSectionAddHom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.SmoothCcTensor.toSectionAddHom ``Submission.DifferentialGeometry.Integral.L2.SmoothCcTensor.toSectionAddHom

instance _root_.Submission.DifferentialGeometry.Integral.L2.instModuleRealSmoothCcTensor : Module ℝ (SmoothCcTensor g r s) :=
  SmoothCcTensor.toSection_injective.module ℝ
    SmoothCcTensor.toSectionAddHom
    SmoothCcTensor.toSection_smul

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.instModuleRealSmoothCcTensor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.instModuleRealSmoothCcTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.instModuleRealSmoothCcTensor ``Submission.DifferentialGeometry.Integral.L2.instModuleRealSmoothCcTensor

@[simp] lemma SmoothCcTensor.toFun_zero :
    (0 : SmoothCcTensor g r s).toFun = 0 := by
  funext x
  simp [SmoothCcTensor.toFun, SmoothCcTensor.toSection_zero,
    ContMDiffSection.coe_zero, TensorRSSpace.toModel_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.SmoothCcTensor.toFun_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.SmoothCcTensor.toFun_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.SmoothCcTensor.toFun_zero ``Submission.DifferentialGeometry.Integral.L2.SmoothCcTensor.toFun_zero

@[simp] lemma SmoothCcTensor.toFun_add (S T : SmoothCcTensor g r s) :
    (S + T).toFun = S.toFun + T.toFun := by
  funext x
  simp [SmoothCcTensor.toFun, SmoothCcTensor.toSection_add,
    ContMDiffSection.coe_add, Pi.add_apply, TensorRSSpace.toModel_add]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.SmoothCcTensor.toFun_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.SmoothCcTensor.toFun_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.SmoothCcTensor.toFun_add ``Submission.DifferentialGeometry.Integral.L2.SmoothCcTensor.toFun_add

@[simp] lemma SmoothCcTensor.toFun_neg (S : SmoothCcTensor g r s) :
    (-S).toFun = -S.toFun := by
  funext x
  simp [SmoothCcTensor.toFun, SmoothCcTensor.toSection_neg,
    ContMDiffSection.coe_neg, Pi.neg_apply, TensorRSSpace.toModel_neg]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.SmoothCcTensor.toFun_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.SmoothCcTensor.toFun_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.SmoothCcTensor.toFun_neg ``Submission.DifferentialGeometry.Integral.L2.SmoothCcTensor.toFun_neg

@[simp] lemma SmoothCcTensor.toFun_sub (S T : SmoothCcTensor g r s) :
    (S - T).toFun = S.toFun - T.toFun := by
  funext x
  simp [SmoothCcTensor.toFun, SmoothCcTensor.toSection_sub,
    ContMDiffSection.coe_sub, Pi.sub_apply, TensorRSSpace.toModel_sub]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.SmoothCcTensor.toFun_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.SmoothCcTensor.toFun_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.SmoothCcTensor.toFun_sub ``Submission.DifferentialGeometry.Integral.L2.SmoothCcTensor.toFun_sub

@[simp] lemma SmoothCcTensor.toFun_smul (c : ℝ) (S : SmoothCcTensor g r s) :
    (c • S).toFun = c • S.toFun := by
  funext x
  simp [SmoothCcTensor.toFun, SmoothCcTensor.toSection_smul,
    ContMDiffSection.coe_smul, Pi.smul_apply, TensorRSSpace.toModel_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.SmoothCcTensor.toFun_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.SmoothCcTensor.toFun_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.SmoothCcTensor.toFun_smul ``Submission.DifferentialGeometry.Integral.L2.SmoothCcTensor.toFun_smul

end Algebra

end L2
end Integral
end DifferentialGeometry

end
