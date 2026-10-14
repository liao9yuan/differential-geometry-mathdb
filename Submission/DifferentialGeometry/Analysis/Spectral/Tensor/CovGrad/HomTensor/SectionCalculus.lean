import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.HomTensor.CovariantCalculus

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators


namespace DifferentialGeometry
namespace Geometry
namespace Connection

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M]

private local instance _root_.Submission.DifferentialGeometry.Geometry.Connection.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Connection.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Connection.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

omit [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_continuous_riemannianFiberNormSq_homSection_clm_le
    (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x))) :
    ∃ Cop : M → ℝ, Continuous Cop ∧ (∀ x : M, 0 ≤ Cop x) ∧
      ∀ (x : M) (v : TensorRSSpace r a I x),
        riemannianFiberNormSq (I := I) (M := M) g r c x (Ψ x v) ≤
          Cop x * riemannianFiberNormSq (I := I) (M := M) g r a x v :=
  exists_continuous_riemannianFiberNormSq_homTensorRS_section_clm_le
    (g := g) (r := r) (a := a) (c := c) (Ψ := Ψ) (hΨ := hΨ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.exists_continuous_riemannianFiberNormSq_homSection_clm_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.exists_continuous_riemannianFiberNormSq_homSection_clm_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.exists_continuous_riemannianFiberNormSq_homSection_clm_le ``Submission.DifferentialGeometry.Geometry.Connection.exists_continuous_riemannianFiberNormSq_homSection_clm_le

omit [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_uniform_riemannianFiberNormSq_homSection_clm_le
    (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : M) (v : TensorRSSpace r a I x),
      riemannianFiberNormSq (I := I) (M := M) g r c x (Ψ x v) ≤
        C * riemannianFiberNormSq (I := I) (M := M) g r a x v :=
  exists_uniform_riemannianFiberNormSq_homTensorRS_section_clm_le
    (g := g) (r := r) (a := a) (c := c) (Ψ := Ψ) (hΨ := hΨ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.exists_uniform_riemannianFiberNormSq_homSection_clm_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.exists_uniform_riemannianFiberNormSq_homSection_clm_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.exists_uniform_riemannianFiberNormSq_homSection_clm_le ``Submission.DifferentialGeometry.Geometry.Connection.exists_uniform_riemannianFiberNormSq_homSection_clm_le

omit [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_uniform_riemannianFiberNormSq_homTensorRSApply_le
    (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (W : SmoothCcTensor g r a) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g r c x
          ((homTensorRSApply (I := I) (M := M) g r a c Ψ hΨ W).toSection x) ≤
        C * riemannianFiberNormSq (I := I) (M := M) g r a x (W.toSection x) := by
  obtain ⟨C, hC_nn, hC⟩ :=
    exists_uniform_riemannianFiberNormSq_homSection_clm_le (I := I) (M := M) g r a c Ψ hΨ
  refine ⟨C, hC_nn, fun W x => ?_⟩
  rw [homTensorRSApply_toSection (I := I) (M := M) g r a c Ψ hΨ W x]
  exact hC x (W.toSection x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.exists_uniform_riemannianFiberNormSq_homTensorRSApply_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.exists_uniform_riemannianFiberNormSq_homTensorRSApply_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.exists_uniform_riemannianFiberNormSq_homTensorRSApply_le ``Submission.DifferentialGeometry.Geometry.Connection.exists_uniform_riemannianFiberNormSq_homTensorRSApply_le

abbrev HomTensorRSField (r a c : ℕ) (I : ModelWithCorners ℝ E H)
    [IsManifold I ∞ M] : Type _ :=
  Cₛ^∞⟮I; HomTensorRSModel r a c ℝ E, (fun x : M => HomTensorRSSpace r a c I x)⟯

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.HomTensorRSField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.HomTensorRSField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.HomTensorRSField ``Submission.DifferentialGeometry.Geometry.Connection.HomTensorRSField

noncomputable def homTensorRSFieldApply (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Q : HomTensorRSField (E := E) (M := M) r a c I) (W : SmoothCcTensor g r a) : SmoothCcTensor g r
      c :=
  homTensorRSApply (I := I) (M := M) g r a c (fun x : M => Q x) Q.contMDiff W

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.homTensorRSFieldApply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.homTensorRSFieldApply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.homTensorRSFieldApply ``Submission.DifferentialGeometry.Geometry.Connection.homTensorRSFieldApply

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
    in
@[simp] lemma homTensorRSFieldApply_toSection (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Q : HomTensorRSField (E := E) (M := M) r a c I) (W : SmoothCcTensor g r a) (x : M) :
    (homTensorRSFieldApply (I := I) (M := M) g r a c Q W).toSection x =
      (show TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x from Q x) (W.toSection x) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.homTensorRSFieldApply_toSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.homTensorRSFieldApply_toSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.homTensorRSFieldApply_toSection ``Submission.DifferentialGeometry.Geometry.Connection.homTensorRSFieldApply_toSection

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
    in
theorem homTensorRSFieldApply_add_left (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Qa Qb : HomTensorRSField (E := E) (M := M) r a c I) (W : SmoothCcTensor g r a) :
    homTensorRSFieldApply (I := I) (M := M) g r a c (Qa + Qb) W =
      homTensorRSFieldApply (I := I) (M := M) g r a c Qa W + homTensorRSFieldApply (I := I) (M := M)
        g r a c Qb W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((homTensorRSFieldApply (I := I) (M := M) g r a c Qa W +
        homTensorRSFieldApply (I := I) (M := M) g r a c Qb W).toSection x) =
      (homTensorRSFieldApply (I := I) (M := M) g r a c Qa W).toSection x +
        (homTensorRSFieldApply (I := I) (M := M) g r a c Qb W).toSection x from rfl]
  rw [homTensorRSFieldApply_toSection, homTensorRSFieldApply_toSection, homTensorRSFieldApply_toSection]
  rw [show ((Qa + Qb) x : TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x) =
      (Qa x : TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x) +
        (Qb x : TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x) from by
    rw [ContMDiffSection.coe_add, Pi.add_apply]]
  rw [add_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.homTensorRSFieldApply_add_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.homTensorRSFieldApply_add_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.homTensorRSFieldApply_add_left ``Submission.DifferentialGeometry.Geometry.Connection.homTensorRSFieldApply_add_left

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
    in
theorem homTensorRSFieldApply_zero_left (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (W : SmoothCcTensor g r a) :
    homTensorRSFieldApply (I := I) (M := M) g r a c (0 : HomTensorRSField (E := E) (M := M) r a c I)
      W = 0 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [homTensorRSFieldApply_toSection]
  rw [show ((0 : HomTensorRSField (E := E) (M := M) r a c I) x :
      TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x) = 0 from by
    rw [ContMDiffSection.coe_zero, Pi.zero_apply]]
  rw [zero_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.homTensorRSFieldApply_zero_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.homTensorRSFieldApply_zero_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.homTensorRSFieldApply_zero_left ``Submission.DifferentialGeometry.Geometry.Connection.homTensorRSFieldApply_zero_left

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
    in
theorem homTensorRSFieldApply_sub_left (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Qa Qb : HomTensorRSField (E := E) (M := M) r a c I) (W : SmoothCcTensor g r a) :
    homTensorRSFieldApply (I := I) (M := M) g r a c (Qa - Qb) W =
      homTensorRSFieldApply (I := I) (M := M) g r a c Qa W - homTensorRSFieldApply (I := I) (M := M)
        g r a c Qb W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((homTensorRSFieldApply (I := I) (M := M) g r a c Qa W -
        homTensorRSFieldApply (I := I) (M := M) g r a c Qb W).toSection x) =
      (homTensorRSFieldApply (I := I) (M := M) g r a c Qa W).toSection x -
        (homTensorRSFieldApply (I := I) (M := M) g r a c Qb W).toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [homTensorRSFieldApply_toSection, homTensorRSFieldApply_toSection, homTensorRSFieldApply_toSection]
  rw [show ((Qa - Qb) x : TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x) =
      (Qa x : TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x) -
        (Qb x : TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x) from by
    rw [ContMDiffSection.coe_sub, Pi.sub_apply]]
  rw [sub_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.homTensorRSFieldApply_sub_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.homTensorRSFieldApply_sub_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.homTensorRSFieldApply_sub_left ``Submission.DifferentialGeometry.Geometry.Connection.homTensorRSFieldApply_sub_left

noncomputable def homTensorRSCovGradSec (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Q : HomTensorRSField (E := E) (M := M) r a c I) : HomTensorRSField (E := E) (M := M) r a
      (c + 1) I where
  toFun := fun x : M => homTensorRSCovGradFib (I := I) (M := M) g r a c (fun y : M => Q y) x
  contMDiff_toFun :=
    homTensorRSCovGradField_contMDiff (I := I) (M := M) g r a c (fun y : M => Q y) Q.contMDiff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.homTensorRSCovGradSec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.homTensorRSCovGradSec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.homTensorRSCovGradSec ``Submission.DifferentialGeometry.Geometry.Connection.homTensorRSCovGradSec

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma homTensorRSCovGradSec_apply (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Q : HomTensorRSField (E := E) (M := M) r a c I) (x : M) :
    (show TensorRSSpace r a I x →L[ℝ] TensorRSSpace r (c + 1) I x from
        homTensorRSCovGradSec (I := I) (M := M) g r a c Q x) =
      homTensorRSCovGradFib (I := I) (M := M) g r a c (fun y : M => Q y) x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.homTensorRSCovGradSec_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.homTensorRSCovGradSec_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.homTensorRSCovGradSec_apply ``Submission.DifferentialGeometry.Geometry.Connection.homTensorRSCovGradSec_apply

noncomputable def slotInsertHomTensorRSField (r a c : ℕ)
    (Q : HomTensorRSField (E := E) (M := M) r a c I) :
    HomTensorRSField (E := E) (M := M) r (a + 1) (c + 1) I where
  toFun := fun x : M => slotInsertHomTensorRSFib (I := I) (M := M) r a c x (Q x)
  contMDiff_toFun :=
    slotInsertHomTensorRSFib_contMDiff (I := I) (M := M) r a c (fun y : M => Q y) Q.contMDiff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.slotInsertHomTensorRSField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.slotInsertHomTensorRSField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.slotInsertHomTensorRSField ``Submission.DifferentialGeometry.Geometry.Connection.slotInsertHomTensorRSField

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    in
@[simp] lemma slotInsertHomTensorRSField_apply (r a c : ℕ)
    (Q : HomTensorRSField (E := E) (M := M) r a c I) (x : M) :
    (show TensorRSSpace r (a + 1) I x →L[ℝ] TensorRSSpace r (c + 1) I x from
        slotInsertHomTensorRSField (I := I) (M := M) r a c Q x) =
      slotInsertHomTensorRSFib (I := I) (M := M) r a c x (Q x) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.slotInsertHomTensorRSField_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.slotInsertHomTensorRSField_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.slotInsertHomTensorRSField_apply ``Submission.DifferentialGeometry.Geometry.Connection.slotInsertHomTensorRSField_apply

omit [NeZero (Module.finrank ℝ E)] in
theorem covGrad_homTensorRSFieldApply_eq (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Q : HomTensorRSField (E := E) (M := M) r a c I) (W : SmoothCcTensor g r a) :
    covGrad (I := I) (M := M) g r c (homTensorRSFieldApply (I := I) (M := M) g r a c Q W) =
      homTensorRSFieldApply (I := I) (M := M) g r a (c + 1)
        (homTensorRSCovGradSec (I := I) (M := M) g r a c Q) W +
        homTensorRSFieldApply (I := I) (M := M) g r (a + 1) (c + 1)
          (slotInsertHomTensorRSField (I := I) (M := M) r a c Q)
          (covGrad (I := I) (M := M) g r a W) :=
  covGrad_homTensorRSApply_eq (I := I) (M := M) g r a c (fun x : M => Q x) Q.contMDiff W

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.covGrad_homTensorRSFieldApply_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.covGrad_homTensorRSFieldApply_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.covGrad_homTensorRSFieldApply_eq ``Submission.DifferentialGeometry.Geometry.Connection.covGrad_homTensorRSFieldApply_eq

def castHomTensorRSFieldTargetRank {c c' : ℕ} (r a : ℕ) (h : c = c')
    (Q : HomTensorRSField (E := E) (M := M) r a c I) :
    HomTensorRSField (E := E) (M := M) r a c' I :=
  h ▸ Q

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.castHomTensorRSFieldTargetRank then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.castHomTensorRSFieldTargetRank"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.castHomTensorRSFieldTargetRank ``Submission.DifferentialGeometry.Geometry.Connection.castHomTensorRSFieldTargetRank

def castHomTensorRSFieldSourceRank {a a' : ℕ} (r c : ℕ) (h : a = a')
    (Q : HomTensorRSField (E := E) (M := M) r a c I) :
    HomTensorRSField (E := E) (M := M) r a' c I :=
  h ▸ Q

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.castHomTensorRSFieldSourceRank then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.castHomTensorRSFieldSourceRank"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.castHomTensorRSFieldSourceRank ``Submission.DifferentialGeometry.Geometry.Connection.castHomTensorRSFieldSourceRank

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
    in
theorem homTensorRSFieldApply_castCcTensorRank {a a' c c' : ℕ} (g : SmoothRiemannianMetric I M) (r : ℕ)
    (ha : a = a') (hc : c = c')
    (Q : HomTensorRSField (E := E) (M := M) r a c I) (V : SmoothCcTensor g r a) :
    castCcTensorRank g r hc (homTensorRSFieldApply (I := I) (M := M) g r a c Q V) =
      homTensorRSFieldApply (I := I) (M := M) g r a' c'
        (castHomTensorRSFieldSourceRank (E := E) (M := M) r c' ha
        (castHomTensorRSFieldTargetRank (E := E) (M := M) r a hc Q)) (castCcTensorRank g r ha V) := by
  subst ha; subst hc; rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.homTensorRSFieldApply_castCcTensorRank then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.homTensorRSFieldApply_castCcTensorRank"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.homTensorRSFieldApply_castCcTensorRank ``Submission.DifferentialGeometry.Geometry.Connection.homTensorRSFieldApply_castCcTensorRank
end Connection
end Geometry
end DifferentialGeometry

end
