import Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.L2Operator.MixedTensor
import Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.Iterates
import Submission.DifferentialGeometry.Analysis.Integration.L2.Hilbert.Defs
import Submission.DifferentialGeometry.Analysis.Integration.L2.Hilbert.DenseSubset
import Submission.DifferentialGeometry.Analysis.Integration.L2.Hilbert.SmoothSectionMap
import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Module.Projective

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators _root_.Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Elliptic
namespace ConnectionLaplacian

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

private local instance _root_.Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.instCompleteSpace_differentialGeometry target :: scope.openDecls } }


def smoothCcToL2Submodule (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    Submodule ℝ (TensorL2 r s g) :=
  LinearMap.range
    ((SmoothCcTensor.toL2 (g := g) (r := r) (s := s)).toLinearMap)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.smoothCcToL2Submodule then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.smoothCcToL2Submodule"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.smoothCcToL2Submodule ``Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.smoothCcToL2Submodule


def connLaplacianL2Action (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    SmoothCcTensor g r s →ₗ[ℝ] TensorL2 r s g where
  toFun T :=
    SmoothCcTensor.toL2 (g := g) (r := r) (s := s)
      (rawTensorConnLapSmooth (I := I) g r s T)
  map_add' T₁ T₂ := by
    have h_lap_add :
        rawTensorConnLapSmooth (I := I) g r s (T₁ + T₂) =
          rawTensorConnLapSmooth (I := I) g r s T₁ +
            rawTensorConnLapSmooth (I := I) g r s T₂ := by
      apply SmoothCcTensor.ext
      apply ContMDiffSection.ext
      intro x
      have hsum :=
        tensorConnLaplacian_of_contMDiff_add (I := I) g r s T₁ T₂
          (rawTensorConnLap_contMDiff (I := I) g r s
            (fun z : M => T₁.toSection z) T₁.toSection.contMDiff_toFun)
          (rawTensorConnLap_contMDiff (I := I) g r s
            (fun z : M => T₂.toSection z) T₂.toSection.contMDiff_toFun)
          (rawTensorConnLap_contMDiff (I := I) g r s
            (fun z : M => (T₁ + T₂).toSection z)
            (T₁ + T₂).toSection.contMDiff_toFun) x
      have hLHS : (rawTensorConnLapSmooth (I := I) g r s (T₁ + T₂)).toSection x =
          (tensorConnLaplacianOfContMDiff (I := I) g r s (T₁ + T₂)
            (rawTensorConnLap_contMDiff (I := I) g r s
              (fun z : M => (T₁ + T₂).toSection z)
              (T₁ + T₂).toSection.contMDiff_toFun)).toSection x := rfl
      have hRHS₁ : (rawTensorConnLapSmooth (I := I) g r s T₁).toSection x =
          (tensorConnLaplacianOfContMDiff (I := I) g r s T₁
            (rawTensorConnLap_contMDiff (I := I) g r s
              (fun z : M => T₁.toSection z)
              T₁.toSection.contMDiff_toFun)).toSection x := rfl
      have hRHS₂ : (rawTensorConnLapSmooth (I := I) g r s T₂).toSection x =
          (tensorConnLaplacianOfContMDiff (I := I) g r s T₂
            (rawTensorConnLap_contMDiff (I := I) g r s
              (fun z : M => T₂.toSection z)
              T₂.toSection.contMDiff_toFun)).toSection x := rfl
      have hsum_section :
          (rawTensorConnLapSmooth (I := I) g r s T₁ +
              rawTensorConnLapSmooth (I := I) g r s T₂).toSection x =
            (rawTensorConnLapSmooth (I := I) g r s T₁).toSection x +
              (rawTensorConnLapSmooth (I := I) g r s T₂).toSection x := by
        rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add]
        rfl
      rw [hLHS, hsum_section, hRHS₁, hRHS₂]
      exact hsum
    rw [h_lap_add, SmoothCcTensor.toL2_add]
  map_smul' c T := by
    have h_lap_smul :
        rawTensorConnLapSmooth (I := I) g r s (c • T) =
          c • rawTensorConnLapSmooth (I := I) g r s T := by
      apply SmoothCcTensor.ext
      apply ContMDiffSection.ext
      intro x
      have hsmul :=
        tensorConnLaplacian_of_contMDiff_smul (I := I) g r s c T
          (rawTensorConnLap_contMDiff (I := I) g r s
            (fun z : M => T.toSection z) T.toSection.contMDiff_toFun)
          (rawTensorConnLap_contMDiff (I := I) g r s
            (fun z : M => (c • T).toSection z)
            (c • T).toSection.contMDiff_toFun) x
      have hLHS : (rawTensorConnLapSmooth (I := I) g r s (c • T)).toSection x =
          (tensorConnLaplacianOfContMDiff (I := I) g r s (c • T)
            (rawTensorConnLap_contMDiff (I := I) g r s
              (fun z : M => (c • T).toSection z)
              (c • T).toSection.contMDiff_toFun)).toSection x := rfl
      have hRHS : (rawTensorConnLapSmooth (I := I) g r s T).toSection x =
          (tensorConnLaplacianOfContMDiff (I := I) g r s T
            (rawTensorConnLap_contMDiff (I := I) g r s
              (fun z : M => T.toSection z)
              T.toSection.contMDiff_toFun)).toSection x := rfl
      have hsmul_section :
          (c • rawTensorConnLapSmooth (I := I) g r s T).toSection x =
            c • (rawTensorConnLapSmooth (I := I) g r s T).toSection x := by
        rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul]
        rfl
      rw [hLHS, hsmul_section, hRHS]
      exact hsmul
    rw [h_lap_smul, SmoothCcTensor.toL2_smul]
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.connLaplacianL2Action then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.connLaplacianL2Action"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.connLaplacianL2Action ``Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.connLaplacianL2Action

omit [CompactSpace M] in
@[simp] lemma connLaplacianL2Action_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s) :
    connLaplacianL2Action (I := I) g r s T =
      SmoothCcTensor.toL2 (g := g) (r := r) (s := s)
        (rawTensorConnLapSmooth (I := I) g r s T) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.connLaplacianL2Action_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.connLaplacianL2Action_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.connLaplacianL2Action_apply ``Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.connLaplacianL2Action_apply


def toL2RangeRestrict (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    SmoothCcTensor g r s →ₗ[ℝ] smoothCcToL2Submodule (I := I) g r s :=
  LinearMap.rangeRestrict
    ((SmoothCcTensor.toL2 (g := g) (r := r) (s := s)).toLinearMap)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.toL2RangeRestrict then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.toL2RangeRestrict"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.toL2RangeRestrict ``Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.toL2RangeRestrict


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
lemma toL2RangeRestrict_surjective
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    Function.Surjective (toL2RangeRestrict (I := I) g r s) := by
  intro u
  obtain ⟨T, hT⟩ := u.property
  refine ⟨T, ?_⟩
  apply Subtype.ext
  exact hT

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.toL2RangeRestrict_surjective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.toL2RangeRestrict_surjective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.toL2RangeRestrict_surjective ``Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.toL2RangeRestrict_surjective


def smoothCcSection (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    smoothCcToL2Submodule (I := I) g r s →ₗ[ℝ] SmoothCcTensor g r s :=
  Classical.choose
    ((toL2RangeRestrict (I := I) g r s).exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr
        (toL2RangeRestrict_surjective (I := I) g r s)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.smoothCcSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.smoothCcSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.smoothCcSection ``Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.smoothCcSection


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
lemma toL2RangeRestrict_smoothCcSection
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    (toL2RangeRestrict (I := I) g r s).comp (smoothCcSection (I := I) g r s) =
      LinearMap.id :=
  Classical.choose_spec
    ((toL2RangeRestrict (I := I) g r s).exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr
        (toL2RangeRestrict_surjective (I := I) g r s)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.toL2RangeRestrict_smoothCcSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.toL2RangeRestrict_smoothCcSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.toL2RangeRestrict_smoothCcSection ``Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.toL2RangeRestrict_smoothCcSection


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
lemma toL2RangeRestrict_smoothCcSection_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u : smoothCcToL2Submodule (I := I) g r s) :
    (toL2RangeRestrict (I := I) g r s) (smoothCcSection (I := I) g r s u) =
      u := by
  have h := toL2RangeRestrict_smoothCcSection (I := I) g r s
  exact congrArg (fun (f : _ →ₗ[ℝ] _) => f u) h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.toL2RangeRestrict_smoothCcSection_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.toL2RangeRestrict_smoothCcSection_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.toL2RangeRestrict_smoothCcSection_apply ``Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.toL2RangeRestrict_smoothCcSection_apply


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
lemma toL2_smoothCcSection
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u : smoothCcToL2Submodule (I := I) g r s) :
    SmoothCcTensor.toL2 (g := g) (r := r) (s := s)
        (smoothCcSection (I := I) g r s u) = (u : TensorL2 r s g) := by
  have h := toL2RangeRestrict_smoothCcSection_apply (I := I) g r s u
  have hval : ((toL2RangeRestrict (I := I) g r s)
      (smoothCcSection (I := I) g r s u)).val = (u : TensorL2 r s g) := by
    exact congrArg Subtype.val h
  change SmoothCcTensor.toL2 (g := g) (r := r) (s := s)
      (smoothCcSection (I := I) g r s u) = (u : TensorL2 r s g)
  have hrr : ((toL2RangeRestrict (I := I) g r s)
      (smoothCcSection (I := I) g r s u)).val =
      SmoothCcTensor.toL2 (g := g) (r := r) (s := s)
        (smoothCcSection (I := I) g r s u) := rfl
  rw [hrr] at hval
  exact hval

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.toL2_smoothCcSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.toL2_smoothCcSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.toL2_smoothCcSection ``Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.toL2_smoothCcSection


def connLaplacianL2OnDomain (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    smoothCcToL2Submodule (I := I) g r s →ₗ[ℝ] TensorL2 r s g :=
  (connLaplacianL2Action (I := I) g r s).comp
    (smoothCcSection (I := I) g r s)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.connLaplacianL2OnDomain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.connLaplacianL2OnDomain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.connLaplacianL2OnDomain ``Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.connLaplacianL2OnDomain

omit [CompactSpace M] in
@[simp] lemma connLaplacianL2OnDomain_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u : smoothCcToL2Submodule (I := I) g r s) :
    connLaplacianL2OnDomain (I := I) g r s u =
      connLaplacianL2Action (I := I) g r s
        (smoothCcSection (I := I) g r s u) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.connLaplacianL2OnDomain_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.connLaplacianL2OnDomain_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.connLaplacianL2OnDomain_apply ``Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.connLaplacianL2OnDomain_apply


def connLaplacianL2 (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    TensorL2 r s g →ₗ.[ℝ] TensorL2 r s g where
  domain := smoothCcToL2Submodule (I := I) g r s
  toFun := connLaplacianL2OnDomain (I := I) g r s

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.connLaplacianL2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.connLaplacianL2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.connLaplacianL2 ``Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.connLaplacianL2


omit [CompactSpace M] in
@[simp] theorem connLaplacianL2_domain_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    (connLaplacianL2 (I := I) g r s).domain =
      smoothCcToL2Submodule (I := I) g r s := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.connLaplacianL2_domain_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.connLaplacianL2_domain_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.connLaplacianL2_domain_eq ``Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.connLaplacianL2_domain_eq


omit [CompactSpace M] in
theorem connLaplacianL2_apply_toL2
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s)
    (hT : SmoothCcTensor.toL2 (g := g) (r := r) (s := s) T ∈
      (connLaplacianL2 (I := I) g r s).domain) :
    (connLaplacianL2 (I := I) g r s)
        ⟨SmoothCcTensor.toL2 (g := g) (r := r) (s := s) T, hT⟩ =
      connLaplacianL2Action (I := I) g r s
        (smoothCcSection (I := I) g r s
          ⟨SmoothCcTensor.toL2 (g := g) (r := r) (s := s) T, hT⟩) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.connLaplacianL2_apply_toL2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.connLaplacianL2_apply_toL2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.connLaplacianL2_apply_toL2 ``Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.connLaplacianL2_apply_toL2


omit [CompactSpace M] in
theorem toL2_mem_connLaplacianL2_domain
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s) :
    SmoothCcTensor.toL2 (g := g) (r := r) (s := s) T ∈
      (connLaplacianL2 (I := I) g r s).domain := by
  rw [connLaplacianL2_domain_eq]
  exact LinearMap.mem_range_self _ T

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.toL2_mem_connLaplacianL2_domain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.toL2_mem_connLaplacianL2_domain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.toL2_mem_connLaplacianL2_domain ``Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.toL2_mem_connLaplacianL2_domain

end ConnectionLaplacian
end Elliptic
end Analysis
end DifferentialGeometry

end
