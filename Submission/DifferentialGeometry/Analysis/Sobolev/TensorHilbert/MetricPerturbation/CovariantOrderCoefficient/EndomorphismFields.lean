import Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricPerturbation.InverseMetricSlotCoefficient

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Connection.Realization
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev

open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open _root_.Submission.DifferentialGeometry.TensorRSNabla
open _root_.Submission.DifferentialGeometry.TensorMultilinear
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization
  (metricCauchySchwarzBound ccTensorBilinSymm)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.instCompleteSpace_differentialGeometry target :: scope.openDecls } }
def connTermEndo (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x) :=
  -(((ContinuousLinearMap.compL ℝ (TangentSpace I x) (TangentSpace I x) (TangentSpace I x)).flip
      (metricComparisonEndomorphism (I := I) g₀ g₁ x)).comp
      (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x).flip)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.connTermEndo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.connTermEndo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.connTermEndo ``Submission.DifferentialGeometry.Analysis.Sobolev.connTermEndo

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma connTermEndo_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v0 w : TangentSpace I x) :
    connTermEndo (I := I) g₀ g₁ x v0 w =
      - PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (metricComparisonEndomorphism (I := I) g₀ g₁ x w) v0 := by
  rw [connTermEndo, neg_apply, neg_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.connTermEndo_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.connTermEndo_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.connTermEndo_apply ``Submission.DifferentialGeometry.Analysis.Sobolev.connTermEndo_apply

def sharpTermEndo (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x) :=
  (endoCovariantDerivative (I := I) (M := M) g₀)
      (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁) x
    - connTermEndo (I := I) g₀ g₁ x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.sharpTermEndo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.sharpTermEndo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.sharpTermEndo ``Submission.DifferentialGeometry.Analysis.Sobolev.sharpTermEndo

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] [SigmaCompactSpace M] in
lemma sharpTermEndo_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v0 w : TangentSpace I x) :
    sharpTermEndo (I := I) g₀ g₁ x v0 w =
      inverseMetricSharpFib (I := I) g₁ x
        (dualToCotangent (I := I)
          (-(cotangentToCLM (I := I) (g0FlatCLM (I := I) g₀ x w)).comp
              ((PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x).flip v0)).toLinearMap) := by
  rw [sharpTermEndo, sub_apply, sub_apply,
    connTermEndo_apply, endoCov_gInvDiffRaisedField_fibrewise (I := I) g₀ g₁ x v0 w]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.sharpTermEndo_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.sharpTermEndo_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.sharpTermEndo_apply ``Submission.DifferentialGeometry.Analysis.Sobolev.sharpTermEndo_apply

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] [SigmaCompactSpace M] in
lemma endoCov_eq_connTerm_add_sharpTerm (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v0 : TangentSpace I x) :
    (endoCovariantDerivative (I := I) (M := M) g₀)
        (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁) x v0 =
      connTermEndo (I := I) g₀ g₁ x v0 + sharpTermEndo (I := I) g₀ g₁ x v0 := by
  apply ContinuousLinearMap.ext; intro w
  rw [add_apply, connTermEndo_apply, sharpTermEndo_apply,
    endoCov_gInvDiffRaisedField_fibrewise (I := I) g₀ g₁ x v0 w]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.endoCov_eq_connTerm_add_sharpTerm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.endoCov_eq_connTerm_add_sharpTerm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.endoCov_eq_connTerm_add_sharpTerm ``Submission.DifferentialGeometry.Analysis.Sobolev.endoCov_eq_connTerm_add_sharpTerm

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private theorem leviCivitaSection_contMDiff (g : SmoothRiemannianMetric I M)
    {σ : Π x : M, TangentSpace I x}
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% σ)) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M =>
        (⟨x, (LeviCivita (I := I) g).toFun σ x⟩ :
          _root_.Bundle.TotalSpace (E →L[ℝ] E) (fun x : M =>
            TangentSpace I x →L[ℝ] TangentSpace I x))) := by
  have hσ' : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1) (T% σ) Set.univ := by
    have h_le : ((∞ : WithTop ℕ∞) + 1) ≤ (∞ : WithTop ℕ∞) := by rw [ENat.coe_top_add_one]
    exact (hσ.of_le h_le).contMDiffOn
  rw [← contMDiffOn_univ]
  exact LeviCivita_section_contMDiffOn_univ (I := I) g hσ'

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.leviCivitaSection_contMDiff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.leviCivitaSection_contMDiff target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem connTermEndo_inner_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M)
    (V0 W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
        (connTermEndo (I := I) g₀ g₁ x (V0 x) (W x))) := by
  have hconn : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
        (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
          (metricComparisonEndomorphism (I := I) g₀ g₁ x (W x)) (V0 x))) :=
    PDE.DeTurck.connectionDifference_contMDiff (I := I) g₁ g₀
      (metricComparisonEndomorphism_section_contMDiff (I := I) g₀ g₁ W) V0.contMDiff
  refine (hconn.neg_section).congr (fun x => ?_)
  rw [connTermEndo_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.connTermEndo_inner_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.connTermEndo_inner_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.connTermEndo_inner_contMDiff ``Submission.DifferentialGeometry.Analysis.Sobolev.connTermEndo_inner_contMDiff

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem sharpTermEndo_inner_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M)
    (V0 W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
        (sharpTermEndo (I := I) g₀ g₁ x (V0 x) (W x))) := by
  have hendo : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
        ((endoCovariantDerivative (I := I) (M := M) g₀)
          (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁) x (V0 x) (W x))) := by
    have hΛcovW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
          ((LeviCivita (I := I) g₀).toFun
            (fun y : M => (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁ y) (W y)) x (V0 x))) :=
      ContMDiff.clm_bundle_apply (b := id)
        (leviCivitaSection_contMDiff (I := I) g₀
          (endoApplySection_contMDiff (I := I) (M := M) (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁) W))
        V0.contMDiff
    have hcovWsec : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
          ((LeviCivita (I := I) g₀).toFun (fun y : M => W y) x (V0 x))) :=
      ContMDiff.clm_bundle_apply (b := id)
        (leviCivitaSection_contMDiff (I := I) g₀ W.contMDiff) V0.contMDiff
    have hcovW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
          ((metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁ x)
            ((LeviCivita (I := I) g₀).toFun (fun y : M => W y) x (V0 x)))) :=
      endoApplySection_contMDiff (I := I) (M := M) (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁)
        ⟨_, hcovWsec⟩
    refine (hΛcovW.sub_section hcovW).congr (fun x => ?_)
    rw [endoCovariantDerivative_apply (I := I) (M := M) g₀
      (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁) W x (V0 x)]
    rfl
  refine (hendo.sub_section (connTermEndo_inner_contMDiff (I := I) g₀ g₁ V0 W)).congr (fun x => ?_)
  rw [show sharpTermEndo (I := I) g₀ g₁ x (V0 x) (W x) =
      (endoCovariantDerivative (I := I) (M := M) g₀)
        (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁) x (V0 x) (W x)
      - connTermEndo (I := I) g₀ g₁ x (V0 x) (W x) from by
    rw [sharpTermEndo, sub_apply, sub_apply]]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.sharpTermEndo_inner_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.sharpTermEndo_inner_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.sharpTermEndo_inner_contMDiff ``Submission.DifferentialGeometry.Analysis.Sobolev.sharpTermEndo_inner_contMDiff

def connTermCc (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 2 3 where
  toSection :=
    { toFun := fun x : M =>
        TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) 1 x
          (connTermEndo (I := I) g₀ g₁ x))
      contMDiff_toFun :=
        termSlotFib_contMDiff (I := I) (M := M) 1 (fun x : M => connTermEndo (I := I) g₀ g₁ x)
          (connTermEndo_inner_contMDiff (I := I) g₀ g₁) }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.connTermCc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.connTermCc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.connTermCc ``Submission.DifferentialGeometry.Analysis.Sobolev.connTermCc

def sharpTermCc (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 2 3 where
  toSection :=
    { toFun := fun x : M =>
        TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) 1 x
          (sharpTermEndo (I := I) g₀ g₁ x))
      contMDiff_toFun :=
        termSlotFib_contMDiff (I := I) (M := M) 1 (fun x : M => sharpTermEndo (I := I) g₀ g₁ x)
          (sharpTermEndo_inner_contMDiff (I := I) g₀ g₁) }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.sharpTermCc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.sharpTermCc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.sharpTermCc ``Submission.DifferentialGeometry.Analysis.Sobolev.sharpTermCc

omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] [SigmaCompactSpace M] in
@[simp] lemma connTermCc_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (connTermCc (I := I) g₀ g₁).toSection x =
      TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) 1 x
        (connTermEndo (I := I) g₀ g₁ x)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.connTermCc_toSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.connTermCc_toSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.connTermCc_toSection ``Submission.DifferentialGeometry.Analysis.Sobolev.connTermCc_toSection

omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] [SigmaCompactSpace M] in
@[simp] lemma sharpTermCc_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (sharpTermCc (I := I) g₀ g₁).toSection x =
      TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) 1 x
        (sharpTermEndo (I := I) g₀ g₁ x)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.sharpTermCc_toSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.sharpTermCc_toSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.sharpTermCc_toSection ``Submission.DifferentialGeometry.Analysis.Sobolev.sharpTermCc_toSection

def connTermEndoCc (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 1 2 where
  toSection :=
    { toFun := fun x : M =>
        TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) 0 x
          (connTermEndo (I := I) g₀ g₁ x))
      contMDiff_toFun :=
        termSlotFib_contMDiff (I := I) (M := M) 0 (fun x : M => connTermEndo (I := I) g₀ g₁ x)
          (connTermEndo_inner_contMDiff (I := I) g₀ g₁) }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.connTermEndoCc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.connTermEndoCc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.connTermEndoCc ``Submission.DifferentialGeometry.Analysis.Sobolev.connTermEndoCc

def sharpTermEndoCc (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 1 2 where
  toSection :=
    { toFun := fun x : M =>
        TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) 0 x
          (sharpTermEndo (I := I) g₀ g₁ x))
      contMDiff_toFun :=
        termSlotFib_contMDiff (I := I) (M := M) 0 (fun x : M => sharpTermEndo (I := I) g₀ g₁ x)
          (sharpTermEndo_inner_contMDiff (I := I) g₀ g₁) }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.sharpTermEndoCc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.sharpTermEndoCc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.sharpTermEndoCc ``Submission.DifferentialGeometry.Analysis.Sobolev.sharpTermEndoCc

omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] [SigmaCompactSpace M] in
@[simp] lemma connTermEndoCc_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (connTermEndoCc (I := I) g₀ g₁).toSection x =
      TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) 0 x
        (connTermEndo (I := I) g₀ g₁ x)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.connTermEndoCc_toSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.connTermEndoCc_toSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.connTermEndoCc_toSection ``Submission.DifferentialGeometry.Analysis.Sobolev.connTermEndoCc_toSection

omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] [SigmaCompactSpace M] in
@[simp] lemma sharpTermEndoCc_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (sharpTermEndoCc (I := I) g₀ g₁).toSection x =
      TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) 0 x
        (sharpTermEndo (I := I) g₀ g₁ x)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.sharpTermEndoCc_toSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.sharpTermEndoCc_toSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.sharpTermEndoCc_toSection ``Submission.DifferentialGeometry.Analysis.Sobolev.sharpTermEndoCc_toSection

private local instance tangentEndomorphismNormedAddCommGroup (x : M) :
    NormedAddCommGroup (TangentSpace I x →L[ℝ] TangentSpace I x) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := TangentSpace I x) (F := TangentSpace I x) (σ₁₂ := RingHom.id ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.tangentEndomorphismNormedAddCommGroup
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.tangentEndomorphismNormedAddCommGroup target :: scope.openDecls } }

private local instance tangentBilinearEndomorphismNormedAddCommGroup (x : M) :
    NormedAddCommGroup
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := TangentSpace I x) (F := TangentSpace I x →L[ℝ] TangentSpace I x)
    (σ₁₂ := RingHom.id ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.tangentBilinearEndomorphismNormedAddCommGroup
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.tangentBilinearEndomorphismNormedAddCommGroup target :: scope.openDecls } }

private local instance tensor0STotalSpaceTopology (s : ℕ) :
    TopologicalSpace (_root_.Bundle.TotalSpace (Tensor0SModel s ℝ E)
      (fun x : M => Tensor0SSpace s I x)) :=
  Tensor0SBundle.tensor0SBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.tensor0STotalSpaceTopology
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.tensor0STotalSpaceTopology target :: scope.openDecls } }

def bilinEndoCovariantDerivative (g : SmoothRiemannianMetric I M) :
    CovariantDerivative I (E →L[ℝ] (E →L[ℝ] E))
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)) :=
  HomConnection.homBundleCovariantDerivative I M
    E (fun x : M => TangentSpace I x)
    (E →L[ℝ] E) (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
    (LeviCivita (I := I) g) (endoCovariantDerivative (I := I) (M := M) g)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.bilinEndoCovariantDerivative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.bilinEndoCovariantDerivative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.bilinEndoCovariantDerivative ``Submission.DifferentialGeometry.Analysis.Sobolev.bilinEndoCovariantDerivative

instance bilinEndoCovariantDerivative_contMDiff (g : SmoothRiemannianMetric I M) :
    (bilinEndoCovariantDerivative (I := I) (M := M) g).ContMDiffCovariantDerivative ∞ :=
  HomConnection.homBundleCovariantDerivative_contMDiff I M
    E (fun x : M => TangentSpace I x)
    (E →L[ℝ] E) (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
    (LeviCivita (I := I) g) (endoCovariantDerivative (I := I) (M := M) g)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.bilinEndoCovariantDerivative_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.bilinEndoCovariantDerivative_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.bilinEndoCovariantDerivative_contMDiff ``Submission.DifferentialGeometry.Analysis.Sobolev.bilinEndoCovariantDerivative_contMDiff

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] in
theorem bilinEndoCovariantDerivative_apply (g : SmoothRiemannianMetric I M)
    (Term : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (Y : ContMDiffSection I E ∞ (TangentSpace I)) (x : M) (v : E) :
    ((bilinEndoCovariantDerivative (I := I) (M := M) g) Term x v) (Y x) =
      (endoCovariantDerivative (I := I) (M := M) g) (fun y => (Term y) (Y y)) x v -
        (Term x) ((LeviCivita (I := I) g) (fun y => Y y) x v) :=
  HomConnection.homBundleCovariantDerivative_apply I M
    E (fun x : M => TangentSpace I x)
    (E →L[ℝ] E) (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
    (LeviCivita (I := I) g) (endoCovariantDerivative (I := I) (M := M) g) Term Y x v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.bilinEndoCovariantDerivative_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.bilinEndoCovariantDerivative_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.bilinEndoCovariantDerivative_apply ``Submission.DifferentialGeometry.Analysis.Sobolev.bilinEndoCovariantDerivative_apply

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem termField_inner_contMDiff
    (Term : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (V0 W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
        (Term x (V0 x) (W x))) := by
  have h1 : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) x
        (Term x (V0 x))) :=
    ContMDiff.clm_bundle_apply (b := id) Term.contMDiff V0.contMDiff
  exact ContMDiff.clm_bundle_apply (b := id) h1 W.contMDiff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.termField_inner_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.termField_inner_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.termField_inner_contMDiff ``Submission.DifferentialGeometry.Analysis.Sobolev.termField_inner_contMDiff

def bilinearSlotInsertionCoefficient (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Term : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x))) :
    SmoothCcTensor g (s + 1) (s + 1 + 1) where
  toSection :=
    { toFun := fun x : M =>
        TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) s x (Term x))
      contMDiff_toFun :=
        termSlotFib_contMDiff (I := I) (M := M) s (fun x : M => Term x)
          (fun V0 W => termField_inner_contMDiff (I := I) (M := M) Term V0 W) }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.bilinearSlotInsertionCoefficient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.bilinearSlotInsertionCoefficient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.bilinearSlotInsertionCoefficient ``Submission.DifferentialGeometry.Analysis.Sobolev.bilinearSlotInsertionCoefficient

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    [SigmaCompactSpace M] in
@[simp] lemma termSlotEndoCc_toSection (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Term : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (x : M) :
    (bilinearSlotInsertionCoefficient (I := I) (M := M) g s Term).toSection x =
      TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) s x (Term x)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.termSlotEndoCc_toSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.termSlotEndoCc_toSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.termSlotEndoCc_toSection ``Submission.DifferentialGeometry.Analysis.Sobolev.termSlotEndoCc_toSection

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [SigmaCompactSpace M] in
theorem bilinEndoField_contMDiff
    (Term : Π x : M, TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x))
    (harm : ∀ (V0 W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
          (Term x (V0 x) (W x)))) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] (E →L[ℝ] E))) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] E))
        (E := fun z : M => TangentSpace I z →L[ℝ] (TangentSpace I z →L[ℝ] TangentSpace I z)) x
        (Term x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := E) (V₁ := fun x : M => TangentSpace I x)
    (F₂ := E →L[ℝ] E) (V₂ := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
    (φ := fun x : M => (show TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x) from
      Term x))
  intro V0
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := E) (V₁ := fun x : M => TangentSpace I x)
    (F₂ := E) (V₂ := fun x : M => TangentSpace I x)
    (φ := fun x : M => (show TangentSpace I x →L[ℝ] TangentSpace I x from Term x (V0 x)))
  intro W
  exact harm V0 W

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.bilinEndoField_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.bilinEndoField_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.bilinEndoField_contMDiff ``Submission.DifferentialGeometry.Analysis.Sobolev.bilinEndoField_contMDiff

def connTermEndoField (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)) :=
  ⟨fun x : M => connTermEndo (I := I) g₀ g₁ x,
    bilinEndoField_contMDiff (I := I) (M := M) (fun x : M => connTermEndo (I := I) g₀ g₁ x)
      (connTermEndo_inner_contMDiff (I := I) g₀ g₁)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.connTermEndoField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.connTermEndoField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.connTermEndoField ``Submission.DifferentialGeometry.Analysis.Sobolev.connTermEndoField

def sharpTermEndoField (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)) :=
  ⟨fun x : M => sharpTermEndo (I := I) g₀ g₁ x,
    bilinEndoField_contMDiff (I := I) (M := M) (fun x : M => sharpTermEndo (I := I) g₀ g₁ x)
      (sharpTermEndo_inner_contMDiff (I := I) g₀ g₁)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.sharpTermEndoField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.sharpTermEndoField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.sharpTermEndoField ``Submission.DifferentialGeometry.Analysis.Sobolev.sharpTermEndoField

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
omit [I.Boundaryless] [SigmaCompactSpace M] in
@[simp] lemma connTermEndoField_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    connTermEndoField (I := I) g₀ g₁ x = connTermEndo (I := I) g₀ g₁ x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.connTermEndoField_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.connTermEndoField_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.connTermEndoField_apply ``Submission.DifferentialGeometry.Analysis.Sobolev.connTermEndoField_apply

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
omit [I.Boundaryless] [SigmaCompactSpace M] in
@[simp] lemma sharpTermEndoField_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    sharpTermEndoField (I := I) g₀ g₁ x = sharpTermEndo (I := I) g₀ g₁ x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.sharpTermEndoField_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.sharpTermEndoField_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.sharpTermEndoField_apply ``Submission.DifferentialGeometry.Analysis.Sobolev.sharpTermEndoField_apply

omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] [SigmaCompactSpace M] in
lemma connTermCc_eq_termSlotEndoCc (g₀ g₁ : SmoothRiemannianMetric I M) :
    connTermCc (I := I) g₀ g₁ = bilinearSlotInsertionCoefficient (I := I) (M := M) g₀ 1
      (connTermEndoField (I := I) g₀ g₁) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [connTermCc_toSection, termSlotEndoCc_toSection, connTermEndoField_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.connTermCc_eq_termSlotEndoCc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.connTermCc_eq_termSlotEndoCc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.connTermCc_eq_termSlotEndoCc ``Submission.DifferentialGeometry.Analysis.Sobolev.connTermCc_eq_termSlotEndoCc

omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] [SigmaCompactSpace M] in
lemma sharpTermCc_eq_termSlotEndoCc (g₀ g₁ : SmoothRiemannianMetric I M) :
    sharpTermCc (I := I) g₀ g₁ = bilinearSlotInsertionCoefficient (I := I) (M := M) g₀ 1
      (sharpTermEndoField (I := I) g₀ g₁) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [sharpTermCc_toSection, termSlotEndoCc_toSection, sharpTermEndoField_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.sharpTermCc_eq_termSlotEndoCc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.sharpTermCc_eq_termSlotEndoCc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.sharpTermCc_eq_termSlotEndoCc ``Submission.DifferentialGeometry.Analysis.Sobolev.sharpTermCc_eq_termSlotEndoCc

omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] [SigmaCompactSpace M] in
lemma connTermEndoCc_eq_termSlotEndoCc (g₀ g₁ : SmoothRiemannianMetric I M) :
    connTermEndoCc (I := I) g₀ g₁ = bilinearSlotInsertionCoefficient (I := I) (M := M) g₀ 0
      (connTermEndoField (I := I) g₀ g₁) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [connTermEndoCc_toSection, termSlotEndoCc_toSection, connTermEndoField_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.connTermEndoCc_eq_termSlotEndoCc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.connTermEndoCc_eq_termSlotEndoCc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.connTermEndoCc_eq_termSlotEndoCc ``Submission.DifferentialGeometry.Analysis.Sobolev.connTermEndoCc_eq_termSlotEndoCc

omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] [SigmaCompactSpace M] in
lemma sharpTermEndoCc_eq_termSlotEndoCc (g₀ g₁ : SmoothRiemannianMetric I M) :
    sharpTermEndoCc (I := I) g₀ g₁ = bilinearSlotInsertionCoefficient (I := I) (M := M) g₀ 0
      (sharpTermEndoField (I := I) g₀ g₁) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [sharpTermEndoCc_toSection, termSlotEndoCc_toSection, sharpTermEndoField_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.sharpTermEndoCc_eq_termSlotEndoCc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.sharpTermEndoCc_eq_termSlotEndoCc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.sharpTermEndoCc_eq_termSlotEndoCc ``Submission.DifferentialGeometry.Analysis.Sobolev.sharpTermEndoCc_eq_termSlotEndoCc

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
lemma curry_termSlotFib_eq_slotInsert (s : ℕ) (x : M)
    (Term : TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x))
    (A : Tensor0SSpace (s + 1) I x) (v0 : TangentSpace I x) :
    (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x
        (bilinearSlotInsertCLM (I := I) (M := M) s x Term A)) v0 =
      slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x (Term v0) A := by
  apply (tensor0SSpaceFiberContinuousLinearEquiv (I := I) (s + 1) x).injective
  refine ContinuousMultilinearMap.ext (fun vt => ?_)
  change Tensor0SSpace.eval
      ((tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x
        (bilinearSlotInsertCLM (I := I) (M := M) s x Term A)) v0) vt =
    Tensor0SSpace.eval
      (slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x (Term v0) A) vt
  rw [tensor0S_curry_apply_eval, termSlotFib_apply_eval]
  simp only [Fin.cons_zero]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.curry_termSlotFib_eq_slotInsert then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.curry_termSlotFib_eq_slotInsert"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.curry_termSlotFib_eq_slotInsert ``Submission.DifferentialGeometry.Analysis.Sobolev.curry_termSlotFib_eq_slotInsert

end Sobolev
end Analysis
end DifferentialGeometry

end
