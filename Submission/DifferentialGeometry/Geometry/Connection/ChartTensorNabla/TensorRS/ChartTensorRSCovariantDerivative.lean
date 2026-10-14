import Submission.DifferentialGeometry.Geometry.Connection.ChartTensorNabla.Tensor0S.ChartTensor0SCovariantDerivative
import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.Chart.Local
import Submission.DifferentialGeometry.Geometry.Connection.ChartTensorNabla.Tensor0S.Tensor0SChartChristoffel
import Submission.DifferentialGeometry.Tensor.RSTensor.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators
open _root_.Submission.DifferentialGeometry.Tensor0SBundle

namespace DifferentialGeometry
namespace Geometry
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem

noncomputable def tensorRSChartESectionRepr (r s : ℕ) (α : M)
    (T : Π b : M, TensorRSSpace r s I b) (b : M) : TensorRSModel r s ℝ E :=
  (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b (T b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensorRSChartESectionRepr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensorRSChartESectionRepr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensorRSChartESectionRepr ``Submission.DifferentialGeometry.Geometry.Connection.tensorRSChartESectionRepr

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
@[simp] lemma tensorRSChartE_section_repr_apply (r s : ℕ) (α : M)
    (T : Π b : M, TensorRSSpace r s I b) (b : M) :
    tensorRSChartESectionRepr (I := I) r s α T b =
      (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b (T b) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr_apply ``Submission.DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr_apply

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma tensorRSChartE_section_repr_add (r s : ℕ) (α : M)
    (T₁ T₂ : Π b : M, TensorRSSpace r s I b) :
    tensorRSChartESectionRepr (I := I) r s α (T₁ + T₂) =
      tensorRSChartESectionRepr (I := I) r s α T₁ +
        tensorRSChartESectionRepr (I := I) r s α T₂ := by
  funext b
  unfold tensorRSChartESectionRepr
  change (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
        ((T₁ + T₂) b) = _
  change (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
        (T₁ b + T₂ b) = _
  exact map_add _ (T₁ b) (T₂ b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr_add ``Submission.DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr_add

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma tensorRSChartE_section_repr_smul (r s : ℕ) (α : M) (c : ℝ)
    (T : Π b : M, TensorRSSpace r s I b) :
    tensorRSChartESectionRepr (I := I) r s α (c • T) =
      c • tensorRSChartESectionRepr (I := I) r s α T := by
  funext b
  unfold tensorRSChartESectionRepr
  change (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
        ((c • T) b) = _
  change (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
        (c • T b) = _
  exact map_smul _ c (T b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr_smul ``Submission.DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr_smul

noncomputable def tensorRSChartFiberFromModel (r s : ℕ) (α : M) (b : M) :
    TensorRSModel r s ℝ E →L[ℝ] TensorRSSpace r s I b :=
  (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).symmL ℝ b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensorRSChartFiberFromModel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensorRSChartFiberFromModel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensorRSChartFiberFromModel ``Submission.DifferentialGeometry.Geometry.Connection.tensorRSChartFiberFromModel

noncomputable def tensorRSIntrinsicChartCLM (r s : ℕ) (α : M)
    (T : Π b : M, TensorRSSpace r s I b) (b : M) :
    TangentSpace I b →L[ℝ] TensorRSSpace r s I b :=
  (tensorRSChartFiberFromModel (I := I) r s α b).comp
    ((fderiv ℝ
        (tensorRSChartESectionRepr (I := I) r s α T ∘ (extChartAt I α).symm)
        (extChartAt I α b)).comp
      (trivToE (I := I) α b))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensorRSIntrinsicChartCLM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensorRSIntrinsicChartCLM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensorRSIntrinsicChartCLM ``Submission.DifferentialGeometry.Geometry.Connection.tensorRSIntrinsicChartCLM

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma tensorRSIntrinsicChartCLM_apply (r s : ℕ) (α : M)
    (T : Π b : M, TensorRSSpace r s I b) (b : M) (v : TangentSpace I b) :
    tensorRSIntrinsicChartCLM (I := I) r s α T b v =
      tensorRSChartFiberFromModel (I := I) r s α b
        (fderiv ℝ
          (tensorRSChartESectionRepr (I := I) r s α T ∘ (extChartAt I α).symm)
          (extChartAt I α b) (trivToE (I := I) α b v)) := by
  classical
  unfold tensorRSIntrinsicChartCLM
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensorRSIntrinsicChartCLM_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensorRSIntrinsicChartCLM_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensorRSIntrinsicChartCLM_apply ``Submission.DifferentialGeometry.Geometry.Connection.tensorRSIntrinsicChartCLM_apply

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma tensorRSIntrinsicChartCLM_add_section (r s : ℕ) (α : M)
    (T₁ T₂ : Π b : M, TensorRSSpace r s I b) (b : M)
    (h₁ : DifferentiableAt ℝ
      (tensorRSChartESectionRepr (I := I) r s α T₁ ∘ (extChartAt I α).symm)
      (extChartAt I α b))
    (h₂ : DifferentiableAt ℝ
      (tensorRSChartESectionRepr (I := I) r s α T₂ ∘ (extChartAt I α).symm)
      (extChartAt I α b)) :
    tensorRSIntrinsicChartCLM (I := I) r s α (T₁ + T₂) b =
      tensorRSIntrinsicChartCLM (I := I) r s α T₁ b +
        tensorRSIntrinsicChartCLM (I := I) r s α T₂ b := by
  classical
  have hsum_pull :
      (tensorRSChartESectionRepr (I := I) r s α (T₁ + T₂) ∘
          (extChartAt I α).symm) =
        (tensorRSChartESectionRepr (I := I) r s α T₁ ∘
            (extChartAt I α).symm) +
          (tensorRSChartESectionRepr (I := I) r s α T₂ ∘
            (extChartAt I α).symm) := by
    funext y
    exact congrFun (tensorRSChartE_section_repr_add (I := I) r s α T₁ T₂)
      ((extChartAt I α).symm y)
  have hfd : fderiv ℝ
        (tensorRSChartESectionRepr (I := I) r s α (T₁ + T₂) ∘
          (extChartAt I α).symm) (extChartAt I α b) =
      fderiv ℝ
          (tensorRSChartESectionRepr (I := I) r s α T₁ ∘
            (extChartAt I α).symm) (extChartAt I α b) +
        fderiv ℝ
          (tensorRSChartESectionRepr (I := I) r s α T₂ ∘
            (extChartAt I α).symm) (extChartAt I α b) := by
    rw [hsum_pull]
    exact fderiv_add h₁ h₂
  unfold tensorRSIntrinsicChartCLM
  rw [hfd]
  ext v
  rw [add_apply]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  rw [add_apply, map_add]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensorRSIntrinsicChartCLM_add_section then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensorRSIntrinsicChartCLM_add_section"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensorRSIntrinsicChartCLM_add_section ``Submission.DifferentialGeometry.Geometry.Connection.tensorRSIntrinsicChartCLM_add_section

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma tensorRSIntrinsicChartCLM_smul_section (r s : ℕ) (α : M)
    (c : ℝ) (T : Π b : M, TensorRSSpace r s I b) (b : M)
    (hT : DifferentiableAt ℝ
      (tensorRSChartESectionRepr (I := I) r s α T ∘ (extChartAt I α).symm)
      (extChartAt I α b)) :
    tensorRSIntrinsicChartCLM (I := I) r s α (c • T) b =
      c • tensorRSIntrinsicChartCLM (I := I) r s α T b := by
  classical
  have hsmul_pull :
      (tensorRSChartESectionRepr (I := I) r s α (c • T) ∘
          (extChartAt I α).symm) =
        c • (tensorRSChartESectionRepr (I := I) r s α T ∘
          (extChartAt I α).symm) := by
    funext y
    exact congrFun (tensorRSChartE_section_repr_smul (I := I) r s α c T)
      ((extChartAt I α).symm y)
  have hfd : fderiv ℝ
        (tensorRSChartESectionRepr (I := I) r s α (c • T) ∘
          (extChartAt I α).symm) (extChartAt I α b) =
      c • fderiv ℝ
          (tensorRSChartESectionRepr (I := I) r s α T ∘
            (extChartAt I α).symm) (extChartAt I α b) := by
    rw [hsmul_pull]
    exact fderiv_const_smul hT c
  unfold tensorRSIntrinsicChartCLM
  rw [hfd]
  ext v
  rw [smul_apply]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  rw [smul_apply, map_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensorRSIntrinsicChartCLM_smul_section then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensorRSIntrinsicChartCLM_smul_section"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensorRSIntrinsicChartCLM_smul_section ``Submission.DifferentialGeometry.Geometry.Connection.tensorRSIntrinsicChartCLM_smul_section

def tangentSlotCLM (n : ℕ) {b : M}
    (k : Fin n) (Φ : TangentSpace I b →L[ℝ] TangentSpace I b)
    (i : Fin n) : TangentSpace I b →L[ℝ] TangentSpace I b :=
  if i = k then Φ else ContinuousLinearMap.id ℝ (TangentSpace I b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tangentSlotCLM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tangentSlotCLM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tangentSlotCLM ``Submission.DifferentialGeometry.Geometry.Connection.tangentSlotCLM

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M]
    [T2Space M] in
lemma tangentSlotCLM_self (n : ℕ) {b : M}
    (k : Fin n) (Φ : TangentSpace I b →L[ℝ] TangentSpace I b) :
    tangentSlotCLM (I := I) n k Φ k = Φ := by
  unfold tangentSlotCLM
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tangentSlotCLM_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tangentSlotCLM_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tangentSlotCLM_self ``Submission.DifferentialGeometry.Geometry.Connection.tangentSlotCLM_self

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M]
    [T2Space M] in
lemma tangentSlotCLM_other (n : ℕ) {b : M}
    (k : Fin n) (Φ : TangentSpace I b →L[ℝ] TangentSpace I b)
    {i : Fin n} (h : i ≠ k) :
    tangentSlotCLM (I := I) n k Φ i = ContinuousLinearMap.id ℝ (TangentSpace I b) := by
  unfold tangentSlotCLM
  simp [h]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tangentSlotCLM_other then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tangentSlotCLM_other"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tangentSlotCLM_other ``Submission.DifferentialGeometry.Geometry.Connection.tangentSlotCLM_other

noncomputable def tangentCompCLMLE (n : ℕ) (b : M)
    (Φ : Fin n → (TangentSpace I b →L[ℝ] TangentSpace I b)) :
    ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℝ →L[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℝ :=
  ContinuousMultilinearMap.compContinuousLinearMapL
    (𝕜 := ℝ) (E := fun _ : Fin n => E) (F := ℝ)
    (show Fin n → (E →L[ℝ] E) from Φ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tangentCompCLMLE then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tangentCompCLMLE"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tangentCompCLMLE ``Submission.DifferentialGeometry.Geometry.Connection.tangentCompCLMLE

noncomputable def tensorSlotSubstCLM (n : ℕ) (b : M)
    (Φ : Fin n → (TangentSpace I b →L[ℝ] TangentSpace I b)) :
    Tensor0SSpace n I b →L[ℝ] Tensor0SSpace n I b :=
  ((tensor0SSpaceContinuousLinearEquiv (I := I) (M := M) n b).symm
      : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℝ →L[ℝ]
          Tensor0SSpace n I b).comp
    ((tangentCompCLMLE (I := I) (M := M) n b Φ).comp
      ((tensor0SSpaceContinuousLinearEquiv (I := I) (M := M) n b)
          : Tensor0SSpace n I b →L[ℝ]
            ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℝ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensorSlotSubstCLM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensorSlotSubstCLM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensorSlotSubstCLM ``Submission.DifferentialGeometry.Geometry.Connection.tensorSlotSubstCLM

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma tensorSlotSubstCLM_apply (n : ℕ) (b : M)
    (Φ : Fin n → (TangentSpace I b →L[ℝ] TangentSpace I b))
    (τ : Tensor0SSpace n I b) (m : Fin n → TangentSpace I b) :
    Tensor0SSpace.eval (tensorSlotSubstCLM (I := I) n b Φ τ) m =
      Tensor0SSpace.eval τ (fun i => Φ i (m i)) := by
  classical
  unfold tensorSlotSubstCLM tangentCompCLMLE
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensorSlotSubstCLM_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensorSlotSubstCLM_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensorSlotSubstCLM_apply ``Submission.DifferentialGeometry.Geometry.Connection.tensorSlotSubstCLM_apply

noncomputable def chartTensorRSInputSlotCorrection (r s : ℕ)
    (g : SmoothRiemannianMetric I M) (α : M)
    (T : Π b' : M, TensorRSSpace r s I b')
    (X : Π b' : M, TangentSpace I b') (b : M) (k : Fin r) :
    TensorRSSpace r s I b :=
  (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b).comp
    (tensorSlotSubstCLM (I := I) r b
      (tangentSlotCLM (I := I) r k
        (chartLeviCivitaParallelCLM (I := I) g α b X)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartTensorRSInputSlotCorrection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartTensorRSInputSlotCorrection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartTensorRSInputSlotCorrection ``Submission.DifferentialGeometry.Geometry.Connection.chartTensorRSInputSlotCorrection

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma chartTensorRSInputSlotCorrection_apply (r s : ℕ)
    (g : SmoothRiemannianMetric I M) (α : M)
    (T : Π b' : M, TensorRSSpace r s I b')
    (X : Π b' : M, TangentSpace I b') (b : M) (k : Fin r)
    (α_input : Tensor0SSpace r I b) (m : Fin s → TangentSpace I b) :
    Tensor0SSpace.eval
        (chartTensorRSInputSlotCorrection (I := I) r s g α T X b k α_input) m =
      Tensor0SSpace.eval
        (T b (tensorSlotSubstCLM (I := I) r b
          (tangentSlotCLM (I := I) r k
            (chartLeviCivitaParallelCLM (I := I) g α b X)) α_input)) m := by
  classical
  unfold chartTensorRSInputSlotCorrection
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartTensorRSInputSlotCorrection_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartTensorRSInputSlotCorrection_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartTensorRSInputSlotCorrection_apply ``Submission.DifferentialGeometry.Geometry.Connection.chartTensorRSInputSlotCorrection_apply

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma chartTensorRSInputSlotCorrection_add (r s : ℕ)
    (g : SmoothRiemannianMetric I M) (α : M)
    (T₁ T₂ : Π b' : M, TensorRSSpace r s I b')
    (X : Π b' : M, TangentSpace I b') (b : M) (k : Fin r) :
    chartTensorRSInputSlotCorrection (I := I) r s g α (T₁ + T₂) X b k =
      chartTensorRSInputSlotCorrection (I := I) r s g α T₁ X b k
        + chartTensorRSInputSlotCorrection (I := I) r s g α T₂ X b k := by
  classical
  unfold chartTensorRSInputSlotCorrection
  have hT_add : ((T₁ + T₂) b
      : Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b) =
      (T₁ b : Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b)
        + (T₂ b : Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b) := rfl
  rw [hT_add]
  exact ContinuousLinearMap.add_comp _ _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartTensorRSInputSlotCorrection_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartTensorRSInputSlotCorrection_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartTensorRSInputSlotCorrection_add ``Submission.DifferentialGeometry.Geometry.Connection.chartTensorRSInputSlotCorrection_add

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma chartTensorRSInputSlotCorrection_smul (r s : ℕ)
    (g : SmoothRiemannianMetric I M) (α : M) (c : ℝ)
    (T : Π b' : M, TensorRSSpace r s I b')
    (X : Π b' : M, TangentSpace I b') (b : M) (k : Fin r) :
    chartTensorRSInputSlotCorrection (I := I) r s g α (c • T) X b k =
      c • chartTensorRSInputSlotCorrection (I := I) r s g α T X b k := by
  classical
  unfold chartTensorRSInputSlotCorrection
  have hT_smul : ((c • T) b
      : Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b) =
      c • (T b : Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b) := rfl
  rw [hT_smul]
  exact ContinuousLinearMap.smul_comp _ _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartTensorRSInputSlotCorrection_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartTensorRSInputSlotCorrection_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartTensorRSInputSlotCorrection_smul ``Submission.DifferentialGeometry.Geometry.Connection.chartTensorRSInputSlotCorrection_smul

noncomputable def chartTensorRSOutputSlotCorrection (r s : ℕ)
    (g : SmoothRiemannianMetric I M) (α : M)
    (T : Π b' : M, TensorRSSpace r s I b')
    (X : Π b' : M, TangentSpace I b') (b : M) (l : Fin s) :
    TensorRSSpace r s I b :=
  (tensorSlotSubstCLM (I := I) s b
      (tangentSlotCLM (I := I) s l
        (chartLeviCivitaParallelCLM (I := I) g α b X))).comp
    (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartTensorRSOutputSlotCorrection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartTensorRSOutputSlotCorrection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartTensorRSOutputSlotCorrection ``Submission.DifferentialGeometry.Geometry.Connection.chartTensorRSOutputSlotCorrection

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma chartTensorRSOutputSlotCorrection_apply (r s : ℕ)
    (g : SmoothRiemannianMetric I M) (α : M)
    (T : Π b' : M, TensorRSSpace r s I b')
    (X : Π b' : M, TangentSpace I b') (b : M) (l : Fin s)
    (α_input : Tensor0SSpace r I b) (m : Fin s → TangentSpace I b) :
    Tensor0SSpace.eval
        (chartTensorRSOutputSlotCorrection (I := I) r s g α T X b l α_input) m =
      Tensor0SSpace.eval (T b α_input) (fun i =>
        tangentSlotCLM (I := I) s l
          (chartLeviCivitaParallelCLM (I := I) g α b X) i (m i)) := by
  classical
  unfold chartTensorRSOutputSlotCorrection
  rw [ContinuousLinearMap.comp_apply]
  exact tensorSlotSubstCLM_apply (I := I) s b
    (tangentSlotCLM (I := I) s l
      (chartLeviCivitaParallelCLM (I := I) g α b X))
    ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b) α_input) m

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartTensorRSOutputSlotCorrection_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartTensorRSOutputSlotCorrection_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartTensorRSOutputSlotCorrection_apply ``Submission.DifferentialGeometry.Geometry.Connection.chartTensorRSOutputSlotCorrection_apply

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma chartTensorRSOutputSlotCorrection_add (r s : ℕ)
    (g : SmoothRiemannianMetric I M) (α : M)
    (T₁ T₂ : Π b' : M, TensorRSSpace r s I b')
    (X : Π b' : M, TangentSpace I b') (b : M) (l : Fin s) :
    chartTensorRSOutputSlotCorrection (I := I) r s g α (T₁ + T₂) X b l =
      chartTensorRSOutputSlotCorrection (I := I) r s g α T₁ X b l
        + chartTensorRSOutputSlotCorrection (I := I) r s g α T₂ X b l := by
  classical
  unfold chartTensorRSOutputSlotCorrection
  have hT_add : ((T₁ + T₂) b
      : Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b) =
      (T₁ b : Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b)
        + (T₂ b : Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b) := rfl
  rw [hT_add]
  exact ContinuousLinearMap.comp_add _ _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartTensorRSOutputSlotCorrection_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartTensorRSOutputSlotCorrection_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartTensorRSOutputSlotCorrection_add ``Submission.DifferentialGeometry.Geometry.Connection.chartTensorRSOutputSlotCorrection_add

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma chartTensorRSOutputSlotCorrection_smul (r s : ℕ)
    (g : SmoothRiemannianMetric I M) (α : M) (c : ℝ)
    (T : Π b' : M, TensorRSSpace r s I b')
    (X : Π b' : M, TangentSpace I b') (b : M) (l : Fin s) :
    chartTensorRSOutputSlotCorrection (I := I) r s g α (c • T) X b l =
      c • chartTensorRSOutputSlotCorrection (I := I) r s g α T X b l := by
  classical
  unfold chartTensorRSOutputSlotCorrection
  have hT_smul : ((c • T) b
      : Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b) =
      c • (T b : Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b) := rfl
  rw [hT_smul]
  exact ContinuousLinearMap.comp_smul _ _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartTensorRSOutputSlotCorrection_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartTensorRSOutputSlotCorrection_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartTensorRSOutputSlotCorrection_smul ``Submission.DifferentialGeometry.Geometry.Connection.chartTensorRSOutputSlotCorrection_smul

noncomputable def chartTensorRSCovariantDerivative (r s : ℕ)
    (g : SmoothRiemannianMetric I M) (α : M)
    (T : Π b : M, TensorRSSpace r s I b)
    (X : Π b : M, TangentSpace I b) (b : M) : TensorRSSpace r s I b :=
  tensorRSIntrinsicChartCLM (I := I) r s α T b (X b)
    + (∑ k : Fin r,
        chartTensorRSInputSlotCorrection (I := I) r s g α T X b k)
    - (∑ l : Fin s,
        chartTensorRSOutputSlotCorrection (I := I) r s g α T X b l)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartTensorRSCovariantDerivative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartTensorRSCovariantDerivative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartTensorRSCovariantDerivative ``Submission.DifferentialGeometry.Geometry.Connection.chartTensorRSCovariantDerivative

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma chartTensorRSCovariantDerivative_def (r s : ℕ)
    (g : SmoothRiemannianMetric I M) (α : M)
    (T : Π b : M, TensorRSSpace r s I b)
    (X : Π b : M, TangentSpace I b) (b : M) :
    chartTensorRSCovariantDerivative (I := I) r s g α T X b =
      tensorRSIntrinsicChartCLM (I := I) r s α T b (X b)
        + (∑ k : Fin r,
            chartTensorRSInputSlotCorrection (I := I) r s g α T X b k)
        - (∑ l : Fin s,
            chartTensorRSOutputSlotCorrection (I := I) r s g α T X b l) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartTensorRSCovariantDerivative_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartTensorRSCovariantDerivative_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartTensorRSCovariantDerivative_def ``Submission.DifferentialGeometry.Geometry.Connection.chartTensorRSCovariantDerivative_def

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma chartTensorRSCovariantDerivative_apply (r s : ℕ)
    (g : SmoothRiemannianMetric I M) (α : M)
    (T : Π b : M, TensorRSSpace r s I b)
    (X : Π b : M, TangentSpace I b) (b : M)
    (α_input : Tensor0SSpace r I b) (m : Fin s → TangentSpace I b) :
    Tensor0SSpace.eval
        (chartTensorRSCovariantDerivative (I := I) r s g α T X b α_input) m =
      Tensor0SSpace.eval
        (tensorRSIntrinsicChartCLM (I := I) r s α T b (X b) α_input) m
      + ∑ k : Fin r,
          Tensor0SSpace.eval
            (chartTensorRSInputSlotCorrection (I := I) r s g α T X b k α_input) m
      - ∑ l : Fin s,
          Tensor0SSpace.eval
            (chartTensorRSOutputSlotCorrection (I := I) r s g α T X b l α_input) m := by
  classical
  rw [chartTensorRSCovariantDerivative_def]
  set Bsum : TensorRSSpace r s I b :=
      ∑ k : Fin r,
        chartTensorRSInputSlotCorrection (I := I) r s g α T X b k with hBdef
  set Csum : TensorRSSpace r s I b :=
      ∑ l : Fin s,
        chartTensorRSOutputSlotCorrection (I := I) r s g α T X b l with hCdef
  have hstep1 :
      Tensor0SSpace.eval
          ((tensorRSIntrinsicChartCLM (I := I) r s α T b (X b) + Bsum - Csum) α_input) m =
        Tensor0SSpace.eval
            (tensorRSIntrinsicChartCLM (I := I) r s α T b (X b) α_input) m
        + Tensor0SSpace.eval (Bsum α_input) m
        - Tensor0SSpace.eval (Csum α_input) m :=
    rfl
  rw [hstep1]
  have hBeval :
      Tensor0SSpace.eval (Bsum α_input) m =
      ∑ k : Fin r,
          Tensor0SSpace.eval
            (chartTensorRSInputSlotCorrection (I := I) r s g α T X b k α_input) m := by
    rw [hBdef, sum_apply]
    unfold Tensor0SSpace.eval
    rw [map_sum, sum_apply]
  have hCeval :
      Tensor0SSpace.eval (Csum α_input) m =
      ∑ l : Fin s,
          Tensor0SSpace.eval
            (chartTensorRSOutputSlotCorrection (I := I) r s g α T X b l α_input) m := by
    rw [hCdef, sum_apply]
    unfold Tensor0SSpace.eval
    rw [map_sum, sum_apply]
  rw [hBeval, hCeval]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartTensorRSCovariantDerivative_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartTensorRSCovariantDerivative_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartTensorRSCovariantDerivative_apply ``Submission.DifferentialGeometry.Geometry.Connection.chartTensorRSCovariantDerivative_apply

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma chartTensorRSCovariantDerivative_add (r s : ℕ)
    (g : SmoothRiemannianMetric I M) (α : M)
    (T₁ T₂ : Π b : M, TensorRSSpace r s I b)
    (X : Π b : M, TangentSpace I b) (b : M)
    (h₁ : DifferentiableAt ℝ
      (tensorRSChartESectionRepr (I := I) r s α T₁ ∘ (extChartAt I α).symm)
      (extChartAt I α b))
    (h₂ : DifferentiableAt ℝ
      (tensorRSChartESectionRepr (I := I) r s α T₂ ∘ (extChartAt I α).symm)
      (extChartAt I α b)) :
    chartTensorRSCovariantDerivative (I := I) r s g α (T₁ + T₂) X b =
      chartTensorRSCovariantDerivative (I := I) r s g α T₁ X b
        + chartTensorRSCovariantDerivative (I := I) r s g α T₂ X b := by
  classical
  rw [chartTensorRSCovariantDerivative_def,
      chartTensorRSCovariantDerivative_def,
      chartTensorRSCovariantDerivative_def]
  have hsplit_intrinsic :
      tensorRSIntrinsicChartCLM (I := I) r s α (T₁ + T₂) b (X b) =
        tensorRSIntrinsicChartCLM (I := I) r s α T₁ b (X b)
          + tensorRSIntrinsicChartCLM (I := I) r s α T₂ b (X b) := by
    have hCLM := tensorRSIntrinsicChartCLM_add_section
      (I := I) r s α T₁ T₂ b h₁ h₂
    have := congrArg (fun L : TangentSpace I b →L[ℝ] TensorRSSpace r s I b
                        => L (X b)) hCLM
    simpa using this
  rw [hsplit_intrinsic]
  have hsplit_input :
      (∑ k : Fin r,
          chartTensorRSInputSlotCorrection (I := I) r s g α (T₁ + T₂) X b k) =
        (∑ k : Fin r,
            chartTensorRSInputSlotCorrection (I := I) r s g α T₁ X b k) +
          (∑ k : Fin r,
              chartTensorRSInputSlotCorrection (I := I) r s g α T₂ X b k) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    exact chartTensorRSInputSlotCorrection_add (I := I) r s g α T₁ T₂ X b k
  rw [hsplit_input]
  have hsplit_output :
      (∑ l : Fin s,
          chartTensorRSOutputSlotCorrection (I := I) r s g α (T₁ + T₂) X b l) =
        (∑ l : Fin s,
            chartTensorRSOutputSlotCorrection (I := I) r s g α T₁ X b l) +
          (∑ l : Fin s,
              chartTensorRSOutputSlotCorrection (I := I) r s g α T₂ X b l) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    exact chartTensorRSOutputSlotCorrection_add (I := I) r s g α T₁ T₂ X b l
  rw [hsplit_output]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartTensorRSCovariantDerivative_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartTensorRSCovariantDerivative_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartTensorRSCovariantDerivative_add ``Submission.DifferentialGeometry.Geometry.Connection.chartTensorRSCovariantDerivative_add

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma chartTensorRSCovariantDerivative_smul (r s : ℕ)
    (g : SmoothRiemannianMetric I M) (α : M) (c : ℝ)
    (T : Π b : M, TensorRSSpace r s I b)
    (X : Π b : M, TangentSpace I b) (b : M)
    (hT : DifferentiableAt ℝ
      (tensorRSChartESectionRepr (I := I) r s α T ∘ (extChartAt I α).symm)
      (extChartAt I α b)) :
    chartTensorRSCovariantDerivative (I := I) r s g α (c • T) X b =
      c • chartTensorRSCovariantDerivative (I := I) r s g α T X b := by
  classical
  rw [chartTensorRSCovariantDerivative_def,
      chartTensorRSCovariantDerivative_def]
  have hsplit_intrinsic :
      tensorRSIntrinsicChartCLM (I := I) r s α (c • T) b (X b) =
        c • tensorRSIntrinsicChartCLM (I := I) r s α T b (X b) := by
    have hCLM := tensorRSIntrinsicChartCLM_smul_section
      (I := I) r s α c T b hT
    have := congrArg (fun L : TangentSpace I b →L[ℝ] TensorRSSpace r s I b
                        => L (X b)) hCLM
    simpa using this
  rw [hsplit_intrinsic]
  have hsplit_input :
      (∑ k : Fin r,
          chartTensorRSInputSlotCorrection (I := I) r s g α (c • T) X b k) =
        c • (∑ k : Fin r,
              chartTensorRSInputSlotCorrection (I := I) r s g α T X b k) := by
    have hterm :
        (∑ k : Fin r,
            chartTensorRSInputSlotCorrection (I := I) r s g α (c • T) X b k) =
          ∑ k : Fin r,
            c • chartTensorRSInputSlotCorrection (I := I) r s g α T X b k := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      exact chartTensorRSInputSlotCorrection_smul (I := I) r s g α c T X b k
    rw [hterm]
    classical
    have hmap :=
      map_sum (LinearMap.lsmul ℝ (TensorRSSpace r s I b) c)
        (fun k => chartTensorRSInputSlotCorrection (I := I) r s g α T X b k)
        Finset.univ
    exact hmap.symm
  rw [hsplit_input]
  have hsplit_output :
      (∑ l : Fin s,
          chartTensorRSOutputSlotCorrection (I := I) r s g α (c • T) X b l) =
        c • (∑ l : Fin s,
              chartTensorRSOutputSlotCorrection (I := I) r s g α T X b l) := by
    have hterm :
        (∑ l : Fin s,
            chartTensorRSOutputSlotCorrection (I := I) r s g α (c • T) X b l) =
          ∑ l : Fin s,
            c • chartTensorRSOutputSlotCorrection (I := I) r s g α T X b l := by
      refine Finset.sum_congr rfl (fun l _ => ?_)
      exact chartTensorRSOutputSlotCorrection_smul (I := I) r s g α c T X b l
    rw [hterm]
    classical
    have hmap :=
      map_sum (LinearMap.lsmul ℝ (TensorRSSpace r s I b) c)
        (fun l => chartTensorRSOutputSlotCorrection (I := I) r s g α T X b l)
        Finset.univ
    exact hmap.symm
  rw [hsplit_output]
  rw [smul_sub, smul_add]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartTensorRSCovariantDerivative_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartTensorRSCovariantDerivative_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartTensorRSCovariantDerivative_smul ``Submission.DifferentialGeometry.Geometry.Connection.chartTensorRSCovariantDerivative_smul

end Connection
end Geometry
end DifferentialGeometry
