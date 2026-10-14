import Submission.DifferentialGeometry.Tensor.RSTensor.Defs
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Bundle.SectionRegularity
import Submission.DifferentialGeometry.Geometry.Metric.PointwiseInner.Defs
import Submission.DifferentialGeometry.Geometry.Metric.PointwiseInner.Algebra
import Submission.DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram
import Submission.DifferentialGeometry.Tensor.Multilinear.Bundle.Basis
import Mathlib.Analysis.LocallyConvex.Bounded
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Topology.VectorBundle.Riemannian

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.IsManifold _root_.ContinuousLinearMap _root_.Submission.ContinuousLinearMap _root_.Bundle.ContinuousLinearMap _root_.Bornology
open scoped _root_.Manifold _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.ContDiff _root_.BigOperators _root_.Matrix

namespace DifferentialGeometry
namespace Tensor
namespace Tensor0SRiemannianBundle

open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Tensor.Tensor0SRiemannian
open _root_.Submission.DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private instance bundleDualTopologicalSpace (s : ℕ) (b : M) :
    TopologicalSpace (Tensor0SSpace s I b →L[ℝ] ℝ) :=
  ContinuousLinearMap.topologicalSpace
    (𝕜₁ := ℝ) (𝕜₂ := ℝ) (σ := RingHom.id ℝ)
    (E := Tensor0SSpace s I b) (F := ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor.Tensor0SRiemannianBundle.bundleDualTopologicalSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor.Tensor0SRiemannianBundle.bundleDualTopologicalSpace target :: scope.openDecls } }

noncomputable def tensor0SRiemannianInnerCLM
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M) :
    Tensor0SSpace s I b →L[ℝ] Tensor0SSpace s I b →L[ℝ] ℝ :=
  innerBundleCLM (I := I) (M := M) g s b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Tensor0SRiemannianBundle.tensor0SRiemannianInnerCLM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Tensor0SRiemannianBundle.tensor0SRiemannianInnerCLM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Tensor0SRiemannianBundle.tensor0SRiemannianInnerCLM ``Submission.DifferentialGeometry.Tensor.Tensor0SRiemannianBundle.tensor0SRiemannianInnerCLM

@[simp] lemma tensor0SRiemannianInnerCLM_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M)
    (T S : Tensor0SSpace s I b) :
    tensor0SRiemannianInnerCLM (I := I) (M := M) g s b T S =
      innerBundleCLM (I := I) (M := M) g s b T S := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Tensor0SRiemannianBundle.tensor0SRiemannianInnerCLM_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Tensor0SRiemannianBundle.tensor0SRiemannianInnerCLM_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Tensor0SRiemannianBundle.tensor0SRiemannianInnerCLM_apply ``Submission.DifferentialGeometry.Tensor.Tensor0SRiemannianBundle.tensor0SRiemannianInnerCLM_apply

theorem tensor0SRiemannianInner_symm
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M)
    (T S : Tensor0SSpace s I b) :
    tensor0SRiemannianInnerCLM (I := I) (M := M) g s b T S =
      tensor0SRiemannianInnerCLM (I := I) (M := M) g s b S T :=
  innerBundleCLM_symm (I := I) (M := M) g s b T S

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Tensor0SRiemannianBundle.tensor0SRiemannianInner_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Tensor0SRiemannianBundle.tensor0SRiemannianInner_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Tensor0SRiemannianBundle.tensor0SRiemannianInner_symm ``Submission.DifferentialGeometry.Tensor.Tensor0SRiemannianBundle.tensor0SRiemannianInner_symm

theorem tensor0SRiemannianInner_pos
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M)
    (T : Tensor0SSpace s I b) (hT : T ≠ 0) :
    0 < tensor0SRiemannianInnerCLM (I := I) (M := M) g s b T T :=
  innerBundleCLM_pos (I := I) (M := M) g s b T hT

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Tensor0SRiemannianBundle.tensor0SRiemannianInner_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Tensor0SRiemannianBundle.tensor0SRiemannianInner_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Tensor0SRiemannianBundle.tensor0SRiemannianInner_pos ``Submission.DifferentialGeometry.Tensor.Tensor0SRiemannianBundle.tensor0SRiemannianInner_pos

theorem tensor0SRiemannianInner_smul_left
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M)
    (c : ℝ) (T S : Tensor0SSpace s I b) :
    tensor0SRiemannianInnerCLM (I := I) (M := M) g s b (c • T) S =
      c * tensor0SRiemannianInnerCLM (I := I) (M := M) g s b T S := by
  have h := ContinuousLinearMap.map_smul
    (innerBundleCLM (I := I) (M := M) g s b) c T
  change innerBundleCLM (I := I) (M := M) g s b (c • T) S = _
  rw [h]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Tensor0SRiemannianBundle.tensor0SRiemannianInner_smul_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Tensor0SRiemannianBundle.tensor0SRiemannianInner_smul_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Tensor0SRiemannianBundle.tensor0SRiemannianInner_smul_left ``Submission.DifferentialGeometry.Tensor.Tensor0SRiemannianBundle.tensor0SRiemannianInner_smul_left

theorem tensor0SRiemannianInner_smul_right
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M)
    (c : ℝ) (T S : Tensor0SSpace s I b) :
    tensor0SRiemannianInnerCLM (I := I) (M := M) g s b T (c • S) =
      c * tensor0SRiemannianInnerCLM (I := I) (M := M) g s b T S := by
  have h := ContinuousLinearMap.map_smul
    ((innerBundleCLM (I := I) (M := M) g s b) T) c S
  change (innerBundleCLM (I := I) (M := M) g s b T) (c • S) = _
  rw [h]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Tensor0SRiemannianBundle.tensor0SRiemannianInner_smul_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Tensor0SRiemannianBundle.tensor0SRiemannianInner_smul_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Tensor0SRiemannianBundle.tensor0SRiemannianInner_smul_right ``Submission.DifferentialGeometry.Tensor.Tensor0SRiemannianBundle.tensor0SRiemannianInner_smul_right

private lemma innerModel_diagonal_continuous
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M) :
    Continuous (fun T : Tensor0SModel s ℝ E =>
      covariantTensorInnerPointwise (I := I) (M := M) s g b T T) := by
  have hModelCLM := (innerModelCLM (I := I) (M := M) g s b).continuous
  have : Continuous (fun T : Tensor0SModel s ℝ E =>
      innerModelCLM (I := I) (M := M) g s b T T) :=
    hModelCLM.clm_apply continuous_id
  simpa [innerModelCLM_apply] using this

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor.Tensor0SRiemannianBundle.innerModel_diagonal_continuous
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor.Tensor0SRiemannianBundle.innerModel_diagonal_continuous target :: scope.openDecls } }

theorem tensor0SRiemannianInner_diagonal_continuous
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M) :
    Continuous (fun v : Tensor0SSpace s I b =>
      tensor0SRiemannianInnerCLM (I := I) (M := M) g s b v v) := by
  have heq : (fun v : Tensor0SSpace s I b =>
      tensor0SRiemannianInnerCLM (I := I) (M := M) g s b v v) =
      (fun v : Tensor0SSpace s I b =>
        covariantTensorInnerPointwise (I := I) (M := M) s g b
          (Tensor0SBundle.Tensor0SSpace.toModel
            (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b) v)
          (Tensor0SBundle.Tensor0SSpace.toModel
            (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b) v)) := by
    funext v
    rw [tensor0SRiemannianInnerCLM_apply, innerBundleCLM_apply]
  rw [heq]
  have htoM : Continuous
      (fun v : Tensor0SSpace s I b =>
        Tensor0SBundle.Tensor0SSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b) v) :=
    Tensor0SBundle.Tensor0SSpace.toModel_continuous
      (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b)
  exact (innerModel_diagonal_continuous (I := I) (M := M) g s b).comp htoM

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Tensor0SRiemannianBundle.tensor0SRiemannianInner_diagonal_continuous then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Tensor0SRiemannianBundle.tensor0SRiemannianInner_diagonal_continuous"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Tensor0SRiemannianBundle.tensor0SRiemannianInner_diagonal_continuous ``Submission.DifferentialGeometry.Tensor.Tensor0SRiemannianBundle.tensor0SRiemannianInner_diagonal_continuous

theorem tensor0SRiemannianInner_diagonal_continuousAt_zero
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M) :
    ContinuousAt (fun v : Tensor0SSpace s I b =>
      tensor0SRiemannianInnerCLM (I := I) (M := M) g s b v v) 0 :=
  (tensor0SRiemannianInner_diagonal_continuous (I := I) (M := M) g s b).continuousAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Tensor0SRiemannianBundle.tensor0SRiemannianInner_diagonal_continuousAt_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Tensor0SRiemannianBundle.tensor0SRiemannianInner_diagonal_continuousAt_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Tensor0SRiemannianBundle.tensor0SRiemannianInner_diagonal_continuousAt_zero ``Submission.DifferentialGeometry.Tensor.Tensor0SRiemannianBundle.tensor0SRiemannianInner_diagonal_continuousAt_zero

private lemma tensor0SRiemannianInner_diagonal_clm_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M)
    (T : Tensor0SSpace s I b) :
    tensor0SRiemannianInnerCLM (I := I) (M := M) g s b T T =
      covariantTensorInnerPointwise (I := I) (M := M) s g b
        (Tensor0SBundle.Tensor0SSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b) T)
        (Tensor0SBundle.Tensor0SSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b) T) := by
  rw [tensor0SRiemannianInnerCLM_apply, innerBundleCLM_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor.Tensor0SRiemannianBundle.tensor0SRiemannianInner_diagonal_clm_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor.Tensor0SRiemannianBundle.tensor0SRiemannianInner_diagonal_clm_apply target :: scope.openDecls } }

private lemma innerModel_diagonal_sublevel_isBounded
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M) :
    Bornology.IsBounded
      {T : Tensor0SModel s ℝ E |
        innerModelCLM (I := I) (M := M) g s b T T < 1} := by
  have hPD : ∀ v : Tensor0SModel s ℝ E,
      v ≠ 0 → 0 < innerModelCLM (I := I) (M := M) g s b v v := by
    intro v hv
    change 0 < covariantTensorInnerPointwise (I := I) (M := M) s g b v v
    have hQpos := (tensorInnerPointwise_0s_eq_zero_iff
      (I := I) (M := M) g b s v).not.mpr hv
    have hnn := tensorInnerPointwise_0s_nonneg (I := I) (M := M) g b s v
    exact lt_of_le_of_ne hnn (Ne.symm hQpos)
  exact Tensor0SRiemannian.posDef_bilin_unit_ball_isBounded
    (innerModelCLM (I := I) (M := M) g s b) hPD

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor.Tensor0SRiemannianBundle.innerModel_diagonal_sublevel_isBounded
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor.Tensor0SRiemannianBundle.innerModel_diagonal_sublevel_isBounded target :: scope.openDecls } }

private lemma innerModel_diagonal_sublevel_isVonNBounded
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M) :
    _root_.Bornology.IsVonNBounded ℝ
      {T : Tensor0SModel s ℝ E |
        innerModelCLM (I := I) (M := M) g s b T T < 1} :=
  NormedSpace.isVonNBounded_of_isBounded ℝ
    (innerModel_diagonal_sublevel_isBounded (I := I) (M := M) g s b)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor.Tensor0SRiemannianBundle.innerModel_diagonal_sublevel_isVonNBounded
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor.Tensor0SRiemannianBundle.innerModel_diagonal_sublevel_isVonNBounded target :: scope.openDecls } }

theorem tensor0SRiemannianInner_isVonNBounded
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M) :
    _root_.Bornology.IsVonNBounded ℝ
      {v : Tensor0SSpace s I b |
        tensor0SRiemannianInnerCLM (I := I) (M := M) g s b v v < 1} := by
  set e : Tensor0SSpace s I b ≃L[ℝ] Tensor0SModel s ℝ E :=
    Tensor0SBundle.tensor0SSpaceContinuousLinearEquiv
      (𝕜 := ℝ) (E := E) (I := I) (M := M) s b with he_def
  have hModel := innerModel_diagonal_sublevel_isVonNBounded
    (I := I) (M := M) g s b
  have hImage :=
    hModel.image (e.symm.toContinuousLinearMap)
  have hSetEq :
      e.symm.toContinuousLinearMap ''
        {T : Tensor0SModel s ℝ E |
          innerModelCLM (I := I) (M := M) g s b T T < 1} =
      {v : Tensor0SSpace s I b |
          tensor0SRiemannianInnerCLM (I := I) (M := M) g s b v v < 1} := by
    ext v
    refine ⟨?_, ?_⟩
    · rintro ⟨T, hT, rfl⟩
      rw [Set.mem_ofPred_eq] at hT
      rw [Set.mem_ofPred_eq, tensor0SRiemannianInner_diagonal_clm_apply]
      have hRound : (e (e.symm T) : _) = T := e.apply_symm_apply T
      have hToModel :
          Tensor0SBundle.Tensor0SSpace.toModel
            (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b)
            ((e.symm.toContinuousLinearMap :
              Tensor0SModel s ℝ E →L[ℝ] Tensor0SSpace s I b) T) = T := hRound
      rw [hToModel]
      change covariantTensorInnerPointwise (I := I) (M := M) s g b T T < 1
      exact hT
    · intro hv
      refine ⟨e v, ?_, ?_⟩
      · rw [Set.mem_ofPred_eq]
        rw [Set.mem_ofPred_eq, tensor0SRiemannianInner_diagonal_clm_apply] at hv
        change covariantTensorInnerPointwise (I := I) (M := M) s g b _ _ < 1
        exact hv
      · exact e.symm_apply_apply v
  rw [← hSetEq]
  exact hImage

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Tensor0SRiemannianBundle.tensor0SRiemannianInner_isVonNBounded then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Tensor0SRiemannianBundle.tensor0SRiemannianInner_isVonNBounded"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Tensor0SRiemannianBundle.tensor0SRiemannianInner_isVonNBounded ``Submission.DifferentialGeometry.Tensor.Tensor0SRiemannianBundle.tensor0SRiemannianInner_isVonNBounded

attribute [-instance] Bundle.continuousMultilinearMap.instNormedAddCommGroup
  Bundle.continuousMultilinearMap.instNormedSpace in
noncomputable def tensor0SRiemannianMetric
    (g : SmoothRiemannianMetric I M) (s : ℕ) :
    Bundle.RiemannianMetric (E := fun b : M => Tensor0SSpace s I b) where
  inner := fun b => tensor0SRiemannianInnerCLM (I := I) (M := M) g s b
  symm := fun b T S =>
    tensor0SRiemannianInner_symm (I := I) (M := M) g s b T S
  pos := fun b T hT =>
    tensor0SRiemannianInner_pos (I := I) (M := M) g s b T hT
  continuousAt := fun b =>
    tensor0SRiemannianInner_diagonal_continuousAt_zero
      (I := I) (M := M) g s b
  isVonNBounded := fun b =>
    tensor0SRiemannianInner_isVonNBounded (I := I) (M := M) g s b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Tensor0SRiemannianBundle.tensor0SRiemannianMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Tensor0SRiemannianBundle.tensor0SRiemannianMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Tensor0SRiemannianBundle.tensor0SRiemannianMetric ``Submission.DifferentialGeometry.Tensor.Tensor0SRiemannianBundle.tensor0SRiemannianMetric

end Tensor0SRiemannianBundle
end Tensor
end DifferentialGeometry

namespace DifferentialGeometry
namespace Tensor0SBundle

open _root_.Submission.DifferentialGeometry.Tensor.Tensor0SRiemannianBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

@[reducible]
noncomputable def tensor0SRiemannianBundle
    (g : SmoothRiemannianMetric I M) (s : ℕ) :
    Bundle.RiemannianBundle (fun b : M => Tensor0SSpace s I b) :=
  ⟨tensor0SRiemannianMetric (I := I) (M := M) g s⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.tensor0SRiemannianBundle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.tensor0SRiemannianBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.tensor0SRiemannianBundle ``Submission.DifferentialGeometry.Tensor0SBundle.tensor0SRiemannianBundle

end Tensor0SBundle
end DifferentialGeometry
