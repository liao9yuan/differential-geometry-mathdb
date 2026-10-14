import Submission.DifferentialGeometry.Geometry.Metric.Basic
import Submission.DifferentialGeometry.Geometry.Metric.Construction.Existence
import Submission.DifferentialGeometry.Bundle.ContinuousLinearMapSection.Basic
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Manifold _root_.Set _root_.Metric _root_.ContinuousLinearMap _root_.Bundle.ContinuousLinearMap _root_.Module
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.RealInnerProductSpace

namespace DifferentialGeometry
namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {n : ℕ} [Fact (finrank ℝ E = n + 1)]

noncomputable def dIncl (x : _root_.Metric.sphere (0 : E) 1) :
    TangentSpace (𝓡 n) x →L[ℝ] E :=
  mvfderiv (𝓡 n) ((↑) : _root_.Metric.sphere (0 : E) 1 → E) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.dIncl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.dIncl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.dIncl ``Submission.DifferentialGeometry.Geometry.dIncl

noncomputable def roundInner (x : _root_.Metric.sphere (0 : E) 1) :
    TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ :=
  (ContinuousLinearMap.precomp ℝ (dIncl (n := n) x)).comp
    ((innerSL ℝ).comp (dIncl (n := n) x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.roundInner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.roundInner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.roundInner ``Submission.DifferentialGeometry.Geometry.roundInner

@[simp] theorem roundInner_apply (x : _root_.Metric.sphere (0 : E) 1)
    (v w : TangentSpace (𝓡 n) x) :
    roundInner (n := n) x v w = ⟪dIncl (n := n) x v, dIncl (n := n) x w⟫ := by
  simp only [roundInner, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.precomp_apply, innerSL_apply_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.roundInner_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.roundInner_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.roundInner_apply ``Submission.DifferentialGeometry.Geometry.roundInner_apply

theorem roundInner_symm (x : _root_.Metric.sphere (0 : E) 1) (v w : TangentSpace (𝓡 n) x) :
    roundInner (n := n) x v w = roundInner (n := n) x w v := by
  rw [roundInner_apply, roundInner_apply, real_inner_comm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.roundInner_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.roundInner_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.roundInner_symm ``Submission.DifferentialGeometry.Geometry.roundInner_symm

theorem dIncl_ne_zero {x : _root_.Metric.sphere (0 : E) 1} {v : TangentSpace (𝓡 n) x}
    (hv : v ≠ 0) : dIncl (n := n) x v ≠ 0 := by
  intro h
  refine hv (injective_mvfderiv_subtypeVal_sphere x ?_)
  rw [map_zero]
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.dIncl_ne_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.dIncl_ne_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.dIncl_ne_zero ``Submission.DifferentialGeometry.Geometry.dIncl_ne_zero

theorem roundInner_pos (x : _root_.Metric.sphere (0 : E) 1) (v : TangentSpace (𝓡 n) x)
    (hv : v ≠ 0) : 0 < roundInner (n := n) x v v := by
  rw [roundInner_apply, real_inner_self_eq_norm_mul_norm]
  exact mul_pos (norm_pos_iff.mpr (dIncl_ne_zero (n := n) hv))
    (norm_pos_iff.mpr (dIncl_ne_zero (n := n) hv))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.roundInner_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.roundInner_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.roundInner_pos ``Submission.DifferentialGeometry.Geometry.roundInner_pos

private theorem flatInner_comp_incl_contMDiff :
    ContMDiff (𝓡 n) (𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : _root_.Metric.sphere (0 : E) 1 => TotalSpace.mk'
        (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : E => TangentSpace 𝓘(ℝ, E) x →L[ℝ] TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ)
        (((↑) : _root_.Metric.sphere (0 : E) 1 → E) x)
        ((riemannianMetricVectorSpace E).inner (((↑) : _root_.Metric.sphere (0 : E) 1 → E) x))) :=
  ((riemannianMetricVectorSpace E).contMDiff.of_le le_top).comp contMDiff_coe_sphere

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.flatInner_comp_incl_contMDiff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.flatInner_comp_incl_contMDiff target :: scope.openDecls } }

private theorem dIncl_apply_section_contMDiff
    (Y : ∀ x : _root_.Metric.sphere (0 : E) 1, TangentSpace (𝓡 n) x)
    (hY : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun x : _root_.Metric.sphere (0 : E) 1 =>
        TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (E := TangentSpace (𝓡 n)) x (Y x))) :
    ContMDiff (𝓡 n) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun x : _root_.Metric.sphere (0 : E) 1 =>
        TotalSpace.mk' E (E := (TangentSpace 𝓘(ℝ, E) : E → Type _))
          (((↑) : _root_.Metric.sphere (0 : E) 1 → E) x)
          (mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : _root_.Metric.sphere (0 : E) 1 → E) x (Y x))) :=
  ((contMDiff_coe_sphere (n := n)).contMDiff_tangentMap (le_refl _)).comp hY

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.dIncl_apply_section_contMDiff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.dIncl_apply_section_contMDiff target :: scope.openDecls } }


noncomputable def roundMetric : SmoothRiemannianMetric (𝓡 n) (_root_.Metric.sphere (0 : E) 1) where
  inner x := roundInner (n := n) x
  symm x v w := roundInner_symm (n := n) x v w
  pos x v hv := roundInner_pos (n := n) x v hv
  isVonNBounded x :=
    posDef_isVonNBounded (E := EuclideanSpace ℝ (Fin n)) (roundInner (n := n) x)
      (fun v hv => roundInner_pos (n := n) x v hv)
  contMDiff := by
    classical
    have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
    have : CompactSpace (_root_.Metric.sphere (0 : E) 1) := Metric.sphere.compactSpace _ _
    apply contMDiff_continuousLinearMap_section_of_apply
      (V₂ := fun x : _root_.Metric.sphere (0 : E) 1 => TangentSpace (𝓡 n) x →L[ℝ] ℝ)
      (φ := fun x : _root_.Metric.sphere (0 : E) 1 => roundInner (n := n) x)
    intro Y
    apply contMDiff_continuousLinearMap_section_of_apply
      (V₂ := fun _ : _root_.Metric.sphere (0 : E) 1 => ℝ)
      (φ := fun x : _root_.Metric.sphere (0 : E) 1 => roundInner (n := n) x (Y x))
    intro W
    have hv := dIncl_apply_section_contMDiff (n := n) (fun x => Y x) Y.contMDiff
    have hw := dIncl_apply_section_contMDiff (n := n) (fun x => W x) W.contMDiff
    have hg := flatInner_comp_incl_contMDiff (E := E) (n := n)
    have h_total : ContMDiff (𝓡 n) (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) ∞
        (fun x : _root_.Metric.sphere (0 : E) 1 => TotalSpace.mk' ℝ
          (E := Bundle.Trivial E ℝ)
          (((↑) : _root_.Metric.sphere (0 : E) 1 → E) x)
          ((riemannianMetricVectorSpace E).inner (((↑) : _root_.Metric.sphere (0 : E) 1 → E) x)
            (mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : _root_.Metric.sphere (0 : E) 1 → E) x (Y x))
            (mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : _root_.Metric.sphere (0 : E) 1 → E) x (W x)))) :=
      ContMDiff.clm_bundle_apply₂
        (E₁ := fun b : E => TangentSpace 𝓘(ℝ, E) b)
        (E₂ := fun b : E => TangentSpace 𝓘(ℝ, E) b)
        (E₃ := fun _ : E => ℝ)
        (b := fun x : _root_.Metric.sphere (0 : E) 1 => ((↑) : _root_.Metric.sphere (0 : E) 1 → E) x)
        (ψ := fun x : _root_.Metric.sphere (0 : E) 1 =>
          (riemannianMetricVectorSpace E).inner (((↑) : _root_.Metric.sphere (0 : E) 1 → E) x))
        (v := fun x : _root_.Metric.sphere (0 : E) 1 =>
          mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : _root_.Metric.sphere (0 : E) 1 → E) x (Y x))
        (w := fun x : _root_.Metric.sphere (0 : E) 1 =>
          mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : _root_.Metric.sphere (0 : E) 1 → E) x (W x))
        hg hv hw
    have h_scalar : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
        (fun x : _root_.Metric.sphere (0 : E) 1 => roundInner (n := n) x (Y x) (W x)) := by
      have h_eq : (fun x : _root_.Metric.sphere (0 : E) 1 => roundInner (n := n) x (Y x) (W x))
          = fun x : _root_.Metric.sphere (0 : E) 1 =>
              (riemannianMetricVectorSpace E).inner (((↑) : _root_.Metric.sphere (0 : E) 1 → E) x)
                (mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : _root_.Metric.sphere (0 : E) 1 → E) x (Y x))
                (mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : _root_.Metric.sphere (0 : E) 1 → E) x (W x)) := by
        funext x
        rw [roundInner_apply]
        rfl
      rw [h_eq]
      intro x
      have h_at := h_total x
      rw [_root_.Bundle.contMDiffAt_totalSpace] at h_at
      exact h_at.2
    intro x
    rw [_root_.Bundle.contMDiffAt_section]
    refine (h_scalar.contMDiffAt).congr_of_eventuallyEq ?_
    filter_upwards with y
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.roundMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.roundMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.roundMetric ``Submission.DifferentialGeometry.Geometry.roundMetric

@[simp] theorem roundMetric_inner (x : _root_.Metric.sphere (0 : E) 1) (v w : TangentSpace (𝓡 n) x) :
    (roundMetric (E := E) (n := n)).inner x v w
      = ⟪dIncl (n := n) x v, dIncl (n := n) x w⟫ :=
  roundInner_apply (n := n) x v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.roundMetric_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.roundMetric_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.roundMetric_inner ``Submission.DifferentialGeometry.Geometry.roundMetric_inner

end Geometry
end DifferentialGeometry
