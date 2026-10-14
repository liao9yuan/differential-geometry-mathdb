import Submission.DifferentialGeometry.Geometry.Neck.PointwiseChart
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.ConformalChart
import Submission.DifferentialGeometry.Geometry.Metric.Gluing
import Submission.DifferentialGeometry.Geometry.Metric.Conformal.Basic
import Submission.DifferentialGeometry.Geometry.Metric.Construction.ConvexCombination
import Submission.DifferentialGeometry.Geometry.Metric.Pullback.Cross
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Submission.DifferentialGeometry.Geometry.Metric.Conformal.OfContDiff
import Submission.DifferentialGeometry.Geometry.Metric.RoundCylinder

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Bundle _root_.Submission.Bundle _root_.TopologicalSpace _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Geometry
open _root_.Submission.DifferentialGeometry.Geometry.Metric
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.E3 target :: scope.openDecls } }
private abbrev S2 := Metric.sphere (0 : E3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.S2 target :: scope.openDecls } }
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.IC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.IC target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }

def insertionCylinder (A B : ℝ) : _root_.TopologicalSpace.Opens (S2 × ℝ) :=
  ⟨{q | q.2 ∈ _root_.Set.Ioo (-2 * A) B}, isOpen_Ioo.preimage continuous_snd⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionCylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionCylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionCylinder ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionCylinder

def insertionAnnulus (A B : ℝ) : _root_.TopologicalSpace.Opens E3 :=
  ⟨{x | conformalRadius (-2 * A) < ‖x‖ ∧ ‖x‖ < conformalRadius B},
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionAnnulus then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionAnnulus"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionAnnulus ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionAnnulus

def insertionInner (A : ℝ) : _root_.TopologicalSpace.Opens E3 :=
  ⟨{x | ‖x‖ < conformalRadius (-7 * A / 4)}, isOpen_lt continuous_norm continuous_const⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionInner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionInner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionInner ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionInner

def insertionBall (B : ℝ) : _root_.TopologicalSpace.Opens E3 :=
  ⟨{x | ‖x‖ < transitionEnd + B}, isOpen_lt continuous_norm continuous_const⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionBall ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionBall

private theorem insertionCylinder_le_original {A B : ℝ} (hAB : 2 * A < B) :
    insertionCylinder A B ≤ DifferentialGeometry.Geometry.Neck.openCylinder B := by
  intro q hq
  change -2 * A < q.2 ∧ q.2 < B at hq
  change -B < q.2 ∧ q.2 < B
  exact ⟨by linarith [hq.1], hq.2⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionCylinder_le_original
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionCylinder_le_original target :: scope.openDecls } }

private theorem insertionAnnulus_le_punctured (A B : ℝ) :
    insertionAnnulus A B ≤ puncturedSpace := by
  intro x hx
  apply norm_pos_iff.mp
  exact (conformalRadius_pos (-2 * A)).trans hx.1

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionAnnulus_le_punctured
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionAnnulus_le_punctured target :: scope.openDecls } }

private theorem insertionChart_forward_mem (A B : ℝ) (q : insertionCylinder A B) :
    conformalMap q.val ∈ insertionAnnulus A B := by
  change conformalRadius (-2 * A) < ‖conformalMap q.val‖ ∧
    ‖conformalMap q.val‖ < conformalRadius B
  rw [conformalMap_norm]
  exact ⟨strictMono_conformalRadius q.property.1, strictMono_conformalRadius q.property.2⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionChart_forward_mem
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionChart_forward_mem target :: scope.openDecls } }

private theorem insertionChart_inverse_mem (A B : ℝ) (x : insertionAnnulus A B) :
    conformalChart.symm (Opens.inclusion (insertionAnnulus_le_punctured A B) x) ∈
      insertionCylinder A B := by
  have hn := conformalChart_norm
    (conformalChart.symm (Opens.inclusion (insertionAnnulus_le_punctured A B) x))
  rw [conformalChart.apply_symm_apply] at hn
  change -2 * A < (conformalChart.symm _).2 ∧ (conformalChart.symm _).2 < B
  constructor
  · apply strictMono_conformalRadius.lt_iff_lt.mp
    rw [← hn]
    exact x.property.1
  · apply strictMono_conformalRadius.lt_iff_lt.mp
    rw [← hn]
    exact x.property.2

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionChart_inverse_mem
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionChart_inverse_mem target :: scope.openDecls } }

def insertionChart (A B : ℝ) :
    insertionCylinder A B ≃ₘ⟮IC, 𝓡 3⟯ insertionAnnulus A B where
  toFun q := ⟨conformalMap q.val, insertionChart_forward_mem A B q⟩
  invFun x := ⟨conformalChart.symm (Opens.inclusion (insertionAnnulus_le_punctured A B) x),
    insertionChart_inverse_mem A B x⟩
  left_inv q := by
    apply Subtype.ext
    exact conformalChart.symm_apply_apply q.val
  right_inv x := by
    apply Subtype.ext
    exact congrArg (fun y : puncturedSpace => (y : E3))
      (conformalChart.apply_symm_apply (Opens.inclusion (insertionAnnulus_le_punctured A B) x))
  contMDiff_toFun _ := codRestr_contMDiffAt
    (insertionChart_forward_mem A B)
    (conformalMap_smooth.comp (contMDiff_subtype_val (U := insertionCylinder A B))).contMDiffAt
  contMDiff_invFun _ := codRestr_contMDiffAt
    (insertionChart_inverse_mem A B)
    (conformalChart.symm.contMDiff.comp
      (contMDiff_inclusion (insertionAnnulus_le_punctured A B))).contMDiffAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionChart ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionChart

theorem insertionChart_apply (A B : ℝ) (q : insertionCylinder A B) :
    (insertionChart A B q : E3) = conformalMap q.val := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionChart_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionChart_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionChart_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionChart_apply

theorem image_conformalMap_insertionCylinder (A B : ℝ) :
    conformalMap '' (insertionCylinder A B : Set (S2 × ℝ)) = (insertionAnnulus A B : Set E3) := by
  ext x
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact insertionChart_forward_mem A B ⟨q, hq⟩
  · intro hx
    obtain ⟨q, hq⟩ := (insertionChart A B).surjective ⟨x, hx⟩
    exact ⟨q.val, q.property, congrArg Subtype.val hq⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.image_conformalMap_insertionCylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.image_conformalMap_insertionCylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.image_conformalMap_insertionCylinder ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.image_conformalMap_insertionCylinder

theorem insertionChart_mfderiv (A B : ℝ) (q : insertionCylinder A B)
    (v : TangentSpace IC q) :
    mfderiv IC (𝓡 3) (insertionChart A B) q v =
      mfderiv IC (𝓡 3) conformalMap q.val v := by
  have hleft := mfderiv_comp q
    ((contMDiff_subtype_val (I := 𝓡 3) (U := insertionAnnulus A B)).mdifferentiableAt
      (by decide : (∞ : ℕ∞ω) ≠ 0))
    ((insertionChart A B).contMDiff.mdifferentiableAt (by decide))
  have hright := mfderiv_comp q
    (conformalMap_smooth.mdifferentiableAt (by decide))
    ((contMDiff_subtype_val (I := IC) (U := insertionCylinder A B)).mdifferentiableAt
      (by decide : (∞ : ℕ∞ω) ≠ 0))
  have h := hleft.symm.trans hright
  rw [mfderiv_subtype_val, mfderiv_subtype_val] at h
  exact congrArg (fun D => D v) h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionChart_mfderiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionChart_mfderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionChart_mfderiv ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionChart_mfderiv

theorem insertionInner_sup_annulus {A B : ℝ} (hA : 0 < A) (hAB : 2 * A < B) :
    insertionInner A ⊔ insertionAnnulus A B = insertionBall B := by
  have hB : 0 < B := by linarith
  have hlow : conformalRadius (-2 * A) < conformalRadius (-7 * A / 4) :=
    strictMono_conformalRadius (by linarith)
  have hhigh : conformalRadius (-7 * A / 4) < conformalRadius B :=
    strictMono_conformalRadius (by linarith)
  ext x
  change (‖x‖ < conformalRadius (-7 * A / 4) ∨
    conformalRadius (-2 * A) < ‖x‖ ∧ ‖x‖ < conformalRadius B) ↔
      ‖x‖ < transitionEnd + B
  rw [← conformalRadius_cylindrical hB.le]
  constructor
  · rintro (hx | hx)
    · exact hx.trans hhigh
    · exact hx.2
  · intro hx
    by_cases hi : ‖x‖ < conformalRadius (-7 * A / 4)
    · exact Or.inl hi
    · exact Or.inr ⟨hlow.trans_le (not_lt.mp hi), hx⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionInner_sup_annulus then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionInner_sup_annulus"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionInner_sup_annulus ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionInner_sup_annulus

def insertionCutoff (A z : ℝ) : ℝ := Real.smoothTransition (2 * (z + 7 * A / 4) / A)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionCutoff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionCutoff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionCutoff ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionCutoff

private theorem contDiff_insertionCutoff (A : ℝ) : ContDiff ℝ ∞ (insertionCutoff A) := by
  unfold insertionCutoff
  fun_prop

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.contDiff_insertionCutoff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.contDiff_insertionCutoff target :: scope.openDecls } }

private theorem insertionCutoff_zero {A z : ℝ} (hA : 0 < A) (hz : z ≤ -7 * A / 4) :
    insertionCutoff A z = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) hA.le

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionCutoff_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionCutoff_zero target :: scope.openDecls } }

private theorem insertionCutoff_one {A z : ℝ} (hA : 0 < A) (hz : -5 * A / 4 ≤ z) :
    insertionCutoff A z = 1 := by
  apply Real.smoothTransition.one_of_one_le
  apply (le_div_iff₀ hA).mpr
  linarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionCutoff_one
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionCutoff_one target :: scope.openDecls } }

private theorem insertionCutoff_mem (A z : ℝ) : insertionCutoff A z ∈ _root_.Set.Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionCutoff_mem
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionCutoff_mem target :: scope.openDecls } }

private theorem smooth_cutoff_collar (A B : ℝ) :
    ContMDiff IC 𝓘(ℝ) ∞ (fun q : insertionCylinder A B => insertionCutoff A q.val.2) :=
  (contDiff_insertionCutoff A).contMDiff.comp
    (contMDiff_snd.comp (contMDiff_subtype_val (U := insertionCylinder A B)))

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.smooth_cutoff_collar
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.smooth_cutoff_collar target :: scope.openDecls } }

private theorem smooth_factor_collar (A B : ℝ) :
    ContMDiff IC 𝓘(ℝ) ∞ (fun q : insertionCylinder A B => conformalFactor q.val.2) :=
  contDiff_conformalFactor.contMDiff.comp
    (contMDiff_snd.comp (contMDiff_subtype_val (U := insertionCylinder A B)))

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.smooth_factor_collar
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.smooth_factor_collar target :: scope.openDecls } }

private def insertionCollarMetric {A B η : ℝ} (hAB : 2 * A < B) (hη : 0 < η)
    (h : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B)) :
    SmoothRiemannianMetric IC (insertionCylinder A B) :=
  conformalMetricOfContDiff
    ((h.restrictOpenOfSubset (insertionCylinder_le_original hAB)).convexComb
      (scaleMetric η hη ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen (insertionCylinder A B)))
      (fun q => insertionCutoff A q.val.2) (smooth_cutoff_collar A B)
      (fun q => insertionCutoff_mem A q.val.2))
    (fun q => conformalFactor q.val.2) (smooth_factor_collar A B)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionCollarMetric
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionCollarMetric target :: scope.openDecls } }

private theorem insertionCollarMetric_inner {A B η : ℝ} (hAB : 2 * A < B) (hη : 0 < η)
    (h : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B))
    (q : insertionCylinder A B) (v w : TangentSpace IC q) :
    (insertionCollarMetric hAB hη h).inner q v w =
      Real.exp (2 * conformalFactor q.val.2) *
        (insertionCutoff A q.val.2 *
          h.inner (Opens.inclusion (insertionCylinder_le_original hAB) q) v w +
        (1 - insertionCutoff A q.val.2) * η *
          (roundCylinderMetric (E := E3) (n := 2)).inner q.val v w) := by
  unfold insertionCollarMetric
  rw [conformalMetricOfContDiff_inner, convexComb_inner, scaleMetric_inner,
    SmoothRiemannianMetric.restrictSubset_inner, SmoothRiemannianMetric.restrictOpen_inner]
  simp only [smul_eq_mul]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionCollarMetric_inner
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionCollarMetric_inner target :: scope.openDecls } }

private def insertionAnnulusMetric {A B η : ℝ} (hAB : 2 * A < B) (hη : 0 < η)
    (h : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B)) :
    SmoothRiemannianMetric (𝓡 3) (insertionAnnulus A B) :=
  Diffeomorph.pullbackMetricCross (insertionCollarMetric hAB hη h) (insertionChart A B).symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionAnnulusMetric
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionAnnulusMetric target :: scope.openDecls } }

private theorem insertionChart_inverse_deriv (A B : ℝ) (q : insertionCylinder A B)
    (v : TangentSpace IC q) :
    mfderiv (𝓡 3) IC (insertionChart A B).symm (insertionChart A B q)
      (mfderiv IC (𝓡 3) (insertionChart A B) q v) = v := by
  have hchain := mfderiv_comp q
    ((insertionChart A B).symm.contMDiff.mdifferentiableAt (by decide : (∞ : ℕ∞ω) ≠ 0))
    ((insertionChart A B).contMDiff.mdifferentiableAt (by decide : (∞ : ℕ∞ω) ≠ 0))
  have hid : (insertionChart A B).symm ∘ (insertionChart A B) = id :=
    funext (insertionChart A B).symm_apply_apply
  rw [hid, mfderiv_id] at hchain
  exact (congrArg (fun D => D v) hchain).symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionChart_inverse_deriv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionChart_inverse_deriv target :: scope.openDecls } }

private theorem insertionChart_deriv_surjective (A B : ℝ) (q : insertionCylinder A B) :
    Function.Surjective (mfderiv IC (𝓡 3) (insertionChart A B) q) := by
  exact ((insertionChart A B).mfderivToContinuousLinearEquiv (by decide) q).surjective

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionChart_deriv_surjective
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionChart_deriv_surjective target :: scope.openDecls } }

private theorem insertionAnnulusMetric_chart_inner {A B η : ℝ}
    (hAB : 2 * A < B) (hη : 0 < η)
    (h : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B))
    (q : insertionCylinder A B) (v w : TangentSpace IC q) :
    (insertionAnnulusMetric hAB hη h).inner (insertionChart A B q)
      (mfderiv IC (𝓡 3) (insertionChart A B) q v)
      (mfderiv IC (𝓡 3) (insertionChart A B) q w) =
      (insertionCollarMetric hAB hη h).inner q v w := by
  rw [insertionAnnulusMetric, Diffeomorph.pullbackMetricCross_inner,
    insertionChart_inverse_deriv, insertionChart_inverse_deriv]
  rw [(insertionChart A B).symm_apply_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionAnnulusMetric_chart_inner
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionAnnulusMetric_chart_inner target :: scope.openDecls } }

private theorem insertionAnnulusMetric_inner_of_inner {A B η : ℝ}
    (hA : 0 < A) (hAB : 2 * A < B) (hη : 0 < η)
    (h : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B))
    (x : insertionAnnulus A B) (hx : ‖(x : E3)‖ < conformalRadius (-7 * A / 4))
    (v w : TangentSpace (𝓡 3) x) :
    (insertionAnnulusMetric hAB hη h).inner x v w = η * metric.inner (x : E3) v w := by
  obtain ⟨q, rfl⟩ := (insertionChart A B).surjective x
  obtain ⟨a, rfl⟩ := insertionChart_deriv_surjective A B q v
  obtain ⟨b, rfl⟩ := insertionChart_deriv_surjective A B q w
  change ‖conformalMap q.val‖ < conformalRadius (-7 * A / 4) at hx
  rw [conformalMap_norm] at hx
  have hz : q.val.2 < -7 * A / 4 := strictMono_conformalRadius.lt_iff_lt.mp hx
  have hcap : metric.inner (insertionChart A B q : E3)
      (mfderiv IC (𝓡 3) (insertionChart A B) q a)
      (mfderiv IC (𝓡 3) (insertionChart A B) q b) =
      Real.exp (2 * conformalFactor q.val.2) *
        (roundCylinderMetric (E := E3) (n := 2)).inner q.val a b := by
    have hm := congrArg₂ (fun v w : E3 => metric.inner (conformalMap q.val) v w)
      (conformalChart_mfderiv_eq_ambient q.val a) (conformalChart_mfderiv_eq_ambient q.val b)
    have hp := hm.symm.trans (conformalChart_metric_inner_exp q.val a b)
    simpa only [insertionChart_apply, insertionChart_mfderiv] using! hp
  calc
    _ = (insertionCollarMetric hAB hη h).inner q a b :=
      insertionAnnulusMetric_chart_inner hAB hη h q a b
    _ = η * (Real.exp (2 * conformalFactor q.val.2) *
        (roundCylinderMetric (E := E3) (n := 2)).inner q.val a b) := by
      rw [insertionCollarMetric_inner, insertionCutoff_zero hA hz.le]
      ring
    _ = _ := congrArg (fun t : ℝ => η * t) hcap.symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionAnnulusMetric_inner_of_inner
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionAnnulusMetric_inner_of_inner target :: scope.openDecls } }

private def insertionInnerMetric (A : ℝ) {η : ℝ} (hη : 0 < η) :
    SmoothRiemannianMetric (𝓡 3) (insertionInner A) :=
  (scaleMetric η hη metric).restrictOpen (insertionInner A)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionInnerMetric
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionInnerMetric target :: scope.openDecls } }

private theorem insertionMetric_overlap {A B η : ℝ}
    (hA : 0 < A) (hAB : 2 * A < B) (hη : 0 < η)
    (h : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B))
    (x : E3) (hi : x ∈ insertionInner A) (ha : x ∈ insertionAnnulus A B)
    (v w : TangentSpace (𝓡 3) x) :
    (insertionInnerMetric A hη).inner ⟨x, hi⟩ v w =
      (insertionAnnulusMetric hAB hη h).inner ⟨x, ha⟩ v w := by
  exact (insertionAnnulusMetric_inner_of_inner hA hAB hη h ⟨x, ha⟩ hi v w).symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionMetric_overlap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionMetric_overlap target :: scope.openDecls } }

private def insertionUnionMetric {A B η : ℝ}
    (hA : 0 < A) (hAB : 2 * A < B) (hη : 0 < η)
    (h : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B)) :
    SmoothRiemannianMetric (𝓡 3) ↥(insertionInner A ⊔ insertionAnnulus A B) :=
  glueMetric (insertionInner A) (insertionAnnulus A B)
    (insertionInnerMetric A hη) (insertionAnnulusMetric hAB hη h)
    (insertionMetric_overlap hA hAB hη h)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionUnionMetric
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionUnionMetric target :: scope.openDecls } }

def insertedMetric {A B η : ℝ}
    (hA : 0 < A) (hAB : 2 * A < B) (hη : 0 < η)
    (h : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B)) :
    SmoothRiemannianMetric (𝓡 3) (insertionBall B) :=
  (insertionUnionMetric hA hAB hη h).restrictOpenOfSubset
    (le_of_eq (insertionInner_sup_annulus hA hAB).symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertedMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.insertedMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertedMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.insertedMetric

def insertionMap {A B : ℝ} (hA : 0 < A) (hAB : 2 * A < B) :
    insertionCylinder A B → insertionBall B :=
  Opens.inclusion (le_trans le_sup_right (le_of_eq (insertionInner_sup_annulus hA hAB))) ∘
    insertionChart A B

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionMap ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionMap

theorem insertionMap_apply {A B : ℝ} (hA : 0 < A) (hAB : 2 * A < B)
    (q : insertionCylinder A B) :
    (insertionMap hA hAB q : E3) = conformalMap q.val := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionMap_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionMap_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionMap_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionMap_apply

theorem contMDiff_insertionMap {A B : ℝ} (hA : 0 < A) (hAB : 2 * A < B) :
    ContMDiff IC (𝓡 3) ∞ (insertionMap hA hAB) :=
  (contMDiff_inclusion
    (le_trans le_sup_right (le_of_eq (insertionInner_sup_annulus hA hAB)))).comp
      (insertionChart A B).contMDiff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.contMDiff_insertionMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.contMDiff_insertionMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.contMDiff_insertionMap ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.contMDiff_insertionMap

theorem injective_insertionMap {A B : ℝ} (hA : 0 < A) (hAB : 2 * A < B) :
    Function.Injective (insertionMap hA hAB) := by
  intro x y hxy
  apply (insertionChart A B).injective
  apply Subtype.ext
  exact congrArg (fun z : insertionBall B => z.val) hxy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.injective_insertionMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.injective_insertionMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.injective_insertionMap ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.injective_insertionMap

theorem range_insertionMap {A B : ℝ} (hA : 0 < A) (hAB : 2 * A < B) :
    _root_.Set.range (insertionMap hA hAB) =
      {x : insertionBall B | x.val ∈ insertionAnnulus A B} := by
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    exact (insertionChart A B q).property
  · intro hx
    refine ⟨(insertionChart A B).symm ⟨x.val, hx⟩, ?_⟩
    apply Subtype.ext
    change ((insertionChart A B) ((insertionChart A B).symm ⟨x.val, hx⟩)).val = x.val
    rw [(insertionChart A B).apply_symm_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.range_insertionMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.range_insertionMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.range_insertionMap ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.range_insertionMap

private theorem insertionMap_mfderiv_chart {A B : ℝ} (hA : 0 < A) (hAB : 2 * A < B)
    (q : insertionCylinder A B) (v : TangentSpace IC q) :
    mfderiv IC (𝓡 3) (insertionMap hA hAB) q v =
      mfderiv IC (𝓡 3) (insertionChart A B) q v := by
  rw [insertionMap, mfderiv_comp q
    ((contMDiff_inclusion _).mdifferentiableAt (by decide : (∞ : ℕ∞ω) ≠ 0))
    ((insertionChart A B).contMDiff.mdifferentiableAt (by decide)), mfderiv_opens_incl]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionMap_mfderiv_chart
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionMap_mfderiv_chart target :: scope.openDecls } }

theorem insertionMap_mfderiv {A B : ℝ} (hA : 0 < A) (hAB : 2 * A < B)
    (q : insertionCylinder A B) (v : TangentSpace IC q) :
    mfderiv IC (𝓡 3) (insertionMap hA hAB) q v =
      mfderiv IC (𝓡 3) conformalMap q.val v :=
  (insertionMap_mfderiv_chart hA hAB q v).trans (insertionChart_mfderiv A B q v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionMap_mfderiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionMap_mfderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionMap_mfderiv ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionMap_mfderiv

theorem insertionMap_mfderiv_injective {A B : ℝ} (hA : 0 < A) (hAB : 2 * A < B)
    (q : insertionCylinder A B) :
    Function.Injective (mfderiv IC (𝓡 3) (insertionMap hA hAB) q) := by
  intro v w hvw
  apply ((insertionChart A B).mfderivToContinuousLinearEquiv (by decide) q).injective
  exact (insertionMap_mfderiv_chart hA hAB q v).symm.trans
    (hvw.trans (insertionMap_mfderiv_chart hA hAB q w))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionMap_mfderiv_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionMap_mfderiv_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionMap_mfderiv_injective ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionMap_mfderiv_injective

theorem insertedMetric_inner_of_inner {A B η : ℝ}
    (hA : 0 < A) (hAB : 2 * A < B) (hη : 0 < η)
    (h : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B))
    (x : insertionBall B) (hx : ‖(x : E3)‖ < conformalRadius (-7 * A / 4))
    (v w : TangentSpace (𝓡 3) x) :
    (insertedMetric hA hAB hη h).inner x v w = η * metric.inner (x : E3) v w := by
  change (insertionUnionMetric hA hAB hη h).inner
    (Opens.inclusion (le_of_eq (insertionInner_sup_annulus hA hAB).symm) x) v w = _
  have heq : Opens.inclusion (le_of_eq (insertionInner_sup_annulus hA hAB).symm) x =
      Opens.inclusion le_sup_left (⟨x.val, hx⟩ : insertionInner A) := Subtype.ext rfl
  rw [heq]
  exact glueMetric_inner_left (insertionInner A) (insertionAnnulus A B)
    (insertionInnerMetric A hη) (insertionAnnulusMetric hAB hη h)
    (insertionMetric_overlap hA hAB hη h) ⟨x.val, hx⟩ v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertedMetric_inner_of_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.insertedMetric_inner_of_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertedMetric_inner_of_inner ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.insertedMetric_inner_of_inner

theorem insertedMetric_interpolation {A B η : ℝ}
    (hA : 0 < A) (hAB : 2 * A < B) (hη : 0 < η)
    (h : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B))
    (q : insertionCylinder A B) (v w : TangentSpace IC q) :
    (insertedMetric hA hAB hη h).inner (insertionMap hA hAB q)
      (mfderiv IC (𝓡 3) (insertionMap hA hAB) q v)
      (mfderiv IC (𝓡 3) (insertionMap hA hAB) q w) =
      Real.exp (2 * conformalFactor q.val.2) *
        (insertionCutoff A q.val.2 *
          h.inner (Opens.inclusion (insertionCylinder_le_original hAB) q) v w +
        (1 - insertionCutoff A q.val.2) * η *
          (roundCylinderMetric (E := E3) (n := 2)).inner q.val v w) := by
  rw [insertionMap_mfderiv_chart, insertionMap_mfderiv_chart]
  change (glueMetric (insertionInner A) (insertionAnnulus A B)
    (insertionInnerMetric A hη) (insertionAnnulusMetric hAB hη h)
    (insertionMetric_overlap hA hAB hη h)).inner
      (Opens.inclusion le_sup_right (insertionChart A B q))
      (mfderiv IC (𝓡 3) (insertionChart A B) q v)
      (mfderiv IC (𝓡 3) (insertionChart A B) q w) = _
  rw [glueMetric_inner_right, insertionAnnulusMetric_chart_inner]
  exact insertionCollarMetric_inner hAB hη h q v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertedMetric_interpolation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.insertedMetric_interpolation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertedMetric_interpolation ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.insertedMetric_interpolation

theorem insertedMetric_retained {A B η : ℝ}
    (hA : 0 < A) (hAB : 2 * A < B) (hη : 0 < η)
    (h : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B))
    (q : insertionCylinder A B) (hq : 0 ≤ q.val.2) (v w : TangentSpace IC q) :
    (insertedMetric hA hAB hη h).inner (insertionMap hA hAB q)
      (mfderiv IC (𝓡 3) (insertionMap hA hAB) q v)
      (mfderiv IC (𝓡 3) (insertionMap hA hAB) q w) =
      h.inner (Opens.inclusion (insertionCylinder_le_original hAB) q) v w := by
  rw [insertedMetric_interpolation, insertionCutoff_one hA (by linarith),
    conformalFactor_eq_zero_of_nonneg hq]
  ring_nf
  simp only [Real.exp_zero, one_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertedMetric_retained then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.insertedMetric_retained"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertedMetric_retained ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.insertedMetric_retained

theorem zero_mem_insertionBall {B : ℝ} (hB : 0 ≤ B) : (0 : E3) ∈ insertionBall B := by
  change ‖(0 : E3)‖ < transitionEnd + B
  rw [norm_zero]
  linarith [transitionEnd_pos]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.zero_mem_insertionBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.zero_mem_insertionBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.zero_mem_insertionBall ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.zero_mem_insertionBall

theorem insertedMetric_smooth_at_tip {A B η : ℝ}
    (hA : 0 < A) (hAB : 2 * A < B) (hη : 0 < η)
    (h : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B)) :
    ContMDiffAt (𝓡 3) ((𝓡 3).prod 𝓘(ℝ, E3 →L[ℝ] E3 →L[ℝ] ℝ)) ∞
      (fun x : insertionBall B => TotalSpace.mk' (E3 →L[ℝ] E3 →L[ℝ] ℝ)
        (E := fun y : insertionBall B => TangentSpace (𝓡 3) y →L[ℝ]
          TangentSpace (𝓡 3) y →L[ℝ] ℝ) x ((insertedMetric hA hAB hη h).inner x))
      ⟨0, zero_mem_insertionBall (by linarith)⟩ :=
  (insertedMetric hA hAB hη h).contMDiff.contMDiffAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertedMetric_smooth_at_tip then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.insertedMetric_smooth_at_tip"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertedMetric_smooth_at_tip ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.insertedMetric_smooth_at_tip

end DifferentialGeometry.PDE.RicciFlow.StandardCap
