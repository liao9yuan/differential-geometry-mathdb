import Submission.DifferentialGeometry.Geometry.Metric.Product
import Submission.DifferentialGeometry.Geometry.Metric.Euclidean
import Submission.DifferentialGeometry.Topology.Manifold.AddCircle.ParameterDerivative
import Submission.DifferentialGeometry.Geometry.Metric.CompactExistence
import Submission.DifferentialGeometry.Geometry.Metric.Conformal.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section
open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff
open _root_.Submission.DifferentialGeometry

namespace AddCircle
open _root_.AddCircle

open _root_.AddCircle in
private def auxiliaryMetric : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)) :=
  Classical.choice (DifferentialGeometry.Geometry.nonempty_smoothRiemannianMetric_of_compact
    (I := 𝓘(ℝ, ℝ)))

run_cmd do
  let target := ``Submission.AddCircle.auxiliaryMetric
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `AddCircle.auxiliaryMetric target :: scope.openDecls } }

open _root_.AddCircle in
theorem parameterTangent_inner_pos
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (z : AddCircle (1 : ℝ)) :
    0 < g.inner z (parameterTangent z) (parameterTangent z) :=
  g.pos z _ (parameterTangent_ne_zero z)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.parameterTangent_inner_pos then
    throwError "Refusing to shadow existing declaration AddCircle.parameterTangent_inner_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.parameterTangent_inner_pos ``Submission.AddCircle.parameterTangent_inner_pos

open _root_.AddCircle in
theorem contMDiff_parameterTangent_inner
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
      (fun z => g.inner z (parameterTangent z) (parameterTangent z)) := by
  have hh := ContMDiff.clm_bundle_apply₂ (F₁ := ℝ) (F₂ := ℝ)
    g.contMDiff contMDiff_parameterTangent contMDiff_parameterTangent
  intro x
  have hx := hh x
  rw [_root_.Bundle.contMDiffAt_totalSpace] at hx
  exact hx.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.contMDiff_parameterTangent_inner then
    throwError "Refusing to shadow existing declaration AddCircle.contMDiff_parameterTangent_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.contMDiff_parameterTangent_inner ``Submission.AddCircle.contMDiff_parameterTangent_inner

open _root_.AddCircle in
noncomputable def metricCoefficient
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) :
    C^∞⟮𝓘(ℝ, ℝ), AddCircle (1 : ℝ); ℝ⟯ :=
  ⟨fun z => g.inner z (parameterTangent z) (parameterTangent z),
    contMDiff_parameterTangent_inner g⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.metricCoefficient then
    throwError "Refusing to shadow existing declaration AddCircle.metricCoefficient"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.metricCoefficient ``Submission.AddCircle.metricCoefficient

open _root_.AddCircle in
theorem metricCoefficient_apply
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (z : AddCircle (1 : ℝ)) :
    metricCoefficient g z = g.inner z (parameterTangent z) (parameterTangent z) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.metricCoefficient_apply then
    throwError "Refusing to shadow existing declaration AddCircle.metricCoefficient_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.metricCoefficient_apply ``Submission.AddCircle.metricCoefficient_apply

open _root_.AddCircle in
theorem metricCoefficient_pos
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (z : AddCircle (1 : ℝ)) :
    0 < metricCoefficient g z := by
  exact parameterTangent_inner_pos g z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.metricCoefficient_pos then
    throwError "Refusing to shadow existing declaration AddCircle.metricCoefficient_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.metricCoefficient_pos ``Submission.AddCircle.metricCoefficient_pos

open _root_.AddCircle in
theorem inner_parameterTangent_injective
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (z : AddCircle (1 : ℝ)) :
    Function.Injective (fun v : TangentSpace 𝓘(ℝ, ℝ) z =>
      g.inner z v (parameterTangent z)) := by
  intro v w h
  change g.inner z v (parameterTangent z) = g.inner z w (parameterTangent z) at h
  apply sub_eq_zero.mp
  have hz : g.inner z (v - w) (parameterTangent z) = 0 := by
    rw [map_sub, sub_apply, h, sub_self]
  obtain ⟨a, ha⟩ := exists_smul_parameterTangent z (v - w)
  rw [← ha, map_smul, smul_apply] at hz
  change a * g.inner z (parameterTangent z) (parameterTangent z) = 0 at hz
  have ha0 : a = 0 := (mul_eq_zero.mp hz).resolve_right (parameterTangent_inner_pos g z).ne'
  rw [← ha, ha0, zero_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.inner_parameterTangent_injective then
    throwError "Refusing to shadow existing declaration AddCircle.inner_parameterTangent_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.inner_parameterTangent_injective ``Submission.AddCircle.inner_parameterTangent_injective

open _root_.AddCircle in
def flatMetric : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)) where
  inner z := (auxiliaryMetric.inner z (parameterTangent z) (parameterTangent z))⁻¹ •
    auxiliaryMetric.inner z
  symm z := (scaleMetric _ (inv_pos.mpr (parameterTangent_inner_pos auxiliaryMetric z)) auxiliaryMetric).symm z
  pos z := (scaleMetric _ (inv_pos.mpr (parameterTangent_inner_pos auxiliaryMetric z)) auxiliaryMetric).pos z
  isVonNBounded z := (scaleMetric _ (inv_pos.mpr (parameterTangent_inner_pos auxiliaryMetric z)) auxiliaryMetric).isVonNBounded z
  contMDiff := by
    have hs : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
        (fun z => (auxiliaryMetric.inner z (parameterTangent z) (parameterTangent z))⁻¹) :=
      (contMDiff_parameterTangent_inner auxiliaryMetric).inv₀
        (fun z => (parameterTangent_inner_pos auxiliaryMetric z).ne')
    exact hs.smul_section auxiliaryMetric.contMDiff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.flatMetric then
    throwError "Refusing to shadow existing declaration AddCircle.flatMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.flatMetric ``Submission.AddCircle.flatMetric

open _root_.AddCircle in
theorem flatMetric_parameterTangent_unit (z : AddCircle (1 : ℝ)) :
    flatMetric.inner z (parameterTangent z) (parameterTangent z) = 1 := by
  change (auxiliaryMetric.inner z (parameterTangent z) (parameterTangent z))⁻¹ *
    auxiliaryMetric.inner z (parameterTangent z) (parameterTangent z) = 1
  exact inv_mul_cancel₀ (parameterTangent_inner_pos auxiliaryMetric z).ne'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.flatMetric_parameterTangent_unit then
    throwError "Refusing to shadow existing declaration AddCircle.flatMetric_parameterTangent_unit"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.flatMetric_parameterTangent_unit ``Submission.AddCircle.flatMetric_parameterTangent_unit






open _root_.AddCircle in
def metricOfCoefficient (a : C^∞⟮𝓘(ℝ, ℝ), AddCircle (1 : ℝ); ℝ⟯)
    (ha : ∀ z, 0 < a z) : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)) :=
  conformalMetric flatMetric ⟨fun z => Real.log (a z) / 2, by
    have hlog : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun z => Real.log (a z)) := by
      intro z
      exact (Real.contDiffAt_log.2 (ha z).ne').comp_contMDiffAt a.contMDiff.contMDiffAt
    exact hlog.div_const 2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.metricOfCoefficient then
    throwError "Refusing to shadow existing declaration AddCircle.metricOfCoefficient"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.metricOfCoefficient ``Submission.AddCircle.metricOfCoefficient

open _root_.AddCircle in
@[simp] theorem metricOfCoefficient_inner
    (a : C^∞⟮𝓘(ℝ, ℝ), AddCircle (1 : ℝ); ℝ⟯) (ha : ∀ z, 0 < a z)
    (z : AddCircle (1 : ℝ)) (v w : TangentSpace 𝓘(ℝ, ℝ) z) :
    (metricOfCoefficient a ha).inner z v w = a z * flatMetric.inner z v w := by
  change Real.exp (2 * (Real.log (a z) / 2)) * _ = _
  rw [show 2 * (Real.log (a z) / 2) = Real.log (a z) by ring, Real.exp_log (ha z)]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.metricOfCoefficient_inner then
    throwError "Refusing to shadow existing declaration AddCircle.metricOfCoefficient_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.metricOfCoefficient_inner ``Submission.AddCircle.metricOfCoefficient_inner

open _root_.AddCircle in
@[simp] theorem metricCoefficient_metricOfCoefficient
    (a : C^∞⟮𝓘(ℝ, ℝ), AddCircle (1 : ℝ); ℝ⟯) (ha : ∀ z, 0 < a z) :
    metricCoefficient (metricOfCoefficient a ha) = a := by
  ext z
  rw [metricCoefficient_apply, metricOfCoefficient_inner, flatMetric_parameterTangent_unit,
    mul_one]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.metricCoefficient_metricOfCoefficient then
    throwError "Refusing to shadow existing declaration AddCircle.metricCoefficient_metricOfCoefficient"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.metricCoefficient_metricOfCoefficient ``Submission.AddCircle.metricCoefficient_metricOfCoefficient

open _root_.AddCircle in
theorem metricCoefficient_injective : Function.Injective metricCoefficient := by
  intro g h heq
  apply SmoothRiemannianMetric.ext_inner
  intro z v w
  obtain ⟨a, rfl⟩ := exists_smul_parameterTangent z v
  obtain ⟨b, rfl⟩ := exists_smul_parameterTangent z w
  have hz := congrArg (fun f : C^∞⟮𝓘(ℝ, ℝ), AddCircle (1 : ℝ); ℝ⟯ => f z) heq
  simp only [map_smul, smul_apply, smul_eq_mul]
  rw [← metricCoefficient_apply, ← metricCoefficient_apply, hz]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.metricCoefficient_injective then
    throwError "Refusing to shadow existing declaration AddCircle.metricCoefficient_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.metricCoefficient_injective ``Submission.AddCircle.metricCoefficient_injective

open _root_.AddCircle in
@[simp] theorem metricOfCoefficient_metricCoefficient
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) :
    metricOfCoefficient (metricCoefficient g) (metricCoefficient_pos g) = g := by
  apply metricCoefficient_injective
  exact metricCoefficient_metricOfCoefficient _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.metricOfCoefficient_metricCoefficient then
    throwError "Refusing to shadow existing declaration AddCircle.metricOfCoefficient_metricCoefficient"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.metricOfCoefficient_metricCoefficient ``Submission.AddCircle.metricOfCoefficient_metricCoefficient

open _root_.AddCircle in
theorem eq_flatMetric_of_parameterTangent_unit
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (h : ∀ z, g.inner z (parameterTangent z) (parameterTangent z) = 1) :
    g = flatMetric := by
  apply SmoothRiemannianMetric.ext_inner
  intro z v w
  obtain ⟨a, rfl⟩ := exists_smul_parameterTangent z v
  obtain ⟨b, rfl⟩ := exists_smul_parameterTangent z w
  simp only [map_smul, smul_apply, smul_eq_mul, h, flatMetric_parameterTangent_unit]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.eq_flatMetric_of_parameterTangent_unit then
    throwError "Refusing to shadow existing declaration AddCircle.eq_flatMetric_of_parameterTangent_unit"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.eq_flatMetric_of_parameterTangent_unit ``Submission.AddCircle.eq_flatMetric_of_parameterTangent_unit

set_option backward.isDefEq.respectTransparency false in
open _root_.AddCircle in
theorem flatMetric_inner_mfderiv_coe (x a b : ℝ) :
    flatMetric.inner (x : AddCircle (1 : ℝ))
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => (t : AddCircle (1 : ℝ))) x a)
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => (t : AddCircle (1 : ℝ))) x b) = a * b := by
  have ha : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
      (fun t : ℝ => (t : AddCircle (1 : ℝ))) x a = a • parameterTangent (x : AddCircle (1 : ℝ)) := by
    rw [parameterTangent_coe, ← map_smul]
    congr 1
    change a = a * 1
    exact (mul_one a).symm
  have hb : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
      (fun t : ℝ => (t : AddCircle (1 : ℝ))) x b = b • parameterTangent (x : AddCircle (1 : ℝ)) := by
    rw [parameterTangent_coe, ← map_smul]
    congr 1
    change b = b * 1
    exact (mul_one b).symm
  rw [ha, hb, (flatMetric.inner (x : AddCircle (1 : ℝ))).map_smul, smul_apply,
    (flatMetric.inner (x : AddCircle (1 : ℝ)) (parameterTangent (x : AddCircle (1 : ℝ)))).map_smul]
  change a * (b * _) = a * b
  rw [flatMetric_parameterTangent_unit, mul_one]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.flatMetric_inner_mfderiv_coe then
    throwError "Refusing to shadow existing declaration AddCircle.flatMetric_inner_mfderiv_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.flatMetric_inner_mfderiv_coe ``Submission.AddCircle.flatMetric_inner_mfderiv_coe


section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

open _root_.AddCircle in
def graphMetricCoefficient (f : C^∞⟮𝓘(ℝ, ℝ), AddCircle (1 : ℝ); 𝓘(ℝ, F), F⟯) :
    C^∞⟮𝓘(ℝ, ℝ), AddCircle (1 : ℝ); ℝ⟯ :=
  ⟨fun z => 1 + ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) f z (parameterTangent z)‖ ^ 2,
    contMDiff_const.add ((contDiff_norm_sq ℝ).contMDiff.comp
      (contMDiff_mfderiv_parameterTangent f.contMDiff (m := ∞) (by simp) le_rfl))⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.graphMetricCoefficient then
    throwError "Refusing to shadow existing declaration AddCircle.graphMetricCoefficient"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.graphMetricCoefficient ``Submission.AddCircle.graphMetricCoefficient

open _root_.AddCircle in
@[simp] theorem graphMetricCoefficient_apply
    (f : C^∞⟮𝓘(ℝ, ℝ), AddCircle (1 : ℝ); 𝓘(ℝ, F), F⟯) (z : AddCircle (1 : ℝ)) :
    graphMetricCoefficient f z =
      1 + ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) f z (parameterTangent z)‖ ^ 2 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.graphMetricCoefficient_apply then
    throwError "Refusing to shadow existing declaration AddCircle.graphMetricCoefficient_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.graphMetricCoefficient_apply ``Submission.AddCircle.graphMetricCoefficient_apply

open _root_.AddCircle in
theorem graphMetricCoefficient_pos
    (f : C^∞⟮𝓘(ℝ, ℝ), AddCircle (1 : ℝ); 𝓘(ℝ, F), F⟯) (z : AddCircle (1 : ℝ)) :
    0 < graphMetricCoefficient f z := by
  rw [graphMetricCoefficient_apply]
  positivity

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.graphMetricCoefficient_pos then
    throwError "Refusing to shadow existing declaration AddCircle.graphMetricCoefficient_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.graphMetricCoefficient_pos ``Submission.AddCircle.graphMetricCoefficient_pos

open _root_.AddCircle in
def graphMetric (f : C^∞⟮𝓘(ℝ, ℝ), AddCircle (1 : ℝ); 𝓘(ℝ, F), F⟯) :
    SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)) :=
  metricOfCoefficient (graphMetricCoefficient f) (graphMetricCoefficient_pos f)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.graphMetric then
    throwError "Refusing to shadow existing declaration AddCircle.graphMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.graphMetric ``Submission.AddCircle.graphMetric

open _root_.AddCircle in
@[simp] theorem metricCoefficient_graphMetric
    (f : C^∞⟮𝓘(ℝ, ℝ), AddCircle (1 : ℝ); 𝓘(ℝ, F), F⟯) :
    metricCoefficient (graphMetric f) = graphMetricCoefficient f :=
  metricCoefficient_metricOfCoefficient _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.metricCoefficient_graphMetric then
    throwError "Refusing to shadow existing declaration AddCircle.metricCoefficient_graphMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.metricCoefficient_graphMetric ``Submission.AddCircle.metricCoefficient_graphMetric

open _root_.AddCircle in
theorem graphMetric_inner
    (f : C^∞⟮𝓘(ℝ, ℝ), AddCircle (1 : ℝ); 𝓘(ℝ, F), F⟯) (z : AddCircle (1 : ℝ))
    (v w : TangentSpace 𝓘(ℝ, ℝ) z) :
    (graphMetric f).inner z v w = flatMetric.inner z v w +
      _root_.Inner.inner ℝ (show F from mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) f z v)
        (show F from mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) f z w) := by
  obtain ⟨a, rfl⟩ := exists_smul_parameterTangent z v
  obtain ⟨b, rfl⟩ := exists_smul_parameterTangent z w
  rw [graphMetric, metricOfCoefficient_inner, graphMetricCoefficient_apply]
  let D : TangentSpace 𝓘(ℝ, ℝ) z →L[ℝ] F := mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) f z
  change (1 + ‖D (parameterTangent z)‖ ^ 2) *
    flatMetric.inner z (a • parameterTangent z) (b • parameterTangent z) =
      flatMetric.inner z (a • parameterTangent z) (b • parameterTangent z) +
        _root_.Inner.inner ℝ (D (a • parameterTangent z)) (D (b • parameterTangent z))
  simp only [map_smul, smul_apply, smul_eq_mul, flatMetric_parameterTangent_unit,
    inner_smul_left, inner_smul_right, conj_trivial, real_inner_self_eq_norm_sq]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.graphMetric_inner then
    throwError "Refusing to shadow existing declaration AddCircle.graphMetric_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.graphMetric_inner ``Submission.AddCircle.graphMetric_inner

end

section

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

open _root_.AddCircle in
private theorem mfderiv_graph_apply
    (f : C^∞⟮𝓘(ℝ, ℝ), AddCircle (1 : ℝ); 𝓘(ℝ, F), F⟯)
    (z : AddCircle (1 : ℝ)) (v : TangentSpace 𝓘(ℝ, ℝ) z) :
    mfderiv 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F))
      (fun y => (y, f y)) z v = (v, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) f z v) := by
  erw [mfderiv_prodMk mdifferentiableAt_id (f.contMDiff.mdifferentiableAt (by simp)),
    mfderiv_id]
  rfl

run_cmd do
  let target := ``Submission.AddCircle.mfderiv_graph_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `AddCircle.mfderiv_graph_apply target :: scope.openDecls } }

open _root_.AddCircle in
private theorem mfderiv_graph_injective
    (f : C^∞⟮𝓘(ℝ, ℝ), AddCircle (1 : ℝ); 𝓘(ℝ, F), F⟯)
    (z : AddCircle (1 : ℝ)) :
    Function.Injective (mfderiv 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F))
      (fun y => (y, f y)) z) := by
  intro v w hvw
  rw [mfderiv_graph_apply, mfderiv_graph_apply] at hvw
  exact congrArg Prod.fst hvw

run_cmd do
  let target := ``Submission.AddCircle.mfderiv_graph_injective
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `AddCircle.mfderiv_graph_injective target :: scope.openDecls } }


end

section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

open _root_.AddCircle in
theorem graphMetric_eq_pullbackOfImmersion
    (f : C^∞⟮𝓘(ℝ, ℝ), AddCircle (1 : ℝ); 𝓘(ℝ, F), F⟯) :
    graphMetric f = (flatMetric.prod (euclideanMetric (E := F))).pullbackOfImmersion
      (fun z => (z, f z)) (contMDiff_id.prodMk f.contMDiff) (mfderiv_graph_injective f) := by
  apply SmoothRiemannianMetric.ext_inner
  intro z v w
  rw [graphMetric_inner, SmoothRiemannianMetric.pullbackOfImmersion_inner,
    mfderiv_graph_apply, mfderiv_graph_apply]
  erw [SmoothRiemannianMetric.prod_inner, euclideanMetric_inner]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.graphMetric_eq_pullbackOfImmersion then
    throwError "Refusing to shadow existing declaration AddCircle.graphMetric_eq_pullbackOfImmersion"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.graphMetric_eq_pullbackOfImmersion ``Submission.AddCircle.graphMetric_eq_pullbackOfImmersion


end


end AddCircle

end

end
