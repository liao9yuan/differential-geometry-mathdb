import Submission.DifferentialGeometry.Geometry.Operator.Gradient.MetricSharpSmoothness
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Cotangent.Riemannian
import Submission.DifferentialGeometry.Tensor.Multilinear.Bundle.Evaluation
import Submission.DifferentialGeometry.Geometry.Connection.Realization.SmoothSections
import Submission.DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Connection.Realization
open _root_.Submission.DifferentialGeometry.Geometry.Operator

noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators

namespace DifferentialGeometry

open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.TensorMultilinear (contMDiffAt_section_apply contMDiff_section_apply)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def inverseMetricSharpFib (g : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 1 I x →L[ℝ] TangentSpace I x :=
  LinearMap.toContinuousLinearMap
    { toFun := fun α => metricSharp (I := I) g x (cotangentToDualLinear (I := I) (x := x) α)
      map_add' := fun α β => by
        rw [map_add (cotangentToDualLinear (I := I) (x := x))]
        rw [metricSharp_def, metricSharp_def, metricSharp_def, map_add]
      map_smul' := fun c α => by
        rw [map_smul (cotangentToDualLinear (I := I) (x := x))]
        rw [metricSharp_def, metricSharp_def, map_smul]; rfl }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.inverseMetricSharpFib then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.inverseMetricSharpFib"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.inverseMetricSharpFib ``Submission.DifferentialGeometry.inverseMetricSharpFib

@[simp] lemma inverseMetricSharpFib_apply (g : SmoothRiemannianMetric I M) (x : M)
    (α : Tensor0SSpace 1 I x) :
    inverseMetricSharpFib (I := I) g x α =
      metricSharp (I := I) g x (cotangentToDualLinear (I := I) (x := x) α) := by
  rw [inverseMetricSharpFib, LinearMap.coe_toContinuousLinearMap']; rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.inverseMetricSharpFib_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.inverseMetricSharpFib_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.inverseMetricSharpFib_apply ``Submission.DifferentialGeometry.inverseMetricSharpFib_apply

lemma inverseMetricSharpFib_inner (g : SmoothRiemannianMetric I M) (x : M)
    (α : Tensor0SSpace 1 I x) (w : TangentSpace I x) :
    g.inner x (inverseMetricSharpFib (I := I) g x α) w =
      cotangentToDualLinear (I := I) (x := x) α w := by
  rw [inverseMetricSharpFib_apply]
  exact inner_metricSharp (I := I) g x (cotangentToDualLinear (I := I) (x := x) α) w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.inverseMetricSharpFib_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.inverseMetricSharpFib_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.inverseMetricSharpFib_inner ``Submission.DifferentialGeometry.inverseMetricSharpFib_inner

lemma inverseMetricSharpFib_zero (g : SmoothRiemannianMetric I M) (x : M) :
    inverseMetricSharpFib (I := I) g x 0 = 0 := by
  rw [inverseMetricSharpFib_apply, map_zero]
  rw [metricSharp_def, map_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.inverseMetricSharpFib_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.inverseMetricSharpFib_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.inverseMetricSharpFib_zero ``Submission.DifferentialGeometry.inverseMetricSharpFib_zero

lemma inverseMetricSharpFib_ne_zero_of_ne_zero (g : SmoothRiemannianMetric I M) (x : M)
    {α : Tensor0SSpace 1 I x} (hα : α ≠ 0) :
    inverseMetricSharpFib (I := I) g x α ≠ 0 := by
  intro hzero
  apply hα
  have hdual : cotangentToDualLinear (I := I) (x := x) α = 0 := by
    ext w
    rw [← inverseMetricSharpFib_inner (I := I) g x α w, hzero]
    simp
  exact cotangentToDualLinear_injective (I := I) (x := x) (by rw [hdual, map_zero])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.inverseMetricSharpFib_ne_zero_of_ne_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.inverseMetricSharpFib_ne_zero_of_ne_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.inverseMetricSharpFib_ne_zero_of_ne_zero ``Submission.DifferentialGeometry.inverseMetricSharpFib_ne_zero_of_ne_zero

def cometricBilin (g : SmoothRiemannianMetric I M) (x : M)
    (α β : Tensor0SSpace 1 I x) : ℝ :=
  g.inner x (inverseMetricSharpFib (I := I) g x α) (inverseMetricSharpFib (I := I) g x β)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.cometricBilin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.cometricBilin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.cometricBilin ``Submission.DifferentialGeometry.cometricBilin

lemma cometricBilin_eq_inner_sharp (g : SmoothRiemannianMetric I M) (x : M)
    (α β : Tensor0SSpace 1 I x) :
    cometricBilin (I := I) g x α β =
      g.inner x (inverseMetricSharpFib (I := I) g x α)
        (inverseMetricSharpFib (I := I) g x β) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.cometricBilin_eq_inner_sharp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.cometricBilin_eq_inner_sharp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.cometricBilin_eq_inner_sharp ``Submission.DifferentialGeometry.cometricBilin_eq_inner_sharp

lemma cometricBilin_eq_dual_sharp (g : SmoothRiemannianMetric I M) (x : M)
    (α β : Tensor0SSpace 1 I x) :
    cometricBilin (I := I) g x α β =
      cotangentToDualLinear (I := I) (x := x) α (inverseMetricSharpFib (I := I) g x β) := by
  rw [cometricBilin_eq_inner_sharp]
  exact inverseMetricSharpFib_inner (I := I) g x α (inverseMetricSharpFib (I := I) g x β)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.cometricBilin_eq_dual_sharp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.cometricBilin_eq_dual_sharp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.cometricBilin_eq_dual_sharp ``Submission.DifferentialGeometry.cometricBilin_eq_dual_sharp

lemma cometricBilin_symm (g : SmoothRiemannianMetric I M) (x : M)
    (α β : Tensor0SSpace 1 I x) :
    cometricBilin (I := I) g x α β = cometricBilin (I := I) g x β α := by
  rw [cometricBilin_eq_inner_sharp, cometricBilin_eq_inner_sharp]
  exact g.symm x _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.cometricBilin_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.cometricBilin_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.cometricBilin_symm ``Submission.DifferentialGeometry.cometricBilin_symm

lemma cometricBilin_self_nonneg (g : SmoothRiemannianMetric I M) (x : M)
    (α : Tensor0SSpace 1 I x) :
    0 ≤ cometricBilin (I := I) g x α α := by
  rw [cometricBilin_eq_inner_sharp]
  rcases eq_or_ne (inverseMetricSharpFib (I := I) g x α) 0 with h | h
  · rw [h]; simp
  · exact le_of_lt (g.pos x (inverseMetricSharpFib (I := I) g x α) h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.cometricBilin_self_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.cometricBilin_self_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.cometricBilin_self_nonneg ``Submission.DifferentialGeometry.cometricBilin_self_nonneg

lemma cometricBilin_self_pos (g : SmoothRiemannianMetric I M) (x : M)
    {α : Tensor0SSpace 1 I x} (hα : α ≠ 0) :
    0 < cometricBilin (I := I) g x α α := by
  rw [cometricBilin_eq_inner_sharp]
  exact g.pos x (inverseMetricSharpFib (I := I) g x α)
    (inverseMetricSharpFib_ne_zero_of_ne_zero (I := I) g x hα)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.cometricBilin_self_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.cometricBilin_self_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.cometricBilin_self_pos ``Submission.DifferentialGeometry.cometricBilin_self_pos

variable [NeZero (Module.finrank ℝ E)]
  [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] [BoundarylessManifold I M]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]
  [I.Boundaryless] [BoundarylessManifold I M] in
theorem cotangentSection_chartComponent_contMDiffOn
    (Y : Cₛ^∞⟮I; Tensor0SModel 1 ℝ E, (fun x : M => Tensor0SSpace 1 I x)⟯)
    (γ : M) (j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M => Tensor0SSpace.toModel (Y b)
        (fun _ : Fin 1 => DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) γ j b))
      (chartAt H γ).source := by
  intro x₀ hx₀
  apply ContMDiffAt.contMDiffWithinAt
  apply contMDiffAt_section_apply (n := 1) (T := fun b => Y b) (x₀ := x₀)
  · exact Y.contMDiff.contMDiffAt
  · intro i
    have hbase : (_root_.FiberBundle.trivializationAt E (TangentSpace I) γ).baseSet = (chartAt H γ).source :=
      TangentBundle.trivializationAt_baseSet (I := I) γ
    have hx₀base : x₀ ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) γ).baseSet := by
      rw [hbase]; exact hx₀
    have hopen : IsOpen (_root_.FiberBundle.trivializationAt E (TangentSpace I) γ).baseSet :=
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) γ).open_baseSet
    exact (DifferentialGeometry.Tensor.Coordinates.chartBasisVec_contMDiffOn (I := I) γ j x₀ hx₀base).contMDiffAt
      (hopen.mem_nhds hx₀base)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.cotangentSection_chartComponent_contMDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.cotangentSection_chartComponent_contMDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.cotangentSection_chartComponent_contMDiffOn ``Submission.DifferentialGeometry.cotangentSection_chartComponent_contMDiffOn

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] [I.Boundaryless] in
theorem inverseMetricSharpField_contMDiff (g : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 1 ℝ E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 1 ℝ E →L[ℝ] E)
        (E := fun z : M => Tensor0SSpace 1 I z →L[ℝ] TangentSpace I z) x
        (inverseMetricSharpFib (I := I) g x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel 1 ℝ E) (V₁ := fun x : M => Tensor0SSpace 1 I x)
    (F₂ := E) (V₂ := fun x : M => TangentSpace I x)
    (φ := fun x => inverseMetricSharpFib (I := I) g x)
  intro Y
  have hmain : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E b
        (metricSharp (I := I) g b (cotangentToDualLinear (I := I) (x := b) (Y b)))) := by
    apply metricSharp_contMDiff_total (I := I) g
    intro γ j
    have hcongr : (fun b : M => (cotangentToDualLinear (I := I) (x := b) (Y b))
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) γ j b)) =
        (fun b : M => Tensor0SSpace.toModel (Y b)
          (fun _ : Fin 1 => DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) γ j b)) := by
      funext b
      rw [cotangentToDualLinear_apply, cotangentToDual_apply]
      rfl
    rw [hcongr]
    exact cotangentSection_chartComponent_contMDiffOn (I := I) Y γ j
  refine hmain.congr (fun x => ?_)
  change TotalSpace.mk' E x
      (metricSharp (I := I) g x (cotangentToDualLinear (I := I) (x := x) (Y x))) =
    TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
      (inverseMetricSharpFib (I := I) g x (Y x))
  rw [inverseMetricSharpFib_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.inverseMetricSharpField_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.inverseMetricSharpField_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.inverseMetricSharpField_contMDiff ``Submission.DifferentialGeometry.inverseMetricSharpField_contMDiff

def inverseMetricSharpField (g : SmoothRiemannianMetric I M) :
    Cₛ^∞⟮I; Tensor0SModel 1 ℝ E →L[ℝ] E,
      (fun x : M => Tensor0SSpace 1 I x →L[ℝ] TangentSpace I x)⟯ where
  toFun := fun x : M => inverseMetricSharpFib (I := I) g x
  contMDiff_toFun := inverseMetricSharpField_contMDiff (I := I) g

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.inverseMetricSharpField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.inverseMetricSharpField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.inverseMetricSharpField ``Submission.DifferentialGeometry.inverseMetricSharpField

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M]
    [BoundarylessManifold I M] in
@[simp] lemma inverseMetricSharpField_apply (g : SmoothRiemannianMetric I M) (x : M) :
    inverseMetricSharpField (I := I) g x = inverseMetricSharpFib (I := I) g x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.inverseMetricSharpField_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.inverseMetricSharpField_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.inverseMetricSharpField_apply ``Submission.DifferentialGeometry.inverseMetricSharpField_apply

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]
    [BoundarylessManifold I M] [I.Boundaryless] in
theorem cometricBilin_contMDiff (g : SmoothRiemannianMetric I M)
    (α β : Cₛ^∞⟮I; Tensor0SModel 1 ℝ E, (fun x : M => Tensor0SSpace 1 I x)⟯) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => cometricBilin (I := I) g x (α x) (β x)) := by
  have hsharpβ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E b
        (metricSharp (I := I) g b (cotangentToDualLinear (I := I) (x := b) (β b)))) := by
    apply metricSharp_contMDiff_total (I := I) g
    intro γ j
    have hcongr : (fun b : M => (cotangentToDualLinear (I := I) (x := b) (β b))
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) γ j b)) =
        (fun b : M => Tensor0SSpace.toModel (β b)
          (fun _ : Fin 1 => DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) γ j b)) := by
      funext b
      rw [cotangentToDualLinear_apply, cotangentToDual_apply]
      rfl
    rw [hcongr]
    exact cotangentSection_chartComponent_contMDiffOn (I := I) β γ j
  have hidentity : (fun x : M => cometricBilin (I := I) g x (α x) (β x)) =
      (fun b : M => Tensor0SSpace.toModel (α b)
        (fun _ : Fin 1 =>
          metricSharp (I := I) g b (cotangentToDualLinear (I := I) (x := b) (β b)))) := by
    funext b
    rw [cometricBilin_eq_dual_sharp, inverseMetricSharpFib_apply,
      cotangentToDualLinear_apply, cotangentToDual_apply]
    rfl
  rw [hidentity]
  apply contMDiff_section_apply (n := 1) (T := fun b => α b) α.contMDiff
  intro i
  exact hsharpβ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.cometricBilin_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.cometricBilin_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.cometricBilin_contMDiff ``Submission.DifferentialGeometry.cometricBilin_contMDiff

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]
    [BoundarylessManifold I M] in
theorem exists_uniform_cometricBilin_bound [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (α β : Cₛ^∞⟮I; Tensor0SModel 1 ℝ E, (fun x : M => Tensor0SSpace 1 I x)⟯) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : M, |cometricBilin (I := I) g x (α x) (β x)| ≤ C := by
  have hcont : Continuous (fun x : M => cometricBilin (I := I) g x (α x) (β x)) :=
    (cometricBilin_contMDiff (I := I) g α β).continuous
  rcases isEmpty_or_nonempty M with hM | hM
  · exact ⟨0, le_refl 0, fun x => (hM.false x).elim⟩
  · obtain ⟨x₀, -, hx₀⟩ := (isCompact_univ (X := M)).exists_isMaxOn (_root_.Set.univ_nonempty)
      (continuous_abs.comp hcont).continuousOn
    refine ⟨|cometricBilin (I := I) g x₀ (α x₀) (β x₀)|, abs_nonneg _, fun x => ?_⟩
    exact hx₀ (_root_.Set.mem_univ x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.exists_uniform_cometricBilin_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.exists_uniform_cometricBilin_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.exists_uniform_cometricBilin_bound ``Submission.DifferentialGeometry.exists_uniform_cometricBilin_bound

end DifferentialGeometry
