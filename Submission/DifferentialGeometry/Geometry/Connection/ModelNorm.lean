import Submission.DifferentialGeometry.Geometry.Metric.HomModelNorm
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle
open _root_.Submission.DifferentialGeometry.Tensor0SBundle (MetricFiberData)
open scoped _root_.Manifold _root_.ContDiff

namespace CovariantDerivative
open _root_.CovariantDerivative

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [oldNorm : NormedAddCommGroup F] [oldSpace : NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

section NormedFibers

variable {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)] [FiberBundle F V]

open _root_.CovariantDerivative in
def withModelMetric (D : MetricFiberData F) (c : CovariantDerivative IB F V) :
    letI : NormedAddCommGroup F := D.toNormedAddCommGroupOfTopology
    letI : InnerProductSpace ℝ F :=
      @MetricFiberData.toInnerProductSpaceOfTopology F oldNorm.toAddCommGroup oldSpace.toModule
        _ _ (by let : SeminormedAddCommGroup F := oldNorm.toSeminormedAddCommGroup
                let : NormedSpace ℝ F := oldSpace
                infer_instance) _ _ D
    CovariantDerivative IB F V := by
  let cfun := c.toFun
  have hc := c.isCovariantDerivativeOnUniv
  let newNorm := D.toNormedAddCommGroupOfTopology
  let : SeminormedAddCommGroup F := newNorm.toSeminormedAddCommGroup
  let newInner :=
    @MetricFiberData.toInnerProductSpaceOfTopology F oldNorm.toAddCommGroup oldSpace.toModule
      _ _ (by let : SeminormedAddCommGroup F := oldNorm.toSeminormedAddCommGroup
              let : NormedSpace ℝ F := oldSpace
              infer_instance) _ _ D
  refine ⟨cfun, ?_⟩
  constructor
  · intro σ τ x hσ hτ hx
    exact @IsCovariantDerivativeOn.add ℝ _ EB _ _ HB _ IB B _ _ F oldNorm oldSpace
      V _ _ _ _ _ _ _ _ _ hc σ τ x
      ((@mdifferentiableAt_totalSpace_model_metric_iff EB _ _ HB _ IB B _ _
      EB _ _ HB _ IB B _ _
        F oldNorm oldSpace _ V _ _ _ D _ x).mp hσ)
      ((@mdifferentiableAt_totalSpace_model_metric_iff EB _ _ HB _ IB B _ _
      EB _ _ HB _ IB B _ _
        F oldNorm oldSpace _ V _ _ _ D _ x).mp hτ) hx
  · intro σ f x hσ hf hx
    exact @IsCovariantDerivativeOn.leibniz ℝ _ EB _ _ HB _ IB B _ _ F oldNorm oldSpace
      V _ _ _ _ _ _ _ _ _ hc σ f x
      ((@mdifferentiableAt_totalSpace_model_metric_iff EB _ _ HB _ IB B _ _
      EB _ _ HB _ IB B _ _
        F oldNorm oldSpace _ V _ _ _ D _ x).mp hσ) hf hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.withModelMetric then
    throwError "Refusing to shadow existing declaration CovariantDerivative.withModelMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.withModelMetric ``Submission.CovariantDerivative.withModelMetric

open _root_.CovariantDerivative in
theorem withModelMetric_apply (D : MetricFiberData F)
    (c : CovariantDerivative IB F V) (σ : ∀ x, V x) (x : B) :
    withModelMetric D c σ x = c σ x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.withModelMetric_apply then
    throwError "Refusing to shadow existing declaration CovariantDerivative.withModelMetric_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.withModelMetric_apply ``Submission.CovariantDerivative.withModelMetric_apply

open _root_.CovariantDerivative in
theorem withModelMetric_contMDiff [IsManifold IB 1 B] [oldVector : VectorBundle ℝ F V]
    (D : MetricFiberData F) (c : CovariantDerivative IB F V)
    {n : ℕ∞ω} [hc : _root_.CovariantDerivative.ContMDiffCovariantDerivative c n] :
    letI : NormedAddCommGroup F := D.toNormedAddCommGroupOfTopology
    letI : InnerProductSpace ℝ F :=
      @MetricFiberData.toInnerProductSpaceOfTopology F oldNorm.toAddCommGroup oldSpace.toModule
        _ _ (by let : SeminormedAddCommGroup F := oldNorm.toSeminormedAddCommGroup
                let : NormedSpace ℝ F := oldSpace
                infer_instance) _ _ D
    letI : VectorBundle ℝ F V :=
      @vector_bundle_model_metric B _ F oldNorm oldSpace _ V _ _ _ _ oldVector D
    _root_.CovariantDerivative.ContMDiffCovariantDerivative
      (@withModelMetric EB _ _ HB _ IB B _ _ F oldNorm oldSpace _ V _ _ _ _ D c) n := by
  have hsmooth := @ContMDiffCovariantDerivativeOn.contMDiff ℝ _ EB _ _ HB _ IB B _ _
    F oldNorm oldSpace V _ _ _ _ _ _ _ _ _ n c.toFun Set.univ hc.contMDiff
  let newNorm := D.toNormedAddCommGroupOfTopology
  let : SeminormedAddCommGroup F := newNorm.toSeminormedAddCommGroup
  let newInner :=
    @MetricFiberData.toInnerProductSpaceOfTopology F oldNorm.toAddCommGroup oldSpace.toModule
      _ _ (by let : SeminormedAddCommGroup F := oldNorm.toSeminormedAddCommGroup
              let : NormedSpace ℝ F := oldSpace
              infer_instance) _ _ D
  let : VectorBundle ℝ F V :=
    @vector_bundle_model_metric B _ F oldNorm oldSpace _ V _ _ _ _ oldVector D
  constructor
  constructor
  intro σ hσ
  have hσold := fun y hy =>
    (@contMDiffWithinAt_totalSpace_model_metric_iff EB _ _ HB _ IB B _ _
      EB _ _ HB _ IB B _ _
      F oldNorm oldSpace _ V _ _ _ D (n + 1) _ Set.univ y).mp (hσ y hy)
  have hcovσ := hsmooth hσold
  intro x hx
  let : ∀ y : B, NormedAddCommGroup (TangentSpace IB y) := fun y =>
    { toNorm := inferInstanceAs (Norm EB)
      toAddCommGroup := instAddCommGroupTangentSpace IB y
      toMetricSpace :=
        let m : MetricSpace (TangentSpace IB y) := inferInstanceAs (MetricSpace EB)
        m.replaceTopology (by rfl)
      dist_eq := by
        intro v w
        unfold TangentSpace at v w ⊢
        exact NormedAddCommGroup.dist_eq v w }
  let : ∀ y : B, NormedSpace ℝ (TangentSpace IB y) := fun y =>
    { toModule := instModuleTangentSpace IB y
      norm_smul_le := by
        intro c v
        unfold TangentSpace at v ⊢
        exact norm_smul_le c v }
  let : FiberBundle EB (TangentSpace IB : B → Type _) := TangentSpace.fiberBundle
  exact (@contMDiffWithinAt_hom_totalSpace_model_metric_iff EB _ _ HB _ IB B _ _
      EB _ _ HB _ IB B _ _
    F oldNorm oldSpace _ V _ _ _ _ oldVector EB _ _ (TangentSpace IB : B → Type _) _ _ _ _ _
    D n _ Set.univ x).mpr (hcovσ x hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.withModelMetric_contMDiff then
    throwError "Refusing to shadow existing declaration CovariantDerivative.withModelMetric_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.withModelMetric_contMDiff ``Submission.CovariantDerivative.withModelMetric_contMDiff

end NormedFibers

variable {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [oldVector : VectorBundle ℝ F V]

open _root_.CovariantDerivative in
theorem withModelMetric_isMetricCompatible [IsManifold IB 1 B]
    [oldSmooth : ContMDiffVectorBundle 1 F V IB]
    [oldMetric : IsContMDiffRiemannianBundle IB 1 F V]
    (D : MetricFiberData F) (c : CovariantDerivative IB F V) (hc : c.IsMetricCompatible) :
    letI : NormedAddCommGroup F := D.toNormedAddCommGroupOfTopology
    letI : InnerProductSpace ℝ F :=
      @MetricFiberData.toInnerProductSpaceOfTopology F oldNorm.toAddCommGroup oldSpace.toModule
        _ _ (by let : SeminormedAddCommGroup F := oldNorm.toSeminormedAddCommGroup
                let : NormedSpace ℝ F := oldSpace
                infer_instance) _ _ D
    letI : VectorBundle ℝ F V :=
      @vector_bundle_model_metric B _ F oldNorm oldSpace _ V _ _ _ _ oldVector D
    letI : ContMDiffVectorBundle 1 F V IB :=
      @contMDiffVectorBundle_model_metric EB _ _ HB _ IB B _ _
        F oldNorm oldSpace _ V _ _ _ _ oldVector 1 oldSmooth D
    letI : IsContMDiffRiemannianBundle IB 1 F V :=
      @isContMDiffRiemannianBundle_model_metric EB _ _ HB _ IB B _ _
        F oldNorm oldSpace _ V _ _ _ _ oldVector D 1 oldMetric
    (@withModelMetric EB _ _ HB _ IB B _ _ F oldNorm oldSpace _ V _ _ _ _ D c).IsMetricCompatible := by
  have hcompat := fun (x : B) (X : ∀ y, TangentSpace IB y) (σ τ : ∀ y, V y) =>
    (_root_.CovariantDerivative.isMetricCompatible_iff c).mp hc (x := x) (X := X) (σ := σ) (τ := τ)
  let vb := @vector_bundle_model_metric B _ F oldNorm oldSpace _ V _ _ _ _ oldVector D
  let svb := @contMDiffVectorBundle_model_metric EB _ _ HB _ IB B _ _
    F oldNorm oldSpace _ V _ _ _ _ oldVector 1 oldSmooth D
  let smetric := @isContMDiffRiemannianBundle_model_metric EB _ _ HB _ IB B _ _
    F oldNorm oldSpace _ V _ _ _ _ oldVector D 1 oldMetric
  let c' := withModelMetric D c
  let newNorm := D.toNormedAddCommGroupOfTopology
  let : SeminormedAddCommGroup F := newNorm.toSeminormedAddCommGroup
  let newInner :=
    @MetricFiberData.toInnerProductSpaceOfTopology F oldNorm.toAddCommGroup oldSpace.toModule
      _ _ (by let : SeminormedAddCommGroup F := oldNorm.toSeminormedAddCommGroup
              let : NormedSpace ℝ F := oldSpace
              infer_instance) _ _ D
  let : VectorBundle ℝ F V := vb
  let : ContMDiffVectorBundle 1 F V IB := svb
  let : IsContMDiffRiemannianBundle IB 1 F V := smetric
  apply (_root_.CovariantDerivative.isMetricCompatible_iff c').mpr
  intro x X σ τ hX hσ hτ
  exact hcompat x X σ τ hX
    ((@mdifferentiableAt_totalSpace_model_metric_iff EB _ _ HB _ IB B _ _
      EB _ _ HB _ IB B _ _
      F oldNorm oldSpace _ V _ _ _ D _ x).mp hσ)
    ((@mdifferentiableAt_totalSpace_model_metric_iff EB _ _ HB _ IB B _ _
      EB _ _ HB _ IB B _ _
      F oldNorm oldSpace _ V _ _ _ D _ x).mp hτ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.withModelMetric_isMetricCompatible then
    throwError "Refusing to shadow existing declaration CovariantDerivative.withModelMetric_isMetricCompatible"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.withModelMetric_isMetricCompatible ``Submission.CovariantDerivative.withModelMetric_isMetricCompatible

end CovariantDerivative
