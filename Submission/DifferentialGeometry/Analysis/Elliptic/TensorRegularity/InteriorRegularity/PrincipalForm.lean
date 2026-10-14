import Submission.DifferentialGeometry.Analysis.Elliptic.TensorRegularity.Defs
import Submission.DifferentialGeometry.Analysis.Elliptic.Operator.ChartLocalLaplacian

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory _root_.Filter _root_.Topology _root_.Function
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.Matrix _root_.InnerProductSpace _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace TensorRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [NeZero (Module.finrank ℝ E)] in
theorem weightedInvGramEuclid_eq_weightedInvGramOnEuclid
    (g : SmoothRiemannianMetric I M) (α : M)
    (k l : Fin (Module.finrank ℝ E)) :
    weightedInvGramEuclid (I := I) g α k l =
      weightedInvGramOnEuclid (I := I) g α k l :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.weightedInvGramEuclid_eq_weightedInvGramOnEuclid then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.weightedInvGramEuclid_eq_weightedInvGramOnEuclid"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.weightedInvGramEuclid_eq_weightedInvGramOnEuclid ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.weightedInvGramEuclid_eq_weightedInvGramOnEuclid

theorem exists_tensorPrincipalForm
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ B : SmoothEllipticBilinearForm (Module.finrank ℝ E) (Set.univ : Set EuclN),
      (∀ y ∈ K, ∀ i j : Fin (Module.finrank ℝ E),
        B.a y i j = weightedInvGramEuclid (I := I) g α i j y) ∧
      B.c = (fun _ : EuclN => (0 : ℝ)) := by
  obtain ⟨_, _, _, _, _, B, hB_agree, hB_c⟩ :=
    exists_smooth_metric_extension (I := I) (M := M) g α hK hK_target
  exact ⟨B, hB_agree, hB_c⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.exists_tensorPrincipalForm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.exists_tensorPrincipalForm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.exists_tensorPrincipalForm ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.exists_tensorPrincipalForm

def tensorPrincipalForm
    [I.Boundaryless] (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    SmoothEllipticBilinearForm (Module.finrank ℝ E) (Set.univ : Set EuclN) :=
  Classical.choose (exists_tensorPrincipalForm (I := I) (M := M) g α hK hK_target)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorPrincipalForm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorPrincipalForm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorPrincipalForm ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorPrincipalForm

theorem tensorPrincipalForm_spec
    [I.Boundaryless] (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∀ y ∈ K, ∀ i j : Fin (Module.finrank ℝ E),
        (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).a y i j =
          weightedInvGramEuclid (I := I) g α i j y) ∧
      (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).c =
        (fun _ : EuclN => (0 : ℝ)) :=
  Classical.choose_spec (exists_tensorPrincipalForm (I := I) (M := M) g α hK hK_target)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorPrincipalForm_spec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorPrincipalForm_spec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorPrincipalForm_spec ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorPrincipalForm_spec

theorem tensorPrincipalForm_a_eq_weightedInvGramEuclid
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    {y : EuclN} (hy : y ∈ K) (i j : Fin (Module.finrank ℝ E)) :
    (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).a y i j =
      weightedInvGramEuclid (I := I) g α i j y := by
  exact (tensorPrincipalForm_spec (I := I) (M := M) g α hK hK_target).1 y hy i j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorPrincipalForm_a_eq_weightedInvGramEuclid then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorPrincipalForm_a_eq_weightedInvGramEuclid"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorPrincipalForm_a_eq_weightedInvGramEuclid ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorPrincipalForm_a_eq_weightedInvGramEuclid

theorem tensorPrincipalForm_c
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).c =
      (fun _ : EuclN => (0 : ℝ)) := by
  exact (tensorPrincipalForm_spec (I := I) (M := M) g α hK hK_target).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorPrincipalForm_c then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorPrincipalForm_c"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorPrincipalForm_c ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorPrincipalForm_c

theorem tensorPrincipalForm_c_apply
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    (y : EuclN) :
    (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).c y = 0 := by
  rw [tensorPrincipalForm_c (I := I) (M := M) g α hK hK_target]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorPrincipalForm_c_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorPrincipalForm_c_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorPrincipalForm_c_apply ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorPrincipalForm_c_apply

theorem tensorPrincipalForm_eq_scalar_metric_form
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ B : SmoothEllipticBilinearForm (Module.finrank ℝ E) (Set.univ : Set EuclN),
      B = tensorPrincipalForm (I := I) (M := M) g α hK hK_target ∧
      (∀ y ∈ K, ∀ i j : Fin (Module.finrank ℝ E),
        B.a y i j = weightedInvGramEuclid (I := I) g α i j y) ∧
      B.c = (fun _ : EuclN => (0 : ℝ)) := by
  exact ⟨tensorPrincipalForm (I := I) (M := M) g α hK hK_target, rfl,
    tensorPrincipalForm_spec (I := I) (M := M) g α hK hK_target⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorPrincipalForm_eq_scalar_metric_form then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorPrincipalForm_eq_scalar_metric_form"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorPrincipalForm_eq_scalar_metric_form ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorPrincipalForm_eq_scalar_metric_form

theorem tensorPrincipalForm_symm
    [I.Boundaryless] (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    (y : EuclN) (i j : Fin (Module.finrank ℝ E)) :
    (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).a y i j =
      (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).a y j i :=
  (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).symm y i j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorPrincipalForm_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorPrincipalForm_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorPrincipalForm_symm ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorPrincipalForm_symm

theorem tensorPrincipalForm_lam_pos
    [I.Boundaryless] (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    0 < (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).lam :=
  (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).ellipticity_pos

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorPrincipalForm_lam_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorPrincipalForm_lam_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorPrincipalForm_lam_pos ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorPrincipalForm_lam_pos

theorem tensorPrincipalForm_coercive
    [I.Boundaryless] (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    (y : EuclN) (ξ : EuclN) :
    (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).lam * ‖ξ‖ ^ 2 ≤
      ⟪ξ, DeGiorgi.matMulE
        ((tensorPrincipalForm (I := I) (M := M) g α hK hK_target).a y) ξ⟫_ℝ :=
  (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).coercive y
    (Set.mem_univ y) ξ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorPrincipalForm_coercive then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorPrincipalForm_coercive"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorPrincipalForm_coercive ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorPrincipalForm_coercive

end TensorRegularity
end Laplacian
end Analysis
end DifferentialGeometry
