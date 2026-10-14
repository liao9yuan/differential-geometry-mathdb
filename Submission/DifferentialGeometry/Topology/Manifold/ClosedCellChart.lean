import Submission.DifferentialGeometry.Topology.Manifold.ClosedBall
import Submission.DifferentialGeometry.Topology.Manifold.ImmersionDifferential
import Mathlib.Geometry.Manifold.LocalDiffeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology.Manifold

private local instance _root_.Submission.DifferentialGeometry.Topology.Manifold.instChartedSpaceEuclideanHalfSpaceHAddNatOfNatClosedCell (m : ℕ) :
    ChartedSpace (EuclideanHalfSpace (m + 1)) (ClosedCell (m + 1)) :=
  Handle.closedCellChartedSpaceSucc m

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.instChartedSpaceEuclideanHalfSpaceHAddNatOfNatClosedCell
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.instChartedSpaceEuclideanHalfSpaceHAddNatOfNatClosedCell target :: scope.openDecls } }

private local instance _root_.Submission.DifferentialGeometry.Topology.Manifold.instIsManifoldRealEuclideanSpaceFinHAddNatOfNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceSomeENatTopClosedCell (m : ℕ) :
    IsManifold (𝓡∂ (m + 1)) ∞ (ClosedCell (m + 1)) :=
  Handle.closedCellIsManifold m

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.instIsManifoldRealEuclideanSpaceFinHAddNatOfNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceSomeENatTopClosedCell
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.instIsManifoldRealEuclideanSpaceFinHAddNatOfNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceSomeENatTopClosedCell target :: scope.openDecls } }

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

def closedCellChartMap
    (Φ : PartialDiffeomorph (𝓡 (m + 1)) I
      (EuclideanSpace ℝ (Fin (m + 1))) M ∞)
    (c : EuclideanSpace ℝ (Fin (m + 1))) (r : ℝ) : ClosedCell (m + 1) → M :=
  fun x => Φ (c + r • x.val)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.closedCellChartMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.closedCellChartMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.closedCellChartMap ``Submission.DifferentialGeometry.Topology.Manifold.closedCellChartMap

@[simp]
theorem closedCellChartMap_apply
    (Φ : PartialDiffeomorph (𝓡 (m + 1)) I
      (EuclideanSpace ℝ (Fin (m + 1))) M ∞)
    (c : EuclideanSpace ℝ (Fin (m + 1))) (r : ℝ) (x : ClosedCell (m + 1)) :
    closedCellChartMap Φ c r x = Φ (c + r • x.val) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.closedCellChartMap_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.closedCellChartMap_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.closedCellChartMap_apply ``Submission.DifferentialGeometry.Topology.Manifold.closedCellChartMap_apply

private theorem closedCellChartMap_argument_mem_source
    (Φ : PartialDiffeomorph (𝓡 (m + 1)) I
      (EuclideanSpace ℝ (Fin (m + 1))) M ∞)
    (c : EuclideanSpace ℝ (Fin (m + 1))) {r : ℝ} (hr : 0 ≤ r)
    (hsource : Metric.closedBall c r ⊆ Φ.source) (x : ClosedCell (m + 1)) :
    c + r • x.val ∈ Φ.source := by
  apply hsource
  change _root_.Dist.dist (c + r • x.val) c ≤ r
  rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
  exact (mul_le_mul_of_nonneg_left x.property hr).trans_eq (mul_one r)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.closedCellChartMap_argument_mem_source
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.closedCellChartMap_argument_mem_source target :: scope.openDecls } }

theorem contMDiff_closedCellChartMap
    (Φ : PartialDiffeomorph (𝓡 (m + 1)) I
      (EuclideanSpace ℝ (Fin (m + 1))) M ∞)
    (c : EuclideanSpace ℝ (Fin (m + 1))) {r : ℝ} (hr : 0 ≤ r)
    (hsource : Metric.closedBall c r ⊆ Φ.source) :
    ContMDiff (𝓡∂ (m + 1)) I ∞ (closedCellChartMap Φ c r) := by
  have hinc := (isSmoothEmbedding_closedCell_inclusion m).contMDiff
  have haff : ContMDiff (𝓡 (m + 1)) (𝓡 (m + 1)) ∞
      (fun z : EuclideanSpace ℝ (Fin (m + 1)) => c + r • z) :=
    (by fun_prop : ContDiff ℝ ∞
      (fun z : EuclideanSpace ℝ (Fin (m + 1)) => c + r • z)).contMDiff
  have hmap := haff.comp hinc
  intro x
  exact (Φ.contMDiffOn_toFun.contMDiffAt
    (Φ.open_source.mem_nhds (closedCellChartMap_argument_mem_source Φ c hr hsource x))).comp x
    (hmap x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.contMDiff_closedCellChartMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.contMDiff_closedCellChartMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.contMDiff_closedCellChartMap ``Submission.DifferentialGeometry.Topology.Manifold.contMDiff_closedCellChartMap

theorem injective_mfderiv_closedCellChartMap
    (Φ : PartialDiffeomorph (𝓡 (m + 1)) I
      (EuclideanSpace ℝ (Fin (m + 1))) M ∞)
    (c : EuclideanSpace ℝ (Fin (m + 1))) {r : ℝ} (hr : 0 < r)
    (hsource : Metric.closedBall c r ⊆ Φ.source) :
    ∀ x : ClosedCell (m + 1),
      Function.Injective
        (mfderiv (𝓡∂ (m + 1)) I (closedCellChartMap Φ c r) x) := by
  let A : Diffeomorph (𝓡 (m + 1)) (𝓡 (m + 1))
      (EuclideanSpace ℝ (Fin (m + 1))) (EuclideanSpace ℝ (Fin (m + 1))) ∞ :=
    { toEquiv :=
        { toFun := fun y => c + r • y
          invFun := fun y => r⁻¹ • (y - c)
          left_inv := fun y => by
            simp only [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
          right_inv := fun y => by
            simp only [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
            abel }
      contMDiff_toFun :=
        (by fun_prop : ContDiff ℝ ∞
          (fun y : EuclideanSpace ℝ (Fin (m + 1)) => c + r • y)).contMDiff
      contMDiff_invFun :=
        (by fun_prop : ContDiff ℝ ∞
          (fun y : EuclideanSpace ℝ (Fin (m + 1)) => r⁻¹ • (y - c))).contMDiff }
  let ι : ClosedCell (m + 1) → EuclideanSpace ℝ (Fin (m + 1)) := Subtype.val
  have hι : _root_.Manifold.IsSmoothEmbedding (𝓡∂ (m + 1)) (𝓡 (m + 1)) ∞ ι :=
    isSmoothEmbedding_closedCell_inclusion m
  have hAι : ContMDiff (𝓡∂ (m + 1)) (𝓡 (m + 1)) ∞ (A ∘ ι) :=
    A.contMDiff.comp hι.contMDiff
  have hmem (x : ClosedCell (m + 1)) : A (ι x) ∈ Φ.source :=
    closedCellChartMap_argument_mem_source Φ c hr.le hsource x
  have hΦ (x : ClosedCell (m + 1)) :
      ContMDiffAt (𝓡 (m + 1)) I ∞ Φ (A (ι x)) :=
    Φ.contMDiffOn_toFun.contMDiffAt (Φ.open_source.mem_nhds (hmem x))
  intro x
  have hιd : MDifferentiableAt (𝓡∂ (m + 1)) (𝓡 (m + 1)) ι x :=
    (hι.contMDiff x).mdifferentiableAt (by simp)
  have hAd : MDifferentiableAt (𝓡 (m + 1)) (𝓡 (m + 1)) A (ι x) :=
    (A.contMDiff (ι x)).mdifferentiableAt (by simp)
  have hAinj : Function.Injective (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) A (ι x)) :=
    (A.mfderivToContinuousLinearEquiv (by simp) (ι x)).injective
  have hιinj : Function.Injective (mfderiv (𝓡∂ (m + 1)) (𝓡 (m + 1)) ι x) :=
    (hι.isImmersion.isImmersionAt x).injective_mfderiv (by simp)
  have hAιinj : Function.Injective
      (mfderiv (𝓡∂ (m + 1)) (𝓡 (m + 1)) (A ∘ ι) x) := by
    rw [mfderiv_comp x hAd hιd]
    exact hAinj.comp hιinj
  have hΦinj : Function.Injective
      (mfderiv (𝓡 (m + 1)) I Φ (A (ι x))) :=
    ((Φ.isLocalDiffeomorphAt (𝓡 (m + 1)) I ∞ (hmem x)).mfderivToContinuousLinearEquiv
      (by simp)).injective
  change Function.Injective
    (mfderiv (𝓡∂ (m + 1)) I (Φ ∘ (A ∘ ι)) x)
  rw [mfderiv_comp x ((hΦ x).mdifferentiableAt (by simp))
    ((hAι x).mdifferentiableAt (by simp))]
  exact hΦinj.comp hAιinj

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.injective_mfderiv_closedCellChartMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.injective_mfderiv_closedCellChartMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.injective_mfderiv_closedCellChartMap ``Submission.DifferentialGeometry.Topology.Manifold.injective_mfderiv_closedCellChartMap

end DifferentialGeometry.Topology.Manifold
