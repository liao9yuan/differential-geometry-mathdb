import Submission.DifferentialGeometry.Geometry.Exponential.NormalBall.Homeomorphism

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open scoped _root_.ContDiff _root_.Manifold
namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

theorem mfderiv_injective {p : M} (c : NormalBallChart (I := I) p)
    {y : M} (hy : y ∈ c.restrictBall.target) :
    Function.Injective (mfderiv 𝓘(ℝ, E) I (fun z : E => c.hom z) (c.inv y)) := by
  have hs : c.inv y ∈ c.restrictBall.source := c.restrictBall.map_target hy
  have hd := PartialDiffeomorph.isLocalDiffeomorphAt 𝓘(ℝ, E) I ∞ c.restrictBall hs
  exact (hd.mfderivToContinuousLinearEquiv (by simp)).injective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.mfderiv_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.mfderiv_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.mfderiv_injective ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.mfderiv_injective

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart
end

set_option autoImplicit false
noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.TopologicalSpace
open scoped _root_.ContDiff _root_.Manifold _root_.Topology
namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

theorem norm_mfderiv_inv_le_of_metric_lower_bound {p : M} (g : SmoothRiemannianMetric I M)
    (c : NormalBallChart (I := I) p) {y : M}
    (hy : y ∈ c.restrictBall.target)
    (hlower : ∀ w : E, (1 / 2 : ℝ) * ‖w‖ ^ 2 ≤ c.metric g (c.inv y) w w)
    (v : TangentSpace I y) :
    ‖mfderiv I (modelWithCornersSelf ℝ E) c.inv y v‖ ≤
      2 * Real.sqrt (g.inner y v v) := by
  let w : E := mfderiv I (modelWithCornersSelf ℝ E) c.inv y v
  change ‖w‖ ≤ 2 * Real.sqrt (g.inner y v v)
  have htarg : (⟨y, v⟩ : TangentBundle I M) ∈ c.tangentHome.target := by
    rw [tangentHome_target]
    exact hy
  have hright := c.tangentHome.right_inv htarg
  have hsymm : c.tangentHome.symm (⟨y, v⟩ : TangentBundle I M) = (c.inv y, w) :=
    c.tangentHome_symm_apply hy v
  have hcomp : c.tangentHome (c.inv y, w) =
      (⟨y, v⟩ : TangentBundle I M) := by
    rw [← hsymm]
    exact hright
  have hx : c.inv y ∈ Metric.ball (0 : E) c.radius := by
    exact c.restrictBall.map_target hy
  rw [c.tangentHome_apply (c.inv y, w) hx] at hcomp
  have hmetric : c.metric g (c.inv y) w w = g.inner y v v := by
    have heq := congrArg (fun z : TangentBundle I M => g.inner z.proj z.2 z.2) hcomp
    exact heq
  have hbound := hlower w
  rw [hmetric] at hbound
  have hnonneg : 0 ≤ g.inner y v v := metric_inner_self_nonneg g y v
  apply le_of_sq_le_sq _ (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
  nlinarith [Real.sq_sqrt hnonneg]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.norm_mfderiv_inv_le_of_metric_lower_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.norm_mfderiv_inv_le_of_metric_lower_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.norm_mfderiv_inv_le_of_metric_lower_bound ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.norm_mfderiv_inv_le_of_metric_lower_bound

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart
end

set_option autoImplicit false
noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.Manifold _root_.TopologicalSpace
open scoped _root_.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem tangentHome_trans_pairHome_symm_apply
    {p : M} (c : NormalBallChart (I := I) p)
    {e : OpenPartialHomeomorph (E × E) (E × E)}
    {a b : E} (ha : a ∈ Metric.ball (0 : E) c.radius)
    (hb : b ∈ Metric.ball (0 : E) c.radius)
    (hfst : (e.symm (a, b)).1 = a) :
    (c.tangentHome.symm.trans (e.trans c.pairHome)).symm
        (c.hom a, c.hom b) =
      (⟨c.hom a,
        mfderiv (modelWithCornersSelf ℝ E) I c.hom a
          (e.symm (a, b)).2⟩ : TangentBundle I M) := by
  have htan : (e.symm (a, b)).1 ∈ Metric.ball (0 : E) c.radius := by
    rwa [hfst]
  have hpairs : (a, b) ∈ c.pairHome.source := by
    rw [c.pairHome_source]
    exact ⟨ha, hb⟩
  have heq : c.pairHome.symm (c.hom a, c.hom b) = (a, b) := by
    exact c.pairHome.left_inv hpairs
  have hinner : (e.trans c.pairHome).symm (c.hom a, c.hom b) = e.symm (a, b) := by
    rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]
    change e.symm (c.pairHome.symm (c.hom a, c.hom b)) = _
    rw [heq]
  have hcomp : (c.tangentHome.symm.trans (e.trans c.pairHome)).symm
      (c.hom a, c.hom b) =
      c.tangentHome (e.symm (a, b)) := by
    rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]
    change c.tangentHome ((e.trans c.pairHome).symm (c.hom a, c.hom b)) = _
    rw [hinner]
  rw [hcomp, c.tangentHome_apply (e.symm (a, b)) htan]
  change c.tangent (e.symm (a, b)) = _
  unfold NormalBallChart.tangent
  change (⟨c.hom (e.symm (a, b)).1,
      mfderiv (modelWithCornersSelf ℝ E) I c.hom (e.symm (a, b)).1
        (e.symm (a, b)).2⟩ : TangentBundle I M) = _
  rw [hfst]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.tangentHome_trans_pairHome_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.tangentHome_trans_pairHome_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.tangentHome_trans_pairHome_symm_apply ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.tangentHome_trans_pairHome_symm_apply
end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart
end
