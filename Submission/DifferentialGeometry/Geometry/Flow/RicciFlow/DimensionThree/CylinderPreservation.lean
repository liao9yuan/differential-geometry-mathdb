import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.Cylinder
import Submission.DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureNullityRank
import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.CurvatureNullity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Connection _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Metric
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

theorem curvatureOperatorImageAt_finrank_le_one_of_initial_cylinder
    {D : RealTimeInterval} (S : SolutionOn (I := I.prod 𝓘(ℝ)) (M := M × ℝ) D)
    (hS : IsSolutionOn S) {a₀ a b : ℝ} (hbuffer : a₀ < a) (hab : a < b)
    (hslab : _root_.Set.Icc a₀ b ⊆ D.carrier) (hreg : _root_.Set.Ioc a₀ b ⊆ D.regular)
    (hcomplete : RiemannianMetricComplete (S.base.metric a₀))
    (hcurv : ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ _root_.Set.Icc a₀ b, ∀ x,
      normSq0S (S.base.metric t) x 4 (S.base.rm04 t x) ≤ K)
    (hRic : ∀ t ∈ _root_.Set.Icc a b, ∀ x (v : TangentSpace (I.prod 𝓘(ℝ)) x),
      0 ≤ ricciTensor (S.base.metric t) x v v)
    (hdim : Module.finrank ℝ E = 2)
    (g : SmoothRiemannianMetric I M) (hinitial : S.base.metric a = cylinderMetric g) :
    ∀ t ∈ _root_.Set.Icc a b, ∀ x,
      Module.finrank ℝ (curvatureOperatorImageAt (S.base.metric t) x
        (metricAlgebraicCurvatureTensorAt (S.base.metric t) x)) ≤ 1 := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hnorm := normGradSqFun_height_eq_one_of_initial_cylinder S hS hbuffer hab hslab hreg
    hcomplete hcurv hRic g hinitial
  have hparallel := covariantDerivative_gradFun_height_eq_zero_of_initial_cylinder S hS
    hbuffer hab hslab hreg hcomplete hcurv hRic g hinitial
  intro t ht x
  have hdim3 : Module.finrank ℝ (E × ℝ) = 3 := by
    rw [Module.finrank_prod, hdim, Module.finrank_self]
  have hnull : gradFun (S.base.metric t) Prod.snd x ∈
      curvatureOperatorImageAnnihilatorAt (S.base.metric t) x
        (metricAlgebraicCurvatureTensorAt (S.base.metric t) x) := by
    apply (mem_curvatureOperatorImageAnnihilatorAt_iff_tensor04StandardAt_eq_zero _ _ _ _).mpr
    intro u v w
    unfold tensor04StandardAt metricAlgebraicCurvatureTensorAt
    rw [metricRm04At_inner]
    change (S.base.metric t).inner x
      (riemannOp (LeviCivita (S.base.metric t)) x u v
        (gradFun (S.base.metric t) Prod.snd x)) w = 0
    have hz := riemannOp_apply_eq_zero_of_covApply_eq_smul
      (cov := LeviCivita (S.base.metric t))
      (LeviCivita_torsion_eq_zero (S.base.metric t))
      (Z := fun y => gradFun (S.base.metric t) Prod.snd y)
      (by simpa only [gradient_eq_gradFun] using
        gradientFun_smooth (S.base.metric t) contMDiff_snd) (c := 0)
      (fun z q => by rw [hparallel t ht z]; simp) x u v
    rw [hz]
    simp
  unfold metricAlgebraicCurvatureTensorAt
  rw [DimensionThree.curvatureOperatorImageAt_finrank_eq_of_unit_curvature_nullity
    (S.base.metric t) x hdim3 (gradFun (S.base.metric t) Prod.snd x) hnull (hnorm t ht x)]
  split <;> omega

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.curvatureOperatorImageAt_finrank_le_one_of_initial_cylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.curvatureOperatorImageAt_finrank_le_one_of_initial_cylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.curvatureOperatorImageAt_finrank_le_one_of_initial_cylinder ``Submission.DifferentialGeometry.PDE.RicciFlow.curvatureOperatorImageAt_finrank_le_one_of_initial_cylinder

end DifferentialGeometry.PDE.RicciFlow
