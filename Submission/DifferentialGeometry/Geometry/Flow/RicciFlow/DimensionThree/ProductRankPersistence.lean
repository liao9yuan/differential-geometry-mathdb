import Submission.DifferentialGeometry.Geometry.Curvature.DimensionThree.SurfaceProductRank
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.IsometryComplete
import Submission.DifferentialGeometry.Geometry.Comparison.Splitting.WarpedProduct
import Submission.DifferentialGeometry.Geometry.Metric.Pullback.ProductReal
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Set _root_.Submission.Set _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M] [ConnectedSpace M]

theorem curvatureOperatorImageAt_finrank_le_one_of_initial_product
    {D : RealTimeInterval} (S : SolutionOn (I := I.prod 𝓘(ℝ, ℝ)) (M := M × ℝ) D)
    (hS : IsSolutionOn S) (hdim : Module.finrank ℝ E = 2)
    {a₀ a b K : ℝ} (ha : a₀ < a) (hab : a < b)
    (hcarrier : _root_.Set.Icc a₀ b ⊆ D.carrier) (hregular : _root_.Set.Ioo a₀ b ⊆ D.regular)
    (hcomplete : ∀ t ∈ _root_.Set.Icc a₀ b, RiemannianMetricComplete (S.base.metric t))
    (hK : 0 ≤ K)
    (hcurvature : ∀ t ∈ _root_.Set.Icc a₀ b, ∀ x : M × ℝ,
      normSq0S (S.base.metric t) x 4 (S.base.rm04 t x) ≤ K)
    (hnonnegative : ∀ t ∈ _root_.Set.Icc a b, ∀ x : M × ℝ,
      metricAlgebraicCurvatureTensorAt (S.base.metric t) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I.prod 𝓘(ℝ, ℝ)) (M := M × ℝ))
    (g₀ : SmoothRiemannianMetric I M)
    (hinitial : S.base.metric a = g₀.prod (euclideanMetric (E := ℝ))) :
    ∀ t ∈ _root_.Set.Icc a b, ∀ x : M × ℝ,
      Module.finrank ℝ (curvatureOperatorImageAt (S.base.metric t) x
        (metricAlgebraicCurvatureTensorAt (S.base.metric t) x)) ≤ 1 := by
  let : NeZero (Module.finrank ℝ (E × ℝ)) := ⟨by simp [Module.finrank_prod, hdim]⟩
  intro t ht x
  have hcomp₀ := hcomplete a₀ ⟨le_rfl, ha.le.trans hab.le⟩
  have htranslate : ∀ c : ℝ,
      Diffeomorph.pullbackMetricCross (S.base.metric t)
        ((Diffeomorph.refl I M ∞).prodCongr (Topology.translateDiffeomorph c)) =
          S.base.metric t := by
    intro c
    apply pullbackMetricCross_eq_of_initial_isometry_of_complete_bounded_curvature
      S hS ha hab hcarrier hregular hcomp₀ hK hcurvature _ ?_ t ht
    rw [hinitial]
    exact Diffeomorph.pullbackMetricCross_prod_real_translation g₀ c
  have hreflect : Diffeomorph.pullbackMetricCross (S.base.metric t)
      ((Diffeomorph.refl I M ∞).prodCongr
        (LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ).toContinuousLinearEquiv.toDiffeomorph) =
          S.base.metric t := by
    apply pullbackMetricCross_eq_of_initial_isometry_of_complete_bounded_curvature
      S hS ha hab hcarrier hregular hcomp₀ hK hcurvature _ ?_ t ht
    rw [hinitial]
    exact Diffeomorph.pullbackMetricCross_prod_real_reflection g₀
  have heq := (S.base.metric t).eq_prod_scaled_real_of_complete_nonnegative_curvature_symmetries
    (hcomplete t ⟨ha.le.trans ht.1, ht.2⟩) (hnonnegative t ht) htranslate hreflect x.1
  rw [heq]
  exact Geometry.Curvature.DimensionThree.curvatureOperatorImageAt_finrank_prod_scaled_real_le_one
    ((S.base.metric t).sliceFst 0) hdim ((S.base.metric t).vertical_inner_pos x.1 0) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.curvatureOperatorImageAt_finrank_le_one_of_initial_product then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.curvatureOperatorImageAt_finrank_le_one_of_initial_product"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.curvatureOperatorImageAt_finrank_le_one_of_initial_product ``Submission.DifferentialGeometry.PDE.RicciFlow.curvatureOperatorImageAt_finrank_le_one_of_initial_product

end DifferentialGeometry.PDE.RicciFlow
