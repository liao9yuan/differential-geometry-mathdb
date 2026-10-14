import Submission.DifferentialGeometry.Topology.LipschitzComposition
import Submission.DifferentialGeometry.Geometry.Metric.SmoothMapLipschitz
import Submission.DifferentialGeometry.Geometry.Metric.Distance.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.Geometry.Riemannian

open _root_.Bundle _root_.Filter _root_.Manifold _root_.Set
open scoped _root_.Manifold _root_.ContDiff _root_.Topology _root_.ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]
  {T F : Type*} [PseudoMetricSpace T] [PseudoMetricSpace F]

theorem locallyLipschitzOn_chart_prod_of_edist_bound
    (g : SmoothRiemannianMetric I M) (x : M) {W : Set E}
    (hW : W ⊆ (extChartAt I x).target) {K : Set M} {J : Set T}
    (hWK : _root_.Set.MapsTo (extChartAt I x).symm W K) {f : M × T → F}
    {C D r : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hr : 0 < r)
    (hf : ∀ y ∈ K, ∀ z ∈ K, ∀ a ∈ J, ∀ b ∈ J,
      riemannianEDistOf g y z < ENNReal.ofReal r →
      _root_.Dist.dist (f (y, a)) (f (z, b)) ≤
        C * (riemannianEDistOf g y z).toReal + D * _root_.Dist.dist a b) :
    LocallyLipschitzOn (W ×ˢ J)
      (fun z : E × T => f ((extChartAt I x).symm z.1, z.2)) := by
  let _ : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional (M := M) I
  let _ : RegularSpace M := inferInstance
  let _ : _root_.Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩
  let _ : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
  have hchart : LocallyLipschitzOn W (extChartAt I x).symm := by
    intro v hv
    have hdiff : ContMDiffWithinAt 𝓘(ℝ, E) I 1
        (extChartAt I x).symm (_root_.Set.range I) v :=
      contMDiffWithinAt_extChartAt_symm_range x (hW hv)
    obtain ⟨L, V, hV, hLV⟩ := hdiff.exists_lipschitzOnWith I.convex_range
    exact ⟨L, V, nhdsWithin_mono v (hW.trans (extChartAt_target_subset_range x)) hV, hLV⟩
  exact locallyLipschitzOn_comp_prod_of_edist_bound hchart hWK hC hD hr hf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.locallyLipschitzOn_chart_prod_of_edist_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.locallyLipschitzOn_chart_prod_of_edist_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.locallyLipschitzOn_chart_prod_of_edist_bound ``Submission.DifferentialGeometry.Geometry.Riemannian.locallyLipschitzOn_chart_prod_of_edist_bound

end DifferentialGeometry.Geometry.Riemannian
