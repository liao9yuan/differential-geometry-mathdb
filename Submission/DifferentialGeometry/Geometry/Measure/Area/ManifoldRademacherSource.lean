import Submission.DifferentialGeometry.Geometry.Measure.Area.ManifoldLipschitz
import Submission.DifferentialGeometry.Geometry.Metric.SmoothLipschitz
import Mathlib.Geometry.Manifold.BumpFunction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission












noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry _root_.Filter _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T3Space M]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {μ : Measure V} [Measure.IsAddHaarMeasure μ]

theorem exists_open_ae_mdifferentiableAt_of_metric_lipschitz
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : V → M} {C : ℝ≥0}
    (hu : ∀ x y, riemannianEDistOf g (u x) (u y) ≤ (C : ℝ≥0∞) * _root_.EDist.edist x y)
    (z : V) : ∃ U : Set V, IsOpen U ∧ z ∈ U ∧
      ∀ᵐ w ∂μ, w ∈ U → MDifferentiableAt 𝓘(ℝ, V) 𝓘(ℝ, E) u w := by
  classical
  have huc := continuous_of_riemannian_lipschitz g hu
  let χ : SmoothBumpFunction 𝓘(ℝ, E) (u z) := Classical.choice inferInstance
  let F : M → E := fun p => χ p • (chartAt E (u z)) p
  have hF : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ F := χ.contMDiff_smul contMDiffOn_chart
  have hFc : HasCompactSupport F := χ.hasCompactSupport.smul_right
  obtain ⟨L, _, hL⟩ := exists_riemannian_lipschitz_of_contMDiff_of_hasCompactSupport
    g (hF.of_le (by simp)) hFc
  have hcomp : LipschitzWith (L * C) (F ∘ u) := by
    intro x y
    apply (hL (u x) (u y)).trans
    calc
      (L : ℝ≥0∞) * riemannianEDistOf g (u x) (u y) ≤
          (L : ℝ≥0∞) * ((C : ℝ≥0∞) * _root_.EDist.edist x y) := by gcongr; exact hu x y
      _ = (↑(L * C) : ℝ≥0∞) * _root_.EDist.edist x y := by simp only [ENNReal.coe_mul, mul_assoc]
  have hlocal : ∀ᶠ w in 𝓝 z,
      χ (u w) = 1 ∧ u w ∈ (chartAt E (u z)).source :=
    (huc.continuousAt.eventually χ.eventuallyEq_one).and
      (huc.continuousAt ((chartAt E (u z)).open_source.mem_nhds (mem_chart_source E (u z))))
  obtain ⟨U, hUsub, hUopen, hzU⟩ := mem_nhds_iff.mp hlocal
  refine ⟨U, hUopen, hzU, ?_⟩
  filter_upwards [hcomp.ae_differentiableAt] with w hw
  intro hwU
  have heq : ((chartAt E (u z)) ∘ u) =ᶠ[𝓝 w] (F ∘ u) := by
    filter_upwards [hUopen.mem_nhds hwU] with y hy
    simp only [Function.comp_apply, F, (hUsub hy).1, one_smul]
  have hchart := hw.congr_of_eventuallyEq heq
  have hi := mdifferentiableAt_atlas_symm (I := 𝓘(ℝ, E))
    (ChartedSpace.chart_mem_atlas (u z)) ((chartAt E (u z)).map_source (hUsub hwU).2)
  have hh := hi.comp w hchart.mdifferentiableAt
  apply hh.congr_of_eventuallyEq
  filter_upwards [hUopen.mem_nhds hwU] with y hy
  exact ((chartAt E (u z)).left_inv (hUsub hy).2).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_open_ae_mdifferentiableAt_of_metric_lipschitz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_open_ae_mdifferentiableAt_of_metric_lipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_open_ae_mdifferentiableAt_of_metric_lipschitz ``Submission.DifferentialGeometry.Geometry.exists_open_ae_mdifferentiableAt_of_metric_lipschitz



theorem ae_mdifferentiableAt_of_metric_lipschitz
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : V → M} {C : ℝ≥0}
    (hu : ∀ x y, riemannianEDistOf g (u x) (u y) ≤ (C : ℝ≥0∞) * _root_.EDist.edist x y) :
    ∀ᵐ z ∂μ, MDifferentiableAt 𝓘(ℝ, V) 𝓘(ℝ, E) u z := by
  classical
  choose U hUopen hzU hd using exists_open_ae_mdifferentiableAt_of_metric_lipschitz (μ := μ) g hu
  have hcover : (_root_.Set.univ : Set V) ⊆ ⋃ z, U z := by
    intro z _
    exact mem_iUnion.mpr ⟨z, hzU z⟩
  obtain ⟨r, hr, hrc⟩ := isLindelof_univ.elim_countable_subcover U hUopen hcover
  let : Countable r := hr.to_subtype
  have ha : ∀ᵐ z ∂μ, ∀ i : r, z ∈ U i → MDifferentiableAt 𝓘(ℝ, V) 𝓘(ℝ, E) u z :=
    (_root_.MeasureTheory.ae_all_iff).mpr (fun i => hd i)
  filter_upwards [ha] with z hz
  obtain ⟨i, hir, hzi⟩ := mem_iUnion₂.mp (hrc (_root_.Set.mem_univ z))
  exact hz ⟨i, hir⟩ hzi

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.ae_mdifferentiableAt_of_metric_lipschitz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.ae_mdifferentiableAt_of_metric_lipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.ae_mdifferentiableAt_of_metric_lipschitz ``Submission.DifferentialGeometry.Geometry.ae_mdifferentiableAt_of_metric_lipschitz

end DifferentialGeometry.Geometry
