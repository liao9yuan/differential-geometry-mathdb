import Submission.DifferentialGeometry.Geometry.Measure.Area.ManifoldMeasurable
import Submission.DifferentialGeometry.Geometry.Measure.Area.ManifoldLipschitz

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

set_option autoImplicit false
noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Filter _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.ContDiff _root_.Topology _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

private def chartDirectionalEnergy (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (p : M)
    (ξ : E) (v : E) : ℝ :=
  g.inner ((chartAt E p).symm ξ)
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E p).symm ξ v)
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E p).symm ξ v)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.chartDirectionalEnergy
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.chartDirectionalEnergy target :: scope.openDecls } }

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem continuousOn_chartDirectionalEnergy (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (p : M) : ContinuousOn (fun q : E × E => chartDirectionalEnergy g p q.1 q.2)
      (Prod.fst ⁻¹' (chartAt E p).target) := by
  have hs := (chartAt E p).open_target
  have ht := (contMDiffOn_chart_symm (I := 𝓘(ℝ, E)) (x := p) (n := ∞)).continuousOn_tangentMapWithin
     (by simp) hs.uniqueMDiffOn
  have hv : Continuous (fun q : E × E =>
      (TotalSpace.mk' E q.1 q.2 : TangentBundle 𝓘(ℝ, E) E)) :=
    (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, E)).symm.continuous
  have hcomp := ht.comp hv.continuousOn (fun q hq => hq)
  have hd : ContinuousOn (fun q : E × E =>
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E p).symm q.1 q.2 :
        _root_.Bundle.TotalSpace E (TangentSpace 𝓘(ℝ, E) : M → Type _)))
      (Prod.fst ⁻¹' (chartAt E p).target) := by
    apply hcomp.congr
    intro q hq
    dsimp only [Function.comp_apply, tangentMapWithin]
    rw [mfderivWithin_of_mem_nhds (hs.mem_nhds hq)]
  let cg := g.toContinuousRiemannianMetric
  let : _root_.Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨cg.toRiemannianMetric⟩
  exact hd.inner_bundle hd

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.continuousOn_chartDirectionalEnergy
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.continuousOn_chartDirectionalEnergy target :: scope.openDecls } }

set_option backward.isDefEq.respectTransparency false in
private theorem metric_mfderiv_apply_eq_chart (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {u : ℂ → M} {z : ℂ} (p : M) (hu : ContinuousAt u z)
    (hp : u z ∈ (chartAt E p).source) (v : ℂ) :
    g.inner (u z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) u z v)
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) u z v) =
      chartDirectionalEnergy g p ((chartAt E p) (u z)) (fderiv ℝ ((chartAt E p) ∘ u) z v) := by
  by_cases hd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) u z
  · have hc := (mdifferentiableAt_iff_differentiableAt_chart p hu hp).mp hd
    have hi := mdifferentiableAt_atlas_symm (I := 𝓘(ℝ, E))
      (ChartedSpace.chart_mem_atlas p) ((chartAt E p).map_source hp)
    have heq := chart_reconstruction_eventuallyEq p hu hp
    unfold chartDirectionalEnergy
    conv_lhs => rw [← heq.mfderiv_eq, ← heq.eq_of_nhds]
    rw [mfderiv_comp z hi (mdifferentiableAt_iff_differentiableAt.mpr hc), mfderiv_eq_fderiv]
    rfl
  · have hc : ¬ DifferentiableAt ℝ ((chartAt E p) ∘ u) z :=
      fun h => hd ((mdifferentiableAt_iff_differentiableAt_chart p hu hp).mpr h)
    simp only [mfderiv_zero_of_not_mdifferentiableAt hd, chartDirectionalEnergy,
      fderiv_zero_of_not_differentiableAt hc, zero_apply, map_zero]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.metric_mfderiv_apply_eq_chart
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.metric_mfderiv_apply_eq_chart target :: scope.openDecls } }

variable [FiniteDimensional ℝ E]

private theorem measurable_metric_mfderiv_apply_in_chart
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : ℂ → M} (hu : Continuous u) (p : M) :
    Measurable (fun q : (fun q : ℂ × ℂ => u q.1) ⁻¹' (chartAt E p).source =>
      g.inner (u q.val.1) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) u q.val.1 q.val.2)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) u q.val.1 q.val.2)) := by
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  have hc : ContinuousOn (fun q : ℂ × ℂ => (chartAt E p) (u q.1))
      ((fun q : ℂ × ℂ => u q.1) ⁻¹' (chartAt E p).source) :=
    (chartAt E p).continuousOn.comp (hu.comp continuous_fst).continuousOn (fun _ hz => hz)
  have hd : Measurable (fun q : ℂ × ℂ => fderiv ℝ ((chartAt E p) ∘ u) q.1 q.2) :=
    ContinuousLinearMap.measurable_apply₂.comp
      (((measurable_fderiv ℝ ((chartAt E p) ∘ u)).comp measurable_fst).prodMk measurable_snd)
  have hm : Measurable (fun q : (fun q : ℂ × ℂ => u q.1) ⁻¹' (chartAt E p).source =>
      ((chartAt E p) (u q.val.1), fderiv ℝ ((chartAt E p) ∘ u) q.val.1 q.val.2)) :=
    (continuousOn_iff_continuous_domRestrict.mp hc).measurable.prodMk
      (hd.comp measurable_subtype_coe)
  have hmt := hm.subtype_mk (p := fun q : E × E => q.1 ∈ (chartAt E p).target)
    (h := fun q => (chartAt E p).map_source q.property)
  have hfinal := (continuousOn_iff_continuous_domRestrict.mp
    (continuousOn_chartDirectionalEnergy g p)).measurable.comp hmt
  convert hfinal using 1
  funext q
  exact metric_mfderiv_apply_eq_chart g p hu.continuousAt q.property q.val.2

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.measurable_metric_mfderiv_apply_in_chart
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.measurable_metric_mfderiv_apply_in_chart target :: scope.openDecls } }

theorem measurable_metric_mfderiv_apply
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : ℂ → M} (hu : Continuous u) :
    Measurable (fun q : ℂ × ℂ => g.inner (u q.1)
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) u q.1 q.2) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) u q.1 q.2)) := by
  classical
  let U : ℂ × ℂ → Set (ℂ × ℂ) := fun z =>
    (fun q : ℂ × ℂ => u q.1) ⁻¹' (chartAt E (u z.1)).source
  have hU : ∀ z, IsOpen (U z) := fun z =>
    (chartAt E (u z.1)).open_source.preimage (hu.comp continuous_fst)
  have hcover : (_root_.Set.univ : Set (ℂ × ℂ)) ⊆ ⋃ z, U z := by
    intro z _
    exact mem_iUnion.mpr ⟨z, mem_chart_source E (u z.1)⟩
  obtain ⟨r, hr, hrc⟩ := isLindelof_univ.elim_countable_subcover U hU hcover
  let : Countable r := hr.to_subtype
  have hrcover : ⋃ z : r, U z = univ := by
    apply _root_.Set.eq_univ_of_univ_subset
    intro z hz
    obtain ⟨w, hwr, hzw⟩ := mem_iUnion₂.mp (hrc hz)
    exact mem_iUnion.mpr ⟨⟨w, hwr⟩, hzw⟩
  let f : (z : r) → U z → ℝ := fun _ q => g.inner (u q.val.1)
    (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) u q.val.1 q.val.2) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) u q.val.1 q.val.2)
  have hf : ∀ z, Measurable (f z) := fun z =>
    measurable_metric_mfderiv_apply_in_chart g hu (u z.val.1)
  have heq : ∀ (i j : r) (z : ℂ × ℂ) (hi : z ∈ U i) (hj : z ∈ U j),
      f i ⟨z, hi⟩ = f j ⟨z, hj⟩ := fun _ _ _ _ _ => rfl
  have hm := measurable_liftCover (fun z : r => U z)
    (fun z => (hU z).measurableSet) f hf heq hrcover
  convert hm using 1
  funext z
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hrcover.symm ▸ _root_.Set.mem_univ z)
  exact (_root_.Set.liftCover_of_mem (S := fun z : r => U z) (f := f) hi).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.measurable_metric_mfderiv_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.measurable_metric_mfderiv_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.measurable_metric_mfderiv_apply ``Submission.DifferentialGeometry.Geometry.measurable_metric_mfderiv_apply

end DifferentialGeometry.Geometry

end

end
