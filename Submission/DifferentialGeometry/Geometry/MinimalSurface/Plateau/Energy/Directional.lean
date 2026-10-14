import Submission.DifferentialGeometry.Geometry.Measure.Area.ManifoldLipschitz
import Mathlib.Analysis.Normed.Operator.Bilinear

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Filter _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.ContDiff _root_.Topology _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

def diskMapDirectionalEnergyDensity (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (U : ℂ → M) (V : ℂ → ℂ) (z : ℂ) : ℝ :=
  g.inner (U z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z (V z))
    (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z (V z))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.diskMapDirectionalEnergyDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.diskMapDirectionalEnergyDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.diskMapDirectionalEnergyDensity ``Submission.DifferentialGeometry.Geometry.diskMapDirectionalEnergyDensity

theorem diskMapDirectionalEnergyDensity_nonneg
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U : ℂ → M) (V : ℂ → ℂ) (z : ℂ) :
    0 ≤ diskMapDirectionalEnergyDensity g U V z :=
  metric_inner_self_nonneg g (U z) _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.diskMapDirectionalEnergyDensity_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.diskMapDirectionalEnergyDensity_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.diskMapDirectionalEnergyDensity_nonneg ``Submission.DifferentialGeometry.Geometry.diskMapDirectionalEnergyDensity_nonneg

private def chartDirectionalEnergyDensity (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (p : M) (ξ w : E) : ℝ :=
  g.inner ((chartAt E p).symm ξ)
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E p).symm ξ w)
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E p).symm ξ w)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.chartDirectionalEnergyDensity
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.chartDirectionalEnergyDensity target :: scope.openDecls } }

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem continuousOn_chartDirectionalEnergyDensity
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (p : M) :
    ContinuousOn (fun q : E × E => chartDirectionalEnergyDensity g p q.1 q.2)
      (Prod.fst ⁻¹' (chartAt E p).target) := by
  let cg := g.toContinuousRiemannianMetric
  let : _root_.Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨cg.toRiemannianMetric⟩
  let R : E →L[ℝ] (ℂ →L[ℝ] E) :=
    ContinuousLinearMap.smulRightL ℝ ℂ E Complex.reCLM
  let H : E × E → E × (ℂ →L[ℝ] E) := fun q => (q.1, R q.2)
  have hH : Continuous H :=
    continuous_fst.prodMk (R.continuous.comp continuous_snd)
  have hR (w : E) : R w (1 : ℂ) = w := by
    change (1 : ℂ).re • w = w
    simp
  have ht := continuousOn_chart_derivative_apply (E := E) p 1
  have hpair : ContinuousOn (fun q : E × (ℂ →L[ℝ] E) =>
      g.inner ((chartAt E p).symm q.1)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E p).symm q.1 (q.2 1))
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E p).symm q.1 (q.2 1)))
      (Prod.fst ⁻¹' (chartAt E p).target) := ht.inner_bundle ht
  have h := hpair.comp hH.continuousOn
    (fun q hq => hq)
  change ContinuousOn (fun q : E × E =>
    g.inner ((chartAt E p).symm q.1)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E p).symm q.1 (R q.2 1))
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E p).symm q.1 (R q.2 1)))
    (Prod.fst ⁻¹' (chartAt E p).target) at h
  simpa only [hR, chartDirectionalEnergyDensity] using h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.continuousOn_chartDirectionalEnergyDensity
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.continuousOn_chartDirectionalEnergyDensity target :: scope.openDecls } }

private theorem diskMapDirectionalEnergyDensity_congr
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U W : ℂ → M} {z : ℂ}
    (h : U =ᶠ[𝓝 z] W) (V : ℂ → ℂ) :
    diskMapDirectionalEnergyDensity g U V z =
      diskMapDirectionalEnergyDensity g W V z := by
  unfold diskMapDirectionalEnergyDensity
  rw [h.mfderiv_eq, h.eq_of_nhds]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.diskMapDirectionalEnergyDensity_congr
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.diskMapDirectionalEnergyDensity_congr target :: scope.openDecls } }

set_option backward.isDefEq.respectTransparency false in
private theorem diskMapDirectionalEnergyDensity_eq_chart
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {z : ℂ}
    (p : M) (hU : ContinuousAt U z) (hp : U z ∈ (chartAt E p).source)
    (V : ℂ → ℂ) :
    diskMapDirectionalEnergyDensity g U V z =
      chartDirectionalEnergyDensity g p ((chartAt E p) (U z))
        (fderiv ℝ ((chartAt E p) ∘ U) z (V z)) := by
  by_cases hd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z
  · have hc := (mdifferentiableAt_iff_differentiableAt_chart p hU hp).mp hd
    have hi := mdifferentiableAt_atlas_symm (I := 𝓘(ℝ, E))
      (ChartedSpace.chart_mem_atlas p) ((chartAt E p).map_source hp)
    have heq := chart_reconstruction_eventuallyEq p hU hp
    rw [← diskMapDirectionalEnergyDensity_congr g heq V]
    unfold diskMapDirectionalEnergyDensity chartDirectionalEnergyDensity
    rw [mfderiv_comp z hi (mdifferentiableAt_iff_differentiableAt.mpr hc),
      mfderiv_eq_fderiv]
    rfl
  · have hc : ¬ DifferentiableAt ℝ ((chartAt E p) ∘ U) z :=
      fun h => hd ((mdifferentiableAt_iff_differentiableAt_chart p hU hp).mpr h)
    simp [diskMapDirectionalEnergyDensity, chartDirectionalEnergyDensity,
      mfderiv_zero_of_not_mdifferentiableAt hd, fderiv_zero_of_not_differentiableAt hc,
      zero_apply, map_zero]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.diskMapDirectionalEnergyDensity_eq_chart
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.diskMapDirectionalEnergyDensity_eq_chart target :: scope.openDecls } }

variable [FiniteDimensional ℝ E]

private theorem measurable_diskMapDirectionalEnergyDensity_in_chart
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} (hU : Continuous U)
    {V : ℂ → ℂ} (hV : Measurable V) (p : M) :
    Measurable (fun z : U ⁻¹' (chartAt E p).source =>
      diskMapDirectionalEnergyDensity g U V z) := by
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  have hc : ContinuousOn ((chartAt E p) ∘ U) (U ⁻¹' (chartAt E p).source) :=
    (chartAt E p).continuousOn.comp hU.continuousOn (fun _ hz => hz)
  have hEval : Continuous (fun q : (ℂ →L[ℝ] E) × ℂ => q.1 q.2) :=
    continuous_fst.clm_apply continuous_snd
  have hD : Measurable (fun z => fderiv ℝ ((chartAt E p) ∘ U) z (V z)) :=
    hEval.measurable.comp ((measurable_fderiv ℝ ((chartAt E p) ∘ U)).prodMk hV)
  have hm : Measurable (fun z : U ⁻¹' (chartAt E p).source =>
      ((chartAt E p) (U z), fderiv ℝ ((chartAt E p) ∘ U) z (V z))) :=
    (continuousOn_iff_continuous_domRestrict.mp hc).measurable.prodMk
      (hD.comp measurable_subtype_coe)
  have hmt := hm.subtype_mk
    (p := fun q : E × E => q.1 ∈ (chartAt E p).target)
    (h := fun z => (chartAt E p).map_source z.property)
  have hd := (continuousOn_iff_continuous_domRestrict.mp
    (continuousOn_chartDirectionalEnergyDensity g p)).measurable.comp hmt
  convert hd using 1
  funext z
  exact diskMapDirectionalEnergyDensity_eq_chart g p hU.continuousAt z.property V

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.measurable_diskMapDirectionalEnergyDensity_in_chart
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.measurable_diskMapDirectionalEnergyDensity_in_chart target :: scope.openDecls } }

theorem measurable_diskMapDirectionalEnergyDensity
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} (hU : Continuous U)
    {V : ℂ → ℂ} (hV : Measurable V) :
    Measurable (diskMapDirectionalEnergyDensity g U V) := by
  classical
  let W : ℂ → Set ℂ := fun z => U ⁻¹' (chartAt E (U z)).source
  have hW : ∀ z, IsOpen (W z) := fun z => (chartAt E (U z)).open_source.preimage hU
  have hcover : (_root_.Set.univ : Set ℂ) ⊆ ⋃ z, W z := by
    intro z _
    exact mem_iUnion.mpr ⟨z, mem_chart_source E (U z)⟩
  obtain ⟨r, hr, hrc⟩ := isLindelof_univ.elim_countable_subcover W hW hcover
  let : Countable r := hr.to_subtype
  have hrcover : ⋃ z : r, W z = univ := by
    apply _root_.Set.eq_univ_of_univ_subset
    intro z hz
    obtain ⟨w, hwr, hzw⟩ := mem_iUnion₂.mp (hrc hz)
    exact mem_iUnion.mpr ⟨⟨w, hwr⟩, hzw⟩
  let f : (z : r) → W z → ℝ := fun _ w => diskMapDirectionalEnergyDensity g U V w
  have hf : ∀ z, Measurable (f z) := fun z =>
    measurable_diskMapDirectionalEnergyDensity_in_chart g hU hV (U z)
  have heq : ∀ (i j : r) (z : ℂ) (hi : z ∈ W i) (hj : z ∈ W j),
      f i ⟨z, hi⟩ = f j ⟨z, hj⟩ := fun _ _ _ _ _ => rfl
  have hm := measurable_liftCover (fun z : r => W z)
    (fun z => (hW z).measurableSet) f hf heq hrcover
  convert hm using 1
  funext z
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hrcover.symm ▸ _root_.Set.mem_univ z)
  exact (_root_.Set.liftCover_of_mem (S := fun z : r => W z) (f := f) hi).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.measurable_diskMapDirectionalEnergyDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.measurable_diskMapDirectionalEnergyDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.measurable_diskMapDirectionalEnergyDensity ``Submission.DifferentialGeometry.Geometry.measurable_diskMapDirectionalEnergyDensity

variable [T3Space M]

set_option backward.isDefEq.respectTransparency false in
theorem diskMapDirectionalEnergyDensity_le_of_lipschitz
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {C : ℝ≥0}
    (hU : ∀ x y, riemannianEDistOf g (U x) (U y) ≤ (C : ℝ≥0∞) * _root_.EDist.edist x y)
    (V : ℂ → ℂ) (z : ℂ) :
    diskMapDirectionalEnergyDensity g U V z ≤ ((C : ℝ) * ‖V z‖) ^ 2 := by
  by_cases hdim : Module.finrank ℝ E = 0
  · have : Subsingleton E := Module.finrank_zero_iff.mp hdim
    let : Subsingleton (TangentSpace 𝓘(ℝ, E) (U z)) := ‹Subsingleton E›
    have hzero : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z = 0 := by
      ext
      exact Subsingleton.elim _ _
    simp only [diskMapDirectionalEnergyDensity, hzero, zero_apply, map_zero]
    exact sq_nonneg _
  · let : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
    by_cases hd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z
    · have h := sqrt_metric_mfderiv_le g hU hd (V z)
      have hsq := (sq_le_sq₀ (Real.sqrt_nonneg _)
        (mul_nonneg C.coe_nonneg (norm_nonneg (V z)))).mpr h
      rw [Real.sq_sqrt (metric_inner_self_nonneg g (U z) _)] at hsq
      exact hsq
    · simp only [diskMapDirectionalEnergyDensity,
        mfderiv_zero_of_not_mdifferentiableAt hd, zero_apply, map_zero]
      exact sq_nonneg _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.diskMapDirectionalEnergyDensity_le_of_lipschitz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.diskMapDirectionalEnergyDensity_le_of_lipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.diskMapDirectionalEnergyDensity_le_of_lipschitz ``Submission.DifferentialGeometry.Geometry.diskMapDirectionalEnergyDensity_le_of_lipschitz

theorem integrableOn_diskMapDirectionalEnergyDensity_of_lipschitz
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {C : ℝ≥0}
    (hU : ∀ x y, riemannianEDistOf g (U x) (U y) ≤ (C : ℝ≥0∞) * _root_.EDist.edist x y)
    {V : ℂ → ℂ} (hV : Measurable V) (s : Set ℂ) {μ : _root_.MeasureTheory.Measure ℂ}
    [_root_.MeasureTheory.IsFiniteMeasure (μ.restrict s)] {B : ℝ≥0}
    (hbound : ∀ᵐ z ∂μ.restrict s, ‖V z‖ ≤ B) :
    IntegrableOn (diskMapDirectionalEnergyDensity g U V) s μ := by
  have hm := measurable_diskMapDirectionalEnergyDensity g
    (continuous_of_riemannian_lipschitz g hU) hV
  apply Integrable.mono' (_root_.MeasureTheory.integrable_const (((C : ℝ) * B) ^ 2)) hm.aestronglyMeasurable
  filter_upwards [hbound] with z hz
  rw [Real.norm_eq_abs, abs_of_nonneg (diskMapDirectionalEnergyDensity_nonneg g U V z)]
  apply (diskMapDirectionalEnergyDensity_le_of_lipschitz g hU V z).trans
  exact pow_le_pow_left₀ (mul_nonneg C.coe_nonneg (norm_nonneg (V z)))
    (mul_le_mul_of_nonneg_left hz C.coe_nonneg) 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.integrableOn_diskMapDirectionalEnergyDensity_of_lipschitz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.integrableOn_diskMapDirectionalEnergyDensity_of_lipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.integrableOn_diskMapDirectionalEnergyDensity_of_lipschitz ``Submission.DifferentialGeometry.Geometry.integrableOn_diskMapDirectionalEnergyDensity_of_lipschitz

end DifferentialGeometry.Geometry
