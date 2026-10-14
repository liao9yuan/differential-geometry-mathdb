import Submission.DifferentialGeometry.Geometry.Neck.InsertionChart
import Submission.DifferentialGeometry.Geometry.Metric.DistancePullback
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CollapseDomination

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.TopologicalSpace _root_.Filter _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Metric _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ENNReal _root_.NNReal
namespace DifferentialGeometry.Geometry.Neck.normalizedDatum

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.normalizedDatum.E3 target :: scope.openDecls } }
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.IC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.normalizedDatum.IC target :: scope.openDecls } }
private abbrev EC := EuclideanSpace ℝ (Fin 2) × ℝ

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.EC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.normalizedDatum.EC target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.normalizedDatum.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}

private local instance _root_.Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.instRegularSpaceSubtypeMemOpensControlledImage (d : normalizedDatum g x₀ δ k) : RegularSpace d.controlledImage :=
  d.controlledChart.symm.toHomeomorph.isEmbedding.isInducing.regularSpace

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.instRegularSpaceSubtypeMemOpensControlledImage
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.normalizedDatum.instRegularSpaceSubtypeMemOpensControlledImage target :: scope.openDecls } }

def positiveSideCollapseMetric (d : normalizedDatum g x₀ δ k) {A : ℝ}
    (hA : 0 < A) (hAB : 2 * A < δ⁻¹) :
    SmoothRiemannianMetric (𝓡 3) (insertionBall δ⁻¹) :=
  scaleMetric (metricScalarAt g x₀)⁻¹ (inv_pos.mpr d.scalar_pos)
    (insertedMetric hA hAB d.controlledMetric_cylinder_lower.1 d.controlledMetric)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideCollapseMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideCollapseMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideCollapseMetric ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideCollapseMetric

theorem positiveSideCollapseMetric_normalization (d : normalizedDatum g x₀ δ k) {A : ℝ}
    (hA : 0 < A) (hAB : 2 * A < δ⁻¹) :
    scaleMetric (metricScalarAt g x₀) d.scalar_pos (d.positiveSideCollapseMetric hA hAB) =
      insertedMetric hA hAB d.controlledMetric_cylinder_lower.1 d.controlledMetric := by
  apply SmoothRiemannianMetric.ext_inner
  intro p v w
  simp only [positiveSideCollapseMetric, scaleMetric_inner]
  rw [← mul_assoc, mul_inv_cancel₀ d.scalar_pos.ne', one_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideCollapseMetric_normalization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideCollapseMetric_normalization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideCollapseMetric_normalization ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideCollapseMetric_normalization

def positiveSideCollapseMap (d : normalizedDatum g x₀ δ k) {A : ℝ}
    (hA : 0 < A) (hAB : 2 * A < δ⁻¹) : d.controlledImage → insertionBall δ⁻¹ :=
  collapseMap hA hAB ∘ d.controlledChart.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideCollapseMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideCollapseMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideCollapseMap ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideCollapseMap

theorem positiveSideCollapseMap_controlledMap (d : normalizedDatum g x₀ δ k) {A : ℝ}
    (hA : 0 < A) (hAB : 2 * A < δ⁻¹) (q : openCylinder δ⁻¹) :
    d.positiveSideCollapseMap hA hAB
      ⟨d.controlledMap q, d.controlledMap_mem_controlledImage q⟩ = collapseMap hA hAB q := by
  simp only [positiveSideCollapseMap, Function.comp_apply, controlledChart_symm_controlledMap]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideCollapseMap_controlledMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideCollapseMap_controlledMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideCollapseMap_controlledMap ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideCollapseMap_controlledMap

theorem positiveSideCollapseMap_retained (d : normalizedDatum g x₀ δ k) {A : ℝ}
    (hA : 0 < A) (hAB : 2 * A < δ⁻¹) (q : openCylinder δ⁻¹) (hq : 0 ≤ q.val.2) :
    (d.positiveSideCollapseMap hA hAB
      ⟨d.controlledMap q, d.controlledMap_mem_controlledImage q⟩ : E3) =
        (transitionEnd + q.val.2) • (q.val.1 : E3) := by
  rw [positiveSideCollapseMap_controlledMap]
  exact collapseMap_retained hA hAB q hq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideCollapseMap_retained then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideCollapseMap_retained"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideCollapseMap_retained ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideCollapseMap_retained

theorem positiveSideCollapseMap_collapsed (d : normalizedDatum g x₀ δ k) {A : ℝ}
    (hA : 0 < A) (hAB : 2 * A < δ⁻¹) (q : openCylinder δ⁻¹)
    (hq : q.val.2 ≤ collapseTip A) :
    (d.positiveSideCollapseMap hA hAB
      ⟨d.controlledMap q, d.controlledMap_mem_controlledImage q⟩ : E3) = 0 := by
  rw [positiveSideCollapseMap_controlledMap]
  exact collapseMap_collapsed hA hAB q hq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideCollapseMap_collapsed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideCollapseMap_collapsed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideCollapseMap_collapsed ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideCollapseMap_collapsed

theorem positiveSideCollapseMap_radial (d : normalizedDatum g x₀ δ k) {A : ℝ}
    (hA : 0 < A) (hAB : 2 * A < δ⁻¹) (q : openCylinder δ⁻¹)
    (hq : collapseTip A ≤ q.val.2) :
    (d.positiveSideCollapseMap hA hAB
      ⟨d.controlledMap q, d.controlledMap_mem_controlledImage q⟩ : E3) =
        collapseRadius A q.val.2 • (q.val.1 : E3) := by
  rw [positiveSideCollapseMap_controlledMap]
  exact collapseMap_radial hA hAB q hq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideCollapseMap_radial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideCollapseMap_radial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideCollapseMap_radial ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideCollapseMap_radial

theorem continuous_positiveSideCollapseMap (d : normalizedDatum g x₀ δ k) {A : ℝ}
    (hA : 0 < A) (hAB : 2 * A < δ⁻¹) : Continuous (d.positiveSideCollapseMap hA hAB) :=
  (continuous_collapseMap hA hAB).comp d.controlledChart.symm.contMDiff.continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.continuous_positiveSideCollapseMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.continuous_positiveSideCollapseMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.continuous_positiveSideCollapseMap ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.continuous_positiveSideCollapseMap

private theorem controlledChart_symm_edist (d : normalizedDatum g x₀ δ k)
    (p q : d.controlledImage) :
    riemannianEDistOf d.controlledMetric (d.controlledChart.symm p) (d.controlledChart.symm q) =
      ENNReal.ofReal (Real.sqrt (metricScalarAt g x₀)) *
        riemannianEDistOf (g.restrictOpen d.controlledImage) p q := by
  rw [controlledMetric_eq_pullback_controlledChart, edistOf_pullbackMetricCross,
    d.controlledChart.apply_symm_apply, d.controlledChart.apply_symm_apply, edistOf_scale]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledChart_symm_edist
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledChart_symm_edist target :: scope.openDecls } }

theorem positiveSideCollapseMap_local_intrinsic_bound (d : normalizedDatum g x₀ δ k) {A : ℝ}
    (hA : 0 < A) (hAB : 2 * A < δ⁻¹) (p : d.controlledImage) :
    ∃ L : ℝ≥0, ∃ t ∈ 𝓝 p, ∀ x ∈ t, ∀ y ∈ t,
      riemannianEDistOf (d.positiveSideCollapseMetric hA hAB)
        (d.positiveSideCollapseMap hA hAB x) (d.positiveSideCollapseMap hA hAB y) ≤
          L * riemannianEDistOf (g.restrictOpen d.controlledImage) x y := by
  obtain ⟨L, t, ht, hL⟩ := collapseMap_local_intrinsic_bound hA hAB d.controlledMetric
    (d.positiveSideCollapseMetric hA hAB) (d.controlledChart.symm p)
  refine ⟨L * Real.toNNReal (Real.sqrt (metricScalarAt g x₀)), d.controlledChart.symm ⁻¹' t,
    d.controlledChart.symm.contMDiff.continuous.continuousAt.preimage_mem_nhds ht, ?_⟩
  intro x hx y hy
  have hb := hL (d.controlledChart.symm x) hx (d.controlledChart.symm y) hy
  rw [controlledChart_symm_edist] at hb
  simpa only [positiveSideCollapseMap, Function.comp_apply, ENNReal.coe_mul,
    ENNReal.ofReal, mul_assoc] using hb

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideCollapseMap_local_intrinsic_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideCollapseMap_local_intrinsic_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideCollapseMap_local_intrinsic_bound ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideCollapseMap_local_intrinsic_bound

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem locallyLipschitz_positiveSideCollapseMap (d : normalizedDatum g x₀ δ k) {A : ℝ}
    (hA : 0 < A) (hAB : 2 * A < δ⁻¹) :
    (let s := g.restrictOpen d.controlledImage
     let cs := s.toContinuousRiemannianMetric
     letI : _root_.Bundle.RiemannianBundle (TangentSpace I : d.controlledImage → Type _) :=
       ⟨cs.toRiemannianMetric⟩
     letI : IsContinuousRiemannianBundle E (TangentSpace I : d.controlledImage → Type _) :=
       inferInstance
     letI : PseudoEMetricSpace d.controlledImage := .ofRiemannianMetric I d.controlledImage
     let h := d.positiveSideCollapseMetric hA hAB
     let ch := h.toContinuousRiemannianMetric
     letI : _root_.Bundle.RiemannianBundle (TangentSpace (𝓡 3) : insertionBall δ⁻¹ → Type _) :=
       ⟨ch.toRiemannianMetric⟩
     letI : IsContinuousRiemannianBundle E3 (TangentSpace (𝓡 3) : insertionBall δ⁻¹ → Type _) :=
       inferInstance
     letI : PseudoEMetricSpace (insertionBall δ⁻¹) := .ofRiemannianMetric (𝓡 3) (insertionBall δ⁻¹)
     LocallyLipschitz (d.positiveSideCollapseMap hA hAB)) :=
  (locallyLipschitz_iff_local_riemannianEDistOf_le (g.restrictOpen d.controlledImage)
    (d.positiveSideCollapseMetric hA hAB) (d.positiveSideCollapseMap hA hAB)).mpr
      (d.positiveSideCollapseMap_local_intrinsic_bound hA hAB)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.locallyLipschitz_positiveSideCollapseMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.locallyLipschitz_positiveSideCollapseMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.locallyLipschitz_positiveSideCollapseMap ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.locallyLipschitz_positiveSideCollapseMap

private theorem eVariationOn_eq_mul_of_edist
    {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
    (f : ℝ → X) (h : ℝ → Y) (s : Set ℝ) (c : ℝ≥0∞)
    (he : ∀ t u, _root_.EDist.edist (f t) (f u) = c * _root_.EDist.edist (h t) (h u)) :
    eVariationOn f s = c * eVariationOn h s := by
  simp only [eVariationOn, he, ← Finset.mul_sum, ENNReal.mul_iSup]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.eVariationOn_eq_mul_of_edist
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.normalizedDatum.eVariationOn_eq_mul_of_edist target :: scope.openDecls } }

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem positiveSideCollapseMap_eVariationOn_le (d : normalizedDatum g x₀ δ k) {A : ℝ}
    (hA : 0 < A) (hAB : 2 * A < δ⁻¹) (γ : ℝ → d.controlledImage)
    (a b : ℝ) (hγ : ContinuousOn γ (_root_.Set.Icc a b)) :
    (let s := g.restrictOpen d.controlledImage
     let cs := s.toContinuousRiemannianMetric
     letI : _root_.Bundle.RiemannianBundle (TangentSpace I : d.controlledImage → Type _) :=
       ⟨cs.toRiemannianMetric⟩
     letI : IsContinuousRiemannianBundle E (TangentSpace I : d.controlledImage → Type _) :=
       inferInstance
     letI : PseudoEMetricSpace d.controlledImage := .ofRiemannianMetric I d.controlledImage
     let h := d.positiveSideCollapseMetric hA hAB
     let ch := h.toContinuousRiemannianMetric
     letI : _root_.Bundle.RiemannianBundle (TangentSpace (𝓡 3) : insertionBall δ⁻¹ → Type _) :=
       ⟨ch.toRiemannianMetric⟩
     letI : IsContinuousRiemannianBundle E3 (TangentSpace (𝓡 3) : insertionBall δ⁻¹ → Type _) :=
       inferInstance
     letI : PseudoEMetricSpace (insertionBall δ⁻¹) := .ofRiemannianMetric (𝓡 3) (insertionBall δ⁻¹)
     eVariationOn (d.positiveSideCollapseMap hA hAB ∘ γ) (_root_.Set.Icc a b) ≤ eVariationOn γ (_root_.Set.Icc a b)) := by
  let s := g.restrictOpen d.controlledImage
  let n := insertedMetric hA hAB d.controlledMetric_cylinder_lower.1 d.controlledMetric
  let h := d.positiveSideCollapseMetric hA hAB
  let mi : PseudoEMetricSpace d.controlledImage := by
    let cs := s.toContinuousRiemannianMetric
    letI : _root_.Bundle.RiemannianBundle (TangentSpace I : d.controlledImage → Type _) :=
      ⟨cs.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (TangentSpace I : d.controlledImage → Type _) :=
      inferInstance
    exact .ofRiemannianMetric I d.controlledImage
  let mc : PseudoEMetricSpace (openCylinder δ⁻¹) := by
    let cc := d.controlledMetric.toContinuousRiemannianMetric
    letI : _root_.Bundle.RiemannianBundle (TangentSpace IC : openCylinder δ⁻¹ → Type _) :=
      ⟨cc.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle EC (TangentSpace IC : openCylinder δ⁻¹ → Type _) :=
      inferInstance
    exact .ofRiemannianMetric IC (openCylinder δ⁻¹)
  let mn : PseudoEMetricSpace (insertionBall δ⁻¹) := by
    let cn := n.toContinuousRiemannianMetric
    letI : _root_.Bundle.RiemannianBundle (TangentSpace (𝓡 3) : insertionBall δ⁻¹ → Type _) :=
      ⟨cn.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E3 (TangentSpace (𝓡 3) : insertionBall δ⁻¹ → Type _) :=
      inferInstance
    exact .ofRiemannianMetric (𝓡 3) (insertionBall δ⁻¹)
  let mh : PseudoEMetricSpace (insertionBall δ⁻¹) := by
    let ch := h.toContinuousRiemannianMetric
    letI : _root_.Bundle.RiemannianBundle (TangentSpace (𝓡 3) : insertionBall δ⁻¹ → Type _) :=
      ⟨ch.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E3 (TangentSpace (𝓡 3) : insertionBall δ⁻¹ → Type _) :=
      inferInstance
    exact .ofRiemannianMetric (𝓡 3) (insertionBall δ⁻¹)
  let α := ENNReal.ofReal (Real.sqrt (metricScalarAt g x₀))
  let β := ENNReal.ofReal (Real.sqrt (metricScalarAt g x₀)⁻¹)
  let ζ := d.controlledChart.symm ∘ γ
  have hζ : ContinuousOn ζ (_root_.Set.Icc a b) :=
    d.controlledChart.symm.contMDiff.continuous.comp_continuousOn hγ
  have hc := collapseMap_eVariationOn_le_of_cylinder_lower hA hAB
    d.controlledMetric_cylinder_lower.1 d.controlledMetric
    d.controlledMetric_cylinder_lower.2 ζ a b hζ
  change @eVariationOn ℝ _ (insertionBall δ⁻¹) mn (collapseMap hA hAB ∘ ζ) (_root_.Set.Icc a b) ≤
    @eVariationOn ℝ _ (openCylinder δ⁻¹) mc ζ (_root_.Set.Icc a b) at hc
  have hs : @eVariationOn ℝ _ (openCylinder δ⁻¹) mc ζ (_root_.Set.Icc a b) =
      α * @eVariationOn ℝ _ d.controlledImage mi γ (_root_.Set.Icc a b) := by
    apply @eVariationOn_eq_mul_of_edist _ _ mc mi ζ γ (_root_.Set.Icc a b) α
    intro t u
    exact controlledChart_symm_edist d (γ t) (γ u)
  have ht : @eVariationOn ℝ _ (insertionBall δ⁻¹) mh
      (d.positiveSideCollapseMap hA hAB ∘ γ) (_root_.Set.Icc a b) =
      β * @eVariationOn ℝ _ (insertionBall δ⁻¹) mn (collapseMap hA hAB ∘ ζ) (_root_.Set.Icc a b) := by
    apply @eVariationOn_eq_mul_of_edist _ _ mh mn
      (d.positiveSideCollapseMap hA hAB ∘ γ) (collapseMap hA hAB ∘ ζ) (_root_.Set.Icc a b) β
    intro t u
    exact edistOf_scale (metricScalarAt g x₀)⁻¹ (inv_pos.mpr d.scalar_pos) n
      (collapseMap hA hAB (ζ t)) (collapseMap hA hAB (ζ u))
  have hscale : β * α = 1 := by
    dsimp only [α, β]
    rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _),
      ← Real.sqrt_mul (inv_pos.mpr d.scalar_pos).le,
      inv_mul_cancel₀ d.scalar_pos.ne', Real.sqrt_one, ENNReal.ofReal_one]
  change @eVariationOn ℝ _ (insertionBall δ⁻¹) mh
    (d.positiveSideCollapseMap hA hAB ∘ γ) (_root_.Set.Icc a b) ≤
      @eVariationOn ℝ _ d.controlledImage mi γ (_root_.Set.Icc a b)
  rw [ht]
  exact (mul_right_mono hc).trans_eq (by
    dsimp only
    rw [hs, ← mul_assoc, hscale, one_mul])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideCollapseMap_eVariationOn_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideCollapseMap_eVariationOn_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideCollapseMap_eVariationOn_le ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideCollapseMap_eVariationOn_le

end DifferentialGeometry.Geometry.Neck.normalizedDatum
