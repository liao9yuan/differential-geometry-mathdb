import Submission.DifferentialGeometry.Geometry.Neck.InsertionInput

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.TopologicalSpace _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Metric _root_.Submission.DifferentialGeometry.Topology.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff
namespace DifferentialGeometry.Geometry.Neck

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.E3 target :: scope.openDecls } }
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.IC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.IC target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Neck.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

namespace normalizedDatum

variable {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}

theorem controlledMap_isLocalDiffeomorph (d : normalizedDatum g x₀ δ k) :
    IsLocalDiffeomorph IC I ∞ d.controlledMap := by
  apply isLocalDiffeomorph_of_injective_mfderiv d.controlledMap d.controlledMap_smooth
  · intro q v w hvw
    rw [controlledMap_mfderiv, controlledMap_mfderiv] at hvw
    exact d.immersion _ hvw
  · rw [show Module.finrank ℝ E = 3 from Fact.out]
    simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledMap_isLocalDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledMap_isLocalDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledMap_isLocalDiffeomorph ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledMap_isLocalDiffeomorph

def controlledImage (d : normalizedDatum g x₀ δ k) : _root_.TopologicalSpace.Opens M :=
  d.controlledMap_isLocalDiffeomorph.image

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledImage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledImage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledImage ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledImage

theorem controlledImage_coe (d : normalizedDatum g x₀ δ k) :
    (d.controlledImage : Set M) = _root_.Set.range d.controlledMap := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledImage_coe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledImage_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledImage_coe ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledImage_coe

theorem controlledMap_mem_controlledImage (d : normalizedDatum g x₀ δ k)
    (q : openCylinder δ⁻¹) : d.controlledMap q ∈ d.controlledImage :=
  ⟨q, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledMap_mem_controlledImage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledMap_mem_controlledImage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledMap_mem_controlledImage ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledMap_mem_controlledImage

theorem center_mem_controlledImage (d : normalizedDatum g x₀ δ k) :
    x₀ ∈ d.controlledImage := by
  have hδ : 0 < δ⁻¹ := inv_pos.mpr d.precision_pos
  let q : openCylinder δ⁻¹ := ⟨(spherePoint, 0), by
    change -δ⁻¹ < 0 ∧ (0 : ℝ) < δ⁻¹
    exact ⟨neg_neg_of_pos hδ, hδ⟩⟩
  refine ⟨q, ?_⟩
  change d.map (cylinderCenter δ d.precision_pos) = x₀
  exact d.center_eq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.center_mem_controlledImage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.center_mem_controlledImage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.center_mem_controlledImage ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.center_mem_controlledImage

def controlledChart (d : normalizedDatum g x₀ δ k) :
    openCylinder δ⁻¹ ≃ₘ⟮IC, I⟯ d.controlledImage :=
  diffeomorphOntoImage d.controlledMap d.controlledMap_isLocalDiffeomorph
    d.controlledMap_isOpenEmbedding.injective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledChart ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledChart

theorem controlledChart_apply (d : normalizedDatum g x₀ δ k) (q : openCylinder δ⁻¹) :
    (d.controlledChart q : M) = d.controlledMap q := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledChart_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledChart_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledChart_apply ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledChart_apply

theorem controlledChart_symm_apply (d : normalizedDatum g x₀ δ k)
    (p : d.controlledImage) :
    d.controlledMap (d.controlledChart.symm p) = p.val :=
  diffeomorphOntoImage_symm_apply d.controlledMap d.controlledMap_isLocalDiffeomorph
    d.controlledMap_isOpenEmbedding.injective p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledChart_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledChart_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledChart_symm_apply ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledChart_symm_apply

theorem controlledChart_symm_controlledMap (d : normalizedDatum g x₀ δ k)
    (q : openCylinder δ⁻¹) :
    d.controlledChart.symm ⟨d.controlledMap q, d.controlledMap_mem_controlledImage q⟩ = q :=
  d.controlledChart.symm_apply_apply q

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledChart_symm_controlledMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledChart_symm_controlledMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledChart_symm_controlledMap ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledChart_symm_controlledMap

theorem controlledChart_mfderiv (d : normalizedDatum g x₀ δ k) (q : openCylinder δ⁻¹)
    (v : TangentSpace IC q) :
    mfderiv IC I d.controlledChart q v = mfderiv IC I d.controlledMap q v := by
  have he : (Subtype.val : d.controlledImage → M) ∘ d.controlledChart = d.controlledMap := rfl
  rw [← he, mfderiv_comp q
    (contMDiff_subtype_val.mdifferentiableAt (by decide : (∞ : ℕ∞ω) ≠ 0))
    (d.controlledChart.contMDiff.mdifferentiableAt (by decide)), mfderiv_subtype_val]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledChart_mfderiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledChart_mfderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledChart_mfderiv ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledChart_mfderiv

theorem controlledMetric_eq_pullback_controlledChart (d : normalizedDatum g x₀ δ k) :
    d.controlledMetric = Diffeomorph.pullbackMetricCross
      (scaleMetric (metricScalarAt g x₀) d.scalar_pos (g.restrictOpen d.controlledImage))
      d.controlledChart := by
  have he : d.controlledMetric = pullbackMetricOfInjectiveLocalDiffeomorph
      (scaleMetric (metricScalarAt g x₀) d.scalar_pos g) d.controlledMap
      d.controlledMap_isLocalDiffeomorph d.controlledMap_isOpenEmbedding.injective := by
    apply SmoothRiemannianMetric.ext_inner
    intro q v w
    rw [controlledMetric_inner, pullbackMetricOfInjectiveLocalDiffeomorph_inner,
      scaleMetric_inner]
  exact he.trans (pullbackMetricOfInjectiveLocalDiffeomorph_scale_eq_chart
    g d.controlledMap d.controlledMap_isLocalDiffeomorph d.controlledMap_isOpenEmbedding.injective
    (metricScalarAt g x₀) d.scalar_pos d.controlledImage d.controlledChart d.controlledChart_apply)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledMetric_eq_pullback_controlledChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledMetric_eq_pullback_controlledChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledMetric_eq_pullback_controlledChart ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledMetric_eq_pullback_controlledChart

private theorem controlledChart_mfderiv_symm (d : normalizedDatum g x₀ δ k)
    (p : d.controlledImage) (v : TangentSpace I p) :
    mfderiv IC I d.controlledChart (d.controlledChart.symm p)
      (mfderiv I IC d.controlledChart.symm p v) = v := by
  have hc := mfderiv_comp p
    (d.controlledChart.contMDiff.mdifferentiableAt (by decide : (∞ : ℕ∞ω) ≠ 0))
    (d.controlledChart.symm.contMDiff.mdifferentiableAt (by decide))
  have he : d.controlledChart ∘ d.controlledChart.symm = id :=
    funext d.controlledChart.apply_symm_apply
  rw [he, mfderiv_id] at hc
  exact (congrArg (fun f => f v) hc).symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledChart_mfderiv_symm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledChart_mfderiv_symm target :: scope.openDecls } }

theorem pullback_controlledMetric_controlledChart_symm (d : normalizedDatum g x₀ δ k) :
    Diffeomorph.pullbackMetricCross d.controlledMetric d.controlledChart.symm =
      scaleMetric (metricScalarAt g x₀) d.scalar_pos (g.restrictOpen d.controlledImage) := by
  rw [controlledMetric_eq_pullback_controlledChart]
  apply SmoothRiemannianMetric.ext_inner
  intro p v w
  rw [Diffeomorph.pullbackMetricCross_inner, Diffeomorph.pullbackMetricCross_inner,
    controlledChart_mfderiv_symm, controlledChart_mfderiv_symm,
    d.controlledChart.apply_symm_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.pullback_controlledMetric_controlledChart_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.pullback_controlledMetric_controlledChart_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.pullback_controlledMetric_controlledChart_symm ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.pullback_controlledMetric_controlledChart_symm

end normalizedDatum
end DifferentialGeometry.Geometry.Neck
