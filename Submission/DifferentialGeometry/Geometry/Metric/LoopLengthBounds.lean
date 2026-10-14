import Submission.DifferentialGeometry.Geometry.Metric.CurveVariation
import Submission.DifferentialGeometry.Geometry.Metric.LoopDistance
import Submission.DifferentialGeometry.Topology.LoopSpace.Lipschitz

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.DifferentialGeometry _root_.Function
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]


theorem riemannianCurveSpeed_const (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (q : M) (t : ℝ) :
    riemannianCurveSpeed g (fun _ => q) t = 0 := by
  unfold riemannianCurveSpeed
  rw [mfderiv_const]
  change Real.sqrt (g.inner q 0 0) = 0
  simp only [map_zero, Real.sqrt_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianCurveSpeed_const then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianCurveSpeed_const"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianCurveSpeed_const ``Submission.DifferentialGeometry.Geometry.riemannianCurveSpeed_const


theorem riemannianCurveLength_const (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (q : M) (a b : ℝ) : riemannianCurveLength g (fun _ => q) a b = 0 := by
  simp [riemannianCurveLength, riemannianCurveELength, riemannianCurveSpeed_const]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianCurveLength_const then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianCurveLength_const"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianCurveLength_const ``Submission.DifferentialGeometry.Geometry.riemannianCurveLength_const

variable [FiniteDimensional ℝ E] [CompactSpace M] [T3Space M] [PreconnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem loopPoint_edist_le_length (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ : freeLoop M) {C : ℝ≥0}
    (hγ : ∀ x y, riemannianEDistOf g (γ x) (γ y) ≤ (C : ℝ≥0∞) * _root_.EDist.edist x y)
    (θ : loopCircle) :
    riemannianEDistOf g (γ 0) (γ θ) ≤
      ENNReal.ofReal (riemannianCurveLength g (fun t => γ (t : loopCircle)) 0 1) := by
  let cg := g.toContinuousRiemannianMetric
  let : _root_.Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨cg.toRiemannianMetric⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  have hγ' : LipschitzWith C γ := hγ
  have hr : LipschitzWith C (fun t : ℝ => γ (t : loopCircle)) := by
    simpa only [mul_one, Function.comp_def] using! hγ'.comp loopCircle_projection_lipschitz
  have hvar := riemannianCurveVariation_eq_elength g hr 0 1
  change eVariationOn (fun t : ℝ => γ (t : loopCircle)) (_root_.Set.Icc 0 1) =
    riemannianCurveELength g (fun t => γ (t : loopCircle)) 0 1 at hvar
  rw [riemannianCurveLength,
    ENNReal.ofReal_toReal (riemannianCurveELength_ne_top_of_lipschitz g hr 0 1), ← hvar]
  let a := AddCircle.equivIco (1 : ℝ) 0 θ
  have ha : (a.val : loopCircle) = θ := AddCircle.coe_equivIco
  have hamem : a.val ∈ _root_.Set.Icc (0 : ℝ) 1 := ⟨a.property.1, by simpa only [zero_add] using a.property.2.le⟩
  change _root_.EDist.edist (γ 0) (γ θ) ≤ _
  rw [← ha]
  exact eVariationOn.edist_le (fun t : ℝ => γ (t : loopCircle))
    (x := 0) (y := a.val) ⟨le_rfl, zero_le_one⟩ hamem

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.loopPoint_edist_le_length then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.loopPoint_edist_le_length"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.loopPoint_edist_le_length ``Submission.DifferentialGeometry.Geometry.loopPoint_edist_le_length



theorem loopDistance_from_constant_le_length (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ : freeLoop M) {C : ℝ≥0}
    (hγ : ∀ x y, riemannianEDistOf g (γ x) (γ y) ≤ (C : ℝ≥0∞) * _root_.EDist.edist x y) :
    (riemannianLoopDistance g (ContinuousMap.const loopCircle (γ 0)) γ : ℝ) ≤
      riemannianCurveLength g (fun t => γ (t : loopCircle)) 0 1 := by
  have h : (riemannianLoopDistance g (ContinuousMap.const loopCircle (γ 0)) γ : ℝ≥0∞) ≤
      ENNReal.ofReal (riemannianCurveLength g (fun t => γ (t : loopCircle)) 0 1) := by
    rw [riemannianLoopDistance_coe]
    exact iSup_le (fun θ => loopPoint_edist_le_length g γ hγ θ)
  have h' := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  simpa only [ENNReal.coe_toReal,
    ENNReal.toReal_ofReal (riemannianCurveLength_nonneg g _ _ _)] using h'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.loopDistance_from_constant_le_length then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.loopDistance_from_constant_le_length"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.loopDistance_from_constant_le_length ``Submission.DifferentialGeometry.Geometry.loopDistance_from_constant_le_length

end DifferentialGeometry.Geometry
