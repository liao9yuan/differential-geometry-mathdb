import Submission.DifferentialGeometry.Geometry.Metric.CurveLengthReparametrization
import Submission.DifferentialGeometry.Geometry.Metric.LoopDistance
import Submission.DifferentialGeometry.Topology.LoopSpace.AffineLift

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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T3Space M] [PreconnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem loop_length_comp_affineCircleMap (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ : freeLoop M) {C D : ℝ≥0}
    (hγ : ∀ x y, riemannianEDistOf g (γ x) (γ y) ≤ (C : ℝ≥0∞) * _root_.EDist.edist x y)
    {ψ : ℝ → ℝ} (hc : Continuous ψ) (hm : Monotone ψ) (hp : ∀ t, ψ (t + 1) = ψ t + 1)
    (hcomp : ∀ x y, riemannianEDistOf g (γ (affineCircleMap ψ hc hp x))
      (γ (affineCircleMap ψ hc hp y)) ≤ (D : ℝ≥0∞) * _root_.EDist.edist x y) :
    riemannianCurveLength g (fun t : ℝ => γ (affineCircleMap ψ hc hp (t : loopCircle))) 0 1 =
      riemannianCurveLength g (fun t : ℝ => γ (t : loopCircle)) 0 1 := by
  let cg := g.toContinuousRiemannianMetric
  let : _root_.Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨cg.toRiemannianMetric⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  have hγ' : LipschitzWith C γ := hγ
  have hcomp' : LipschitzWith D (γ ∘ affineCircleMap ψ hc hp) := hcomp
  have hγreal : LipschitzWith C (fun t : ℝ => γ (t : loopCircle)) := by
    simpa only [mul_one, Function.comp_def] using! hγ'.comp loopCircle_projection_lipschitz
  have hcompreal : LipschitzWith D (fun t : ℝ => γ (ψ t : loopCircle)) := by
    simpa only [mul_one, Function.comp_def, affineCircleMap_coe] using!
      hcomp'.comp loopCircle_projection_lipschitz
  have hperiod : _root_.Function.Periodic (fun t : ℝ => γ (t : loopCircle)) 1 := by
    intro t
    simp only [QuotientAddGroup.mk_add, AddCircle.coe_period, add_zero]
  exact riemannianCurveLength_comp_monotone_lift g hγreal hperiod hc hm hp hcompreal

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.loop_length_comp_affineCircleMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.loop_length_comp_affineCircleMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.loop_length_comp_affineCircleMap ``Submission.DifferentialGeometry.Geometry.loop_length_comp_affineCircleMap

omit [FiniteDimensional ℝ E] [CompactSpace M] in
theorem riemannianLoopDistance_le_of_pointwise (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ δ : freeLoop M) {B : ℝ≥0}
    (h : ∀ θ, riemannianEDistOf g (γ θ) (δ θ) ≤ (B : ℝ≥0∞)) :
    riemannianLoopDistance g γ δ ≤ B := by
  apply ENNReal.coe_le_coe.mp
  rw [riemannianLoopDistance_coe]
  exact iSup_le h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianLoopDistance_le_of_pointwise then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianLoopDistance_le_of_pointwise"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianLoopDistance_le_of_pointwise ``Submission.DifferentialGeometry.Geometry.riemannianLoopDistance_le_of_pointwise

omit [FiniteDimensional ℝ E] [CompactSpace M] in
theorem loopDistance_precompose_le (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ : freeLoop M) {C B : ℝ≥0}
    (hγ : ∀ x y, riemannianEDistOf g (γ x) (γ y) ≤ (C : ℝ≥0∞) * _root_.EDist.edist x y)
    (ψ φ : C(loopCircle, loopCircle)) (h : ∀ θ, _root_.Dist.dist (ψ θ) (φ θ) ≤ B) :
    riemannianLoopDistance g (γ.comp ψ) (γ.comp φ) ≤ C * B := by
  apply riemannianLoopDistance_le_of_pointwise
  intro θ
  apply (hγ (ψ θ) (φ θ)).trans
  rw [ENNReal.coe_mul]
  apply mul_le_mul' le_rfl
  rw [edist_dist, ← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_le_ofReal (h θ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.loopDistance_precompose_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.loopDistance_precompose_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.loopDistance_precompose_le ``Submission.DifferentialGeometry.Geometry.loopDistance_precompose_le

end DifferentialGeometry.Geometry
