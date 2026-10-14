import Submission.DifferentialGeometry.Geometry.Metric.CurveSpeedCalculus
import Mathlib.Analysis.Calculus.Deriv.AffineMap

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.DifferentialGeometry _root_.MeasureTheory
open scoped _root_.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Geometry

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

set_option backward.isDefEq.respectTransparency false in


theorem riemannian_edist_le_on_convex_source
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {f : V → M} {U S : Set V} {C : ℝ≥0}
    (hU : IsOpen U) (hf : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) 1 f U)
    (hSU : S ⊆ U) (hS : Convex ℝ S)
    (hC : ∀ p ∈ S, ∀ v : V,
      Real.sqrt (g.inner (f p) (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f p v)
        (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f p v)) ≤ C * ‖v‖)
    {x y : V} (hx : x ∈ S) (hy : y ∈ S) :
    riemannianEDistOf g (f x) (f y) ≤ (C : ℝ≥0∞) * _root_.EDist.edist x y := by
  let η := ContinuousAffineMap.lineMap (R := ℝ) x y
  have hη : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, V) 1 η := η.contDiff.contMDiff
  have hηS : _root_.Set.MapsTo η (_root_.Set.Icc (0 : ℝ) 1) S := hS.mapsTo_lineMap hx hy
  have hγ : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 (f ∘ η) (_root_.Set.Icc 0 1) :=
    hf.comp hη.contMDiffOn (fun t ht => hSU (hηS ht))
  have hspeed : ∀ t ∈ _root_.Set.Icc (0 : ℝ) 1,
      riemannianCurveSpeed g (f ∘ η) t ≤ (C * ‖y - x‖₊ : ℝ≥0) := by
    intro t ht
    have hdf := ((hf _ (hSU (hηS ht))).contMDiffAt
      (hU.mem_nhds (hSU (hηS ht)))).mdifferentiableAt one_ne_zero
    have hder : HasDerivAt η (y - x) t := AffineMap.hasDerivAt_lineMap
    rw [riemannianCurveSpeed_comp g hdf hder.differentiableAt, hder.deriv]
    exact hC _ (hηS ht) _
  have hlen := riemannianCurveELength_le g hspeed
  let : _root_.Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  have hd : riemannianEDistOf g (f x) (f y) ≤ riemannianCurveELength g (f ∘ η) 0 1 := by
    rw [riemannianCurveELength_eq_pathELength]
    apply _root_.Manifold.riemannianEDist_le_pathELength hγ _ _ zero_le_one
    · simp only [Function.comp_apply, η, ContinuousAffineMap.coe_lineMap_eq, AffineMap.lineMap_apply_zero]
    · simp only [Function.comp_apply, η, ContinuousAffineMap.coe_lineMap_eq, AffineMap.lineMap_apply_one]
  apply hd.trans
  simpa only [sub_zero, ENNReal.ofReal_one, mul_one, ENNReal.coe_mul,
    ← edist_nndist, ← nndist_eq_nnnorm_sub, _root_.PseudoEMetricSpace.edist_comm] using hlen

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannian_edist_le_on_convex_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannian_edist_le_on_convex_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannian_edist_le_on_convex_source ``Submission.DifferentialGeometry.Geometry.riemannian_edist_le_on_convex_source

end DifferentialGeometry.Geometry
