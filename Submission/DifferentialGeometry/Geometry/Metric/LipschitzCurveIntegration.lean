import Submission.DifferentialGeometry.Geometry.Metric.LipschitzCurves
import Submission.DifferentialGeometry.Geometry.Metric.NeighborhoodRetraction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Submission.DifferentialGeometry _root_.Filter
open scoped _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T3Space M]

set_option backward.isDefEq.respectTransparency false in


theorem aestronglyMeasurable_riemannianCurveSpeed
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : ℝ → M} {C : ℝ≥0}
    (hγ : ∀ x y, riemannianEDistOf g (γ x) (γ y) ≤ (C : ℝ≥0∞) * _root_.EDist.edist x y) :
    AEStronglyMeasurable (riemannianCurveSpeed g γ) volume := by
  let : Nonempty M := ⟨γ 0⟩
  obtain ⟨n, e, r, U, he, _, _, hU, heU, hr, hleft⟩ :=
    exists_compact_embedding_and_retraction (E := E) (M := M)
  let B : ℝ → EuclideanSpace ℝ (Fin n) := e ∘ γ
  have hB : Continuous B := he.continuous.comp (continuous_of_riemannian_lipschitz g hγ)
  have hBU (t : ℝ) : B t ∈ U := heU (_root_.Set.mem_range_self (γ t))
  let A : ℝ → U ×ˢ (_root_.Set.univ : Set (EuclideanSpace ℝ (Fin n))) :=
    fun t => ⟨(B t, deriv B t), hBU t, _root_.Set.mem_univ _⟩
  have hA : Measurable A := (hB.measurable.prodMk (measurable_deriv B)).subtype_mk
  let N : U ×ˢ (_root_.Set.univ : Set (EuclideanSpace ℝ (Fin n))) → ℝ := fun p =>
    Real.sqrt (g.inner (r p.val.1)
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E) r p.val.1 p.val.2)
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E) r p.val.1 p.val.2))
  have hN : Continuous N :=
    continuousOn_iff_continuous_domRestrict.mp
      (continuousOn_metric_mfderiv_norm g hU (hr.of_le (by simp)))
  have heq : riemannianCurveSpeed g γ =ᵐ[_root_.MeasureTheory.MeasureSpace.volume] N ∘ A := by
    filter_upwards [ae_mdifferentiableAt_riemannian_curve g hγ] with t ht
    have hdB : DifferentiableAt ℝ B t :=
      ((he.mdifferentiableAt (by simp)).comp t ht).differentiableAt
    have hdr := ((hr _ (hBU t)).contMDiffAt (hU.mem_nhds (hBU t))).mdifferentiableAt (by simp)
    have hγeq : r ∘ B = γ := by
      funext s
      exact hleft (γ s)
    have h := riemannianCurveSpeed_comp g hdr hdB
    rw [hγeq] at h
    exact h
  exact (hN.measurable.comp hA).aestronglyMeasurable.congr heq.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.aestronglyMeasurable_riemannianCurveSpeed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.aestronglyMeasurable_riemannianCurveSpeed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.aestronglyMeasurable_riemannianCurveSpeed ``Submission.DifferentialGeometry.Geometry.aestronglyMeasurable_riemannianCurveSpeed


theorem integrableOn_riemannianCurveSpeed
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : ℝ → M} {C : ℝ≥0}
    (hγ : ∀ x y, riemannianEDistOf g (γ x) (γ y) ≤ (C : ℝ≥0∞) * _root_.EDist.edist x y)
    (s : Set ℝ) [_root_.MeasureTheory.IsFiniteMeasure (volume.restrict s)] :
    IntegrableOn (riemannianCurveSpeed g γ) s := by
  apply Integrable.mono' (_root_.MeasureTheory.integrable_const (C : ℝ))
    (aestronglyMeasurable_riemannianCurveSpeed g hγ).restrict
  exact Eventually.of_forall (fun t => by
    rw [Real.norm_eq_abs, abs_of_nonneg (riemannianCurveSpeed_nonneg g γ t)]
    exact riemannianCurveSpeed_le_of_lipschitz g hγ t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.integrableOn_riemannianCurveSpeed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.integrableOn_riemannianCurveSpeed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.integrableOn_riemannianCurveSpeed ``Submission.DifferentialGeometry.Geometry.integrableOn_riemannianCurveSpeed

end DifferentialGeometry.Geometry
