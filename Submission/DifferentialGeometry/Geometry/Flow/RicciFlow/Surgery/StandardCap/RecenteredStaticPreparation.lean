import Submission.DifferentialGeometry.Geometry.Neck.OrderReduction
import Submission.DifferentialGeometry.Geometry.Neck.Recentering
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.StaticPinchingInsertion

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.TopologicalSpace _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Neck
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
universe u v w

theorem exists_uniform_recentered_static_preparation :
    ∃ c : ℝ, 4 ≤ c ∧ ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧
      ∃ (A : ℝ) (hA : 0 < A), 2 * A < 1 / 2 ∧
      ∀ (D : ℝ), 0 < D → ∀ (m : ℕ) (ε : ℝ), 0 < ε →
      ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < 1 / 4 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ {E : Type u} {H : Type v} {M : Type w}
        [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M],
        ∀ (g : SmoothRiemannianMetric I M) (x₀ : M) (d : normalizedDatum g x₀ δ (m + 6)),
        ∀ (σ : ℝ) (hσ : σ ^ 2 = 1),
          ∃ hfit : (c * δ)⁻¹ + 1 ≤ δ⁻¹,
          ∃ d' : normalizedDatum g (d.offsetPoint hσ) (c * δ) (m + 4),
            d'.map = d.recenteringMap hσ hfit ∧ d'.retainedSide = _root_.Bool.true ∧
            |metricScalarAt g (d.offsetPoint hσ) / metricScalarAt g x₀ - 1| ≤ c * δ ∧
            ∃ out : CanonicalStaticInsertionWitness d' A hA D m ε,
              StaticInsertionAdditionalProperties C out := by
  obtain ⟨c, δrec, hc, hδrec, hrec⟩ := exists_fixed_offset_recentering.{u, v, w}
  obtain ⟨C, hC, A, hA, hsmall, hmod⟩ := exists_staticInsertion_with_additional_properties.{u, v, w}
  have hcpos : 0 < c := lt_of_lt_of_le (by norm_num) hc
  refine ⟨c, hc, C, hC, A, hA, hsmall, ?_⟩
  intro D hD m ε hε
  obtain ⟨δi, hδi, _, hinsert⟩ := hmod D hD m ε hε
  let δ₀ := _root_.Min.min δrec (_root_.Min.min (δi / c) (1 / 8))
  have hδ₀ : 0 < δ₀ := lt_min hδrec (lt_min (div_pos hδi hcpos) (by norm_num))
  refine ⟨δ₀, hδ₀, ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (by norm_num), ?_⟩
  intro δ hδ hle E H M _ _ _ _ _ I _ _ _ _ _ g x₀ d σ hσ
  have hrecSmall : δ ≤ δrec := hle.trans (min_le_left _ _)
  have hδiSmall : c * δ ≤ δi := by
    have he : δ ≤ δi / c := hle.trans ((min_le_right _ _).trans (min_le_left _ _))
    exact (mul_comm c δ) ▸ (le_div_iff₀ hcpos).mp he
  obtain ⟨hfit, drec, hmap, hside, hratio⟩ :=
    hrec E H I M g x₀ δ (m + 6) d (by omega) hrecSmall σ hσ
  let d' := drec.lowerOrder (show m + 4 ≤ m + 6 by omega)
  obtain ⟨out, hout⟩ := hinsert (c * δ) (mul_pos hcpos hδ) hδiSmall g (d.offsetPoint hσ) d'
  exact ⟨hfit, d', hmap, hside, hratio, out, hout⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_uniform_recentered_static_preparation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_uniform_recentered_static_preparation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_uniform_recentered_static_preparation ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_uniform_recentered_static_preparation
end DifferentialGeometry.PDE.RicciFlow.StandardCap
