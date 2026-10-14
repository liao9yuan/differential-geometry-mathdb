import Submission.DifferentialGeometry.Geometry.Metric.MetricGeodesic
import Mathlib.Topology.Connected.TotallyDisconnected

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.DifferentialGeometry
open scoped _root_.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]

omit [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M] in
theorem subsingleton_of_zero_model [PreconnectedSpace M]
    (h : Module.finrank ℝ E = 0) : Subsingleton M := by
  let : Subsingleton E := Module.finrank_zero_iff.mp h
  let : DiscreteTopology M := ChartedSpace.discreteTopology E M
  exact subsingleton_of_preconnected_totallyDisconnected

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.subsingleton_of_zero_model then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.subsingleton_of_zero_model"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.subsingleton_of_zero_model ``Submission.DifferentialGeometry.Geometry.subsingleton_of_zero_model



def geodesicInterpolation (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (x y : M) (t : ℝ) : M :=
  if h : Module.finrank ℝ E = 0 then x else
    letI : NeZero (Module.finrank ℝ E) := ⟨h⟩
    metricShortGeodesic g x y t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.geodesicInterpolation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.geodesicInterpolation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.geodesicInterpolation ``Submission.DifferentialGeometry.Geometry.geodesicInterpolation



theorem geodesicInterpolation_spec [PreconnectedSpace M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) :
    (∀ x y, geodesicInterpolation g x y 0 = x) ∧
    (∀ x y, riemannianEDistOf g x y ≠ ⊤ → geodesicInterpolation g x y 1 = y) ∧
    (∀ x t, geodesicInterpolation g x x t = x) ∧
    (∀ x y, riemannianEDistOf g x y ≠ ⊤ → ∀ t,
      Real.sqrt (g.inner (geodesicInterpolation g x y t)
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (geodesicInterpolation g x y) t 1)
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (geodesicInterpolation g x y) t 1)) =
          (riemannianEDistOf g x y).toReal) ∧
    ∃ (ρ : ℝ≥0) (W : Set (ℝ × (M × M))), 0 < ρ ∧ IsOpen W ∧
      (∀ t ∈ _root_.Set.Icc (0 : ℝ) 1, ∀ x y,
        riemannianEDistOf g x y ≤ (ρ : ℝ≥0∞) → (t, (x, y)) ∈ W) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓘(ℝ, E).prod 𝓘(ℝ, E))) 𝓘(ℝ, E) ∞
        (fun p : ℝ × (M × M) => geodesicInterpolation g p.2.1 p.2.2 p.1) W := by
  by_cases h : Module.finrank ℝ E = 0
  · let : Subsingleton M := subsingleton_of_zero_model h
    have hG : geodesicInterpolation g = fun x _ _ => x := by
      funext x y t
      simp only [geodesicInterpolation, dif_pos h]
    rw [hG]
    refine ⟨fun _ _ => rfl, fun _ _ _ => Subsingleton.elim _ _, fun _ _ => rfl, ?_,
      1, _root_.Set.univ, zero_lt_one, isOpen_univ, fun _ _ _ _ _ => _root_.Set.mem_univ _, ?_⟩
    · intro x y _ t
      have hxy : y = x := Subsingleton.elim _ _
      subst y
      simp only [mfderiv_const, zero_apply, map_zero, Real.sqrt_zero]
      rw [riemannianEDistOf_self, ENNReal.toReal_zero]
    · exact (contMDiff_fst.comp (I' := 𝓘(ℝ, E).prod 𝓘(ℝ, E)) contMDiff_snd).contMDiffOn
  · let : NeZero (Module.finrank ℝ E) := ⟨h⟩
    have hG : geodesicInterpolation g = metricShortGeodesic g := by
      funext x y t
      simp only [geodesicInterpolation, dif_neg h]
    rw [hG]
    exact metricShortGeodesic_spec g

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.geodesicInterpolation_spec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.geodesicInterpolation_spec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.geodesicInterpolation_spec ``Submission.DifferentialGeometry.Geometry.geodesicInterpolation_spec

end DifferentialGeometry.Geometry
