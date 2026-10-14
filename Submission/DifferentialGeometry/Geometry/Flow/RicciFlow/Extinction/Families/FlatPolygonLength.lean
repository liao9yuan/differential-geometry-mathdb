import Submission.DifferentialGeometry.Geometry.Metric.Comparison.CurveLengthPartition
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.InitialRampLength

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]

theorem polygonVertex_distance_sum_le_loopLength (g : SmoothRiemannianMetric I Q)
    (γ : RegularLoop I Q) {N : ℕ} (hN : 0 < N) :
    (∑ i : Fin N, (riemannianEDistOf g (polygonVertex γ N i.val)
      (polygonVertex γ N (i.val + 1))).toReal) ≤ loopLength g γ.toContinuousLoop := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hmono : Monotone (fun i : ℕ => (i : ℝ) / N) := by
    intro i j hij
    exact div_le_div_of_nonneg_right (by exact_mod_cast hij) hNR.le
  have h := DifferentialGeometry.sum_toReal_riemannianEDistOf_le_arcLength g
    γ.contMDiff_lift (fun i : ℕ => (i : ℝ) / N) hmono N
  rw [Nat.cast_zero, zero_div, div_self hNR.ne'] at h
  have hlen : DifferentialGeometry.Geometry.Riemannian.Variation.arcLength g
      (fun t : ℝ => γ.toContinuousLoop (t : Surgery.Topology.Circle)) 0 1 =
      loopLength g γ.toContinuousLoop := by
    rw [loopLength, ← _root_.MeasureTheory.restrict_Ioc_eq_restrict_Icc,
      ← intervalIntegral.integral_of_le zero_le_one]
    rfl
  rw [hlen] at h
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ => (riemannianEDistOf g (polygonVertex γ N (k : ℤ))
      (polygonVertex γ N ((k : ℤ) + 1))).toReal)]
  simpa only [polygonVertex, Int.cast_natCast, Int.cast_add, Int.cast_one,
    Nat.cast_add, Nat.cast_one] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.polygonVertex_distance_sum_le_loopLength then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Families.polygonVertex_distance_sum_le_loopLength"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.polygonVertex_distance_sum_le_loopLength ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.polygonVertex_distance_sum_le_loopLength

variable [FiniteDimensional ℝ E] [T2Space Q] [I.Boundaryless]

theorem flatPolygon_loopLength_le (g : SmoothRiemannianMetric I Q) (P : FlatteningProfile)
    {N : ℕ} (hN : 0 < N) (γ c : RegularLoop I Q)
    (hc : ∀ z, c z = flatPolygon g P N γ z)
    (hseg : ∀ i : ℤ, 0 ≤ i → i < N → IsShortSegment g (polygonVertex γ N i)
      (polygonVertex γ N (i + 1))
      (shortSegment g (polygonVertex γ N i) (polygonVertex γ N (i + 1)))) :
    loopLength g c.toContinuousLoop ≤ loopLength g γ.toContinuousLoop := by
  rw [flatPolygon_loopLength_eq_sum g P hN γ c hc hseg]
  exact polygonVertex_distance_sum_le_loopLength g γ hN

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.flatPolygon_loopLength_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Families.flatPolygon_loopLength_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.flatPolygon_loopLength_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.flatPolygon_loopLength_le

theorem initialRamp_flatPolygon_length_le (g : SmoothRiemannianMetric I Q)
    (P : FlatteningProfile) {N : ℕ} (hN : 0 < N) (γ c : RegularLoop I Q)
    (hc : ∀ z, c z = flatPolygon g P N γ z)
    (hseg : ∀ i : ℤ, 0 ≤ i → i < N → IsShortSegment g (polygonVertex γ N i)
      (polygonVertex γ N (i + 1))
      (shortSegment g (polygonVertex γ N i) (polygonVertex γ N (i + 1))))
    (lambda t : ℝ) :
    (initialRamp c).length (fun _ => g) lambda t ≤
      loopLength g γ.toContinuousLoop + |lambda| :=
  (initialRamp_length_le g c lambda t).trans
    (add_le_add_left (flatPolygon_loopLength_le g P hN γ c hc hseg) _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.initialRamp_flatPolygon_length_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Families.initialRamp_flatPolygon_length_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.initialRamp_flatPolygon_length_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.initialRamp_flatPolygon_length_le

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families
