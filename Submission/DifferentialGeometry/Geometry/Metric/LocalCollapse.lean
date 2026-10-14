import Submission.DifferentialGeometry.Geometry.Metric.LocalRetraction
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission









noncomputable section

open _root_.Set _root_.Filter _root_.Function _root_.Manifold _root_.Metric
open scoped _root_.Topology _root_.ContDiff _root_.Manifold

namespace DifferentialGeometry.Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem exists_smooth_local_collapse {e : M → F}
    (he : ContMDiff I 𝓘(ℝ, F) ∞ e) (hemb : _root_.Topology.IsEmbedding e)
    (p : M) (hi : _root_.Function.Injective (mfderiv I 𝓘(ℝ, F) e p)) :
    ∃ (Φ : F → F) (V : Set F), ContDiff ℝ ∞ Φ ∧
      (∀ q, Φ (e q) = e q) ∧ IsOpen V ∧ e p ∈ V ∧ _root_.Set.MapsTo Φ V (_root_.Set.range e) := by
  obtain ⟨r, U, hU, hpU, hr, hleft⟩ := exists_local_retraction_of_embedding he hemb p hi
  obtain ⟨δ, hδ, hδU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hpU)
  let χ : ContDiffBump (e p) := ⟨δ / 2, δ, half_pos hδ, half_lt_self hδ⟩
  have hsupp : tsupport χ ⊆ U := by rw [χ.tsupport_eq]; exact hδU
  let Φ : F → F := fun z => z + χ z • (e (r z) - z)
  have hΦ : ContDiff ℝ ∞ Φ := by
    apply contDiff_id.add
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ tsupport χ
    · have hrz := (hr z (hsupp hz)).contMDiffAt (hU.mem_nhds (hsupp hz))
      exact χ.contDiff.contDiffAt.smul
        ((he.contMDiffAt.comp z hrz).contDiffAt.sub contDiffAt_id)
    · apply (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hz] with y hy
      simp only [hy, Pi.zero_apply, zero_smul]
  have hfix (q : M) : Φ (e q) = e q := by
    by_cases hq : e q ∈ U
    · simp only [Φ, hleft q hq, sub_self, smul_zero, add_zero]
    · have hχ : χ (e q) = 0 := by
        by_contra hn
        exact hq (hsupp (subset_closure hn))
      simp only [Φ, hχ, zero_smul, add_zero]
  refine ⟨Φ, Metric.ball (e p) (δ / 2), hΦ, hfix,
    _root_.Metric.isOpen_ball, _root_.Metric.mem_ball_self (half_pos hδ), ?_⟩
  intro z hz
  have hχ : χ z = 1 := χ.one_of_mem_closedBall (_root_.Metric.ball_subset_closedBall hz)
  refine ⟨r z, ?_⟩
  simp only [Φ, hχ, one_smul, add_sub_cancel]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_smooth_local_collapse then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_smooth_local_collapse"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_smooth_local_collapse ``Submission.DifferentialGeometry.Geometry.exists_smooth_local_collapse

end DifferentialGeometry.Geometry
