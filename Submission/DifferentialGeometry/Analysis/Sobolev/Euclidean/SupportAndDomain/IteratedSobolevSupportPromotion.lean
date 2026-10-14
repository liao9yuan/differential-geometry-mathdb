import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.Density
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.MultiplyQuantK

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory _root_.Set _root_.Filter _root_.Topology
open scoped _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Euclidean

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
theorem MemWkp_of_memWkp_precompact_of_ae_zero_off_compact
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {Ω Ω' K : Set E} {u : E → ℝ}
    (hΩ_open : IsOpen Ω) (hΩ'_open : IsOpen Ω')
    (hK_compact : IsCompact K) (hKΩ' : K ⊆ Ω')
    (hΩ'_cl : closure Ω' ⊆ Ω)
    (hu_ae_zero : u =ᵐ[(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E).restrict (Ω \ K)] 0)
    (hu_precompact : MemWkp (d := d) k p u Ω') :
    MemWkp (d := d) k p u Ω := by
  classical
  have hΩ'Ω : Ω' ⊆ Ω := subset_closure.trans hΩ'_cl
  obtain ⟨δ, χ, hδ_pos, _hδ_sub, hχ_smooth, hχ_compact, _hχ_range,
      hχ_one, hχ_support⟩ :=
    exists_smooth_cutoff_with_neighborhood (d := d) hK_compact hΩ'_open hKΩ'
  set N : Set E := Metric.cthickening δ K with hN_def
  have hN_closed : IsClosed N := Metric.isClosed_cthickening
  have hN_meas : MeasurableSet N := hN_closed.measurableSet
  have hK_sub_N : K ⊆ N := Metric.self_subset_cthickening K
  set v : E → ℝ := fun x => χ x * u x with hv_def
  obtain ⟨C, _hC_nn, hC_bound⟩ :=
    exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport (d := d)
      hχ_smooth hχ_compact k
  have hv_memWkp_Ω' : MemWkp (d := d) k p v Ω' :=
    MemWkp.smul_smooth_bounded (d := d) k hp hΩ'_open hχ_smooth
      (fun j _hj x _hx => hC_bound x j _hj) hu_precompact
  have hv_tsupp : tsupport v ⊆ Ω' :=
    (tsupport_smul_subset_left χ u).trans hχ_support
  have hv_compact : HasCompactSupport v := hχ_compact.mul_right
  have hv_memWkp_Ω : MemWkp (d := d) k p v Ω :=
    MemWkp.extend_zero (d := d) hp hΩ'_open hΩ_open hΩ'Ω
      hv_memWkp_Ω' hv_tsupp hv_compact
  have hv_ae_eq_u : v =ᵐ[(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E).restrict Ω] u := by
    have h_split : Ω = (Ω ∩ N) ∪ (Ω \ N) := by
      rw [Set.inter_union_sdiff]
    have h_on_inter : v =ᵐ[(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E).restrict (Ω ∩ N)] u := by
      refine (_root_.MeasureTheory.ae_restrict_iff' (hΩ_open.measurableSet.inter hN_meas)).mpr ?_
      refine Filter.Eventually.of_forall fun x hx => ?_
      have hxN : x ∈ N := hx.2
      simp only [hv_def, hχ_one x hxN, one_mul]
    have h_on_diff : v =ᵐ[(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E).restrict (Ω \ N)] u := by
      have h_sub : Ω \ N ⊆ Ω \ K := Set.sdiff_subset_sdiff_right hK_sub_N
      have hu_zero_diff : u =ᵐ[(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E).restrict (Ω \ N)] 0 :=
        hu_ae_zero.filter_mono
          (_root_.MeasureTheory.ae_mono (Measure.restrict_mono_set _root_.MeasureTheory.MeasureSpace.volume h_sub))
      filter_upwards [hu_zero_diff] with x hx
      simp only [hv_def, hx, Pi.zero_apply, _root_.MulZeroClass.mul_zero]
    have h_union : v =ᵐ[(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E).restrict ((Ω ∩ N) ∪ (Ω \ N))] u := by
      rw [Filter.EventuallyEq, _root_.MeasureTheory.ae_restrict_union_eq]
      exact ⟨h_on_inter, h_on_diff⟩
    rwa [← h_split] at h_union
  exact (MemWkp_congr_ae (d := d) hp hΩ_open hv_ae_eq_u).mp hv_memWkp_Ω

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_of_memWkp_precompact_of_ae_zero_off_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_of_memWkp_precompact_of_ae_zero_off_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_of_memWkp_precompact_of_ae_zero_off_compact ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_of_memWkp_precompact_of_ae_zero_off_compact

end Euclidean
end Sobolev
end Analysis
end DifferentialGeometry
