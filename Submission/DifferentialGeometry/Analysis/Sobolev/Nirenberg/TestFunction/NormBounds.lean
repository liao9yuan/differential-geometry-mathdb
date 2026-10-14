import Submission.DifferentialGeometry.Analysis.Sobolev.Tools.DiffQuotLocal
import Submission.DifferentialGeometry.Analysis.Sobolev.Nirenberg.TestFunction.Sobolev
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolevQuant

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergCrossBoundsNonSmooth

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem eLpNorm_translate_two_eq (k : Fin d) (h : ℝ) (u : E → ℝ) :
    eLpNorm (translate k h u) 2 _root_.MeasureTheory.MeasureSpace.volume = _root_.MeasureTheory.eLpNorm u 2 volume := by
  let τ : E ≃ₜ E := Homeomorph.addRight (h • EuclideanSpace.single k 1)
  have hMP : _root_.MeasureTheory.MeasurePreserving τ _root_.MeasureTheory.MeasureSpace.volume volume := by
    change _root_.MeasureTheory.MeasurePreserving (fun x : E => x + h • EuclideanSpace.single k 1) _root_.MeasureTheory.MeasureSpace.volume _root_.MeasureTheory.MeasureSpace.volume
    exact _root_.MeasureTheory.measurePreserving_add_right _root_.MeasureTheory.MeasureSpace.volume _
  change _root_.MeasureTheory.eLpNorm (u ∘ τ) 2 _root_.MeasureTheory.MeasureSpace.volume = _root_.MeasureTheory.eLpNorm u 2 _root_.MeasureTheory.MeasureSpace.volume
  calc
    eLpNorm (u ∘ τ) 2 _root_.MeasureTheory.MeasureSpace.volume = _root_.MeasureTheory.eLpNorm u 2 (Measure.map τ _root_.MeasureTheory.MeasureSpace.volume) :=
      (τ.measurableEmbedding.eLpNorm_map_measure (g := u) (p := 2)).symm
    _ = _root_.MeasureTheory.eLpNorm u 2 volume := by rw [hMP.map_eq]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.eLpNorm_translate_two_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Euclidean.eLpNorm_translate_two_eq target :: scope.openDecls } }

private theorem eLpNorm_diffQuot_le_inv
    (k : Fin d) (h : ℝ) {u : E → ℝ} (hu : _root_.MeasureTheory.AEStronglyMeasurable u _root_.MeasureTheory.MeasureSpace.volume) :
    _root_.MeasureTheory.eLpNorm (diffQuot k h u) 2 _root_.MeasureTheory.MeasureSpace.volume ≤
      ENNReal.ofReal (2 * |h⁻¹|) * _root_.MeasureTheory.eLpNorm u 2 volume := by
  by_cases hh : h = 0
  · simp [hh]
  have heq : diffQuot k h u = h⁻¹ • (translate k h u - u) := by
    funext x
    simp only [diffQuot_apply_of_ne k hh, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
      translate, div_eq_mul_inv, mul_comm]
  have hMP : _root_.MeasureTheory.MeasurePreserving (fun x : E => x + h • EuclideanSpace.single k 1)
      volume volume := _root_.MeasureTheory.measurePreserving_add_right _root_.MeasureTheory.MeasureSpace.volume _
  have ht : _root_.MeasureTheory.AEStronglyMeasurable (translate k h u) volume :=
    hu.comp_measurePreserving hMP
  have hnorm := eLpNorm_translate_two_eq k h u
  rw [heq, _root_.MeasureTheory.eLpNorm_const_smul, Real.enorm_eq_ofReal_abs]
  calc
    ENNReal.ofReal |h⁻¹| * _root_.MeasureTheory.eLpNorm (translate k h u - u) 2 _root_.MeasureTheory.MeasureSpace.volume ≤
        ENNReal.ofReal |h⁻¹| * (_root_.MeasureTheory.eLpNorm u 2 _root_.MeasureTheory.MeasureSpace.volume + _root_.MeasureTheory.eLpNorm u 2 _root_.MeasureTheory.MeasureSpace.volume) :=
      mul_le_mul' le_rfl (by simpa only [hnorm] using _root_.MeasureTheory.eLpNorm_sub_le ht hu (by norm_num : (1 : ℝ≥0∞) ≤ 2))
    _ = ENNReal.ofReal (2 * |h⁻¹|) * _root_.MeasureTheory.eLpNorm u 2 volume := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, ← two_mul]
      ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.eLpNorm_diffQuot_le_inv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Euclidean.eLpNorm_diffQuot_le_inv target :: scope.openDecls } }

theorem memWkp_diffQuot_one_two
    {u : E → ℝ} (hu : MemWkp 1 2 u _root_.Set.univ) (k : Fin d) (h : ℝ) :
    MemWkp 1 2 (diffQuot k h u) univ := by
  have huLp : _root_.MeasureTheory.MemLp u 2 volume := by simpa only [Measure.restrict_univ] using hu.memLp
  apply MemWkp.one_iff_memW1p.mpr
  refine ⟨?_, fun j => ?_⟩
  · simpa only [Measure.restrict_univ] using memLp_diffQuot_two k h huLp
  let g := chosenWeakPartialOrZero 2 j u _root_.Set.univ
  have hgLp : _root_.MeasureTheory.MemLp g 2 volume := by
    simpa only [Measure.restrict_univ] using chosenWeakPartialOrZero_memLp_of_mem hu.memW1p j
  refine ⟨diffQuot k h g, ?_, ?_⟩
  · simpa only [Measure.restrict_univ] using memLp_diffQuot_two k h hgLp
  · exact hasWeakPartialDeriv_diffQuot k j h
      (hu.memLp.locallyIntegrable (by norm_num))
      ((chosenWeakPartialOrZero_memLp_of_mem hu.memW1p j).locallyIntegrable (by norm_num))
      (chosenWeakPartialOrZero_isWeakPartial_of_mem hu.memW1p j)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.memWkp_diffQuot_one_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.memWkp_diffQuot_one_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.memWkp_diffQuot_one_two ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.memWkp_diffQuot_one_two

theorem chosenWeakPartialOrZero_diffQuot_ae
    {u : E → ℝ} (hu : MemWkp 1 2 u _root_.Set.univ) (k j : Fin d) (h : ℝ) :
    chosenWeakPartialOrZero 2 j (diffQuot k h u) _root_.Set.univ =ᵐ[_root_.MeasureTheory.MeasureSpace.volume]
      diffQuot k h (chosenWeakPartialOrZero 2 j u _root_.Set.univ) := by
  have hq := memWkp_diffQuot_one_two hu k h
  have hg := chosenWeakPartialOrZero_memLp_of_mem hu.memW1p j
  have hgLp : _root_.MeasureTheory.MemLp (chosenWeakPartialOrZero 2 j u _root_.Set.univ) 2 volume := by
    simpa only [Measure.restrict_univ] using hg
  have hqg : _root_.MeasureTheory.MemLp (diffQuot k h (chosenWeakPartialOrZero 2 j u _root_.Set.univ)) 2
      (volume.restrict _root_.Set.univ) := by
    simpa only [Measure.restrict_univ] using memLp_diffQuot_two k h hgLp
  have heq := DeGiorgi.HasWeakPartialDeriv.ae_eq isOpen_univ
    (chosenWeakPartialOrZero_isWeakPartial_of_mem hq.memW1p j)
    (hasWeakPartialDeriv_diffQuot k j h
      (hu.memLp.locallyIntegrable (by norm_num)) (hg.locallyIntegrable (by norm_num))
      (chosenWeakPartialOrZero_isWeakPartial_of_mem hu.memW1p j))
    ((chosenWeakPartialOrZero_memLp_of_mem hq.memW1p j).locallyIntegrable (by norm_num))
    (hqg.locallyIntegrable (by norm_num))
  simpa only [Measure.restrict_univ] using heq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartialOrZero_diffQuot_ae then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartialOrZero_diffQuot_ae"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartialOrZero_diffQuot_ae ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartialOrZero_diffQuot_ae

theorem wkpNorm_diffQuot_one_two_le
    {u : E → ℝ} (hu : MemWkp 1 2 u _root_.Set.univ) (k : Fin d) (h : ℝ) :
    iteratedWeakSobolevNorm 1 2 (diffQuot k h u) _root_.Set.univ ≤
      ENNReal.ofReal (2 * |h⁻¹|) * iteratedWeakSobolevNorm 1 2 u univ := by
  classical
  rw [wkpNorm_succ_eq_eLpNorm_add_sum_partial 0, wkpNorm_succ_eq_eLpNorm_add_sum_partial 0]
  simp only [wkpNorm_zero, Measure.restrict_univ, mul_add, Finset.mul_sum]
  apply add_le_add
  · apply eLpNorm_diffQuot_le_inv
    simpa only [Measure.restrict_univ] using hu.memLp.aestronglyMeasurable
  · apply Finset.sum_le_sum
    intro j _
    rw [_root_.MeasureTheory.eLpNorm_congr_ae (chosenWeakPartialOrZero_diffQuot_ae hu k j h)]
    apply eLpNorm_diffQuot_le_inv
    simpa only [Measure.restrict_univ] using
      (chosenWeakPartialOrZero_memLp_of_mem hu.memW1p j).aestronglyMeasurable

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_diffQuot_one_two_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_diffQuot_one_two_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_diffQuot_one_two_le ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_diffQuot_one_two_le

theorem exists_wkpNorm_nirenbergTestFunction_le
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    : ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : Fin d) (h : ℝ) {u : E → ℝ}, MemWkp 1 2 u _root_.Set.univ →
      iteratedWeakSobolevNorm 1 2 (nirenbergTestFunction k h η u) _root_.Set.univ ≤
        ENNReal.ofReal (C * |h⁻¹| ^ 2) * iteratedWeakSobolevNorm 1 2 u univ := by
  have hηsq : ContDiff ℝ (⊤ : ℕ∞) (fun x => (η x) ^ 2) := hη.pow 2
  have hηsqc : HasCompactSupport (fun x => (η x) ^ 2) := by
    exact hηc.comp_left (g := fun y : ℝ => y ^ 2) (by simp)
  obtain ⟨B, hB, hBd⟩ := exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport hηsq hηsqc 1
  obtain ⟨K, hK, hKb⟩ := wkpNorm_smul_smooth_bounded_le_one 1 le_rfl
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num : (2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞))
    isOpen_univ hηsq hB (fun j hj x _ => hBd x j hj)
  refine ⟨4 * K, by positivity, ?_⟩
  intro k h u hu
  have hq := memWkp_diffQuot_one_two hu k h
  have hmul : MemWkp 1 2 (fun x => (η x)^2 * diffQuot k h u x) univ :=
    hq.smul_smooth_bounded 1 (by norm_num) isOpen_univ hηsq
      (fun j hj x _ => hBd x j hj)
  unfold nirenbergTestFunction
  calc
    iteratedWeakSobolevNorm 1 2
        (diffQuot k (-h) (fun x => (η x)^2 * diffQuot k h u x)) _root_.Set.univ ≤
        ENNReal.ofReal (2 * |(-h)⁻¹|) * iteratedWeakSobolevNorm 1 2
          (fun x => (η x)^2 * diffQuot k h u x) univ :=
      wkpNorm_diffQuot_one_two_le hmul k (-h)
    _ ≤ ENNReal.ofReal (2 * |(-h)⁻¹|) * (ENNReal.ofReal K *
        (ENNReal.ofReal (2 * |h⁻¹|) * iteratedWeakSobolevNorm 1 2 u _root_.Set.univ)) :=
      mul_le_mul' le_rfl ((hKb hq).trans (mul_le_mul' le_rfl
        (wkpNorm_diffQuot_one_two_le hu k h)))
    _ = ENNReal.ofReal ((4 * K) * |h⁻¹| ^ 2) *
        iteratedWeakSobolevNorm 1 2 u univ := by
      rw [inv_neg, abs_neg]
      have hfactor : ENNReal.ofReal ((2 * |h⁻¹|) * K * (2 * |h⁻¹|)) =
          ENNReal.ofReal (2 * |h⁻¹|) * ENNReal.ofReal K * ENNReal.ofReal (2 * |h⁻¹|) := by
        rw [ENNReal.ofReal_mul (mul_nonneg (by positivity) hK.le),
          ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * |h⁻¹|)]
      rw [show (4 * K) * |h⁻¹| ^ 2 = (2 * |h⁻¹|) * K * (2 * |h⁻¹|) by ring, hfactor]
      simp only [mul_assoc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_wkpNorm_nirenbergTestFunction_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_wkpNorm_nirenbergTestFunction_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_wkpNorm_nirenbergTestFunction_le ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_wkpNorm_nirenbergTestFunction_le

theorem exists_wkpNorm_nirenbergTestFunction_le_local
    {Ω : Set E} (hΩ : IsOpen Ω) {η : E → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    {r : ℝ} (hηs : Metric.cthickening r (tsupport η) ⊆ Ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : Fin d) (h : ℝ), |h| ≤ r →
      ∀ {u : E → ℝ}, MemWkp 1 2 u Ω →
      iteratedWeakSobolevNorm 1 2 (nirenbergTestFunction k h η u) _root_.Set.univ ≤
        ENNReal.ofReal (C * |h⁻¹| ^ 2) * iteratedWeakSobolevNorm 1 2 u Ω := by
  obtain ⟨δ, χ, _, _, hχ, hχc, _, hχone, hχs⟩ :=
    exists_smooth_cutoff_with_neighborhood (hηc.cthickening (r := r)) hΩ hηs
  obtain ⟨B, hB, hBd⟩ := exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport hχ hχc 1
  obtain ⟨K, hK, hKb⟩ := wkpNorm_smul_smooth_bounded_le_one 1 le_rfl
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num : (2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞))
    hΩ hχ hB (fun j hj x _ => hBd x j hj)
  obtain ⟨L, hL, hLb⟩ := exists_wkpNorm_nirenbergTestFunction_le hη hηc
  refine ⟨L * K, mul_nonneg hL hK.le, ?_⟩
  intro k h hh u hu
  have hv : MemWkp 1 2 (fun x => χ x * u x) Ω :=
    hu.smul_smooth_bounded 1 (by norm_num) hΩ hχ (fun j hj x _ => hBd x j hj)
  have hvs : tsupport (fun x => χ x * u x) ⊆ Ω :=
    (tsupport_smul_subset_left χ u).trans hχs
  have hvc : HasCompactSupport (fun x => χ x * u x) := hχc.mul_right
  have hvu := hv.extend_zero (by norm_num) hΩ isOpen_univ (_root_.Set.subset_univ _) hvs hvc
  have heq : nirenbergTestFunction k h η u =
      nirenbergTestFunction k h η (fun x => χ x * u x) := by
    apply nirenbergTestFunction_congr_of_eqOn_cthickening
    intro x hx
    have hxr := Metric.cthickening_mono hh (tsupport η) hx
    simp only [hχone x (Metric.self_subset_cthickening _ hxr), one_mul]
  rw [heq]
  calc
    iteratedWeakSobolevNorm 1 2 (nirenbergTestFunction k h η (fun x => χ x * u x)) _root_.Set.univ ≤
        ENNReal.ofReal (L * |h⁻¹| ^ 2) * iteratedWeakSobolevNorm 1 2 (fun x => χ x * u x) univ :=
      hLb k h hvu
    _ = ENNReal.ofReal (L * |h⁻¹| ^ 2) * iteratedWeakSobolevNorm 1 2 (fun x => χ x * u x) Ω := by
      rw [wkpNorm_extend_zero (by norm_num) hΩ isOpen_univ (_root_.Set.subset_univ _) hv hvs hvc]
    _ ≤ ENNReal.ofReal (L * |h⁻¹| ^ 2) * (ENNReal.ofReal K * iteratedWeakSobolevNorm 1 2 u Ω) :=
      mul_le_mul' le_rfl (hKb hu)
    _ = ENNReal.ofReal ((L * K) * |h⁻¹| ^ 2) * iteratedWeakSobolevNorm 1 2 u Ω := by
      rw [show (L * K) * |h⁻¹| ^ 2 = (L * |h⁻¹| ^ 2) * K by ring,
        ENNReal.ofReal_mul (mul_nonneg hL (sq_nonneg _))]
      simp only [mul_assoc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_wkpNorm_nirenbergTestFunction_le_local then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_wkpNorm_nirenbergTestFunction_le_local"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_wkpNorm_nirenbergTestFunction_le_local ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_wkpNorm_nirenbergTestFunction_le_local

end DifferentialGeometry.Analysis.Sobolev.Euclidean


namespace DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem diffQuot_congr_ae (k : Fin d) (h : ℝ) {u v : E → ℝ}
    (huv : u =ᵐ[_root_.MeasureTheory.MeasureSpace.volume] v) : diffQuot k h u =ᵐ[_root_.MeasureTheory.MeasureSpace.volume] diffQuot k h v := by
  have hs : (fun x : E => u (x + h • EuclideanSpace.single k 1)) =ᵐ[_root_.MeasureTheory.MeasureSpace.volume]
      (fun x : E => v (x + h • EuclideanSpace.single k 1)) :=
    (_root_.MeasureTheory.measurePreserving_add_right _root_.MeasureTheory.MeasureSpace.volume (h • EuclideanSpace.single k (1 : ℝ))).quasiMeasurePreserving.ae_eq huv
  filter_upwards [huv, hs] with x hx hsx
  simp only [diffQuot, hx, hsx]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.diffQuot_congr_ae
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.diffQuot_congr_ae target :: scope.openDecls } }

theorem nirenbergTestFunction_congr_ae (k : Fin d) (h : ℝ) (η : E → ℝ) {u v : E → ℝ}
    (huv : u =ᵐ[_root_.MeasureTheory.MeasureSpace.volume] v) :
    nirenbergTestFunction k h η u =ᵐ[_root_.MeasureTheory.MeasureSpace.volume] nirenbergTestFunction k h η v := by
  apply diffQuot_congr_ae
  filter_upwards [diffQuot_congr_ae k h huv] with x hx
  rw [hx]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction_congr_ae then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction_congr_ae"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction_congr_ae ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction_congr_ae

theorem nirenbergTestFunction_congr_ae_local
    {Ω : Set E} (hΩ : MeasurableSet Ω) (k : Fin d) (h : ℝ) (η : E → ℝ)
    (hηs : Metric.cthickening |h| (tsupport η) ⊆ Ω) {u v : E → ℝ}
    (huv : u =ᵐ[volume.restrict Ω] v) :
    nirenbergTestFunction k h η u =ᵐ[_root_.MeasureTheory.MeasureSpace.volume] nirenbergTestFunction k h η v := by
  classical
  have hind : Ω.indicator u =ᵐ[_root_.MeasureTheory.MeasureSpace.volume] Ω.indicator v := by
    rw [Filter.EventuallyEq, _root_.MeasureTheory.ae_restrict_iff' hΩ] at huv
    filter_upwards [huv] with x hx
    by_cases hxΩ : x ∈ Ω
    · simp only [_root_.Set.indicator_of_mem hxΩ, hx hxΩ]
    · simp only [_root_.Set.indicator_of_notMem hxΩ]
  have heq (w : E → ℝ) : nirenbergTestFunction k h η w =
      nirenbergTestFunction k h η (Ω.indicator w) := by
    apply nirenbergTestFunction_congr_of_eqOn_cthickening
    intro x hx
    simp only [_root_.Set.indicator_of_mem (hηs hx)]
  rw [heq u, heq v]
  exact nirenbergTestFunction_congr_ae k h η hind

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction_congr_ae_local then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction_congr_ae_local"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction_congr_ae_local ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction_congr_ae_local

theorem nirenbergTestFunction_add (k : Fin d) (h : ℝ) (η u v : E → ℝ) :
    nirenbergTestFunction k h η (u + v) =
      nirenbergTestFunction k h η u + nirenbergTestFunction k h η v := by
  unfold nirenbergTestFunction
  rw [diffQuot_add]
  have heq : (fun x => (η x)^2 * (diffQuot k h u + diffQuot k h v) x) =
      (fun x => (η x)^2 * diffQuot k h u x) +
        (fun x => (η x)^2 * diffQuot k h v x) := by
    funext x
    simp only [Pi.add_apply, mul_add]
  rw [heq, diffQuot_add]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction_add ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction_add

theorem nirenbergTestFunction_smul (k : Fin d) (h c : ℝ) (η u : E → ℝ) :
    nirenbergTestFunction k h η (c • u) = c • nirenbergTestFunction k h η u := by
  unfold nirenbergTestFunction
  rw [diffQuot_smul]
  have heq : (fun x => (η x)^2 * (c • diffQuot k h u) x) =
      c • (fun x => (η x)^2 * diffQuot k h u x) := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [heq, diffQuot_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction_smul ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction_smul

end DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction

namespace DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction

open _root_.Metric

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem integral_cutoff_sq_diffQuot_le_eLpNorm_weakPartial_sq
    {Ω Ω' Ω'' : Set E} (hΩ : IsOpen Ω) (hΩ' : IsOpen Ω') (hΩ'' : IsOpen Ω'')
    (hΩ'c : IsCompact (closure Ω')) (hΩ'Ω : closure Ω' ⊆ Ω)
    (hΩ''c : IsCompact (closure Ω''))
    {u g η : E → ℝ} (hu : _root_.MeasureTheory.MemLp u 2 (volume.restrict Ω))
    (hg : _root_.MeasureTheory.MemLp g 2 (volume.restrict Ω))
    (hη : Continuous η) (hηc : HasCompactSupport η) (hηs : tsupport η ⊆ Ω'')
    {A : ℝ} (hA : 0 ≤ A) (hηbound : ∀ x, |η x| ≤ A)
    (k : Fin d) (hweak : DeGiorgi.HasWeakPartialDeriv k g u Ω)
    {r : ℝ} (hr : 0 < r) (hroom : _root_.Metric.cthickening r (closure Ω'') ⊆ Ω')
    {h : ℝ} (hh : |h| ≤ r) :
    (∫ x, η x ^ 2 * (diffQuot k h u x) ^ 2) ≤
      A ^ 2 * (_root_.MeasureTheory.eLpNorm g 2 (volume.restrict Ω')).toReal ^ 2 := by
  have hηroom : _root_.Metric.cthickening |h| (tsupport η) ⊆ Ω :=
    (_root_.Metric.cthickening_mono hh _).trans ((_root_.Metric.cthickening_subset_of_subset r
      (hηs.trans subset_closure)).trans (hroom.trans (subset_closure.trans hΩ'Ω)))
  have hηq := memLp_cutoff_mul_diffQuot_local hΩ.measurableSet hu hη hηc k h hηroom
  have hdq := eLpNorm_diffQuot_le_eLpNorm_weakPartial_local hΩ hΩ' hΩ'' hΩ'c hΩ'Ω
    hΩ''c hu hg k hweak hr hroom hh
  have hnorm : _root_.MeasureTheory.eLpNorm (fun x => η x * diffQuot k h u x) 2 _root_.MeasureTheory.MeasureSpace.volume ≤
      ENNReal.ofReal A * _root_.MeasureTheory.eLpNorm g 2 (volume.restrict Ω') := by
    calc
      _ ≤ _root_.MeasureTheory.eLpNorm (fun x => A * Ω''.indicator (diffQuot k h u) x) 2 volume := by
        apply _root_.MeasureTheory.eLpNorm_mono_ae
        filter_upwards [] with x
        by_cases hx : x ∈ Ω''
        · simp only [_root_.Set.indicator_of_mem hx, norm_mul, Real.norm_eq_abs, abs_of_nonneg hA]
          exact mul_le_mul_of_nonneg_right (hηbound x) (abs_nonneg _)
        · have hzero : η x = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hx (hηs ht))
          simp only [hzero, _root_.MulZeroClass.zero_mul, norm_zero, norm_nonneg]
      _ = ENNReal.ofReal A * _root_.MeasureTheory.eLpNorm (diffQuot k h u) 2 (volume.restrict Ω'') := by
        change _root_.MeasureTheory.eLpNorm (A • Ω''.indicator (diffQuot k h u)) 2 _root_.MeasureTheory.MeasureSpace.volume = _
        rw [_root_.MeasureTheory.eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, abs_of_nonneg hA,
          _root_.MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict hΩ''.measurableSet]
      _ ≤ _ := mul_le_mul' le_rfl hdq
  have hg' : _root_.MeasureTheory.MemLp g 2 (volume.restrict Ω') :=
    hg.mono_measure (Measure.restrict_mono (subset_closure.trans hΩ'Ω) le_rfl)
  have hnormReal : (_root_.MeasureTheory.eLpNorm (fun x => η x * diffQuot k h u x) 2 _root_.MeasureTheory.MeasureSpace.volume).toReal ≤
      A * (_root_.MeasureTheory.eLpNorm g 2 (volume.restrict Ω')).toReal := by
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hg'.eLpNorm_ne_top) hnorm
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hA] using h
  have hid : (∫ x, η x ^ 2 * (diffQuot k h u x) ^ 2) =
      (_root_.MeasureTheory.eLpNorm (fun x => η x * diffQuot k h u x) 2 _root_.MeasureTheory.MeasureSpace.volume).toReal ^ 2 := by
    let v := hηq.toLp (fun x => η x * diffQuot k h u x)
    rw [← Lp.norm_toLp _ hηq, ← real_inner_self_eq_norm_sq, L2.inner_def]
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [hηq.coeFn_toLp] with x hx
    simp only [Real.inner_apply, hx]
    ring
  rw [hid, ← mul_pow]
  exact pow_le_pow_left₀ ENNReal.toReal_nonneg hnormReal 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.integral_cutoff_sq_diffQuot_le_eLpNorm_weakPartial_sq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.integral_cutoff_sq_diffQuot_le_eLpNorm_weakPartial_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.integral_cutoff_sq_diffQuot_le_eLpNorm_weakPartial_sq ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.integral_cutoff_sq_diffQuot_le_eLpNorm_weakPartial_sq

end DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction
