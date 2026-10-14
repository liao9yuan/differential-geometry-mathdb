import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Topology.UrysohnsLemma
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Topology.Order.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Filter _root_.MeasureTheory _root_.Set
open scoped _root_.CompactlySupported _root_.Topology

namespace DifferentialGeometry.Analysis.Measure

theorem tendsto_mass_of_integral_tendsto_of_tight
    {X ι : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] [T2Space X] [LocallyCompactSpace X]
    {F : Filter ι} {mus : ι → _root_.MeasureTheory.FiniteMeasure X} {mu : _root_.MeasureTheory.FiniteMeasure X}
    (hlocal : ∀ f : C_c(X, ℝ),
      _root_.Filter.Tendsto (fun i ↦ ∫ x, f x ∂(mus i : _root_.MeasureTheory.Measure X)) F
        (𝓝 (∫ x, f x ∂(mu : _root_.MeasureTheory.Measure X))))
    (htail : ∀ ε : ℝ, 0 < ε →
      ∃ K : Set X, IsCompact K ∧
        (∀ᶠ i in F, ((mus i) Kᶜ : ℝ) ≤ ε) ∧
        (mu Kᶜ : ℝ) ≤ ε) :
    Tendsto (fun i ↦ (mus i).mass) F (𝓝 mu.mass) := by
  rw [← NNReal.tendsto_coe, Metric.tendsto_nhds]
  intro ε hε
  have hεhalf : 0 < ε / 2 := half_pos hε
  obtain ⟨K, hK, htail_mus, htail_mu⟩ := htail (ε / 2) hεhalf
  obtain ⟨f, hfK, hfrange⟩ :
      ∃ f : C_c(X, ℝ), _root_.Set.EqOn (⇑f) 1 K ∧ ∀ x, f x ∈ _root_.Set.Icc (0 : ℝ) 1 := by
    obtain ⟨f, hfK, hfsupp, -, hfrange⟩ :=
      exists_continuousMap_one_of_isCompact_subset_isOpen
        hK isOpen_univ K.subset_univ
    exact ⟨⟨f, hasCompactSupport_def.mpr hfsupp⟩, hfK, hfrange⟩
  have hKle (x : X) : K.indicator 1 x ≤ f x := by
    by_cases hx : x ∈ K
    · simp [hx, hfK hx]
    · simp [hx, (hfrange x).1]
  have hlow (nu : _root_.MeasureTheory.FiniteMeasure X) :
      (nu K : ℝ) ≤ ∫ x, f x ∂(nu : _root_.MeasureTheory.Measure X) := by
    calc
      (nu K : ℝ) = (nu : _root_.MeasureTheory.Measure X).real K := by simp
      _ = ∫ x, K.indicator 1 x ∂(nu : _root_.MeasureTheory.Measure X) :=
        (_root_.MeasureTheory.integral_indicator_one hK.measurableSet).symm
      _ ≤ ∫ x, f x ∂(nu : _root_.MeasureTheory.Measure X) := by
        refine _root_.MeasureTheory.integral_mono ?_ f.integrable hKle
        exact (continuousOn_const.integrableOn_compact hK).integrable_indicator
          hK.measurableSet
  have hhigh (nu : _root_.MeasureTheory.FiniteMeasure X) :
      ∫ x, f x ∂(nu : _root_.MeasureTheory.Measure X) ≤ (nu.mass : ℝ) := by
    calc
      (∫ x, f x ∂(nu : _root_.MeasureTheory.Measure X)) ≤ ∫ _ : X, (1 : ℝ) ∂(nu : _root_.MeasureTheory.Measure X) := by
        exact _root_.MeasureTheory.integral_mono f.integrable (_root_.MeasureTheory.integrable_const 1) fun x ↦ (hfrange x).2
      _ = (nu.mass : ℝ) := by simp [FiniteMeasure.mass]
  have hmass_le (nu : _root_.MeasureTheory.FiniteMeasure X) :
      (nu.mass : ℝ) ≤ ∫ x, f x ∂(nu : _root_.MeasureTheory.Measure X) + (nu Kᶜ : ℝ) := by
    have hsplit : (nu.mass : ℝ) = (nu K : ℝ) + (nu Kᶜ : ℝ) := by
      simpa [FiniteMeasure.mass] using
        (_root_.MeasureTheory.measureReal_add_measureReal_compl
          (μ := (nu : _root_.MeasureTheory.Measure X)) hK.measurableSet).symm
    rw [hsplit]
    exact add_le_add (hlow nu) le_rfl
  have hlocal_f :
      ∀ᶠ i in F,
        _root_.Dist.dist (∫ x, f x ∂(mus i : _root_.MeasureTheory.Measure X))
          (∫ x, f x ∂(mu : _root_.MeasureTheory.Measure X)) < ε / 2 :=
    (Metric.tendsto_nhds.1 (hlocal f)) (ε / 2) hεhalf
  filter_upwards [htail_mus, hlocal_f] with i htail_i hlocal_i
  rw [Real.dist_eq] at hlocal_i ⊢
  apply abs_lt.2
  constructor
  · have hlocal_lower := (abs_lt.1 hlocal_i).1
    linarith [hmass_le mu, hhigh (mus i), htail_mu]
  · have hlocal_upper := (abs_lt.1 hlocal_i).2
    linarith [hmass_le (mus i), hhigh mu, htail_i]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Measure.tendsto_mass_of_integral_tendsto_of_tight then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Measure.tendsto_mass_of_integral_tendsto_of_tight"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Measure.tendsto_mass_of_integral_tendsto_of_tight ``Submission.DifferentialGeometry.Analysis.Measure.tendsto_mass_of_integral_tendsto_of_tight

end DifferentialGeometry.Analysis.Measure

end

noncomputable section

namespace DifferentialGeometry.Analysis.Measure

open _root_.MeasureTheory _root_.Set
open scoped _root_.ENNReal

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem map_restrict_compl_le_of_mapsTo
    (mu : _root_.MeasureTheory.Measure Y) {F : Y → X} {T B : Set Y} {K : Set X}
    (hK : MeasurableSet K)
    (hF : AEMeasurable F (mu.restrict T)) (hBK : _root_.Set.MapsTo F (B ∩ T) K) :
    Measure.map F (mu.restrict T) Kᶜ ≤ mu Bᶜ := by
  rw [Measure.map_apply_of_aemeasurable hF hK.compl,
    Measure.restrict_apply₀ (hF.nullMeasurable hK.compl)]
  apply _root_.MeasureTheory.measure_mono
  intro y hy hyB
  exact hy.1 (hBK ⟨hyB, hy.2⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Measure.map_restrict_compl_le_of_mapsTo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Measure.map_restrict_compl_le_of_mapsTo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Measure.map_restrict_compl_le_of_mapsTo ``Submission.DifferentialGeometry.Analysis.Measure.map_restrict_compl_le_of_mapsTo

theorem measure_univ_le_map_restrict_univ_add_compl
    (mu : _root_.MeasureTheory.Measure Y) {F : Y → X} {T B : Set Y}
    (hF : AEMeasurable F (mu.restrict T)) (hBT : B ⊆ T) :
    mu Set.univ ≤ Measure.map F (mu.restrict T) Set.univ + mu Bᶜ := by
  rw [Measure.map_apply_of_aemeasurable hF MeasurableSet.univ,
    Set.preimage_univ, Measure.restrict_apply_univ]
  calc
    mu Set.univ ≤ mu (T ∪ Bᶜ) := by
      apply _root_.MeasureTheory.measure_mono
      intro y _
      by_cases hy : y ∈ B
      · exact Or.inl (hBT hy)
      · exact Or.inr hy
    _ ≤ mu T + mu Bᶜ := _root_.MeasureTheory.measure_union_le T Bᶜ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Measure.measure_univ_le_map_restrict_univ_add_compl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Measure.measure_univ_le_map_restrict_univ_add_compl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Measure.measure_univ_le_map_restrict_univ_add_compl ``Submission.DifferentialGeometry.Analysis.Measure.measure_univ_le_map_restrict_univ_add_compl

theorem lintegral_le_lintegral_mul_add_compl
    (mu : _root_.MeasureTheory.Measure Y) (density cutoff : Y → ℝ≥0∞) {B : Set Y}
    (hB : MeasurableSet B) (hone : _root_.Set.EqOn cutoff 1 B) :
    (∫⁻ y, density y ∂mu) ≤
      (∫⁻ y, cutoff y * density y ∂mu) + ∫⁻ y in Bᶜ, density y ∂mu := by
  have hBint : (∫⁻ y in B, density y ∂mu) ≤
      ∫⁻ y, cutoff y * density y ∂mu := by
    calc
      (∫⁻ y in B, density y ∂mu) = ∫⁻ y in B, cutoff y * density y ∂mu := by
        apply _root_.MeasureTheory.setLIntegral_congr_fun hB
        intro y hy
        simp only [hone hy, Pi.one_apply, one_mul]
      _ ≤ _ := _root_.MeasureTheory.setLIntegral_le_lintegral B _
  calc
    (∫⁻ y, density y ∂mu) = (∫⁻ y in B, density y ∂mu) +
        ∫⁻ y in Bᶜ, density y ∂mu := (_root_.MeasureTheory.lintegral_add_compl density hB).symm
    _ ≤ _ := add_le_add hBint le_rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Measure.lintegral_le_lintegral_mul_add_compl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Measure.lintegral_le_lintegral_mul_add_compl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Measure.lintegral_le_lintegral_mul_add_compl ``Submission.DifferentialGeometry.Analysis.Measure.lintegral_le_lintegral_mul_add_compl

end DifferentialGeometry.Analysis.Measure

end

noncomputable section

namespace DifferentialGeometry.Analysis.Measure

open _root_.Filter _root_.MeasureTheory _root_.Set
open scoped _root_.ENNReal _root_.Topology

theorem tendsto_measure_univ_of_map_restrict_and_compl
    {ι X : Type*} {Y : ι → Type*} [MeasurableSpace X] [∀ i, MeasurableSpace (Y i)]
    {l : Filter ι} (mu : ∀ i, _root_.MeasureTheory.Measure (Y i)) (f : ∀ i, Y i → X)
    (T B : ∀ i, Set (Y i)) {mass : ℝ≥0∞}
    (hf : ∀ᶠ i in l, AEMeasurable (f i) ((mu i).restrict (T i)))
    (hBT : ∀ᶠ i in l, B i ⊆ T i)
    (hmap : _root_.Filter.Tendsto (fun i => Measure.map (f i) ((mu i).restrict (T i)) Set.univ)
      l (𝓝 mass))
    (htail : _root_.Filter.Tendsto (fun i => (mu i) (B i)ᶜ) l (𝓝 0)) :
    Tendsto (fun i => (mu i) Set.univ) l (𝓝 mass) := by
  have hupper : _root_.Filter.Tendsto
      (fun i => Measure.map (f i) ((mu i).restrict (T i)) Set.univ + (mu i) (B i)ᶜ)
      l (𝓝 mass) := by
    simpa only [add_zero] using hmap.add htail
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hmap hupper
  · filter_upwards [hf] with i hi
    rw [Measure.map_apply_of_aemeasurable hi MeasurableSet.univ,
      Set.preimage_univ, Measure.restrict_apply_univ]
    exact _root_.MeasureTheory.measure_mono (_root_.Set.subset_univ _)
  · filter_upwards [hf, hBT] with i hi hBi
    exact measure_univ_le_map_restrict_univ_add_compl (mu i) hi hBi

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Measure.tendsto_measure_univ_of_map_restrict_and_compl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Measure.tendsto_measure_univ_of_map_restrict_and_compl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Measure.tendsto_measure_univ_of_map_restrict_and_compl ``Submission.DifferentialGeometry.Analysis.Measure.tendsto_measure_univ_of_map_restrict_and_compl

end DifferentialGeometry.Analysis.Measure

end
