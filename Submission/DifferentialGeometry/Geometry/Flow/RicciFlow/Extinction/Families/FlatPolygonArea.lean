import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.FlatPolygonApproximation
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.FlatPolygonLength

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
    [T2Space Q] [CompactSpace Q] [ConnectedSpace Q] [I.Boundaryless]

theorem exists_uniform_flatPolygon_area_error {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (g : SmoothRiemannianMetric I Q) (P : FlatteningProfile)
    (Γ : RegularFamily (I := I) (Q := Q) K) {eta : ℝ} (heta : 0 < eta) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ k,
      ∀ c : ContractibleRegularLoop (I := I) (Q := Q),
        (∀ z, c.1 z = flatPolygon g P n (Γ k).1 z) →
        |regularLeastArea g c - regularLeastArea g (Γ k)| < eta := by
  obtain ⟨L, hL, hlen⟩ := regularFamily_uniform_bounds g Γ
  obtain ⟨radius, hradius, hshort, _, _⟩ := shortSegment_neighborhood g
  obtain ⟨N₀, hN₀, hedge⟩ := exists_uniform_short_polygon_edges g Γ hradius
  obtain ⟨ρ, C, hρ, hC, harea⟩ := leastArea_nearby_abs_bound g
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt (2 * (L : ℝ) / ρ)
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt (4 * C * (L : ℝ) ^ 2 / eta)
  refine ⟨max N₀ (_root_.Max.max N₁ N₂), hN₀.trans (le_max_left _ _), ?_⟩
  intro n hn k c hc
  have hn₀ : N₀ ≤ n := (le_max_left N₀ _).trans hn
  have hn₁ : N₁ ≤ n := (le_max_left N₁ N₂).trans ((le_max_right N₀ _).trans hn)
  have hn₂ : N₂ ≤ n := (le_max_right N₁ N₂).trans ((le_max_right N₀ _).trans hn)
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hseg : ∀ i : ℤ, 0 ≤ i → i < n → IsShortSegment g (polygonVertex (Γ k).1 n i)
      (polygonVertex (Γ k).1 n (i + 1))
      (shortSegment g (polygonVertex (Γ k).1 n i) (polygonVertex (Γ k).1 n (i + 1))) :=
    fun i _ _ => (hshort _ _ (hedge n hn₀ k i)).1
  have hdist := flatPolygon_loopUniformDistance_le g P (Γ k).1 c.1 L (hL k) hnpos hc hseg
  have hnear : loopUniformDistance g c.1.toContinuousLoop (Γ k).1.toContinuousLoop < ρ := by
    apply hdist.trans_lt
    apply (div_lt_iff₀ hnR).mpr
    have h := (div_lt_iff₀ hρ).mp
      (hN₁.trans_le (by exact_mod_cast hn₁ : (N₁ : ℝ) ≤ n))
    nlinarith
  have hca : loopLength g c.1.toContinuousLoop ≤ L :=
    (flatPolygon_loopLength_le g P hnpos (Γ k).1 c.1 hc hseg).trans (hlen k)
  have hdnonneg : 0 ≤ loopUniformDistance g c.1.toContinuousLoop (Γ k).1.toContinuousLoop := by
    apply le_csSup_of_le ⟨2 * (L : ℝ) / n, ?_⟩ (Set.mem_range_self (0 : Surgery.Topology.Circle))
      ENNReal.toReal_nonneg
    rintro r ⟨z, rfl⟩
    have hd := flatPolygon_edist_le_of_lipschitz g P (Γ k).1 L (hL k) hnpos hseg z
    rw [← hc z] at hd
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hd).trans_eq
      (ENNReal.toReal_ofReal (by positivity))
  have hestimate := harea c.1.toContinuousLoop (Γ k).1.toContinuousLoop c.2 (Γ k).2
    (c.1.isLipschitz g) ((Γ k).1.isLipschitz g) hnear
  change |regularLeastArea g c - regularLeastArea g (Γ k)| ≤ _ at hestimate
  have hcoef : 0 ≤ C * loopUniformDistance g c.1.toContinuousLoop (Γ k).1.toContinuousLoop :=
    mul_nonneg hC.le hdnonneg
  apply hestimate.trans_lt
  have hsum : loopLength g c.1.toContinuousLoop + loopLength g (Γ k).1.toContinuousLoop ≤ 2 * L := by
    linarith [hlen k]
  apply (mul_le_mul_of_nonneg_left hsum hcoef).trans_lt
  have hmul := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdist hC.le)
    (by positivity : (0 : ℝ) ≤ 2 * L)
  apply hmul.trans_lt
  have hfin : 4 * C * (L : ℝ) ^ 2 < (n : ℝ) * eta :=
    (div_lt_iff₀ heta).mp (hN₂.trans_le (by exact_mod_cast hn₂ : (N₂ : ℝ) ≤ n))
  calc
    C * (2 * (L : ℝ) / n) * (2 * L) = 4 * C * (L : ℝ) ^ 2 / n := by ring
    _ < eta := (div_lt_iff₀ hnR).mpr (by nlinarith)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.exists_uniform_flatPolygon_area_error then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Families.exists_uniform_flatPolygon_area_error"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.exists_uniform_flatPolygon_area_error ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.exists_uniform_flatPolygon_area_error

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families
