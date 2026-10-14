import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CrossModelDistanceTransfer

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section
set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u v

variable {N : Type u} [TopologicalSpace N] [ChartedSpace ThreeSpace N]
  [IsManifold I3 ∞ N] [T2Space N] [SigmaCompactSpace N] [PreconnectedSpace N]

private local instance comparisonDistanceC1 : IsManifold I3 1 N :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.comparisonDistanceC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.comparisonDistanceC1 target :: scope.openDecls } }

theorem eventually_metricDistance_bounds_on_compact_of_comparisons
    {ι : Type*} {l : Filter ι} {M : ι → Type v}
    [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace ThreeSpace (M i)]
    [∀ i, IsManifold I3 ∞ (M i)] [∀ i, T2Space (M i)]
    (h : ℝ → SmoothRiemannianMetric I3 N) (g : ∀ i, ℝ → SmoothRiemannianMetric I3 (M i))
    (F : ∀ i, PartialDiffeomorph I3 I3 N (M i) ∞)
    {times : Set ℝ} {s eps : ℝ} (hs : s ∈ times) (heps : 0 ≤ eps) (heps1 : eps < 1)
    (hcomplete : RiemannianMetricComplete (h s))
    (hcompare : ∀ K : Set N, IsCompact K → ∀ᶠ i in l, K ⊆ (F i).source ∧
      Nonempty (MetricComparisonOn h (g i) (F i) K times 0 eps))
    {K : Set N} (hK : IsCompact K) :
    ∀ᶠ i in l, ∀ a ∈ K, ∀ b ∈ K,
      Real.sqrt (1 - eps) * metricDistance (h s) a b ≤ metricDistance (g i s) (F i a) (F i b) ∧
        metricDistance (g i s) (F i a) (F i b) ≤ Real.sqrt (1 + eps) * metricDistance (h s) a b := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨p, hp⟩ := hne
  have hcont : Continuous (fun x : N => (riemannianEDistOf (h s) p x).toReal) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (ENNReal.continuousAt_toReal (riemannianEDistOf_ne_top (h s) p x)).comp
      (continuous_riemannianEDist (h s) p).continuousAt
  obtain ⟨B, hB⟩ := hK.bddAbove_image hcont.continuousOn
  let rho := _root_.Max.max B 0 + 1
  have hrho : 0 < rho := by dsimp only [rho]; linarith [le_max_right B 0]
  have hKR : K ⊆ riemannianClosedBallOf (h s) p rho := by
    intro x hx
    apply (ENNReal.toReal_le_toReal (riemannianEDistOf_ne_top (h s) p x)
      ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal hrho.le]
    exact (hB ⟨x, hx, rfl⟩).trans (by dsimp only [rho]; linarith [le_max_left B 0])
  have hm : 0 < Real.sqrt (1 - eps) := Real.sqrt_pos.mpr (by linarith)
  let R := (Real.sqrt (1 + eps) * (3 * rho) + 1) / Real.sqrt (1 - eps)
  have hR : 0 < R := by dsimp only [R]; positivity
  have hroom : Real.sqrt (1 + eps) * (3 * rho) < Real.sqrt (1 - eps) * R := by
    dsimp only [R]
    rw [mul_div_cancel₀ _ hm.ne']
    linarith
  have hball := hcomplete.closedEBall_isCompact p R
  filter_upwards [hcompare _ hball] with i hi
  obtain ⟨hsource, ⟨C⟩⟩ := hi
  have hequiv : ∀ y ∈ riemannianClosedBallOf (h s) p R, ∀ v : TangentSpace I3 y,
      (1 - eps) * (h s).inner y v v ≤ (g i s).inner (F i y)
        (mfderiv I3 I3 (F i) y v) (mfderiv I3 I3 (F i) y v) ∧
      (g i s).inner (F i y) (mfderiv I3 I3 (F i) y v) (mfderiv I3 I3 (F i) y v) ≤
        (1 + eps) * (h s).inner y v v := by
    intro y hy v
    have hh := C.equivalence s hs y hy v
    rwa [C.pullback_eq s y hy (fun _ => v)] at hh
  intro a ha b hb
  exact crossModel_metricDistance_transfer (h s) (g i s) (F i) p hR heps heps1 hrho.le
    hball hsource hequiv hroom a (hKR ha) b (hKR hb)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.eventually_metricDistance_bounds_on_compact_of_comparisons then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.eventually_metricDistance_bounds_on_compact_of_comparisons"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.eventually_metricDistance_bounds_on_compact_of_comparisons ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.eventually_metricDistance_bounds_on_compact_of_comparisons

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end

section
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u v

variable {N : Type u} [TopologicalSpace N] [ChartedSpace ThreeSpace N]
  [IsManifold I3 ∞ N] [T2Space N] [SigmaCompactSpace N] [PreconnectedSpace N]

private local instance inverseComparisonC1 : IsManifold I3 1 N :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.inverseComparisonC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.inverseComparisonC1 target :: scope.openDecls } }

theorem tendsto_metricDistance_sub_of_comparisons
    {ι : Type*} {l : Filter ι} {M : ι → Type v}
    [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace ThreeSpace (M i)]
    [∀ i, IsManifold I3 ∞ (M i)] [∀ i, T2Space (M i)]
    (h : ℝ → SmoothRiemannianMetric I3 N) (g : ∀ i, ℝ → SmoothRiemannianMetric I3 (M i))
    (F : ∀ i, PartialDiffeomorph I3 I3 N (M i) ∞)
    {times : Set ℝ} {s : ℝ} (hs : s ∈ times)
    (hcomplete : RiemannianMetricComplete (h s))
    (hcompare : ∀ eps : ℝ, 0 < eps → ∀ K : Set N, IsCompact K →
      ∀ᶠ i in l, K ⊆ (F i).source ∧
        Nonempty (MetricComparisonOn h (g i) (F i) K times 0 eps))
    {K : Set N} (hK : IsCompact K) (a b : ι → N)
    (hmem : ∀ᶠ i in l, a i ∈ K ∧ b i ∈ K) :
    _root_.Filter.Tendsto (fun i => metricDistance (g i s) (F i (a i)) (F i (b i)) -
      metricDistance (h s) (a i) (b i)) l (𝓝 0) := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp only [_root_.Set.mem_empty_iff_false, false_and, _root_.Filter.eventually_false_iff_eq_bot] at hmem
    simp [hmem]
  obtain ⟨p, hp⟩ := hne
  have hc : Continuous (fun z : N => metricDistance (h s) p z) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact (ENNReal.continuousAt_toReal (riemannianEDistOf_ne_top (h s) p z)).comp
      ((continuous_riemannianEDist (h s) p).continuousAt)
  obtain ⟨B₀, hB₀⟩ := hK.bddAbove_image hc.continuousOn
  let B := 2 * _root_.Max.max B₀ 0
  have hB : 0 ≤ B := mul_nonneg (by norm_num) (le_max_right _ _)
  apply Metric.tendsto_nhds.mpr
  intro eta heta
  let eps := _root_.Min.min (1 / 2 : ℝ) (eta / (2 * (B + 1)))
  have heps : 0 < eps := lt_min (by norm_num) (by positivity)
  have heps1 : eps < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hprod : eps * B < eta := by
    have hb : 0 < 2 * (B + 1) := by positivity
    have hh := (le_div_iff₀ hb).mp (min_le_right (1 / 2 : ℝ) (eta / (2 * (B + 1))))
    change eps * (2 * (B + 1)) ≤ eta at hh
    nlinarith
  have hlow : 1 - eps ≤ Real.sqrt (1 - eps) := by
    have hh := Real.sq_sqrt (by linarith : 0 ≤ 1 - eps)
    have hn := Real.sqrt_nonneg (1 - eps)
    nlinarith [sq_nonneg (Real.sqrt (1 - eps) - (1 - eps))]
  have hupp : Real.sqrt (1 + eps) ≤ 1 + eps := by
    have hh := Real.sq_sqrt (by linarith : 0 ≤ 1 + eps)
    have hn := Real.sqrt_nonneg (1 + eps)
    nlinarith
  filter_upwards [hmem, eventually_metricDistance_bounds_on_compact_of_comparisons
    h g F hs heps.le heps1 hcomplete (hcompare eps heps) hK] with i hi hdist
  have hbound : metricDistance (h s) (a i) (b i) ≤ B := by
    have ha := hB₀ ⟨a i, hi.1, rfl⟩
    have hb := hB₀ ⟨b i, hi.2, rfl⟩
    have ht := riemannianEDistOf_triangle (h s) (a i) p (b i)
    rw [riemannianEDistOf_comm (h s) (a i) p] at ht
    have ht' := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨riemannianEDistOf_ne_top (h s) p (a i),
        riemannianEDistOf_ne_top (h s) p (b i)⟩) ht
    rw [ENNReal.toReal_add (riemannianEDistOf_ne_top (h s) p (a i))
      (riemannianEDistOf_ne_top (h s) p (b i))] at ht'
    dsimp only [metricDistance] at ha hb ⊢
    dsimp only [B]
    linarith [le_max_left B₀ 0]
  have hn : 0 ≤ metricDistance (h s) (a i) (b i) := ENNReal.toReal_nonneg
  have hlo := (mul_le_mul_of_nonneg_right hlow hn).trans (hdist _ hi.1 _ hi.2).1
  have hup := (hdist _ hi.1 _ hi.2).2.trans (mul_le_mul_of_nonneg_right hupp hn)
  rw [Real.dist_eq, sub_zero, abs_lt]
  have hh := mul_le_mul_of_nonneg_left hbound heps.le
  constructor <;> nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.tendsto_metricDistance_sub_of_comparisons then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.tendsto_metricDistance_sub_of_comparisons"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.tendsto_metricDistance_sub_of_comparisons ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.tendsto_metricDistance_sub_of_comparisons


end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
end

end
