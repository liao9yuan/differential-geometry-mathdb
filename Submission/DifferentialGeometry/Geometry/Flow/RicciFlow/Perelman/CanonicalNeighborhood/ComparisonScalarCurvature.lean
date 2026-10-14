import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedWitnessTransport
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ScalarComparison
import Submission.DifferentialGeometry.Geometry.Curvature.RicciRestriction
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Self

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology _root_.BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {N : Type u} [TopologicalSpace N] [ChartedSpace ThreeSpace N]
  [IsManifold I3 ∞ N] [T2Space N] [SigmaCompactSpace N]

private local instance comparisonScalarC1 : IsManifold I3 1 N :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.comparisonScalarC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.comparisonScalarC1 target :: scope.openDecls } }

theorem MetricComparisonOn.scalar_sub_le_of_ricci_bound
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
    {h : ℝ → SmoothRiemannianMetric I3 N} {g : ℝ → SmoothRiemannianMetric I3 M}
    {F : PartialDiffeomorph I3 I3 N M ∞} {A : Set N} {times : Set ℝ}
    {order : ℕ} {eps Kb : ℝ} (C : MetricComparisonOn h g F A times order eps)
    (U : TopologicalSpace.Opens N) (hU : (U : Set N) ⊆ F.source)
    (hUA : (U : Set N) ⊆ A) {s : ℝ} (hs : s ∈ times)
    (heps : 0 ≤ eps) (heps1 : eps < 1) (horder : 2 ≤ order)
    {y : N} (hy : y ∈ U)
    (hRic : ∀ v w : TangentSpace I3 y, |ricciTensor (h s) y v w| ≤
      Kb * Real.sqrt ((h s).inner y v v) * Real.sqrt ((h s).inner y w w)) :
    |metricScalarAt (g s) (F y) - metricScalarAt (h s) y| ≤ scalarComparisonC 3 eps Kb := by
  let : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I3 U.isOpen)
  let G := (h s).restrictOpen U
  let gp := openPullbackMetric F U hU (g s)
  let yU : U := ⟨y, hy⟩
  have hEq : MetricUniformEquivalentOn (_root_.Set.univ : Set U) G gp (witnessLambda eps) := by
    refine ⟨one_le_witnessLambda heps heps1, ?_⟩
    intro z _hz v
    have hh := C.equivalence s hs (z : N) (hUA z.property) v
    rw [C.pullback_eq s (z : N) (hUA z.property) (fun _ => v)] at hh
    change (witnessLambda eps)⁻¹ * G.inner z v v ≤ gp.inner z v v ∧
      gp.inner z v v ≤ witnessLambda eps * G.inner z v v
    dsimp only [G, gp]
    rw [openPullbackMetric_inner, SmoothRiemannianMetric.restrictOpen_inner]
    constructor
    · simpa only [witnessLambda, inv_inv] using hh.1
    · exact hh.2.trans (mul_le_mul_of_nonneg_right (one_add_le_witnessLambda heps heps1)
        (inner_self_nonneg (h s) (z : N) v))
  have hJet (a : ℕ) (ha0 : 1 ≤ a) (ha : a ≤ 2) :
      MetricCovDerivOrderBoundOn (_root_.Set.univ : Set U) a gp G eps := by
    intro z _hz
    have hh := covNorm_le_add a gp G G z
    obtain ⟨b, rfl⟩ : ∃ b : ℕ, a = b + 1 := ⟨a - 1, by omega⟩
    rw [covNorm_self_succ, zero_add] at hh
    apply hh.trans
    rw [C.openPullback_metricDerivNorm U hU hUA]
    exact C.close (b + 1) 0 (by omega) s hs (z : N) (hUA z.property)
  have hRicU (v w : TangentSpace I3 yU) : |ricciTensor G yU v w| ≤
      Kb * Real.sqrt (G.inner yU v v) * Real.sqrt (G.inner yU w w) := by
    dsimp only [G]
    rw [DifferentialGeometry.Geometry.Curvature.ricciTensor_restrictOpen, SmoothRiemannianMetric.restrictOpen_inner,
      SmoothRiemannianMetric.restrictOpen_inner]
    simp only [mfderiv_subtype_val_apply]
    exact hRic v w
  have hh := abs_metricScalarAt_sub_le_of_jetBounds G gp hEq
    (hJet 1 le_rfl (by norm_num)) (hJet 2 (by norm_num) le_rfl) (_root_.Set.mem_univ yU) hRicU
  dsimp only [G, gp] at hh
  rw [openPullbackMetric_scalar, metricScalarAt_restrictOpen] at hh
  simpa only [show Module.finrank ℝ ThreeSpace = 3 from by simp [ThreeSpace], Nat.cast_ofNat,
    scalarComparisonC, witnessRiemannC] using hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.MetricComparisonOn.scalar_sub_le_of_ricci_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.MetricComparisonOn.scalar_sub_le_of_ricci_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.MetricComparisonOn.scalar_sub_le_of_ricci_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.MetricComparisonOn.scalar_sub_le_of_ricci_bound

theorem tendsto_metricScalarAt_of_comparisons
    {ι : Type*} {l : Filter ι} {M : ι → Type u}
    [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace ThreeSpace (M i)]
    [∀ i, IsManifold I3 ∞ (M i)] [∀ i, T2Space (M i)] [∀ i, SigmaCompactSpace (M i)]
    (h : ℝ → SmoothRiemannianMetric I3 N) (g : ∀ i, ℝ → SmoothRiemannianMetric I3 (M i))
    (F : ∀ i, PartialDiffeomorph I3 I3 N (M i) ∞)
    (U : TopologicalSpace.Opens N) {times : Set ℝ} {s : ℝ} (hs : s ∈ times)
    {order : ℕ} (horder : 2 ≤ order) {p : N} (hp : p ∈ U)
    (hsource : ∀ᶠ i in l, (U : Set N) ⊆ (F i).source)
    (hcompare : ∀ delta : ℝ, 0 < delta → ∀ᶠ i in l,
      Nonempty (MetricComparisonOn h (g i) (F i) U times order delta)) :
    Tendsto (fun i => metricScalarAt (g i s) (F i p)) l (𝓝 (metricScalarAt (h s) p)) := by
  let Kb := Real.sqrt (normSq0S (h s) p 2 (metricRicciAt (h s) p))
  have hKb : 0 ≤ Kb := Real.sqrt_nonneg _
  have hRic (v w : TangentSpace I3 p) : |ricciTensor (h s) p v w| ≤
      Kb * Real.sqrt ((h s).inner p v v) * Real.sqrt ((h s).inner p w w) := by
    have hh := abs_apply_le_norm0S (h s) p 2 (metricRicciAt (h s) p)
      (vec2 v w)
    rw [metricRicciAt_apply_eq_ricciTensor] at hh
    simpa [vec2, Fin.prod_univ_two, mul_assoc, Kb] using hh
  apply Metric.tendsto_nhds.mpr
  intro eps heps
  let delta := _root_.Min.min (1 / 4) (eps / (486 * (1 + Kb)))
  have hdelta : 0 < delta := lt_min (by norm_num) (div_pos heps (by positivity))
  have hdsmall : delta ≤ 1 / 4 := min_le_left _ _
  have hderr : 243 * (delta + delta * Kb) < eps := by
    have hh := (le_div_iff₀ (by positivity : 0 < 486 * (1 + Kb))).mp (min_le_right (1 / 4)
      (eps / (486 * (1 + Kb))))
    change delta * (486 * (1 + Kb)) ≤ eps at hh
    nlinarith
  filter_upwards [hsource, hcompare delta hdelta] with i hi hcmp
  obtain ⟨C⟩ := hcmp
  have hh := (C.scalar_sub_le_of_ricci_bound U hi (subset_refl _) hs hdelta.le
    (by linarith) horder hp hRic).trans (scalarComparisonC_le (n := 3) hdelta.le hdsmall hKb)
  rw [Real.dist_eq]
  exact hh.trans_lt (by norm_num at *; exact hderr)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.tendsto_metricScalarAt_of_comparisons then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.tendsto_metricScalarAt_of_comparisons"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.tendsto_metricScalarAt_of_comparisons ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.tendsto_metricScalarAt_of_comparisons

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
