import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessNormalizedNormConvergence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


set_option autoImplicit false
noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Filter _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Tensor.Coordinates
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private local instance movingNormC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.movingNormC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.movingNormC1 target :: scope.openDecls } }

omit [CompleteSpace E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
private theorem exists_compact_chart_sequence (p : M)
    {V : Set E} (hV : IsOpen V) (hpV : extChartAt I p p ∈ V)
    (y : ℕ → M) (hy : _root_.Filter.Tendsto y _root_.Filter.atTop (𝓝 p)) :
    ∃ (K : Set E) (z : ℕ → E), IsCompact K ∧ K ⊆ V ∧ extChartAt I p p ∈ K ∧
      (∀ n, z n ∈ K) ∧ _root_.Filter.Tendsto z _root_.Filter.atTop (𝓝 (extChartAt I p p)) ∧
      ∀ᶠ n in _root_.Filter.atTop, (extChartAt I p).symm (z n) = y n := by
  classical
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hpV)
  let K := Metric.closedBall (extChartAt I p p) (r / 2)
  have hK : IsCompact K := _root_.ProperSpace.isCompact_closedBall _ _
  have hKV : K ⊆ V := (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hpK : extChartAt I p p ∈ K := Metric.mem_closedBall_self (by linarith)
  have hchart : _root_.Filter.Tendsto (fun n => extChartAt I p (y n)) _root_.Filter.atTop (𝓝 (extChartAt I p p)) :=
    (continuousAt_extChartAt (I := I) p).tendsto.comp hy
  have hnear : ∀ᶠ n in _root_.Filter.atTop, extChartAt I p (y n) ∈ K :=
    hchart (Metric.closedBall_mem_nhds _ (by linarith))
  let z (n : ℕ) := if extChartAt I p (y n) ∈ K then extChartAt I p (y n)
    else extChartAt I p p
  have hzK (n : ℕ) : z n ∈ K := by
    dsimp only [z]
    split_ifs with hn
    · exact hn
    · exact hpK
  have heq : z =ᶠ[_root_.Filter.atTop] (fun n => extChartAt I p (y n)) := by
    filter_upwards [hnear] with n hn
    exact if_pos hn
  have hz := (_root_.Filter.tendsto_congr' heq).2 hchart
  refine ⟨K, z, hK, hKV, hpK, hzK, hz, ?_⟩
  filter_upwards [heq, hy (extChartAt_source_mem_nhds (I := I) p)] with n hn hsrc
  rw [hn, (extChartAt I p).left_inv hsrc]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_compact_chart_sequence
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_compact_chart_sequence target :: scope.openDecls } }


theorem weighted_error_covariant_norm_tendsto_at_point
    (g : ℝ → SmoothRiemannianMetric I M)
    (A B : ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2) (p : M)
    {V : Set E} (hV : IsOpen V) (hpV : extChartAt I p p ∈ V)
    (hVt : V ⊆ (extChartAt I p).target)
    {J L : Set ℝ}
    (hgram : ∀ i j : Fin (Module.finrank ℝ E), ContDiffOn ℝ ∞
      (fun z : ℝ × E => chartGramOnE (I := I) (g z.1) p i j z.2) (L ×ˢ V))
    (hA : ∀ slots : Fin 2 → Fin (Module.finrank ℝ E), ContDiffOn ℝ ∞
      (fun z : ℝ × E => A z.1 ((extChartAt I p).symm z.2)
        (fun j => chartBasisVecFiber (I := I) p (slots j) ((extChartAt I p).symm z.2))) (J ×ˢ V))
    (hB : ∀ slots : Fin 2 → Fin (Module.finrank ℝ E), ContDiffOn ℝ ∞
      (fun z : ℝ × E => B z.1 ((extChartAt I p).symm z.2)
        (fun j => chartBasisVecFiber (I := I) p (slots j) ((extChartAt I p).symm z.2))) (L ×ˢ V))
    (tau upsilon : ℕ → ℝ) (htau : ∀ n, tau n ∈ J) (hupsilon : ∀ n, upsilon n ∈ L)
    {t u : ℝ} (ht : t ∈ J) (hu : u ∈ L)
    (htlim : _root_.Filter.Tendsto tau _root_.Filter.atTop (𝓝 t)) (hulim : _root_.Filter.Tendsto upsilon _root_.Filter.atTop (𝓝 u))
    (c alpha beta : ℕ → ℝ) (hc : ∀ n, 0 < c n)
    {c₀ alpha₀ beta₀ : ℝ} (hc₀ : 0 < c₀)
    (hclim : _root_.Filter.Tendsto c _root_.Filter.atTop (𝓝 c₀))
    (halim : _root_.Filter.Tendsto alpha _root_.Filter.atTop (𝓝 alpha₀)) (hblim : _root_.Filter.Tendsto beta _root_.Filter.atTop (𝓝 beta₀))
    (y : ℕ → M) (hy : _root_.Filter.Tendsto y _root_.Filter.atTop (𝓝 p)) (a : ℕ) :
    Tendsto (fun n => tensor02CovDerivNormWith (I := I) a
      (alpha n • A (tau n) - beta n • B (upsilon n))
      (scaleMetric (c n) (hc n) (g (upsilon n)))
      (scaleMetric (c n) (hc n) (g (upsilon n))) (y n))
      atTop (𝓝 (tensor02CovDerivNormWith (I := I) a
        (alpha₀ • A t - beta₀ • B u)
        (scaleMetric c₀ hc₀ (g u)) (scaleMetric c₀ hc₀ (g u)) p)) := by
  obtain ⟨K, z, hK, hKV, hpK, hzK, hz, heq⟩ := exists_compact_chart_sequence p hV hpV y hy
  have hn := weighted_error_covariant_norm_tendsto g A B p hV hVt hgram hA hB
    tau upsilon htau hupsilon ht hu htlim hulim c alpha beta hc hc₀ hclim halim hblim
    hK hKV z hzK hpK hz a
  rw [(extChartAt I p).left_inv (mem_extChartAt_source p)] at hn
  apply hn.congr'
  filter_upwards [heq] with n hn
  rw [hn]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.weighted_error_covariant_norm_tendsto_at_point then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.weighted_error_covariant_norm_tendsto_at_point"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.weighted_error_covariant_norm_tendsto_at_point ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.weighted_error_covariant_norm_tendsto_at_point

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
