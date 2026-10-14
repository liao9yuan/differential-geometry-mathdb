import Submission.DifferentialGeometry.Geometry.Neck.SectionCurvature
import Submission.DifferentialGeometry.Geometry.Curvature.ProductGraphPerturbation
import Submission.DifferentialGeometry.Topology.GraphBandChart
import Submission.DifferentialGeometry.Geometry.Neck.SpatialLevelEmbedding
import Submission.DifferentialGeometry.Topology.Manifold.SmoothEmbeddingOpenTarget
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.Defs
import Submission.DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Embedding
import Submission.DifferentialGeometry.Geometry.Metric.Construction.Immersion

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.instFactEqNatFinrankRealEuclideanSpaceFinOfNatHAdd_differentialGeometry : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.instFactEqNatFinrankRealEuclideanSpaceFinOfNatHAdd_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.instFactEqNatFinrankRealEuclideanSpaceFinOfNatHAdd_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.instConnectedSpaceElemEuclideanSpaceRealFinHAddNatOfNatSphere : ConnectedSpace (Sphere 2) :=
  isConnected_iff_connectedSpace.mp
    (isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num)
      (0 : ThreeSpace) (by norm_num : (0 : ℝ) ≤ 1))

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.instConnectedSpaceElemEuclideanSpaceRealFinHAddNatOfNatSphere
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.instConnectedSpaceElemEuclideanSpaceRealFinHAddNatOfNatSphere target :: scope.openDecls } }

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {p : M}
  {F H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [J.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N]
  [T2Space N] [ConnectedSpace N] [SigmaCompactSpace N]

theorem SpatialNeck.exists_diffeomorph_graph_in_product_chart
    (nk : SpatialNeck g eps p) (heps : eps ≤ 1 / 1000)
    {s : ℝ} (hs : s ∈ _root_.Set.Ioo (-eps⁻¹) eps⁻¹)
    (h : SmoothRiemannianMetric J N) (hdim : Module.finrank ℝ F = 2)
    (O : TopologicalSpace.Opens (N × ℝ)) (V : TopologicalSpace.Opens M)
    (Φ : O ≃ₘ⟮J.prod 𝓘(ℝ), I3⟯ V)
    (himage : ∀ q : Sphere 2, nk.map (q, s) ∈ V)
    {η : ℝ} (hη : η ≤ 1 / 4) (hsmallη : 720 * η < metricScalarAt g p / 16)
    (hsmall : ∀ y : V, y.val ∈ _root_.Set.range (fun q : Sphere 2 => nk.map (q, s)) → ∀ m : ℕ, m ≤ 2 →
      metricDerivNorm m (Diffeomorph.pullbackMetricCross (g.restrictOpen V) Φ)
        ((h.prod (euclideanMetric (E := ℝ))).restrictOpen O)
        ((h.prod (euclideanMetric (E := ℝ))).restrictOpen O) (Φ.symm y) ≤ η) :
    ∃ (ψ : N ≃ₘ⟮J, I2⟯ Sphere 2) (a : N → ℝ), ContMDiff J 𝓘(ℝ) ∞ a ∧
      ∀ z : N, (Φ.symm ⟨nk.map (ψ z, s), himage (ψ z)⟩).val = (z, a z) := by
  exact exists_diffeomorph_graph_of_tangent_sectional_lower_bound_in_product_chart
    (fun q : Sphere 2 => nk.map (q, s)) (nk.isSmoothEmbedding_level (abs_lt.mpr hs))
    h (by simpa using hdim.symm) (by simp) O V Φ himage hη hsmallη hsmall
    (fun q u v => nk.metricRm04_section_lower_bound heps hs q u v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.exists_diffeomorph_graph_in_product_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.exists_diffeomorph_graph_in_product_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.exists_diffeomorph_graph_in_product_chart ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.exists_diffeomorph_graph_in_product_chart

theorem SpatialNeck.interior_eq_empty_of_frontier_in_product_chart
    (nk : SpatialNeck g eps p) (heps : eps ≤ 1 / 1000)
    {s : ℝ} (hs : s ∈ _root_.Set.Ioo (-eps⁻¹) eps⁻¹)
    (h : SmoothRiemannianMetric J N) (hdim : Module.finrank ℝ F = 2)
    (O : TopologicalSpace.Opens (N × ℝ)) (V : TopologicalSpace.Opens M)
    (Φ : O ≃ₘ⟮J.prod 𝓘(ℝ), I3⟯ V)
    {K : Set M} (hK : IsCompact K) (hKV : K ⊆ V)
    (hfront : frontier K = _root_.Set.range (fun q : Sphere 2 => nk.map (q, s)))
    {η : ℝ} (hη : η ≤ 1 / 4) (hsmallη : 720 * η < metricScalarAt g p / 16)
    (hsmall : ∀ y : V, y.val ∈ frontier K → ∀ m : ℕ, m ≤ 2 →
      metricDerivNorm m (Diffeomorph.pullbackMetricCross (g.restrictOpen V) Φ)
        ((h.prod (euclideanMetric (E := ℝ))).restrictOpen O)
        ((h.prod (euclideanMetric (E := ℝ))).restrictOpen O) (Φ.symm y) ≤ η) :
    interior K = ∅ := by
  exact interior_eq_empty_of_frontier_sectional_lower_bound_in_product_chart
    (fun q : Sphere 2 => nk.map (q, s)) (nk.isSmoothEmbedding_level (abs_lt.mpr hs))
    h (by simpa using hdim.symm) (by simp) O V Φ hK hKV hfront hη hsmallη hsmall
    (fun q u v => nk.metricRm04_section_lower_bound heps hs q u v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.interior_eq_empty_of_frontier_in_product_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.interior_eq_empty_of_frontier_in_product_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.interior_eq_empty_of_frontier_in_product_chart ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.interior_eq_empty_of_frontier_in_product_chart

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Filter
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : ℕ → Type u} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace ThreeSpace (M i)]
  [∀ i, IsManifold I3 ∞ (M i)] [∀ i, T2Space (M i)]
  {F H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [J.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N]
  [T2Space N] [ConnectedSpace N] [SigmaCompactSpace N]

theorem eventually_interior_eq_empty_of_frontier_necks_of_product_convergence
    (g : ∀ i, SmoothRiemannianMetric I3 (M i)) (eps : ℕ → ℝ) (p : ∀ i, M i)
    (nk : ∀ i, SpatialNeck (g i) (eps i) (p i))
    (heps : ∀ᶠ i in _root_.Filter.atTop, eps i ≤ 1 / 1000)
    (s : ℕ → ℝ) (hs : ∀ i, s i ∈ _root_.Set.Ioo (-(eps i)⁻¹) (eps i)⁻¹)
    (h : SmoothRiemannianMetric J N) (hdim : Module.finrank ℝ F = 2)
    (O : TopologicalSpace.Opens (N × ℝ)) (V : ∀ i, TopologicalSpace.Opens (M i))
    (Φ : ∀ i, O ≃ₘ⟮J.prod 𝓘(ℝ), I3⟯ V i)
    (K : ∀ i, Set (M i)) (hK : ∀ i, IsCompact (K i)) (hKV : ∀ i, K i ⊆ V i)
    (hfront : ∀ i, frontier (K i) = _root_.Set.range (fun q : Sphere 2 => (nk i).map (q, s i)))
    (A : Set O) (hA : IsCompact A)
    (hfrontA : ∀ᶠ i in _root_.Filter.atTop, ∀ y : V i, y.val ∈ frontier (K i) → (Φ i).symm y ∈ A)
    (hconv : MetricCPConvergenceOn A 2
      (fun i => Diffeomorph.pullbackMetricCross ((g i).restrictOpen (V i)) (Φ i))
      ((h.prod (euclideanMetric (E := ℝ))).restrictOpen O)
      ((h.prod (euclideanMetric (E := ℝ))).restrictOpen O))
    {q : ℝ} (hq : 0 < q)
    (hscalar : ∀ᶠ i in _root_.Filter.atTop, q ≤ metricScalarAt (g i) (p i)) :
    ∀ᶠ i in _root_.Filter.atTop, interior (K i) = ∅ := by
  let η : ℝ := _root_.Min.min (1 / 8) (q / 23040)
  have hη : 0 < η := by dsimp only [η]; positivity
  have hηquarter : η ≤ 1 / 4 := (min_le_left _ _).trans (by norm_num)
  have hηq : 720 * η < q / 16 := by
    have hm : η ≤ q / 23040 := min_le_right _ _
    linarith
  obtain ⟨j, hj⟩ := hconv η hη
  filter_upwards [heps, hfrontA, hscalar, _root_.Filter.eventually_ge_atTop j] with i hei hAi hqi hji
  apply (nk i).interior_eq_empty_of_frontier_in_product_chart hei (hs i) h hdim O (V i) (Φ i)
    (hK i) (hKV i) (hfront i) hηquarter
    (hηq.trans_le (div_le_div_of_nonneg_right hqi (by norm_num)))
  intro y hy m hm
  exact ((derivNorm_le_sup hA hm _ _ _ (hAi y hy)).trans_lt (hj i hji)).le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.eventually_interior_eq_empty_of_frontier_necks_of_product_convergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.eventually_interior_eq_empty_of_frontier_necks_of_product_convergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.eventually_interior_eq_empty_of_frontier_necks_of_product_convergence ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.eventually_interior_eq_empty_of_frontier_necks_of_product_convergence

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn


open _root_.Submission.DifferentialGeometry
open scoped _root_.ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]

omit [T2Space M] in
private theorem scale_metric_ratio (g : SmoothRiemannianMetric I3 M)
    {q Q : ℝ} (hq : 0 < q) (hQ : 0 < Q) :
    scaleMetric (Q / q) (div_pos hQ hq) (DifferentialGeometry.scaleMetric q hq g) = scaleMetric Q hQ g := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  simp only [scaleMetric_inner]
  field_simp

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.scale_metric_ratio
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.scale_metric_ratio target :: scope.openDecls } }

omit [T2Space M] in
private theorem cap_subset_ball_at_mem_of_scale_ratio
    (g : SmoothRiemannianMetric I3 M) {q Q A R : ℝ}
    (hq : 0 < q) (hQ : 0 < Q) (hA : 0 < A) (hR : 0 < R)
    (hratio : Q / q ≤ A) {K : Set M} {x z : M} (hx : x ∈ K)
    (hball : K ⊆ riemannianBallOf (DifferentialGeometry.scaleMetric q hq g) z R) :
    K ⊆ riemannianBallOf (DifferentialGeometry.scaleMetric Q hQ g) x (2 * Real.sqrt A * R) := by
  have hqratio : 0 < Q / q := div_pos hQ hq
  intro y hy
  have hd : riemannianEDistOf (DifferentialGeometry.scaleMetric q hq g) x y < ENNReal.ofReal (2*R) := by
    have hxR := hball hx
    have hyR := hball hy
    change riemannianEDistOf (DifferentialGeometry.scaleMetric q hq g) z x < ENNReal.ofReal R at hxR
    change riemannianEDistOf (DifferentialGeometry.scaleMetric q hq g) z y < ENNReal.ofReal R at hyR
    have ht := (riemannianEDistOf_triangle (DifferentialGeometry.scaleMetric q hq g) x z y).trans_lt
      (ENNReal.add_lt_add (by rwa [riemannianEDistOf_comm] at hxR) hyR)
    rw [← ENNReal.ofReal_add hR.le hR.le] at ht
    convert ht using 1; congr 1; ring
  change riemannianEDistOf (DifferentialGeometry.scaleMetric Q hQ g) x y < ENNReal.ofReal (2 * Real.sqrt A * R)
  rw [← scale_metric_ratio g hq hQ,edistOf_scale]
  have hs : ENNReal.ofReal (Real.sqrt (Q / q)) ≤ ENNReal.ofReal (Real.sqrt A) :=
    ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt hratio)
  have hprod := ENNReal.mul_lt_mul_right
    (ENNReal.ofReal_ne_zero_iff.mpr (Real.sqrt_pos.mpr hA)) ENNReal.ofReal_ne_top hd
  have hb := (mul_le_mul' hs le_rfl).trans_lt hprod
  rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg A)] at hb
  convert hb using 1; congr 1; ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cap_subset_ball_at_mem_of_scale_ratio
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cap_subset_ball_at_mem_of_scale_ratio target :: scope.openDecls } }

theorem SpatialNeck.not_mem_interior_of_frontier_in_scaled_product_chart
    (g : SmoothRiemannianMetric I3 M) {q Q A b R eps : ℝ}
    (hq : 0 < q) (hQ : 0 < Q) (hb : 0 ≤ b)
    (hratio : Q / q ≤ A) {p x z : M}
    (nk : SpatialNeck (DifferentialGeometry.scaleMetric q hq g) eps p) (heps : eps ≤ 1 / 1000)
    {s : ℝ} (hs : s ∈ _root_.Set.Ioo (-eps⁻¹) eps⁻¹)
    {K : Set M} (hK : IsCompact K)
    (hfront : frontier K = _root_.Set.range (fun u : Sphere 2 => nk.map (u,s)))
    (hscalar : b ≤ metricScalarAt (DifferentialGeometry.scaleMetric q hq g) p)
    (hball : K ⊆ riemannianBallOf (DifferentialGeometry.scaleMetric q hq g) z R)
    {F H' : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'} [J.Boundaryless]
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
    [T2Space N] [ConnectedSpace N] [SigmaCompactSpace N]
    (hprod : SmoothRiemannianMetric J N) (hdim : Module.finrank ℝ F = 2)
    (O : TopologicalSpace.Opens (N × ℝ)) (V : TopologicalSpace.Opens M)
    (Φ : O ≃ₘ⟮J.prod 𝓘(ℝ), I3⟯ V)
    (hcapture : riemannianBallOf (DifferentialGeometry.scaleMetric Q hQ g) x (2 * Real.sqrt A * R) ⊆ V)
    {δ : ℝ} (hδ : δ ≤ 1/4) (hδsmall : 720*δ < (b/A)/16)
    (hproduct : ∀ y : V, y.val ∈ frontier K → ∀ m : ℕ, m ≤ 2 →
      metricDerivNorm m (Diffeomorph.pullbackMetricCross ((DifferentialGeometry.scaleMetric Q hQ g).restrictOpen V) Φ)
        ((hprod.prod (euclideanMetric (E := ℝ))).restrictOpen O)
        ((hprod.prod (euclideanMetric (E := ℝ))).restrictOpen O) (Φ.symm y) ≤ δ) :
    x ∉ interior K := by
  intro hx
  have hc : 0 < Q / q := div_pos hQ hq
  have hA : 0 < A := hc.trans_le hratio
  have hR : 0 < R := by
    have hd := hball (interior_subset hx)
    exact ENNReal.ofReal_pos.mp (bot_le.trans_lt hd)
  let nk' := nk.scaleMetric (Q / q) hc
  have heq := scale_metric_ratio g hq hQ
  have hscaled : b/A ≤ metricScalarAt (DifferentialGeometry.scaleMetric Q hQ g) p := by
    rw [← heq,metricScalarAt_scaleMetric]
    rw [← div_eq_inv_mul]
    exact (div_le_div_of_nonneg_left hb hc hratio).trans
      (div_le_div_of_nonneg_right hscalar hc.le)
  have hKV := (cap_subset_ball_at_mem_of_scale_ratio g hq hQ hA hR hratio
    (interior_subset hx) hball).trans hcapture
  have hfront' : frontier K = _root_.Set.range (fun u : Sphere 2 => nk'.map (u,s)) := hfront
  have hmetricClose : ∀ y : V, y.val ∈ frontier K → ∀ m : ℕ, m ≤ 2 →
      metricDerivNorm m (Diffeomorph.pullbackMetricCross
        ((DifferentialGeometry.scaleMetric (Q / q) hc (DifferentialGeometry.scaleMetric q hq g)).restrictOpen V) Φ)
        ((hprod.prod (euclideanMetric (E := ℝ))).restrictOpen O)
        ((hprod.prod (euclideanMetric (E := ℝ))).restrictOpen O) (Φ.symm y) ≤ δ := by
    rw [heq]
    exact hproduct
  have hsmall : 720*δ < metricScalarAt (DifferentialGeometry.scaleMetric (Q / q) hc (DifferentialGeometry.scaleMetric q hq g)) p / 16 := by
    rw [heq]
    exact hδsmall.trans_le (div_le_div_of_nonneg_right hscaled (by norm_num))
  have hempty := nk'.interior_eq_empty_of_frontier_in_product_chart heps hs hprod hdim
    O V Φ hK hKV hfront' hδ hsmall hmetricClose
  simp only [hempty,_root_.Set.mem_empty_iff_false] at hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.not_mem_interior_of_frontier_in_scaled_product_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.not_mem_interior_of_frontier_in_scaled_product_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.not_mem_interior_of_frontier_in_scaled_product_chart ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.not_mem_interior_of_frontier_in_scaled_product_chart

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
