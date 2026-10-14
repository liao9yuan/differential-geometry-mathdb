import Submission.DifferentialGeometry.Geometry.Comparison.Soul.NormalBundle
import Submission.DifferentialGeometry.Geometry.Metric.QuadraticBounds.Unit

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.Set
open scoped _root_.Topology _root_.ContDiff _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

omit [FiniteDimensional ℝ E] in
theorem tangentSquaredLength_contMDiff (g : SmoothRiemannianMetric I M) :
    ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞
      (fun z : TangentBundle I M => g.inner z.proj z.snd z.snd) := by
  have happ : ContMDiff I.tangent (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun z : TangentBundle I M => (⟨z.proj, g.inner z.proj z.snd z.snd⟩ :
        TotalSpace ℝ (Bundle.Trivial M ℝ))) :=
    ContMDiff.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
      (b := fun z : TangentBundle I M => z.proj)
      (g.contMDiff.comp (Bundle.contMDiff_proj (TangentSpace I)))
      contMDiff_id contMDiff_id
  intro z
  exact (Bundle.contMDiffAt_totalSpace.mp (happ z)).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.tangentSquaredLength_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.tangentSquaredLength_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.tangentSquaredLength_contMDiff ``Submission.DifferentialGeometry.Geometry.Topology.tangentSquaredLength_contMDiff

omit [FiniteDimensional ℝ E] in
private theorem continuous_scaled_vector
    {P : Type*} [TopologicalSpace P] {b : P → M}
    {v : (x : P) → TangentSpace I (b x)} {f : P → ℝ}
    (hv : Continuous (fun x => (⟨b x, v x⟩ : TangentBundle I M)))
    (hf : Continuous f) :
    Continuous (fun x => (⟨b x, f x • v x⟩ : TangentBundle I M)) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hvc := (FiberBundle.continuousAt_totalSpace E _).mp (hv.continuousAt (x := x))
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨hvc.1, ?_⟩
  let e := _root_.FiberBundle.trivializationAt E (TangentSpace I) (b x)
  have he : ∀ᶠ y in 𝓝 x, b y ∈ e.baseSet :=
    hvc.1.preimage_mem_nhds (e.open_baseSet.mem_nhds (_root_.FiberBundle.mem_baseSet_trivializationAt E _ _))
  apply (hf.continuousAt.smul hvc.2).congr_of_eventuallyEq
  filter_upwards [he] with y hy
  exact (e.linear ℝ hy).map_smul (f y) (v y)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Topology.continuous_scaled_vector
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Topology.continuous_scaled_vector target :: scope.openDecls } }

theorem exists_tangent_radius_subset_of_isOpen
    (g : SmoothRiemannianMetric I M) {K : Set M} (hK : IsCompact K)
    {U : Set (TangentBundle I M)} (hU : IsOpen U)
    (hzero : ∀ x ∈ K, (⟨x, 0⟩ : TangentBundle I M) ∈ U) :
    ∃ ε > 0, ∀ x ∈ K, ∀ v : TangentSpace I x,
      Real.sqrt (g.inner x v v) < ε → (⟨x, v⟩ : TangentBundle I M) ∈ U := by
  classical
  let f : ℝ × MetricUnitTangent g → TangentBundle I M :=
    fun z => ⟨z.2.base, z.1 • z.2.vec⟩
  have hf : Continuous f :=
    continuous_scaled_vector (continuous_subtype_val.comp continuous_snd) continuous_fst
  have hprod : ({0} : Set ℝ) ×ˢ {u : MetricUnitTangent g | u.base ∈ K} ⊆ f ⁻¹' U := by
    rintro ⟨r, u⟩ ⟨hr, hu⟩
    have hr0 : r = 0 := Set.mem_singleton_iff.mp hr
    simpa only [Set.mem_preimage, f, hr0, zero_smul] using hzero u.base hu
  obtain ⟨A, B, hA, _, h0A, hKB, hAB⟩ :=
    generalized_tube_lemma (isCompact_singleton (x := (0 : ℝ)))
      (metricUnitOn_compact g hK) (hU.preimage hf) hprod
  obtain ⟨ε, hε, hεA⟩ := Metric.isOpen_iff.mp hA 0 (h0A (by simp))
  refine ⟨ε, hε, ?_⟩
  intro x hx v hv
  by_cases hv0 : v = 0
  · simpa only [hv0] using hzero x hx
  let r := Real.sqrt (g.inner x v v)
  have hr : 0 < r := Real.sqrt_pos.2 (g.pos x v hv0)
  have hunit : g.inner x (r⁻¹ • v) (r⁻¹ • v) = 1 := by
    rw [gInner_smul_self (I := I) g x r⁻¹ v,
      ← Real.sq_sqrt (gInner_self_nonneg (I := I) g x v), inv_pow,
      inv_mul_cancel₀ (pow_ne_zero 2 hr.ne')]
  let u : MetricUnitTangent g := ⟨⟨x, r⁻¹ • v⟩, hunit⟩
  have hrA : r ∈ A := hεA (by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hr] using hv)
  have huB : u ∈ B := hKB (show u.base ∈ K from hx)
  have hmem := hAB (show (r, u) ∈ A ×ˢ B from ⟨hrA, huB⟩)
  change (⟨x, r • (r⁻¹ • v)⟩ : TangentBundle I M) ∈ U at hmem
  simpa only [smul_smul, mul_inv_cancel₀ hr.ne', one_smul] using hmem

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.exists_tangent_radius_subset_of_isOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.exists_tangent_radius_subset_of_isOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.exists_tangent_radius_subset_of_isOpen ``Submission.DifferentialGeometry.Geometry.Topology.exists_tangent_radius_subset_of_isOpen

theorem tendsto_tangent_zero_of_tendsto_length
    (g : SmoothRiemannianMetric I M) {K : Set M} (hK : IsCompact K)
    {α : Type*} {l : Filter α} {b : α → M} {v : (i : α) → TangentSpace I (b i)}
    {p : M} (hmem : ∀ᶠ i in l, b i ∈ K) (hb : _root_.Filter.Tendsto b l (𝓝 p))
    (hv : _root_.Filter.Tendsto (fun i => Real.sqrt (g.inner (b i) (v i) (v i))) l (𝓝 0)) :
    _root_.Filter.Tendsto (fun i => (⟨b i, v i⟩ : TangentBundle I M)) l
      (𝓝 (⟨p, 0⟩ : TangentBundle I M)) := by
  rw [_root_.Filter.tendsto_def]
  intro U hU
  obtain ⟨V, hVU, hV, hpV⟩ := mem_nhds_iff.mp hU
  have hz : Continuous (fun x : M => (⟨x, 0⟩ : TangentBundle I M)) :=
    Bundle.Trivialization.continuous_zeroSection ℝ
  have hW := hV.preimage hz
  obtain ⟨δ, hδ, hδW⟩ := Metric.isOpen_iff.mp hW p hpV
  have hK' : IsCompact (K ∩ Metric.closedBall p (δ / 2)) :=
    hK.inter_right Metric.isClosed_closedBall
  have hzero : ∀ x ∈ K ∩ Metric.closedBall p (δ / 2),
      (⟨x, 0⟩ : TangentBundle I M) ∈ V := by
    intro x hx
    apply hδW
    exact Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hx.2) (by linarith))
  obtain ⟨ε, hε, hεV⟩ := exists_tangent_radius_subset_of_isOpen g hK' hV hzero
  have hb' : ∀ᶠ i in l, b i ∈ Metric.ball p (δ / 2) :=
    hb (Metric.ball_mem_nhds p (half_pos hδ))
  have hv' : ∀ᶠ i in l, Real.sqrt (g.inner (b i) (v i) (v i)) < ε :=
    hv (Iio_mem_nhds hε)
  filter_upwards [hmem, hb', hv'] with i hi hbi hvi
  exact hVU (hεV (b i) ⟨hi, Metric.mem_closedBall.mpr (Metric.mem_ball.mp hbi).le⟩ (v i) hvi)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.tendsto_tangent_zero_of_tendsto_length then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.tendsto_tangent_zero_of_tendsto_length"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.tendsto_tangent_zero_of_tendsto_length ``Submission.DifferentialGeometry.Geometry.Topology.tendsto_tangent_zero_of_tendsto_length

section NormalBundle

variable [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)]

theorem normalLength_continuous
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    {S : Set M} (hconv : IsTotallyConvex (I := I) g S) (hB : relBoundary I S = ∅) :
    let a := normalBundlePrebundle g hEnorm hconv hB
    let _ := a.totalSpaceTopology
    Continuous (fun z : _root_.Bundle.TotalSpace (Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ)
      (normalBundleFiber (I := I) g S) =>
        Real.sqrt (g.inner z.proj.1 z.snd.1 z.snd.1)) := by
  let a := normalBundlePrebundle g hEnorm hconv hB
  let _ := a.totalSpaceTopology
  exact Real.continuous_sqrt.comp ((tangentSquaredLength_contMDiff g).continuous.comp
    (normalBundleInclusion_isEmbedding g hEnorm hconv hB).continuous)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.normalLength_continuous then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.normalLength_continuous"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.normalLength_continuous ``Submission.DifferentialGeometry.Geometry.Topology.normalLength_continuous

theorem exists_normal_radius_subset_of_isOpen
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    {S : Set M} (hS : IsCompact S) (hconv : IsTotallyConvex (I := I) g S)
    (hB : relBoundary I S = ∅) :
    let a := normalBundlePrebundle g hEnorm hconv hB
    let _ := a.totalSpaceTopology
    ∀ U : Set (_root_.Bundle.TotalSpace (Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ)
        (normalBundleFiber (I := I) g S)), IsOpen U →
      (∀ p : S, (⟨p, 0⟩ : _root_.Bundle.TotalSpace _ (normalBundleFiber (I := I) g S)) ∈ U) →
      ∃ ε > 0, ∀ z : _root_.Bundle.TotalSpace _ (normalBundleFiber (I := I) g S),
        Real.sqrt (g.inner z.proj.1 z.snd.1 z.snd.1) < ε → z ∈ U := by
  classical
  let a := normalBundlePrebundle g hEnorm hconv hB
  let _ := a.totalSpaceTopology
  change ∀ U : Set (_root_.Bundle.TotalSpace (Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ)
      (normalBundleFiber (I := I) g S)), IsOpen U →
    (∀ p : S, (⟨p, 0⟩ : _root_.Bundle.TotalSpace _ (normalBundleFiber (I := I) g S)) ∈ U) →
    ∃ ε > 0, ∀ z : _root_.Bundle.TotalSpace _ (normalBundleFiber (I := I) g S),
      Real.sqrt (g.inner z.proj.1 z.snd.1 z.snd.1) < ε → z ∈ U
  intro U hU hzero
  have hi := normalBundleInclusion_isEmbedding g hEnorm hconv hB
  obtain ⟨V, hV, hVU⟩ := hi.isInducing.isOpen_iff.mp hU
  have hzeroV : ∀ x ∈ S, (⟨x, 0⟩ : TangentBundle I M) ∈ V := by
    intro x hx
    have hz := hzero ⟨x, hx⟩
    rw [← hVU] at hz
    exact hz
  obtain ⟨ε, hε, hεV⟩ := exists_tangent_radius_subset_of_isOpen g hS hV hzeroV
  refine ⟨ε, hε, ?_⟩
  intro z hz
  rw [← hVU]
  exact hεV z.proj.1 z.proj.2 z.snd.1 hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.exists_normal_radius_subset_of_isOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.exists_normal_radius_subset_of_isOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.exists_normal_radius_subset_of_isOpen ``Submission.DifferentialGeometry.Geometry.Topology.exists_normal_radius_subset_of_isOpen

theorem tendsto_normal_zero_of_tendsto_length
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    {S : Set M} (hS : IsCompact S) (hconv : IsTotallyConvex (I := I) g S)
    (hB : relBoundary I S = ∅) {α : Type*} {l : Filter α}
    (z : α → _root_.Bundle.TotalSpace (Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ)
      (normalBundleFiber (I := I) g S)) (p : S)
    (hb : _root_.Filter.Tendsto (fun i => (z i).proj.1) l (𝓝 p.1))
    (hv : _root_.Filter.Tendsto (fun i => Real.sqrt
      (g.inner (z i).proj.1 (z i).snd.1 (z i).snd.1)) l (𝓝 0)) :
    let a := normalBundlePrebundle g hEnorm hconv hB
    let _ := a.totalSpaceTopology
    Tendsto z l (𝓝 (⟨p, 0⟩ : _root_.Bundle.TotalSpace _ (normalBundleFiber (I := I) g S))) := by
  let a := normalBundlePrebundle g hEnorm hconv hB
  let _ := a.totalSpaceTopology
  apply (normalBundleInclusion_isEmbedding g hEnorm hconv hB).tendsto_nhds_iff.mpr
  exact tendsto_tangent_zero_of_tendsto_length g hS
    (Filter.Eventually.of_forall (fun i => (z i).proj.2)) hb hv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.tendsto_normal_zero_of_tendsto_length then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.tendsto_normal_zero_of_tendsto_length"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.tendsto_normal_zero_of_tendsto_length ``Submission.DifferentialGeometry.Geometry.Topology.tendsto_normal_zero_of_tendsto_length

end NormalBundle

end DifferentialGeometry.Geometry.Topology
