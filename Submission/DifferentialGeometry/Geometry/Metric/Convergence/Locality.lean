import Submission.DifferentialGeometry.Geometry.Metric.Convergence.Time.Lipschitz
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Continuity
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Restriction
import Mathlib.Topology.Compactness.LocallyCompact
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Pullback
import Submission.DifferentialGeometry.Geometry.Metric.Pullback.Local
import Submission.DifferentialGeometry.Topology.Manifold.LocalDiffeomorphRange

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

set_option autoImplicit false
noncomputable section
open _root_.Filter _root_.Set
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Topology
namespace DifferentialGeometry.CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

theorem metricCInfConvergenceOnCompacts_of_local_norm_convergence
    (gSeq : ℕ → SmoothRiemannianMetric I M) (gInf gRef : SmoothRiemannianMetric I M)
    (hloc : ∀ x : M, ∃ U : Set M, U ∈ 𝓝 x ∧
      ∀ p : ℕ, ∀ ε : ℝ, 0 < ε → ∀ᶠ k in _root_.Filter.atTop,
        ∀ a ≤ p, ∀ y ∈ U, metricDerivNorm (I := I) a (gSeq k) gInf gRef y < ε) :
    MetricCInfConvergenceOnCompacts (I := I) gSeq gInf gRef := by
  classical
  intro K hK p ε hε
  choose U hU hconv using hloc
  obtain ⟨s, hs⟩ := hK.elim_nhds_subcover' (fun x _ => U x) (fun x _ => hU x)
  have hevent : ∀ᶠ k in _root_.Filter.atTop,
      ∀ x ∈ s, ∀ a ≤ p, ∀ y ∈ U x,
        metricDerivNorm (I := I) a (gSeq k) gInf gRef y < ε / 2 := by
    exact s.finite_toSet.eventually_all.mpr fun x _ => hconv x p (ε / 2) (by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  refine ⟨N, fun k hk => ?_⟩
  apply lt_of_le_of_lt
    (metricDerivNormSupOn_le_of_forall K p (gSeq k) gInf gRef
      (ε / 2) (by positivity) ?_) (by linarith)
  intro a ha y hy
  obtain ⟨x, hx, hyU⟩ := mem_iUnion₂.mp (hs hy)
  exact (hN k hk x hx a ha y hyU).le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.metricCInfConvergenceOnCompacts_of_local_norm_convergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.metricCInfConvergenceOnCompacts_of_local_norm_convergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.metricCInfConvergenceOnCompacts_of_local_norm_convergence ``Submission.DifferentialGeometry.CheegerGromovCompactness.metricCInfConvergenceOnCompacts_of_local_norm_convergence

theorem metricCInfConvergenceOnCompacts_of_restrict_open_cover
    {ι : Type*} (U : ι → TopologicalSpace.Opens M)
    [∀ i, SigmaCompactSpace (U i)]
    (hcover : ∀ x : M, ∃ i, x ∈ U i)
    (gSeq : ℕ → SmoothRiemannianMetric I M) (gInf gRef : SmoothRiemannianMetric I M)
    (hconv : ∀ i, MetricCInfConvergenceOnCompacts (I := I)
      (fun k => (gSeq k).restrictOpen (U i))
      (gInf.restrictOpen (U i)) (gRef.restrictOpen (U i))) :
    MetricCInfConvergenceOnCompacts (I := I) gSeq gInf gRef := by
  let : LocallyCompactSpace H := I.locallyCompactSpace
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  apply metricCInfConvergenceOnCompacts_of_local_norm_convergence gSeq gInf gRef
  intro x
  obtain ⟨i, hxi⟩ := hcover x
  obtain ⟨K, hK, hxK, hKU⟩ := exists_compact_subset (U i).isOpen hxi
  have hpre : IsCompact ((Subtype.val : U i → M) ⁻¹' K) :=
    Topology.IsInducing.subtypeVal.isCompact_preimage' hK
      (by simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq] using hKU)
  refine ⟨K, _root_.Filter.mem_of_superset (isOpen_interior.mem_nhds hxK) interior_subset,
    fun p ε hε => ?_⟩
  obtain ⟨N, hN⟩ := hconv i _ hpre p ε hε
  filter_upwards [_root_.Filter.eventually_ge_atTop N] with k hk
  intro a ha y hy
  have hn := derivNorm_le_sup (I := I) hpre ha
    ((gSeq k).restrictOpen (U i)) (gInf.restrictOpen (U i))
    (gRef.restrictOpen (U i)) (x := (⟨y, hKU hy⟩ : U i)) hy
  rw [metricDerivNorm_restrictOpen] at hn
  exact hn.trans_lt (hN k hk)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.metricCInfConvergenceOnCompacts_of_restrict_open_cover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.metricCInfConvergenceOnCompacts_of_restrict_open_cover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.metricCInfConvergenceOnCompacts_of_restrict_open_cover ``Submission.DifferentialGeometry.CheegerGromovCompactness.metricCInfConvergenceOnCompacts_of_restrict_open_cover

end DifferentialGeometry.CheegerGromovCompactness

end

end

section

set_option autoImplicit false
noncomputable section
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Topology
namespace DifferentialGeometry.CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

theorem metricCInfConvergenceOnCompacts_of_diffeomorph_open_cover
    {ι : Type*} (U : ι → TopologicalSpace.Opens M)
    [∀ i, SigmaCompactSpace (U i)]
    (hcover : ∀ x : M, ∃ i, x ∈ U i)
    {N : ι → Type*} [∀ i, TopologicalSpace (N i)] [∀ i, ChartedSpace H (N i)]
    [∀ i, IsManifold I ∞ (N i)] [∀ i, T2Space (N i)]
    (e : ∀ i, N i ≃ₘ⟮I, I⟯ U i)
    (gSeq : ℕ → SmoothRiemannianMetric I M) (gInf gRef : SmoothRiemannianMetric I M)
    (hconv : ∀ i, MetricCInfConvergenceOnCompacts (I := I)
      (fun k => Diffeomorph.pullbackMetric ((gSeq k).restrictOpen (U i)) (e i))
      (Diffeomorph.pullbackMetric (gInf.restrictOpen (U i)) (e i))
      (Diffeomorph.pullbackMetric (gRef.restrictOpen (U i)) (e i))) :
    MetricCInfConvergenceOnCompacts (I := I) gSeq gInf gRef := by
  apply metricCInfConvergenceOnCompacts_of_restrict_open_cover U hcover gSeq gInf gRef
  intro i
  have h := metricCInf_pullback
    (fun k => Diffeomorph.pullbackMetric ((gSeq k).restrictOpen (U i)) (e i))
    (Diffeomorph.pullbackMetric (gInf.restrictOpen (U i)) (e i))
    (Diffeomorph.pullbackMetric (gRef.restrictOpen (U i)) (e i))
    (e i).symm (hconv i)
  simpa only [Diffeomorph.pullbackMetric_trans, Diffeomorph.symm_trans_self,
    Diffeomorph.pullbackMetric_refl] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.metricCInfConvergenceOnCompacts_of_diffeomorph_open_cover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.metricCInfConvergenceOnCompacts_of_diffeomorph_open_cover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.metricCInfConvergenceOnCompacts_of_diffeomorph_open_cover ``Submission.DifferentialGeometry.CheegerGromovCompactness.metricCInfConvergenceOnCompacts_of_diffeomorph_open_cover

end DifferentialGeometry.CheegerGromovCompactness

end

end

section

set_option autoImplicit false
noncomputable section
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Topology
namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

theorem localPullMetric_eq_pullbackMetric_range
    {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]
    (g : SmoothRiemannianMetric I M) (f : N → M)
    (hf : IsLocalDiffeomorph I I ∞ f) (hinj : Function.Injective f) :
    localPullMetric g f hf = Diffeomorph.pullbackMetric (g.restrictOpen hf.image)
      (Topology.diffeomorphRangeOfInjective hf hinj) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [localPullMetric_inner, Diffeomorph.pullbackMetric_inner,
    SmoothRiemannianMetric.restrictOpen_inner]
  have hd := DifferentialGeometry.mfderiv_subtypeVal_comp (I := I) (J := I)
    (Topology.diffeomorphRangeOfInjective hf hinj) x
  exact congrArg₂ (fun a b => g.inner (f x) a b)
    (DFunLike.congr_fun hd v) (DFunLike.congr_fun hd w)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.localPullMetric_eq_pullbackMetric_range then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.localPullMetric_eq_pullbackMetric_range"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.localPullMetric_eq_pullbackMetric_range ``Submission.DifferentialGeometry.localPullMetric_eq_pullbackMetric_range

namespace CheegerGromovCompactness

variable [CompleteSpace E]

theorem metricCInfConvergenceOnCompacts_of_injective_localDiffeomorph_cover
    {ι : Type*} {N : ι → Type*}
    [∀ i, TopologicalSpace (N i)] [∀ i, ChartedSpace H (N i)]
    [∀ i, IsManifold I ∞ (N i)] [∀ i, T2Space (N i)] [∀ i, SigmaCompactSpace (N i)]
    (f : ∀ i, N i → M) (hf : ∀ i, IsLocalDiffeomorph I I ∞ (f i))
    (hinj : ∀ i, Function.Injective (f i))
    (hcover : ∀ x : M, ∃ i y, f i y = x)
    (gSeq : ℕ → SmoothRiemannianMetric I M) (gInf gRef : SmoothRiemannianMetric I M)
    (hconv : ∀ i, MetricCInfConvergenceOnCompacts (I := I)
      (fun k => localPullMetric (gSeq k) (f i) (hf i))
      (localPullMetric gInf (f i) (hf i)) (localPullMetric gRef (f i) (hf i))) :
    MetricCInfConvergenceOnCompacts (I := I) gSeq gInf gRef := by
  let U : ι → TopologicalSpace.Opens M := fun i => (hf i).image
  let e := fun i => Topology.diffeomorphRangeOfInjective (hf i) (hinj i)
  let _ : ∀ i, SigmaCompactSpace (U i) := fun i =>
    isSigmaCompact_iff_sigmaCompactSpace.mp (isSigmaCompact_range (hf i).contMDiff.continuous)
  apply metricCInfConvergenceOnCompacts_of_diffeomorph_open_cover U
    (fun x => by obtain ⟨i, y, hy⟩ := hcover x; exact ⟨i, y, hy⟩)
    e gSeq gInf gRef
  intro i
  simpa only [localPullMetric_eq_pullbackMetric_range _ _ (hf i) (hinj i)] using hconv i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.metricCInfConvergenceOnCompacts_of_injective_localDiffeomorph_cover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.metricCInfConvergenceOnCompacts_of_injective_localDiffeomorph_cover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.metricCInfConvergenceOnCompacts_of_injective_localDiffeomorph_cover ``Submission.DifferentialGeometry.CheegerGromovCompactness.metricCInfConvergenceOnCompacts_of_injective_localDiffeomorph_cover

end CheegerGromovCompactness
end DifferentialGeometry

end

end
