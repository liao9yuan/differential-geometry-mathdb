import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedComparisonComposition
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.BallImage

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Filter _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

variable {M : ℕ → Type u} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace ThreeSpace (M i)]
  [∀ i, IsManifold I3 ∞ (M i)] [∀ i, T2Space (M i)] [∀ i, SigmaCompactSpace (M i)]

theorem WindowedModelWitness.eventually_composed_comparison
    {D : ℕ → RealTimeInterval} {S : ∀ i, SolutionOn (I := I3) (M := M i) (D i)}
    (hS : ∀ i, IsSolutionOn (S i)) {delta : ℕ → ℝ} {kappa : ℝ}
    {x : ∀ i, M i} {t : ℕ → ℝ}
    (W : ∀ i, WindowedModelWitness (delta i) kappa (S i) (x i) (t i))
    (hdelta : _root_.Filter.Tendsto delta _root_.Filter.atTop (𝓝 0))
    (hreg : ∀ i s, s ∈ _root_.Set.Ioo (-modelDepth (delta i)) 0 →
      parabolicTime (t i) ((S i).scalar (t i) (x i)) s ∈ (D i).regular)
    (L : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)
    [PreconnectedSpace L.M] (hcomplete : MetricComplete (L.atTime 0))
    {phi : ℕ → ℕ} (hphi : _root_.Filter.Tendsto phi _root_.Filter.atTop _root_.Filter.atTop)
    (F : PointedRiemannianConvergenceMaps ⟨fun i => (W i).model.atTime 0⟩
      (L.atTime 0) phi)
    (hcmp : ∀ K : Set L.M, IsCompact K → ∀ A : ℝ, 0 < A → ∀ order : ℕ,
      ∀ alpha : ℝ, 0 < alpha → ∀ᶠ i in _root_.Filter.atTop,
        Nonempty (MetricComparisonOn L.S.base.metric (W (phi i)).model.S.base.metric
          (F.map i) K (_root_.Set.Icc (-A) 0) order alpha))
    {K : Set L.M} (hK : IsCompact K) {A : ℝ} (hA : 0 < A)
    (order : ℕ) {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ i in _root_.Filter.atTop,
      K ⊆ (partialDiffeomorphTransMixed (F.partialDiffeomorph i)
        (W (phi i)).embedding).source ∧
      Nonempty (MetricComparisonOn L.S.base.metric
        (rescaledMetric (S (phi i)) (t (phi i)) ((S (phi i)).scalar (t (phi i)) (x (phi i)))
          (W (phi i)).scalar_pos)
        (fun y => (W (phi i)).embedding (F.map i y)) K (_root_.Set.Icc (-A) 0) order eta) := by
  let _ : PreconnectedSpace (L.atTime 0).M := ‹PreconnectedSpace L.M›
  let _ : LocallyCompactSpace L.M := ChartedSpace.locallyCompactSpace ThreeSpace L.M
  let _ : RegularSpace L.M := inferInstance
  obtain ⟨U, hUopen, hKU, _hUuniv, hUcompact⟩ :=
    exists_open_between_and_isCompact_closure hK isOpen_univ (_root_.Set.subset_univ K)
  let U' : TopologicalSpace.Opens L.M := ⟨U, hUopen⟩
  have hupper : ∀ K' : Set L.M, IsCompact K' → ∀ᶠ i in _root_.Filter.atTop,
      ∀ z ∈ K', ∀ v : TangentSpace I3 z,
        ((W (phi i)).model.S.base.metric 0).inner (F.map i z)
          (mfderiv I3 I3 (F.map i) z v) (mfderiv I3 I3 (F.map i) z v) ≤
          (2 : ℝ) ^ 2 * (L.S.base.metric 0).inner z v v := by
    intro K' hK'
    filter_upwards [hcmp K' hK' 1 zero_lt_one 0 1 zero_lt_one] with i hi
    obtain ⟨C⟩ := hi
    intro z hz v
    have hh := (C.equivalence 0 (by norm_num) z hz v).2
    rw [C.pullback_eq 0 z hz (fun _ => v)] at hh
    have hn := inner_self_nonneg (L.S.base.metric 0) z v
    exact hh.trans (mul_le_mul_of_nonneg_right (by norm_num) hn)
  obtain ⟨R, hR, himage⟩ := F.exists_eventually_image_compact_subset_ball_of_metric_upper
    hcomplete (by norm_num : (0 : ℝ) < 2) hupper hUcompact
  let alpha := _root_.Min.min (eta / 2) (backgroundJetSmallness ThreeSpace order)
  have halpha : 0 < alpha := lt_min (by positivity) (backgroundJetSmallness_pos _ _)
  have halphaeta : alpha ≤ eta / 2 := min_le_left _ _
  have halphasmall : alpha ≤ backgroundJetSmallness ThreeSpace order := min_le_right _ _
  have hd : _root_.Filter.Tendsto (fun i => delta (phi i)) _root_.Filter.atTop (𝓝 0) := hdelta.comp hphi
  have hdpos : ∀ᶠ i in _root_.Filter.atTop, 0 < delta (phi i) := .of_forall fun i => (W (phi i)).eps_pos
  have hdinv : _root_.Filter.Tendsto (fun i => (delta (phi i))⁻¹) _root_.Filter.atTop atTop :=
    tendsto_inv_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.mpr ⟨hd, hdpos⟩)
  have hdrad : _root_.Filter.Tendsto (fun i => (Real.sqrt (delta (phi i)))⁻¹) _root_.Filter.atTop atTop := by
    apply tendsto_inv_nhdsGT_zero.comp
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨by simpa using hd.sqrt, hdpos.mono fun i hi => Real.sqrt_pos.mpr hi⟩
  have herr : ∀ᶠ i in _root_.Filter.atTop,
      backgroundJetConstant ThreeSpace order * ((order : ℝ) + 1) * delta (phi i) < eta / 2 := by
    have hh := hd.const_mul (backgroundJetConstant ThreeSpace order * ((order : ℝ) + 1))
    have hh' : _root_.Filter.Tendsto (fun i => backgroundJetConstant ThreeSpace order *
        ((order : ℝ) + 1) * delta (phi i)) _root_.Filter.atTop (𝓝 0) := by simpa only [_root_.MulZeroClass.mul_zero] using hh
    exact hh'.eventually_lt_const (by positivity : (0 : ℝ) < eta / 2)
  filter_upwards [himage, hdrad.eventually_ge_atTop R, hdinv.eventually_gt_atTop A,
    hdinv.eventually_ge_atTop (order : ℝ), herr,
    hcmp (closure U) hUcompact A hA order alpha halpha] with i hi hrad hdepth horder he hiCmp
  let Phi : PartialDiffeomorph I3 I3 L.M (W (phi i)).model.M ∞ := F.partialDiffeomorph i
  have hsource : (U' : Set L.M) ⊆ Phi.source :=
    subset_closure.trans hi.1
  have him : _root_.Set.MapsTo Phi (U' : Set L.M)
      (riemannianClosedBallOf ((W (phi i)).model.S.base.metric 0)
        (W (phi i)).model.basepoint (modelRadius (delta (phi i)))) := by
    intro y hy
    exact (riemannianClosedBallOf_mono _ _ hrad) (hi.2 ⟨y, subset_closure hy, rfl⟩)
  have hceil : order ≤ ⌈(delta (phi i))⁻¹⌉₊ := by
    exact_mod_cast horder.trans (Nat.le_ceil ((delta (phi i))⁻¹))
  have horder' : order ≤ modelOrder (delta (phi i)) := hceil.trans (Nat.le_succ _)
  obtain ⟨C⟩ := hiCmp
  obtain ⟨C'⟩ := (W (phi i)).exists_composed_comparison (hS (phi i)) (hreg (phi i)) L
    Phi U' hsource him hA hdepth horder' halpha halphasmall
    (C.mono subset_closure le_rfl le_rfl) hK hKU
  refine ⟨?_, ⟨C'.mono subset_rfl le_rfl (by linarith)⟩⟩
  intro y hy
  refine ⟨hsource (hKU hy), ?_⟩
  exact (W (phi i)).buffered_ball
    ((riemannianClosedBallOf_mono _ _ (le_add_of_nonneg_right zero_le_one)) (him (hKU hy)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.WindowedModelWitness.eventually_composed_comparison then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.WindowedModelWitness.eventually_composed_comparison"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.WindowedModelWitness.eventually_composed_comparison ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.WindowedModelWitness.eventually_composed_comparison

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
