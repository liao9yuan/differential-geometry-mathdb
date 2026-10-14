import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckRegionBoundary
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedModelConvergence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckLimitTransport
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckParabolicTransport
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedShiTerminal

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

variable {M : ℕ → Type u} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace ThreeSpace (M i)]
  [∀ i, IsManifold I3 ∞ (M i)] [∀ i, T2Space (M i)] [∀ i, SigmaCompactSpace (M i)]

theorem StrongNeck.eventually_transport_of_windowed_models
    {D : ℕ → RealTimeInterval} {S : ∀ i, SolutionOn (I := I3) (M := M i) (D i)}
    (hS : ∀ i, IsSolutionOn (S i)) {delta : ℕ → ℝ} {kappa : ℝ}
    {x : ∀ i, M i} {t : ℕ → ℝ}
    (W : ∀ i, WindowedModelWitness (delta i) kappa (S i) (x i) (t i))
    (hdelta : _root_.Filter.Tendsto delta _root_.Filter.atTop (𝓝 0))
    (hreg : ∀ i, _root_.Set.Ioo (t i - (delta i * (S i).scalar (t i) (x i))⁻¹) (t i) ⊆ (D i).regular)
    (L : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)
    [PreconnectedSpace L.M] (hcomplete : MetricComplete (L.atTime 0))
    {phi : ℕ → ℕ} (hphi : _root_.Filter.Tendsto phi _root_.Filter.atTop _root_.Filter.atTop)
    (F : PointedRiemannianConvergenceMaps ⟨fun i => (W i).model.atTime 0⟩
      (L.atTime 0) phi)
    (hcmp : ∀ K : Set L.M, IsCompact K → ∀ A : ℝ, 0 < A → ∀ order : ℕ,
      ∀ eta : ℝ, 0 < eta → ∀ᶠ i in _root_.Filter.atTop,
        Nonempty (MetricComparisonOn L.S.base.metric (W (phi i)).model.S.base.metric
          (F.map i) K (_root_.Set.Icc (-A) 0) order eta))
    {eps alpha : ℝ} {p : L.M} (nk : StrongNeck L.S eps p 0)
    (ha : 0 < alpha) (hsmall : 2 * alpha < 1 / 11)
    (heps : eps < neckModelTolerance alpha) :
    ∀ᶠ i in _root_.Filter.atTop, ∃ nk' : StrongNeck (S (phi i)) (2 * alpha)
        ((W (phi i)).embedding (F.map i p)) (t (phi i)),
      nk'.map = partialDiffeomorphTransMixed nk.map
        (partialDiffeomorphTransMixed (F.partialDiffeomorph i) (W (phi i)).embedding) := by
  let Psi := fun i => partialDiffeomorphTransMixed (F.partialDiffeomorph i) (W (phi i)).embedding
  let T := fun i => parabolicSolution (S (phi i)) (t (phi i))
    ((S (phi i)).scalar (t (phi i)) (x (phi i))) (W (phi i)).scalar_pos (W (phi i)).time_mem
  have hT (i : ℕ) : IsSolutionOn (T i) :=
    parabolicSolution_isSolutionOn (S (phi i)) (hS (phi i)) _ _ _ _
  let B : Set Cylinder := _root_.Set.univ ×ˢ _root_.Set.Icc (-alpha⁻¹) alpha⁻¹
  have hB : IsCompact B := isCompact_univ.prod _root_.CompactIccSpace.isCompact_Icc
  have hrad : alpha⁻¹ < eps⁻¹ :=
    inv_strictAnti₀ nk.eps_pos (heps.trans_le (neckModelTolerance_le alpha))
  have hBsource : B ⊆ nk.map.source := by
    intro y hy
    exact nk.domain ⟨hy.1, by linarith [hy.2.1], by linarith [hy.2.2]⟩
  let K := nk.map '' B
  have hK : IsCompact K := hB.image_of_continuousOn
    (nk.map.contMDiffOn_toFun.continuousOn.mono hBsource)
  let _ : LocallyCompactSpace L.M := ChartedSpace.locallyCompactSpace ThreeSpace L.M
  let _ : RegularSpace L.M := inferInstance
  obtain ⟨U, hUopen, hKU, _hUuniv, hUcompact⟩ :=
    exists_open_between_and_isCompact_closure hK isOpen_univ (_root_.Set.subset_univ K)
  let U' : TopologicalSpace.Opens L.M := ⟨U, hUopen⟩
  let nk0 := nk.mono heps.le
    ((neckModelTolerance_le alpha).trans_lt (by linarith : alpha < 1 / 11))
  have houter : ∀ y ∈ _root_.Set.univ ×ˢ _root_.Set.Ioo (-alpha⁻¹) alpha⁻¹, nk0.map y ∈ K := by
    intro y hy
    exact ⟨y, ⟨hy.1, hy.2.1.le, hy.2.2.le⟩, rfl⟩
  have hcomp (A : ℝ) (hA : 0 < A) (order : ℕ) (eta : ℝ) (heta : 0 < eta) :
      ∀ᶠ i in _root_.Filter.atTop, closure U ⊆ (Psi i).source ∧
        Nonempty (MetricComparisonOn L.S.base.metric (T i).base.metric
          (Psi i) (closure U) (_root_.Set.Icc (-A) 0) order eta) :=
    WindowedModelWitness.eventually_composed_comparison hS W hdelta
      (fun i s hs => ((W i).normalized_window (hreg i)).2 hs) L hcomplete hphi F hcmp
      hUcompact hA order heta
  have hsource : ∀ᶠ i in _root_.Filter.atTop, (U' : Set L.M) ⊆ (Psi i).source :=
    (hcomp 1 zero_lt_one 0 1 zero_lt_one).mono fun _ hi => subset_closure.trans hi.1
  have hdinv : _root_.Filter.Tendsto (fun i => (delta (phi i))⁻¹) _root_.Filter.atTop atTop :=
    tendsto_inv_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.mpr
      ⟨hdelta.comp hphi, .of_forall fun i => (W (phi i)).eps_pos⟩)
  have htimes : ∀ A : ℝ, 0 < A → ∀ᶠ i in _root_.Filter.atTop,
      _root_.Set.Icc (-A) 0 ⊆ (parabolicInterval (D (phi i)) (t (phi i))
        ((S (phi i)).scalar (t (phi i)) (x (phi i))) (W (phi i)).time_mem).carrier ∧
      _root_.Set.Ioo (-A) 0 ⊆ (parabolicInterval (D (phi i)) (t (phi i))
        ((S (phi i)).scalar (t (phi i)) (x (phi i))) (W (phi i)).time_mem).regular := by
    intro A _hA
    filter_upwards [hdinv.eventually_ge_atTop A] with i hi
    obtain ⟨hcarrier, hregular⟩ := (W (phi i)).normalized_window (hreg (phi i))
    exact ⟨(_root_.Set.Icc_subset_Icc (neg_le_neg hi) le_rfl).trans hcarrier,
      (_root_.Set.Ioo_subset_Ioo (neg_le_neg hi) le_rfl).trans hregular⟩
  have hcompare : ∀ A : ℝ, 0 < A → ∀ order : ℕ, ∀ eta : ℝ, 0 < eta → ∀ᶠ i in _root_.Filter.atTop,
      Nonempty (MetricComparisonOn L.S.base.metric (T i).base.metric
        (Psi i) U' (_root_.Set.Icc (-A) 0) order eta) := by
    intro A hA order eta heta
    filter_upwards [hcomp A hA order eta heta] with i hi
    obtain ⟨C⟩ := hi.2
    exact ⟨C.mono subset_closure le_rfl le_rfl⟩
  have hnecks := nk0.eventually_transport_of_comparisons L.isSolution ha hsmall U' hUcompact
    hK hKU houter T hT Psi hsource htimes hcompare
  filter_upwards [hnecks] with i hi
  obtain ⟨nk', hmap⟩ := hi
  have hh : ∃ out : StrongNeck (S (phi i)) (2 * alpha) (Psi i p)
      (parabolicTime (t (phi i)) ((S (phi i)).scalar (t (phi i)) (x (phi i))) 0),
      out.map = partialDiffeomorphTransMixed nk.map (Psi i) := by
    refine ⟨nk'.ofParabolic (t (phi i)) ((S (phi i)).scalar (t (phi i)) (x (phi i)))
      (W (phi i)).scalar_pos (W (phi i)).time_mem 0, ?_⟩
    exact hmap
  rw [parabolicTime_zero] at hh
  exact hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.eventually_transport_of_windowed_models then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.eventually_transport_of_windowed_models"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.eventually_transport_of_windowed_models ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.eventually_transport_of_windowed_models

theorem LocalNeck.eventually_transport_of_windowed_models
    {D : ℕ → RealTimeInterval} {S : ∀ i, SolutionOn (I := I3) (M := M i) (D i)}
    (hS : ∀ i, IsSolutionOn (S i)) {delta : ℕ → ℝ} {kappa : ℝ}
    {x : ∀ i, M i} {t : ℕ → ℝ}
    (W : ∀ i, WindowedModelWitness (delta i) kappa (S i) (x i) (t i))
    (hdelta : _root_.Filter.Tendsto delta _root_.Filter.atTop (𝓝 0))
    (hreg : ∀ i, _root_.Set.Ioo (t i - (delta i * (S i).scalar (t i) (x i))⁻¹) (t i) ⊆ (D i).regular)
    (L : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)
    [PreconnectedSpace L.M] (hcomplete : MetricComplete (L.atTime 0))
    {phi : ℕ → ℕ} (hphi : _root_.Filter.Tendsto phi _root_.Filter.atTop _root_.Filter.atTop)
    (F : PointedRiemannianConvergenceMaps ⟨fun i => (W i).model.atTime 0⟩
      (L.atTime 0) phi)
    (hcmp : ∀ K : Set L.M, IsCompact K → ∀ A : ℝ, 0 < A → ∀ order : ℕ,
      ∀ eta : ℝ, 0 < eta → ∀ᶠ i in _root_.Filter.atTop,
        Nonempty (MetricComparisonOn L.S.base.metric (W (phi i)).model.S.base.metric
          (F.map i) K (_root_.Set.Icc (-A) 0) order eta))
    {eps alpha : ℝ} {p : L.M} {U : Set L.M} (nk : LocalNeck L.S eps p 0 U)
    (ha : 0 < alpha) (hsmall : 2 * alpha < 1 / 11)
    (heps : eps < neckModelTolerance alpha) :
    ∀ᶠ i in _root_.Filter.atTop, ∃ nk' : LocalNeck (S (phi i)) (2 * alpha)
        ((W (phi i)).embedding (F.map i p)) (t (phi i))
        ((partialDiffeomorphTransMixed (F.partialDiffeomorph i) (W (phi i)).embedding) '' U),
      nk'.strong.map = partialDiffeomorphTransMixed nk.strong.map
        (partialDiffeomorphTransMixed (F.partialDiffeomorph i) (W (phi i)).embedding) := by
  have hh := nk.strong.eventually_transport_of_windowed_models hS W hdelta hreg
    L hcomplete hphi F hcmp ha hsmall heps
  filter_upwards [hh] with i hi
  obtain ⟨nk', hmap⟩ := hi
  let Psi : PartialDiffeomorph I3 I3 L.M (M (phi i)) ∞ :=
    partialDiffeomorphTransMixed (F.partialDiffeomorph i) (W (phi i)).embedding
  have hregion : nk'.region = Psi '' U := by
    change nk'.map '' (_root_.Set.univ ×ˢ _root_.Set.Icc (-10 : ℝ) 10) = Psi '' U
    calc
      nk'.map '' (_root_.Set.univ ×ˢ _root_.Set.Icc (-10 : ℝ) 10) =
          Psi '' (nk.strong.map '' (_root_.Set.univ ×ˢ _root_.Set.Icc (-10 : ℝ) 10)) := by
        rw [hmap]
        exact (Set.image_image (fun y : L.M => Psi y) nk.strong.map
          (_root_.Set.univ ×ˢ _root_.Set.Icc (-10 : ℝ) 10)).symm
      _ = Psi '' U := congrArg (fun V : Set L.M => Psi '' V) nk.region_eq.symm
  have hout : ∃ out : LocalNeck (S (phi i)) (2 * alpha)
      ((W (phi i)).embedding (F.map i p)) (t (phi i)) nk'.region,
      out.strong.map = partialDiffeomorphTransMixed nk.strong.map Psi :=
    ⟨nk'.toLocalNeck, hmap⟩
  rwa [hregion] at hout

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalNeck.eventually_transport_of_windowed_models then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalNeck.eventually_transport_of_windowed_models"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalNeck.eventually_transport_of_windowed_models ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalNeck.eventually_transport_of_windowed_models


end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
