import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.MetricEnergy.FirstVariation
import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.WeakReplacement
import Submission.DifferentialGeometry.Geometry.HarmonicMap.Variation
import Submission.DifferentialGeometry.Geometry.HarmonicMap.WeakCoordinates
import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.ContinuousRepresentative

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Filter _root_.Submission.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Topology
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.NNReal _root_.ENNReal _root_.Topology

namespace DifferentialGeometry.Geometry

local notation "V" => EuclideanSpace ℝ (Fin 2)

private theorem restrict_ball_eq_restrict_closedBall_plane (a : ℝ) :
    volume.restrict (Metric.ball (0 : V) a) =
      volume.restrict (Metric.closedBall (0 : V) a) := by
  rw [← (measurePreserving_complex_plane_repr_ball a).map_eq,
    ← (measurePreserving_complex_plane_repr_closedBall a).map_eq,
    restrict_ball_eq_restrict_closedBall_complex]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.restrict_ball_eq_restrict_closedBall_plane
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.restrict_ball_eq_restrict_closedBall_plane target :: scope.openDecls } }


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M]

local notation "F" => EuclideanSpace ℝ (Fin n)

theorem integral_pullback_metric_energy_variation_eq_zero_of_disk_energy_minimizing_sequence
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Φ : M → F}
    (hΦ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ Φ)
    {r : F → M} {U : Set F} (hU : IsOpen U)
    (hr : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ r U)
    (hΦU : _root_.Set.range Φ ⊆ U) (hleft : Function.LeftInverse r Φ)
    {γ : freeLoop M} (u : ℕ → C(closedDisk, M))
    (hu : ∀ n, u n ∈ weaklyMonotoneDiskCompetitors g γ)
    (hmin : _root_.Filter.Tendsto (fun n => riemannianDiskEnergy g (u n)) _root_.Filter.atTop
      (𝓝 (_root_.InfSet.sInf ((fun v : C(closedDisk, M) => riemannianDiskEnergy g v) ''
        weaklyMonotoneDiskCompetitors g γ))))
    (hs : ∀ n i, DeGiorgi.MemW1pWitness 2
      (fun x => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)) i)
      (Metric.ball 0 1))
    (w : V → F) (hw : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => w x i) (Metric.ball 0 1))
    (hrep : ∀ n i j, (fun x => (hs n i).weakGrad x j) =ᵐ[
      volume.restrict (Metric.ball (0 : V) 1)]
      (fun x => fderiv ℝ
        (fun y => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm y)) i)
        x (EuclideanSpace.single j 1)))
    (hL2 : _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x =>
      Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)) - w x)
      2 (volume.restrict (Metric.ball 0 1))) _root_.Filter.atTop (𝓝 0))
    (hae : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : V) 1),
      _root_.Filter.Tendsto (fun n => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)))
        _root_.Filter.atTop (𝓝 (w x)))
    (hweak : ∀ i (z : _root_.MeasureTheory.Lp V 2 (volume.restrict (Metric.ball 0 1))),
      _root_.Filter.Tendsto (fun n => _root_.Inner.inner ℝ (DeGiorgi.gradLpOfWitness (hs n i)) z) _root_.Filter.atTop
        (𝓝 (_root_.Inner.inner ℝ (DeGiorgi.gradLpOfWitness (hw i)) z)))
    {φ : V → F} (hφ : ContDiff ℝ ∞ φ) (hφB : tsupport φ ⊆ Metric.ball (0 : V) 1) :
    (∫ x in Metric.ball (0 : V) 1, ∑ j : Fin 2,
      ((fderiv ℝ (pullbackMetricCoefficients g r) (w x) (φ x))
        (DeGiorgi.weakGradientColumn hw x j) (DeGiorgi.weakGradientColumn hw x j) +
      2 * pullbackMetricCoefficients g r (w x) (DeGiorgi.weakGradientColumn hw x j)
        (fderiv ℝ φ x (EuclideanSpace.single j 1)))) = 0 := by
  classical
  let A := pullbackMetricCoefficients g r
  let K := _root_.Set.range Φ
  have hK : IsCompact K := isCompact_range hΦ.continuous
  have hA : ContDiffOn ℝ 1 A U :=
    (contDiffOn_pullback_metric_coefficients g hU hr).of_le (by simp)
  have hwK : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : V) 1), w x ∈ K :=
    hae.mono fun x hx => hK.isClosed.mem_of_tendsto hx
      (Eventually.of_forall fun _ => _root_.Set.mem_range_self _)
  have hφs : HasCompactSupport φ :=
    (_root_.ProperSpace.isCompact_closedBall (0 : V) 1).of_isClosed_subset (isClosed_tsupport φ)
      (hφB.trans Metric.ball_subset_closedBall)
  obtain ⟨a₀, ha₀, hφa₀⟩ := exists_lt_subset_ball (isClosed_tsupport φ) hφB
  let a : ℝ := _root_.Max.max a₀ (1 / 2)
  have ha : 0 < a := (by norm_num : (0 : ℝ) < 1 / 2).trans_le (le_max_right _ _)
  have ha1 : a < 1 := max_lt ha₀ (by norm_num)
  have hφa : tsupport φ ⊆ Metric.ball (0 : V) a :=
    hφa₀.trans (Metric.ball_subset_ball (le_max_left _ _))
  let c : ℝ := (a + 1) / 2
  have hac : a < c := by dsimp only [c]; linarith
  have hc1 : c < 1 := by dsimp only [c]; linarith
  let hwa (i : Fin n) : DeGiorgi.MemW1pWitness 2 (fun x => w x i) (Metric.ball (0 : V) a) :=
    DeGiorgi.MemW1pWitness.restrict Metric.isOpen_ball (Metric.ball_subset_ball ha1.le) (hw i)
  have hwKa : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : V) a), w x ∈ K :=
    _root_.MeasureTheory.ae_mono (Measure.restrict_mono_set _root_.MeasureTheory.MeasureSpace.volume (Metric.ball_subset_ball ha1.le)) hwK
  have hret : ContDiffOn ℝ ∞ (Φ ∘ r) U := (hΦ.comp_contMDiffOn hr).contDiffOn
  have hretK : _root_.Set.MapsTo (Φ ∘ r) U K := fun y _ => _root_.Set.mem_range_self _
  have hretfix : ∀ y ∈ K, (Φ ∘ r) y = y := by
    rintro y ⟨p, rfl⟩
    exact congrArg Φ (hleft p)
  obtain ⟨Ut, T, L, hUt, hKUt, hUtU, hTeq, hT, _, _, hTL, _, _⟩ :=
    DifferentialGeometry.Analysis.exists_contDiff_retraction_extension_fderiv_bound
      hK hU hΦU (Φ ∘ r) hret hretK hretfix
  obtain ⟨P₀, hP₀⟩ := hφ.continuous.bounded_above_of_compact_support hφs
  let P : ℝ := _root_.Max.max P₀ 0
  have hP : 0 ≤ P := le_max_right _ _
  have hPφ (x : V) : ‖φ x‖ ≤ P := (hP₀ x).trans (le_max_left _ _)
  obtain ⟨δ, hδ, C, _, hbound⟩ := exists_compact_metric_range_bounds
    hUt (hA.mono hUtU) hK hKUt P hP
  have hsym (y : F) (_hy : y ∈ K) (v z : F) : A y v z = A y z v := by
    exact g.symm (r y) _ _
  have hmin : ∀ᶠ t in 𝓝 (0 : ℝ), metricDirichletEnergy A hwa ≤
      metricDirichletEnergy A
        (DeGiorgi.componentAffineVariationWitness Metric.isOpen_ball hwa hφ hφs t) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with t ht
    have htδ : |t| < δ := by
      simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using ht
    have htU : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : V) c), w x + t • φ x ∈ Ut := by
      filter_upwards [_root_.MeasureTheory.ae_mono (Measure.restrict_mono_set _root_.MeasureTheory.MeasureSpace.volume
        (Metric.ball_subset_ball hc1.le)) hwK] with x hx
      exact (hbound (w x) hx (φ x) (hPφ x) t htδ).1
    obtain ⟨hqt, _, hqtK, hqtOutside, _, hqtEnergy⟩ :=
      exists_retracted_affine_variation_memW1p_energy_eq g (hΦ.of_le (by simp)) hU
        (hr.of_le (by simp)) hleft hUt hKUt hUtU T (hT.of_le (by simp)) hTL hTeq
        Metric.isOpen_ball hw hwK (Metric.closedBall_subset_ball hc1)
        hφ (hφa.trans (Metric.ball_subset_ball hac.le)) t htU
    have hqtCollar : (fun x => T (w x + t • φ x)) =ᵐ[
        volume.restrict (Metric.ball (0 : V) c \ Metric.closedBall 0 a)] w := by
      have hsub : Metric.ball (0 : V) c \ Metric.closedBall 0 a ⊆ Metric.ball (0 : V) 1 :=
        sdiff_subset.trans (Metric.ball_subset_ball hc1.le)
      filter_upwards [_root_.MeasureTheory.ae_mono (Measure.restrict_mono_set _root_.MeasureTheory.MeasureSpace.volume hsub) hqtOutside,
        _root_.MeasureTheory.ae_restrict_mem (Metric.isOpen_ball.measurableSet.diff measurableSet_closedBall)]
        with x hx hxC
      apply hx
      exact fun hxφ => hxC.2 (Metric.ball_subset_closedBall (hφa hxφ))
    have hlocal := weak_replacement_energy_le_of_disk_energy_minimizing_sequence
      g hΦ hU hr hΦU hleft u hu hmin hs w hw hrep hL2 hae hweak ha hac hc1
      (fun x => T (w x + t • φ x)) hqt hqtK hqtCollar
    let haff := DeGiorgi.componentAffineVariationWitness Metric.isOpen_ball hwa hφ hφs t
    have hbaseM : _root_.MeasureTheory.MemLp w 2 (volume.restrict (Metric.ball (0 : V) a)) :=
      MemLp.of_eval_piLp fun i => (hwa i).memLp
    have haffM : _root_.MeasureTheory.MemLp (fun x => w x + t • φ x) 2
        (volume.restrict (Metric.ball (0 : V) a)) :=
      MemLp.of_eval_piLp fun i => (haff i).memLp
    have hAm : Measurable (Ut.piecewise A 0) :=
      (hA.continuousOn.mono hUtU).measurable_piecewise
        continuous_zero.continuousOn hUt.measurableSet
    have hbaseA : _root_.MeasureTheory.AEStronglyMeasurable (fun x => A (w x))
        (volume.restrict (Metric.ball (0 : V) a)) := by
      apply (hAm.comp_aemeasurable hbaseM.aemeasurable).aestronglyMeasurable.congr
      filter_upwards [hwKa] with x hx
      exact Set.piecewise_eq_of_mem Ut A 0 (hKUt hx)
    have haffA : _root_.MeasureTheory.AEStronglyMeasurable (fun x => A (w x + t • φ x))
        (volume.restrict (Metric.ball (0 : V) a)) := by
      apply (hAm.comp_aemeasurable haffM.aemeasurable).aestronglyMeasurable.congr
      filter_upwards [hwKa] with x hx
      exact Set.piecewise_eq_of_mem Ut A 0 (hbound (w x) hx (φ x) (hPφ x) t htδ).1
    have hbaseBound : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : V) a), ‖A (w x)‖ ≤ C := by
      filter_upwards [hwKa] with x hx
      simpa only [zero_smul, add_zero] using
        (hbound (w x) hx (φ x) (hPφ x) 0 (by simpa using hδ)).2.1
    have haffBound : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : V) a),
        ‖A (w x + t • φ x)‖ ≤ C :=
      hwKa.mono fun x hx => (hbound (w x) hx (φ x) (hPφ x) t htδ).2.1
    have hiBase (j : Fin 2) := integrable_quadratic_weakGradientColumn hwa
      (fun x => A (w x)) hbaseA hbaseBound j
    have hiAff (j : Fin 2) := integrable_quadratic_weakGradientColumn haff
      (fun x => A (w x + t • φ x)) haffA haffBound j
    have heq (j : Fin 2) : (∫ x in Metric.closedBall (0 : V) a,
        A (T (w x + t • φ x)) (DeGiorgi.weakGradientColumn hqt x j)
          (DeGiorgi.weakGradientColumn hqt x j)) =
        ∫ x in Metric.ball (0 : V) a, A (w x + t • φ x)
          (DeGiorgi.weakGradientColumn haff x j) (DeGiorgi.weakGradientColumn haff x j) := by
      rw [← restrict_ball_eq_restrict_closedBall_plane]
      apply _root_.MeasureTheory.integral_congr_ae
      filter_upwards [_root_.MeasureTheory.ae_mono (Measure.restrict_mono_set _root_.MeasureTheory.MeasureSpace.volume
        (Metric.ball_subset_ball hac.le)) hqtEnergy] with x hx
      change A (T (w x + t • φ x)) (DeGiorgi.weakGradientColumn hqt x j)
          (DeGiorgi.weakGradientColumn hqt x j) =
        A (w x + t • φ x)
          (DeGiorgi.weakGradientColumn
            (DeGiorgi.componentAffineVariationWitness Metric.isOpen_ball hwa hφ hφs t) x j)
          (DeGiorgi.weakGradientColumn
            (DeGiorgi.componentAffineVariationWitness Metric.isOpen_ball hwa hφ hφs t) x j)
      rw [DeGiorgi.weakGradientColumn_componentAffineVariationWitness]
      exact hx j
    change (∑ j, ∫ x in Metric.closedBall (0 : V) a,
      A (w x) (DeGiorgi.weakGradientColumn hwa x j) (DeGiorgi.weakGradientColumn hwa x j)) ≤
        ∑ j, ∫ x in Metric.closedBall (0 : V) a,
          A (T (w x + t • φ x)) (DeGiorgi.weakGradientColumn hqt x j)
            (DeGiorgi.weakGradientColumn hqt x j) at hlocal
    simp_rw [heq, ← restrict_ball_eq_restrict_closedBall_plane] at hlocal
    unfold metricDirichletEnergy
    rw [_root_.MeasureTheory.integral_finsetSum _ (fun j _ => hiBase j),
      _root_.MeasureTheory.integral_finsetSum _ (fun j _ => hiAff j)]
    exact hlocal
  have hel := integral_metric_energy_variation_eq_zero_of_eventually_energy_le
    Metric.isOpen_ball hwa hU hA hK hΦU hwKa hsym hφ hφs hmin
  have houtside (x : V) (hx : x ∉ Metric.ball (0 : V) a) :
      (∑ j : Fin 2, ((fderiv ℝ A (w x) (φ x))
          (DeGiorgi.weakGradientColumn hw x j) (DeGiorgi.weakGradientColumn hw x j) +
        2 * A (w x) (DeGiorgi.weakGradientColumn hw x j)
          (fderiv ℝ φ x (EuclideanSpace.single j 1)))) = 0 := by
    have hxφ : x ∉ tsupport φ := fun hx' => hx (hφa hx')
    rw [image_eq_zero_of_notMem_tsupport hxφ, fderiv_of_notMem_tsupport ℝ hxφ]
    simp only [map_zero, zero_apply, _root_.MulZeroClass.mul_zero, add_zero, Finset.sum_const_zero]
  change (∫ x in Metric.ball (0 : V) 1, ∑ j : Fin 2,
    ((fderiv ℝ A (w x) (φ x)) (DeGiorgi.weakGradientColumn hw x j)
      (DeGiorgi.weakGradientColumn hw x j) + 2 * A (w x) (DeGiorgi.weakGradientColumn hw x j)
        (fderiv ℝ φ x (EuclideanSpace.single j 1)))) = 0
  rw [_root_.MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero Metric.isOpen_ball.measurableSet
    (Metric.ball_subset_ball ha1.le) (fun x hx => houtside x hx.2)]
  exact hel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.integral_pullback_metric_energy_variation_eq_zero_of_disk_energy_minimizing_sequence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.integral_pullback_metric_energy_variation_eq_zero_of_disk_energy_minimizing_sequence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.integral_pullback_metric_energy_variation_eq_zero_of_disk_energy_minimizing_sequence ``Submission.DifferentialGeometry.Geometry.integral_pullback_metric_energy_variation_eq_zero_of_disk_energy_minimizing_sequence

end DifferentialGeometry.Geometry

end

noncomputable section

open _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Filter _root_.Submission.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Topology
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.NNReal _root_.ENNReal _root_.Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M]

local notation "V" => EuclideanSpace ℝ (Fin 2)
local notation "F" => EuclideanSpace ℝ (Fin n)
local notation "H" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

theorem exists_continuous_weak_euler_lagrange_representative_of_disk_energy_minimizing_sequence
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Φ : M → F}
    (hΦ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ Φ)
    {r : F → M} {U : Set F} (hU : IsOpen U)
    (hr : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ r U)
    (hΦU : _root_.Set.range Φ ⊆ U) (hleft : Function.LeftInverse r Φ)
    {γ : freeLoop M} (u : ℕ → C(closedDisk, M))
    (hu : ∀ n, u n ∈ weaklyMonotoneDiskCompetitors g γ)
    (hmin : _root_.Filter.Tendsto (fun n => riemannianDiskEnergy g (u n)) _root_.Filter.atTop
      (𝓝 (_root_.InfSet.sInf ((fun v : C(closedDisk, M) => riemannianDiskEnergy g v) ''
        weaklyMonotoneDiskCompetitors g γ))))
    (hs : ∀ n i, DeGiorgi.MemW1pWitness 2
      (fun x => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)) i)
      (Metric.ball 0 1))
    (w : V → F) (hw : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => w x i) (Metric.ball 0 1))
    (hrep : ∀ n i j, (fun x => (hs n i).weakGrad x j) =ᵐ[
      volume.restrict (Metric.ball (0 : V) 1)]
      (fun x => fderiv ℝ
        (fun y => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm y)) i)
        x (EuclideanSpace.single j 1)))
    (hL2 : _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x =>
      Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)) - w x)
      2 (volume.restrict (Metric.ball 0 1))) _root_.Filter.atTop (𝓝 0))
    (hae : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : V) 1),
      _root_.Filter.Tendsto (fun n => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)))
        _root_.Filter.atTop (𝓝 (w x)))
    (hweak : ∀ i (z : _root_.MeasureTheory.Lp V 2 (volume.restrict (Metric.ball 0 1))),
      _root_.Filter.Tendsto (fun n => _root_.Inner.inner ℝ (DeGiorgi.gradLpOfWitness (hs n i)) z) _root_.Filter.atTop
        (𝓝 (_root_.Inner.inner ℝ (DeGiorgi.gradLpOfWitness (hw i)) z)))
    : ∃ (v : V → F) (hv : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => v x i) (Metric.ball 0 1)),
      ContinuousOn v (Metric.ball (0 : V) 1) ∧
      (v =ᵐ[volume.restrict (Metric.ball (0 : V) 1)] w) ∧
      _root_.Set.MapsTo v (Metric.ball (0 : V) 1) (_root_.Set.range Φ) ∧
      (∀ i, (hv i).weakGrad = (hw i).weakGrad) ∧
      (∀ φ : V → F, ContDiff ℝ ∞ φ → tsupport φ ⊆ Metric.ball (0 : V) 1 →
        (∫ x in Metric.ball (0 : V) 1, ∑ j : Fin 2,
          ((fderiv ℝ (pullbackMetricCoefficients g r) (v x) (φ x))
            (DeGiorgi.weakGradientColumn hv x j) (DeGiorgi.weakGradientColumn hv x j) +
          2 * pullbackMetricCoefficients g r (v x) (DeGiorgi.weakGradientColumn hv x j)
            (fderiv ℝ φ x (EuclideanSpace.single j 1)))) = 0) ∧
      ∀ x₀ ∈ Metric.ball (0 : V) 1,
        let p := r (v x₀)
        let χ : F → H := fun y => toEuclidean (extChartAt 𝓘(ℝ, E) p (r y))
        let z : V → H := χ ∘ v
        ∃ ρ : ℝ, 0 < ρ ∧ Metric.closedBall x₀ ρ ⊆ Metric.ball (0 : V) 1 ∧
          _root_.Set.MapsTo (r ∘ v) (Metric.closedBall x₀ ρ) (extChartAt 𝓘(ℝ, E) p).source ∧
          _root_.Set.MapsTo z (Metric.closedBall x₀ ρ)
            (DifferentialGeometry.Analysis.Laplacian.MetricExtension.chartTargetEuclid
              (I := 𝓘(ℝ, E)) p) ∧ ContinuousOn z (Metric.closedBall x₀ ρ) ∧
          (∀ x ∈ Metric.closedBall x₀ ρ,
            (extChartAt 𝓘(ℝ, E) p).symm ((toEuclidean (E := E)).symm (z x)) = r (v x)) ∧
          ∃ hz : ∀ k, DeGiorgi.MemW1pWitness 2 (fun x => z x k) (Metric.ball x₀ ρ),
            ∀ x ∈ Metric.ball x₀ ρ, ∀ j,
              WithLp.toLp 2 (fun k => (hz k).weakGrad x j) =
                fderiv ℝ χ (v x) (WithLp.toLp 2 (fun i => (hv i).weakGrad x j)) := by
  obtain ⟨v, hv, hvc, hvw, hvK, hgrad, _⟩ :=
    exists_continuous_weak_representative_of_disk_energy_minimizing_sequence
      g hΦ hU hr hΦU hleft u hu hmin hs w hw hrep hL2 hae hweak
  refine ⟨v, hv, hvc, hvw, hvK, hgrad, ?_, ?_⟩
  · intro φ hφ hφB
    have h := integral_pullback_metric_energy_variation_eq_zero_of_disk_energy_minimizing_sequence
      g hΦ hU hr hΦU hleft u hu hmin hs w hw hrep hL2 hae hweak hφ hφB
    have heq (x : V) (j : Fin 2) : DeGiorgi.weakGradientColumn hv x j =
        DeGiorgi.weakGradientColumn hw x j := by
      unfold DeGiorgi.weakGradientColumn
      simp_rw [hgrad]
    rw [← h]
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [hvw] with x hx
    simp only [hx, heq]
  · intro x₀ hx₀
    exact exists_weak_chart_coordinates_of_continuousOn Metric.isOpen_ball hvc hv hU hr
      (fun x hx => hΦU (hvK hx)) hx₀

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_continuous_weak_euler_lagrange_representative_of_disk_energy_minimizing_sequence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_continuous_weak_euler_lagrange_representative_of_disk_energy_minimizing_sequence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_continuous_weak_euler_lagrange_representative_of_disk_energy_minimizing_sequence ``Submission.DifferentialGeometry.Geometry.exists_continuous_weak_euler_lagrange_representative_of_disk_energy_minimizing_sequence

end DifferentialGeometry.Geometry

end
