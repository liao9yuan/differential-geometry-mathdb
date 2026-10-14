import Submission.DifferentialGeometry.Geometry.Metric.Completeness.ConnectedComponent
import Submission.DifferentialGeometry.Geometry.Comparison.HopfRinow.Component
import Submission.DifferentialGeometry.Topology.LoopSpace.ManifoldComponent
import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.DistanceMoments
import Submission.DifferentialGeometry.Analysis.Sobolev.MetricTarget.Compactness
import Mathlib.Topology.MetricSpace.ProperSpace

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Metric
open _root_.Submission.DifferentialGeometry.Topology
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
  (exists_aemeasurable_ae_tendsto_subseq_complex_of_dist_energy_bounded)
open scoped _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal _root_.NNReal _root_.Topology

namespace DifferentialGeometry.Geometry

private theorem integral_openDisk_eq_closedDisk (F : ℂ → ℝ) :
    (∫ z in _root_.Metric.ball (0 : ℂ) 1, F z) = ∫ z in _root_.Metric.closedBall (0 : ℂ) 1, F z := by
  have hrestrict : (volume.restrict (_root_.Metric.closedBall (0 : ℂ) 1)).restrict (_root_.Metric.ball 0 1) =
      volume.restrict (_root_.Metric.closedBall (0 : ℂ) 1) :=
    Measure.restrict_eq_self_of_ae_mem ae_disk_interior
  rw [Measure.restrict_restrict measurableSet_ball,
    inter_eq_left.mpr _root_.Metric.ball_subset_closedBall] at hrestrict
  rw [hrestrict]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.integral_openDisk_eq_closedDisk
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.integral_openDisk_eq_closedDisk target :: scope.openDecls } }

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_aemeasurable_ae_tendsto_subseq_of_disk_energy_bounded
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (hg : RiemannianMetricComplete g)
    (γ : freeLoop M) (u : ℕ → C(closedDisk, M)) {A : ℝ}
    (hLip : ∀ n, ∃ L : ℝ≥0, ∀ z w,
      riemannianEDistOf g (u n z) (u n w) ≤ (L : ℝ≥0∞) * _root_.EDist.edist z w)
    (htrace : ∀ n, ∃ σ : C(loopCircle, loopCircle), diskTrace (u n) = γ.comp σ)
    (henergy : ∀ n, (∫ z in _root_.Metric.closedBall (0 : ℂ) 1,
      diskMapEnergyDensity g (diskExtension (u n)) z) ≤ A) :
    let : MeasurableSpace M := borel M
    ∃ (φ : ℕ → ℕ) (v : ℂ → M), StrictMono φ ∧
      AEMeasurable v (volume.restrict (_root_.Metric.ball (0 : ℂ) 1)) ∧
      ∀ᵐ z ∂volume.restrict (_root_.Metric.ball (0 : ℂ) 1),
        Tendsto (fun n => diskExtension (u (φ n)) z) _root_.Filter.atTop (𝓝 (v z)) := by
  classical
  let : MeasurableSpace M := borel M
  let : BorelSpace M := ⟨rfl⟩
  let C := connectedComponentOpen (I := 𝓘(ℝ, E)) (γ 0)
  let gC : SmoothRiemannianMetric 𝓘(ℝ, E) C := g.restrictOpen C
  let p₀ : C := connectedComponentPoint (I := 𝓘(ℝ, E)) (γ 0)
  let : ConnectedSpace C := connectedComponentOpen_connectedSpace (I := 𝓘(ℝ, E)) (γ 0)
  let : SigmaCompactSpace C := sigmaCompactSpace_connectedComponent_of_riemannianMetric g (γ 0)
  let : IsManifold 𝓘(ℝ, E) 1 C :=
    IsManifold.of_le (I := 𝓘(ℝ, E)) (M := C) (n := ∞) (by decide)
  let : _root_.Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, E) : C → Type _) :=
    ⟨gC.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : C → Type _) :=
    ⟨gC.inner, gC.contMDiff.continuous, fun _ _ _ => rfl⟩
  let eC : EMetricSpace C := EMetricSpace.ofRiemannianMetric 𝓘(ℝ, E) C
  let : EMetricSpace C := eC
  let mC : MetricSpace C := EMetricSpace.toMetricSpace
    (fun x y : C => DifferentialGeometry.Analysis.edist_ne_top_of_preconnected x y)
  let : MetricSpace C := mC
  let : UniformSpace C := mC.toUniformSpace
  have hedist (x y : C) : _root_.EDist.edist x y = riemannianEDistOf g (x : M) (y : M) :=
    Metric.edistOf_restrictOpen_connCompOpen g (γ 0) x y
  have hdist (x y : C) : _root_.Dist.dist x y = (riemannianEDistOf g (x : M) (y : M)).toReal := by
    rw [dist_edist, hedist]
  let : ProperSpace C := by
    apply ProperSpace.of_isCompact_closedBall_of_le (α := C) 0
    intro q r hr
    have heq : _root_.Metric.closedBall q r = {x : C |
        riemannianEDistOf g (q : M) (x : M) ≤ ENNReal.ofReal r} := by
      ext x
      change _root_.Dist.dist x q ≤ r ↔ _
      rw [hdist, riemannianEDistOf_comm g (x : M) (q : M)]
      exact (ENNReal.le_ofReal_iff_toReal_le
        (by rw [← hedist]; exact edist_ne_top _ _) hr).symm
    rw [heq]
    exact hg.isCompact_intrinsicClosedBall_connectedComponent g (γ 0) q r
  obtain ⟨a, ha⟩ := TopologicalSpace.exists_dense_seq C
  have ht := htrace
  choose σ hσ using ht
  let uC : ℕ → C(closedDisk, C) := fun n => diskInLoopComponent γ (σ n) (u n) (hσ n)
  let U : ℕ → ℂ → C := fun n => diskExtension (uC n)
  have hU (n : ℕ) (z : ℂ) : (U n z : M) = diskExtension (u n) z := rfl
  have hprobe (n i : ℕ) : (fun z => _root_.Dist.dist (U n z) (a i)) =
      (fun z => (riemannianEDistOf g (diskExtension (u n) z) (a i : M)).toReal) := by
    funext z
    rw [hdist, hU]
  have hanchor (i : ℕ) : riemannianEDistOf g (γ 0) (a i : M) ≠ ⊤ := by
    change riemannianEDistOf g (p₀ : M) (a i : M) ≠ ⊤
    rw [← hedist]
    exact edist_ne_top _ _
  have hfinite (n i : ℕ) : ∃ z : closedDisk, riemannianEDistOf g (u n z) (a i : M) ≠ ⊤ := by
    refine ⟨diskBoundary 0, ?_⟩
    change riemannianEDistOf g (uC n (diskBoundary 0) : M) (a i : M) ≠ ⊤
    rw [← hedist]
    exact edist_ne_top _ _
  have hULip : ∀ n i, ∃ L : ℝ≥0, LipschitzWith L (fun z => _root_.Dist.dist (U n z) (a i)) := by
    intro n i
    obtain ⟨L, hL⟩ := hLip n
    refine ⟨L, ?_⟩
    rw [hprobe]
    exact lipschitzWith_disk_distance g (u n) (a i : M) hL (hfinite n i)
  have hmoment : ∀ i, ∃ B : ℝ, 0 ≤ B ∧ ∀ n,
      (∫ z in _root_.Metric.closedBall (0 : ℂ) 1,
        (riemannianEDistOf g (diskExtension (u n) z) (a i : M)).toReal ^ 2) ≤ B :=
    fun i => exists_uniform_disk_distance_moment_bound_at_point g γ u (a i : M)
      (hanchor i) hLip htrace henergy
  choose B hBnonneg hB using hmoment
  have hA : ∀ n i, (∫ z in _root_.Metric.ball (0 : ℂ) 1, _root_.Dist.dist (U n z) (a i) ^ 2) ≤ B i := by
    intro n i
    have heq : (fun z => _root_.Dist.dist (U n z) (a i) ^ 2) =
        (fun z => (riemannianEDistOf g (diskExtension (u n) z) (a i : M)).toReal ^ 2) :=
      funext fun z => congrArg (fun t : ℝ => t ^ 2) (congrFun (hprobe n i) z)
    rw [heq]
    rw [integral_openDisk_eq_closedDisk]
    exact hB i n
  have hD : ∀ n i, (∫ z in _root_.Metric.ball (0 : ℂ) 1,
      ‖fderiv ℝ (fun w => _root_.Dist.dist (U n w) (a i)) z‖ ^ 2) ≤ 2 * A := by
    intro n i
    obtain ⟨L, hL⟩ := hLip n
    rw [hprobe, integral_openDisk_eq_closedDisk]
    exact (integral_norm_fderiv_disk_distance_sq_le g (u n) (a i : M)
      hL (hfinite n i)).trans (mul_le_mul_of_nonneg_left (henergy n) (by norm_num))
  obtain ⟨φ, v, hφ, hvm, hv⟩ :=
    exists_aemeasurable_ae_tendsto_subseq_complex_of_dist_energy_bounded
      ha U hULip hA hD
  refine ⟨φ, fun z => (v z : M), hφ, ?_, ?_⟩
  · exact measurable_subtype_coe.comp_aemeasurable hvm
  · filter_upwards [hv] with z hz
    exact (continuous_subtype_val.tendsto (v z)).comp hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_aemeasurable_ae_tendsto_subseq_of_disk_energy_bounded then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_aemeasurable_ae_tendsto_subseq_of_disk_energy_bounded"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_aemeasurable_ae_tendsto_subseq_of_disk_energy_bounded ``Submission.DifferentialGeometry.Geometry.exists_aemeasurable_ae_tendsto_subseq_of_disk_energy_bounded

end DifferentialGeometry.Geometry

end

end
