import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.InteriorEnergy
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.Campanato
import Submission.DifferentialGeometry.Analysis.Integration.Measure.ContinuousRepresentative
import Submission.DifferentialGeometry.Topology.MetricSpace.HolderContinuity
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.WitnessCongruence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Filter _root_.Submission.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Topology
open _root_.Submission.DifferentialGeometry.Analysis
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.NNReal _root_.ENNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M]

local notation "V" => EuclideanSpace ℝ (Fin 2)
local notation "F" => EuclideanSpace ℝ ι

theorem exists_local_holder_representative_of_disk_energy_minimizing_sequence
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
    : ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧ ∀ x₀ : V, ‖x₀‖ < 1 →
      ∃ (a C : ℝ) (v : V → F), 0 < a ∧ 0 ≤ C ∧
        Metric.ball x₀ a ⊆ Metric.ball (0 : V) 1 ∧
        (v =ᵐ[volume.restrict (Metric.ball x₀ a)] w) ∧
        ∀ x ∈ Metric.ball x₀ (a / 2), ∀ y ∈ Metric.ball x₀ (a / 2),
          ‖v x - v y‖ ≤ C * ‖x - y‖ ^ α := by
  obtain ⟨α, hα, hα1, hpower⟩ :=
    exists_weak_gradient_power_bound_on_interior_balls_of_minimizing_sequence
      g hΦ hU hr hΦU hleft u hu hmin hs w hw hrep hL2 hae hweak
  refine ⟨α, hα, hα1, ?_⟩
  intro x₀ hx₀
  let t := (‖x₀‖ + 1) / 2
  have ht : 0 < t := by dsimp only [t]; linarith [norm_nonneg x₀]
  have ht1 : t < 1 := by dsimp only [t]; linarith
  have hx₀t : ‖x₀‖ < t := by dsimp only [t]; linarith
  obtain ⟨δ, K, hδ, _, hK, hgrad⟩ := hpower t ht ht1
  let a := _root_.Min.min δ ((t - ‖x₀‖) / 2)
  have ha : 0 < a := lt_min hδ (by linarith)
  have haδ : a ≤ δ := min_le_left _ _
  have hxa : ‖x₀‖ + a < t := by
    have hm := min_le_right δ ((t - ‖x₀‖) / 2)
    dsimp only [a]
    linarith
  have hball : Metric.ball x₀ a ⊆ Metric.ball (0 : V) 1 := by
    intro x hx
    rw [Metric.mem_ball, dist_zero_right]
    have hx' : ‖x - x₀‖ < a := by simpa only [Metric.mem_ball, dist_eq_norm] using hx
    have hn : ‖x‖ ≤ ‖x - x₀‖ + ‖x₀‖ := by
      simpa only [sub_add_cancel] using norm_add_le (x - x₀) x₀
    linarith
  have hcamp (i : ι) : ∃ C : ℝ, DeGiorgi.HasCampanatoBound (fun x => w x i) x₀ a α C := by
    have henergy (b : DeGiorgi.CampanatoBall x₀ a) :
        (∫ x in Metric.ball b.center b.radius, ‖(hw i).weakGrad x‖ ^ 2) ≤
          K * b.radius ^ (2 * α) := by
      have hb : b.center ∈ Metric.ball x₀ a :=
        b.subset_ball (Metric.mem_ball_self b.radius_pos)
      have hb' : ‖b.center - x₀‖ < a := by
        simpa only [Metric.mem_ball, dist_eq_norm] using hb
      have hn : ‖b.center‖ ≤ ‖b.center - x₀‖ + ‖x₀‖ := by
        simpa only [sub_add_cancel] using norm_add_le (b.center - x₀) x₀
      exact hgrad b.center (by linarith) b.radius b.radius_pos (b.radius_le.trans haδ) i
    obtain ⟨C, _, hC⟩ :=
      exists_campanato_bound_of_weak_gradient_energy
        (hw i) hball hK henergy
    exact ⟨C, hC⟩
  obtain ⟨v, C, hC, hv, hholder⟩ :=
    exists_holder_representative_of_component_campanato_bounds
      ha hα hα1 hcamp
  exact ⟨a, C, v, ha, hC, hball, hv, hholder⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_local_holder_representative_of_disk_energy_minimizing_sequence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_local_holder_representative_of_disk_energy_minimizing_sequence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_local_holder_representative_of_disk_energy_minimizing_sequence ``Submission.DifferentialGeometry.Geometry.exists_local_holder_representative_of_disk_energy_minimizing_sequence

end DifferentialGeometry.Geometry

end

noncomputable section
open _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Filter _root_.Submission.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Topology
open _root_.Submission.DifferentialGeometry.Analysis
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.NNReal _root_.ENNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M]

local notation "V" => EuclideanSpace ℝ (Fin 2)
local notation "F" => EuclideanSpace ℝ ι

theorem exists_continuous_weak_representative_of_disk_energy_minimizing_sequence
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
      ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧ ∀ x₀ : V, ‖x₀‖ < 1 →
        ∃ a C : ℝ, 0 < a ∧ 0 ≤ C ∧ Metric.ball x₀ a ⊆ Metric.ball (0 : V) 1 ∧
          ∀ x ∈ Metric.ball x₀ a, ∀ y ∈ Metric.ball x₀ a,
            ‖v x - v y‖ ≤ C * ‖x - y‖ ^ α := by
  obtain ⟨α, hα, hα1, hlocal⟩ :=
    exists_local_holder_representative_of_disk_energy_minimizing_sequence
      g hΦ hU hr hΦU hleft u hu hmin hs w hw hrep hL2 hae hweak
  have hloc : ∀ x ∈ Metric.ball (0 : V) 1, ∃ (U : Set V) (f : V → F),
      IsOpen U ∧ x ∈ U ∧ U ⊆ Metric.ball (0 : V) 1 ∧ ContinuousOn f U ∧
        f =ᵐ[volume.restrict U] w := by
    intro x hx
    have hx' : ‖x‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hx
    obtain ⟨a, C, f, ha, hC, hball, hfw, hholder⟩ := hlocal x hx'
    have hhalf : Metric.ball x (a / 2) ⊆ Metric.ball x a :=
      Metric.ball_subset_ball (by linarith)
    exact ⟨Metric.ball x (a / 2), f, Metric.isOpen_ball, Metric.mem_ball_self (by positivity),
      hhalf.trans hball, continuousOn_of_norm_sub_le_rpow hC hα hholder,
      _root_.MeasureTheory.ae_restrict_of_ae_restrict_of_subset hhalf hfw⟩
  obtain ⟨v, hvc, hvw⟩ := exists_continuousOn_ae_eq_of_locally_continuousOn_ae_eq _root_.MeasureTheory.MeasureSpace.volume hloc
  have hK : IsCompact (_root_.Set.range Φ) := isCompact_range hΦ.continuous
  have hwK : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : V) 1), w x ∈ _root_.Set.range Φ :=
    hae.mono fun x hx => hK.isClosed.mem_of_tendsto hx
      (Eventually.of_forall fun n => _root_.Set.mem_range_self _)
  have hvK : _root_.Set.MapsTo v (Metric.ball (0 : V) 1) (_root_.Set.range Φ) := by
    apply MeasureTheory.ContinuousOn.mapsTo_of_ae_mem_closed _root_.MeasureTheory.MeasureSpace.volume Metric.isOpen_ball
      hK.isClosed hvc
    filter_upwards [hvw, hwK] with x hx hKx
    rwa [hx]
  let hv (i : ι) := (hw i).congr
    (hvw.symm.mono fun x hx => congrArg (fun z : F => z i) hx)
  refine ⟨v, hv, hvc, hvw, hvK, fun i => rfl, α, hα, hα1, ?_⟩
  intro x₀ hx₀
  obtain ⟨a, C, f, ha, hC, hball, hfw, hholder⟩ := hlocal x₀ hx₀
  have hhalf : Metric.ball x₀ (a / 2) ⊆ Metric.ball x₀ a :=
    Metric.ball_subset_ball (by linarith)
  have hsub : Metric.ball x₀ (a / 2) ⊆ Metric.ball (0 : V) 1 := hhalf.trans hball
  have hvc' : ContinuousOn v (Metric.ball x₀ (a / 2)) := hvc.mono hsub
  have hfc : ContinuousOn f (Metric.ball x₀ (a / 2)) :=
    continuousOn_of_norm_sub_le_rpow hC hα hholder
  have hvwa : v =ᵐ[volume.restrict (Metric.ball x₀ (a / 2))] w :=
    _root_.MeasureTheory.ae_restrict_of_ae_restrict_of_subset hsub hvw
  have hfwa : f =ᵐ[volume.restrict (Metric.ball x₀ (a / 2))] w :=
    _root_.MeasureTheory.ae_restrict_of_ae_restrict_of_subset hhalf hfw
  have hvf : _root_.Set.EqOn v f (Metric.ball x₀ (a / 2)) :=
    volume.eqOn_open_of_ae_eq (hvwa.trans hfwa.symm) Metric.isOpen_ball hvc' hfc
  refine ⟨a / 2, C, by positivity, hC, hsub, ?_⟩
  intro x hx y hy
  rw [hvf hx, hvf hy]
  exact hholder x hx y hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_continuous_weak_representative_of_disk_energy_minimizing_sequence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_continuous_weak_representative_of_disk_energy_minimizing_sequence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_continuous_weak_representative_of_disk_energy_minimizing_sequence ``Submission.DifferentialGeometry.Geometry.exists_continuous_weak_representative_of_disk_energy_minimizing_sequence

end DifferentialGeometry.Geometry

end
