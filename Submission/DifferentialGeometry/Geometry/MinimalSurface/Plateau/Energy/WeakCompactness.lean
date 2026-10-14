import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.Rellich.Lipschitz
import Submission.DifferentialGeometry.Analysis.Integration.Measure.EmbeddedLimit
import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.Composition
import Submission.DifferentialGeometry.Analysis.Integration.Integral.IsometricDerivative
import Submission.DifferentialGeometry.Geometry.Metric.NeighborhoodRetraction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.NNReal _root_.ENNReal _root_.Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]

theorem exists_embedded_disk_weak_memW1p_subseq
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (u : ℕ → C(closedDisk, M))
    (hLip : ∀ n, ∃ K : ℝ≥0, ∀ x y,
      riemannianEDistOf g (u n x) (u n y) ≤ (K : ℝ≥0∞) * _root_.EDist.edist x y)
    {B : ℝ} (henergy : ∀ n,
      (∫ z in Metric.closedBall (0 : ℂ) 1,
        diskMapEnergyDensity g (diskExtension (u n)) z) ≤ B) :
    ∃ (m : ℕ) (Φ : M → EuclideanSpace ℝ (Fin m)),
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ Φ ∧
      _root_.Topology.IsClosedEmbedding Φ ∧
      (∀ p, Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) Φ p)) ∧
      ∃ (hs : ∀ n i, DeGiorgi.MemW1pWitness 2
          (fun x => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)) i)
          (Metric.ball 0 1))
        (φ : ℕ → ℕ) (v : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m))
        (hv : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => v x i) (Metric.ball 0 1))
        (w : EuclideanSpace ℝ (Fin 2) → M),
        StrictMono φ ∧
        (∀ n i x j, (hs n i).weakGrad x j =
          fderiv ℝ (fun y => Φ (diskExtension (u n)
            (Complex.orthonormalBasisOneI.repr.symm y)) i) x (EuclideanSpace.single j 1)) ∧
        _root_.MeasureTheory.MemLp v 2 (volume.restrict (Metric.ball 0 1)) ∧
        _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x =>
          Φ (diskExtension (u (φ n)) (Complex.orthonormalBasisOneI.repr.symm x)) - v x)
          2 (volume.restrict (Metric.ball 0 1))) _root_.Filter.atTop (𝓝 0) ∧
        (∀ᵐ x ∂volume.restrict (Metric.ball 0 1),
          _root_.Filter.Tendsto (fun n => Φ (diskExtension (u (φ n))
            (Complex.orthonormalBasisOneI.repr.symm x))) _root_.Filter.atTop (𝓝 (v x))) ∧
        (∀ᵐ x ∂volume.restrict (Metric.ball 0 1), v x ∈ _root_.Set.range Φ) ∧
        @AEMeasurable (EuclideanSpace ℝ (Fin 2)) M (borel M) _ w
          (volume.restrict (Metric.ball 0 1)) ∧
        ((fun x => Φ (w x)) =ᵐ[volume.restrict (Metric.ball 0 1)] v) ∧
        (∀ᵐ x ∂volume.restrict (Metric.ball 0 1),
          _root_.Filter.Tendsto (fun n => diskExtension (u (φ n))
            (Complex.orthonormalBasisOneI.repr.symm x)) _root_.Filter.atTop (𝓝 (w x))) ∧
        ∀ i (z : _root_.MeasureTheory.Lp (EuclideanSpace ℝ (Fin 2)) 2 (volume.restrict (Metric.ball 0 1))),
          _root_.Filter.Tendsto (fun n => _root_.Inner.inner ℝ (DeGiorgi.gradLpOfWitness (hs (φ n) i)) z) _root_.Filter.atTop
            (𝓝 (_root_.Inner.inner ℝ (DeGiorgi.gradLpOfWitness (hv i)) z)) := by
  obtain ⟨m, Φ, hΦ, hΦemb, hΦimm⟩ := exists_compact_smooth_embedding (E := E) (M := M)
  refine ⟨m, Φ, hΦ, hΦemb, hΦimm, ?_⟩
  choose K hK using hLip
  obtain ⟨C, _, hC⟩ := exists_integral_norm_fderiv_comp_diskExtension_sq_le g
    (hΦ.of_le (by simp))
  let e := Complex.orthonormalBasisOneI.repr.symm
  let f (n : ℕ) : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m) :=
    (Φ ∘ diskExtension (u n)) ∘ e
  obtain ⟨D, hD⟩ := (isCompact_range hΦ.continuous).isBounded.exists_norm_le
  have hfun (n : ℕ) (x : EuclideanSpace ℝ (Fin 2)) : ‖f n x‖ ≤ D :=
    hD _ (_root_.Set.mem_range_self (diskExtension (u n) (e x)))
  have hf (n : ℕ) : LipschitzWith (C * K n) (f n) := by
    simpa only [mul_one] using ((hC (u n) (K n) (hK n)).1.comp e.isometry.lipschitz)
  have hfi (n : ℕ) : _root_.MeasureTheory.IntegrableOn (fun x => ‖fderiv ℝ (f n) x‖ ^ 2)
      (Metric.closedBall 0 1) := by
    apply (_root_.MeasureTheory.integrableOn_const (C := ((C * K n : ℝ≥0) : ℝ) ^ 2)
      (_root_.ProperSpace.isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1).measure_ne_top).mono'
      ((measurable_fderiv ℝ (f n)).norm.pow_const 2).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
        (norm_fderiv_le_of_lipschitz ℝ (hf n))
  have hbound (n : ℕ) : (∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1,
        ‖fderiv ℝ (f n) x‖ ^ 2) ≤ 4 * (C : ℝ) ^ 2 * B := by
    apply (_root_.MeasureTheory.setIntegral_mono_set (hfi n) (Filter.Eventually.of_forall fun _ => sq_nonneg _)
      (Filter.Eventually.of_forall fun x hx => Metric.ball_subset_closedBall hx)).trans
    rw [show f n = (Φ ∘ diskExtension (u n)) ∘ e by rfl,
      e.integral_norm_fderiv_sq_comp_closedBall]
    exact ((hC (u n) (K n) (hK n)).2.2).trans
      (mul_le_mul_of_nonneg_left (henergy n) (by positivity))
  obtain ⟨hs, φ, v, hv, hφ, hrep, hvm, hL2, hae, hvS, hweak⟩ :=
    Analysis.Sobolev.exists_weak_memW1p_subseq_of_lipschitz_of_energy_bound
      f (fun n => C * K n) hf (fun n => Filter.Eventually.of_forall (hfun n))
      hbound hΦemb.isClosed_range (fun n => Filter.Eventually.of_forall fun x =>
        _root_.Set.mem_range_self (diskExtension (u n) (e x)))
  let : Nonempty M := ⟨u 0 (diskRetraction 0)⟩
  let : MeasurableSpace M := borel M
  let : BorelSpace M := ⟨rfl⟩
  obtain ⟨w, hwm, hw, hwlim⟩ :=
    MeasureTheory.exists_aemeasurable_tendsto_ae_of_closed_embedding_ae_limit Φ hΦemb
      (fun n x => diskExtension (u (φ n)) (e x)) hvm.aestronglyMeasurable.aemeasurable hvS hae
  exact ⟨hs, φ, v, hv, w, hφ, hrep, hvm, hL2, hae, hvS, hwm, hw, hwlim, hweak⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_embedded_disk_weak_memW1p_subseq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_embedded_disk_weak_memW1p_subseq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_embedded_disk_weak_memW1p_subseq ``Submission.DifferentialGeometry.Geometry.exists_embedded_disk_weak_memW1p_subseq

end DifferentialGeometry.Geometry
