import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.LocalLowerSemicontinuity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

set_option autoImplicit false
noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Filter _root_.Submission.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Metric
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_centered_chart_cutoffs_of_continuous_ae_limit
    {m : ℕ} (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (L : E ≃L[ℝ] EuclideanSpace ℝ (Fin m))
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E M ∞)
    (hsource : (0 : E) ∈ Φ.source)
    (u : ℕ → C(closedDisk, M)) (V : ℂ → M) {A : ℝ}
    (hLip : ∀ n, ∃ C : ℝ≥0, ∀ z w,
      riemannianEDistOf g (u n z) (u n w) ≤ (C : ℝ≥0∞) * _root_.EDist.edist z w)
    (hae : ∀ᵐ z ∂volume.restrict (_root_.Metric.ball (0 : ℂ) 1),
      _root_.Filter.Tendsto (fun n => diskExtension (u n) z) _root_.Filter.atTop (𝓝 (V z)))
    (henergy : ∀ n, (∫ z in _root_.Metric.closedBall (0 : ℂ) 1,
      diskMapEnergyDensity g (diskExtension (u n)) z) ≤ A)
    (hV : ContinuousOn V (_root_.Metric.ball (0 : ℂ) 1))
    (b : EuclideanSpace ℝ (Fin 2)) (hb : ‖b‖ < 1)
    (hcenter : Φ 0 = V (Complex.orthonormalBasisOneI.repr.symm b)) :
    let e := Complex.orthonormalBasisOneI.repr.symm
    ∃ χ ρ : SmoothBumpFunction 𝓘(ℝ, E) (V (e b)),
      tsupport (χ : M → ℝ) ⊆ Φ.target ∧
      tsupport (ρ : M → ℝ) ⊆ interior {p | χ p = 1} ∩ Φ.target ∧
      ∃ (_ : ∀ i : Fin m, DeGiorgi.MemW1pWitness 2
          (fun x => L (χ (V (e x)) • Φ.symm (V (e x))) i) (_root_.Metric.ball 0 1)),
        ∃ a R : ℝ, 0 < a ∧ 0 < R ∧ ‖b‖ + R < 1 ∧
          _root_.Set.MapsTo L.symm (_root_.Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) a) Φ.source ∧
          _root_.Set.MapsTo (fun x => V (e x)) (_root_.Metric.closedBall b R) {p | ρ p = 1} ∧
          MapsTo (fun x => L (Φ.symm (V (e x)))) (_root_.Metric.closedBall b R) (_root_.Metric.ball 0 a) := by
  classical
  let e := Complex.orthonormalBasisOneI.repr.symm
  have htarget : V (e b) ∈ Φ.target := hcenter ▸ Φ.toOpenPartialHomeomorph.map_source hsource
  obtain ⟨χ, _, hχ⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, E)) (V (e b))).mem_iff.mp
      (Φ.open_target.mem_nhds htarget)
  have hρnb : interior {p : M | χ p = 1} ∩ Φ.target ∈ 𝓝 (V (e b)) :=
    _root_.Filter.inter_mem (isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr χ.eventuallyEq_one))
      (Φ.open_target.mem_nhds htarget)
  obtain ⟨ρ, _, hρ⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, E)) (V (e b))).mem_iff.mp hρnb
  obtain ⟨hw, _⟩ := exists_weighted_chart_energy_le_liminf_of_cutoffs
    g L Φ χ ρ χ.contMDiff χ.hasCompactSupport hχ ρ.contMDiff ρ.hasCompactSupport
    (fun _ => ρ.nonneg) hρ u V hLip hae henergy
  have hLn : L.symm ⁻¹' Φ.source ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin m)) := by
    apply L.symm.continuous.continuousAt.preimage_mem_nhds
    simpa only [map_zero] using Φ.open_source.mem_nhds hsource
  obtain ⟨a, ha, haS⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hLn
  have hVc : ContinuousAt (fun x => V (e x)) b :=
    (hV.continuousAt (isOpen_ball.mem_nhds (by
      simpa only [mem_ball_zero_iff, e.norm_map] using hb))).comp e.continuous.continuousAt
  have hΦ : ContinuousAt (fun p : M => Φ.symm p) (V (e b)) :=
    Φ.contMDiffOn_invFun.continuousOn.continuousAt (Φ.open_target.mem_nhds htarget)
  have hΦV : ContinuousAt (fun x : EuclideanSpace ℝ (Fin 2) => Φ.symm (V (e x))) b :=
    hΦ.comp (f := fun x : EuclideanSpace ℝ (Fin 2) => V (e x)) hVc
  have hcoord : ContinuousAt (fun x => L (Φ.symm (V (e x)))) b :=
    L.continuous.continuousAt.comp hΦV
  have hzero : L (Φ.symm (V (e b))) = 0 := by
    have hi : Φ.symm (Φ 0) = 0 := Φ.toOpenPartialHomeomorph.left_inv hsource
    rw [← hcenter, hi, map_zero]
  have hnear : {x | ρ (V (e x)) = 1 ∧ L (Φ.symm (V (e x))) ∈ _root_.Metric.ball 0 a} ∈ 𝓝 b :=
    (hVc.eventually ρ.eventuallyEq_one).and
      (hcoord.preimage_mem_nhds (by rw [hzero]; exact _root_.Metric.ball_mem_nhds _ ha))
  obtain ⟨R₀, hR₀, hnearR⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hnear
  let R := _root_.Min.min R₀ ((1 - ‖b‖) / 2)
  refine ⟨χ, ρ, hχ, hρ, hw, a, R, ha, lt_min hR₀ (by linarith), ?_, haS, ?_, ?_⟩
  · have h := min_le_right R₀ ((1 - ‖b‖) / 2)
    dsimp only [R]
    linarith
  · intro x hx
    exact (hnearR (_root_.Metric.closedBall_subset_closedBall (min_le_left _ _) hx)).1
  · intro x hx
    exact (hnearR (_root_.Metric.closedBall_subset_closedBall (min_le_left _ _) hx)).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_centered_chart_cutoffs_of_continuous_ae_limit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_centered_chart_cutoffs_of_continuous_ae_limit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_centered_chart_cutoffs_of_continuous_ae_limit ``Submission.DifferentialGeometry.Geometry.exists_centered_chart_cutoffs_of_continuous_ae_limit

end DifferentialGeometry.Geometry

end

end
