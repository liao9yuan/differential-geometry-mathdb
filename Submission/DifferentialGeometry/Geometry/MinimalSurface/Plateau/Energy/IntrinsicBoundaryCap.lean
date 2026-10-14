import Submission.DifferentialGeometry.Topology.MetricSpace.BallPasting
import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.MinimizingSequence
import Submission.DifferentialGeometry.Geometry.Metric.CompactSourceDerivative
import Submission.DifferentialGeometry.Geometry.Metric.ConvexSourceLipschitz
import Submission.DifferentialGeometry.Geometry.Metric.Pullback.Coefficients
import Mathlib.Topology.MetricSpace.Thickening
import Submission.DifferentialGeometry.Geometry.Metric.CompactSourceNeighborhood
import Submission.DifferentialGeometry.Geometry.Metric.LoopNeighborhood
import Submission.DifferentialGeometry.Geometry.Metric.CurveEnergy.Lipschitz
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.Replacement.BoundaryCapRange

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section

open _root_.Set _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Metric _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Topology.Manifold _root_.ContDiff _root_.Topology _root_.NNReal _root_.ENNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

omit [FiniteDimensional ℝ E] [T3Space M] in
private theorem disk_energy_density_congr {g : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {f h : ℂ → M} {z : ℂ} (heq : f =ᶠ[𝓝 z] h) :
    diskMapEnergyDensity g f z = diskMapEnergyDensity g h z := by
  unfold diskMapEnergyDensity diskMapPartial
  rw [heq.mfderiv_eq, heq.eq_of_nhds]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.disk_energy_density_congr
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.disk_energy_density_congr target :: scope.openDecls } }

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_disk_cap_replacement_of_eqOn_sphere
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (u : C(closedDisk, M))
    {v : ℂ → M} {K L : ℝ≥0} {c : ℂ} {r : ℝ}
    (hu : ∀ z w : closedDisk,
      riemannianEDistOf g (u z) (u w) ≤ (K : ℝ≥0∞) * _root_.EDist.edist z w)
    (hv : ∀ z ∈ _root_.Metric.closedBall (0 : ℂ) 1 ∩ _root_.Metric.closedBall c r,
      ∀ w ∈ _root_.Metric.closedBall (0 : ℂ) 1 ∩ _root_.Metric.closedBall c r,
      riemannianEDistOf g (v z) (v w) ≤ (L : ℝ≥0∞) * _root_.EDist.edist z w)
    (hseam : _root_.Set.EqOn v (diskExtension u) (_root_.Metric.closedBall (0 : ℂ) 1 ∩ _root_.Metric.sphere c r)) :
    ∃ w : C(closedDisk, M),
      (∀ z z', riemannianEDistOf g (w z) (w z') ≤
        ((L + K : ℝ≥0) : ℝ≥0∞) * _root_.EDist.edist z z') ∧
      (∀ z : closedDisk, _root_.Dist.dist (z : ℂ) c ≤ r → w z = v z) ∧
      (∀ z : closedDisk, r ≤ _root_.Dist.dist (z : ℂ) c → w z = u z) ∧
      _root_.MeasureTheory.IntegrableOn (diskMapEnergyDensity g v) (_root_.Metric.closedBall (0 : ℂ) 1 ∩ _root_.Metric.closedBall c r) ∧
      riemannianDiskEnergy g w = riemannianDiskEnergy g u -
        (∫ z in _root_.Metric.closedBall (0 : ℂ) 1 ∩ _root_.Metric.closedBall c r,
          diskMapEnergyDensity g (diskExtension u) z) +
        ∫ z in _root_.Metric.closedBall (0 : ℂ) 1 ∩ _root_.Metric.closedBall c r, diskMapEnergyDensity g v z := by
  classical
  let : _root_.Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  let D : Set ℂ := _root_.Metric.closedBall 0 1
  let A : Set ℂ := _root_.Metric.closedBall c r
  let U := diskExtension u
  let f : ℂ → M := A.piecewise v U
  have hULip : LipschitzWith K U := diskExtension_riemannian_lipschitz g hu
  have hf : LipschitzOnWith (L + K) f D :=
    Analysis.lipschitzOnWith_piecewise_closedBall_of_eqOn_sphere
      (convex_closedBall (0 : ℂ) 1) hv hULip.lipschitzOnWith hseam
  let w : C(closedDisk, M) := ⟨fun z => f z, hf.continuousOn.domRestrict⟩
  have hwLip (z z' : closedDisk) : riemannianEDistOf g (w z) (w z') ≤
      ((L + K : ℝ≥0) : ℝ≥0∞) * _root_.EDist.edist z z' := hf z.property z'.property
  have hinner (z : closedDisk) (hz : _root_.Dist.dist (z : ℂ) c ≤ r) : w z = v z :=
    _root_.Set.piecewise_eq_of_mem A v U (show (z : ℂ) ∈ A from hz)
  have houter (z : closedDisk) (hz : r ≤ _root_.Dist.dist (z : ℂ) c) : w z = u z := by
    by_cases heq : _root_.Dist.dist (z : ℂ) c = r
    · rw [hinner z heq.le, hseam ⟨z.property, heq⟩]
      exact diskExtension_coe u z
    · change A.piecewise v U z = _
      have hzA : (z : ℂ) ∉ A := not_le.mpr (lt_of_le_of_ne hz (Ne.symm heq))
      rw [_root_.Set.piecewise_eq_of_notMem A v U hzA]
      exact diskExtension_coe u z
  have hext (z : ℂ) (hz : z ∈ _root_.Metric.ball (0 : ℂ) 1) : diskExtension w =ᶠ[𝓝 z] f := by
    filter_upwards [isOpen_ball.mem_nhds hz] with y hy
    exact diskExtension_coe w ⟨y, _root_.Metric.ball_subset_closedBall hy⟩
  have hin (z : ℂ) (hz : z ∈ _root_.Metric.ball c r) : f =ᶠ[𝓝 z] v := by
    filter_upwards [isOpen_ball.mem_nhds hz] with y hy
    exact _root_.Set.piecewise_eq_of_mem _ _ _ (_root_.Metric.ball_subset_closedBall hy)
  have hout (z : ℂ) (hz : z ∉ A) : f =ᶠ[𝓝 z] U := by
    filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds hz] with y hy
    exact _root_.Set.piecewise_eq_of_notMem _ _ _ hy
  have hWI := integrable_diskMapEnergyDensity g hwLip
  have hUI := integrable_diskMapEnergyDensity g hu
  have hinside : diskMapEnergyDensity g (diskExtension w) =ᵐ[volume.restrict (D ∩ A)]
      diskMapEnergyDensity g v := by
    have hD : ∀ᵐ z ∂volume.restrict (D ∩ A), z ∈ _root_.Metric.ball (0 : ℂ) 1 :=
      _root_.MeasureTheory.ae_restrict_of_ae_restrict_of_subset _root_.Set.inter_subset_left ae_disk_interior
    have hA : ∀ᵐ z ∂volume.restrict (D ∩ A), z ∈ _root_.Metric.ball c r :=
      _root_.MeasureTheory.ae_restrict_of_ae_restrict_of_subset _root_.Set.inter_subset_right
      (ae_mem_ball_of_measure_sphere_eq_zero (Measure.addHaar_sphere _root_.MeasureTheory.MeasureSpace.volume c r))
    filter_upwards [hD, hA] with z hzD hzA
    exact disk_energy_density_congr ((hext z hzD).trans (hin z hzA))
  have houtside : diskMapEnergyDensity g (diskExtension w) =ᵐ[volume.restrict (D \ A)]
      diskMapEnergyDensity g U := by
    have hD : ∀ᵐ z ∂volume.restrict (D \ A), z ∈ _root_.Metric.ball (0 : ℂ) 1 :=
      _root_.MeasureTheory.ae_restrict_of_ae_restrict_of_subset _root_.Set.sdiff_subset ae_disk_interior
    filter_upwards [hD, _root_.MeasureTheory.ae_restrict_mem (measurableSet_closedBall.diff measurableSet_closedBall)]
      with z hzD hz
    exact disk_energy_density_congr ((hext z hzD).trans (hout z hz.2))
  have hVint : _root_.MeasureTheory.IntegrableOn (diskMapEnergyDensity g v) (D ∩ A) :=
    (hWI.mono_set _root_.Set.inter_subset_left).congr hinside
  refine ⟨w, hwLip, hinner, houter, hVint, ?_⟩
  have hwdecomp := _root_.MeasureTheory.integral_inter_add_sdiff (t := A) measurableSet_closedBall hWI
  have hudecomp := _root_.MeasureTheory.integral_inter_add_sdiff (t := A) measurableSet_closedBall hUI
  have hieq := _root_.MeasureTheory.integral_congr_ae hinside
  have hoeq := _root_.MeasureTheory.integral_congr_ae houtside
  change (∫ z in D ∩ A, diskMapEnergyDensity g (diskExtension w) z) +
    (∫ z in D \ A, diskMapEnergyDensity g (diskExtension w) z) =
      riemannianDiskEnergy g w at hwdecomp
  change (∫ z in D ∩ A, diskMapEnergyDensity g U z) +
    (∫ z in D \ A, diskMapEnergyDensity g U z) = riemannianDiskEnergy g u at hudecomp
  rw [hieq, hoeq] at hwdecomp
  change riemannianDiskEnergy g w = riemannianDiskEnergy g u -
    (∫ z in D ∩ A, diskMapEnergyDensity g U z) + ∫ z in D ∩ A, diskMapEnergyDensity g v z
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_disk_cap_replacement_of_eqOn_sphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_disk_cap_replacement_of_eqOn_sphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_disk_cap_replacement_of_eqOn_sphere ``Submission.DifferentialGeometry.Geometry.exists_disk_cap_replacement_of_eqOn_sphere

theorem disk_cap_energy_le_add_minimizing_defect
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (u : C(closedDisk, M))
    {v : ℂ → M} {K L : ℝ≥0} {c : ℂ} {r : ℝ}
    (hu : ∀ z w : closedDisk,
      riemannianEDistOf g (u z) (u w) ≤ (K : ℝ≥0∞) * _root_.EDist.edist z w)
    (hv : ∀ z ∈ _root_.Metric.closedBall (0 : ℂ) 1 ∩ _root_.Metric.closedBall c r,
      ∀ w ∈ _root_.Metric.closedBall (0 : ℂ) 1 ∩ _root_.Metric.closedBall c r,
      riemannianEDistOf g (v z) (v w) ≤ (L : ℝ≥0∞) * _root_.EDist.edist z w)
    (hseam : _root_.Set.EqOn v (diskExtension u) (_root_.Metric.closedBall (0 : ℂ) 1 ∩ _root_.Metric.sphere c r))
    {γ : freeLoop M} {τ : C(loopCircle, loopCircle)} (hτ : IsWeaklyMonotoneOnce τ)
    (htraceIn : ∀ θ, _root_.Dist.dist (diskBoundary θ : ℂ) c ≤ r → v (diskBoundary θ) = γ (τ θ))
    (htraceOut : ∀ θ, r ≤ _root_.Dist.dist (diskBoundary θ : ℂ) c → u (diskBoundary θ) = γ (τ θ)) :
    (∫ z in _root_.Metric.closedBall (0 : ℂ) 1 ∩ _root_.Metric.closedBall c r,
      diskMapEnergyDensity g (diskExtension u) z) ≤
      (∫ z in _root_.Metric.closedBall (0 : ℂ) 1 ∩ _root_.Metric.closedBall c r, diskMapEnergyDensity g v z) +
        (riemannianDiskEnergy g u -
          _root_.InfSet.sInf ((fun q : C(closedDisk, M) => riemannianDiskEnergy g q) ''
            weaklyMonotoneDiskCompetitors g γ)) := by
  obtain ⟨w, hwLip, hwin, hwout, _, henergy⟩ :=
    exists_disk_cap_replacement_of_eqOn_sphere g u hu hv hseam
  have hwtrace : diskTrace w = γ.comp τ := by
    ext θ
    change w (diskBoundary θ) = γ (τ θ)
    by_cases hθ : _root_.Dist.dist (diskBoundary θ : ℂ) c ≤ r
    · rw [hwin (diskBoundary θ) hθ]
      exact htraceIn θ hθ
    · rw [hwout (diskBoundary θ) (not_le.mp hθ).le]
      exact htraceOut θ (not_le.mp hθ).le
  have hw : w ∈ weaklyMonotoneDiskCompetitors g γ :=
    ⟨⟨τ, hτ, hwtrace⟩, L + K, hwLip⟩
  have hbound : BddBelow ((fun q : C(closedDisk, M) => riemannianDiskEnergy g q) ''
      weaklyMonotoneDiskCompetitors g γ) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨q, _, rfl⟩
    exact riemannianDiskEnergy_nonneg g q
  have hinf := csInf_le hbound (_root_.Set.mem_image_of_mem
    (fun q : C(closedDisk, M) => riemannianDiskEnergy g q) hw)
  rw [henergy] at hinf
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.disk_cap_energy_le_add_minimizing_defect then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.disk_cap_energy_le_add_minimizing_defect"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.disk_cap_energy_le_add_minimizing_defect ``Submission.DifferentialGeometry.Geometry.disk_cap_energy_le_add_minimizing_defect

end DifferentialGeometry.Geometry

end

end

section

noncomputable section

open _root_.Set _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Metric _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Topology _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Topology.Manifold _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Geometry

variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

variable [FiniteDimensional ℝ E] [T3Space M]

theorem exists_local_reconstructed_disk_cap_energy_bound
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {r : F → M} {U K : Set F}
    (hU : IsOpen U) (hr : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) 1 r U)
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ (η : ℝ) (C : ℝ≥0), 0 < η ∧ ∀ p ∈ K,
      ∀ (u : C(closedDisk, M)) (q : ℂ → F) (L Lq : ℝ≥0) (c : ℂ) (s : ℝ),
      (∀ z w : closedDisk, riemannianEDistOf g (u z) (u w) ≤
        (L : ℝ≥0∞) * _root_.EDist.edist z w) → LipschitzWith Lq q →
      _root_.Set.MapsTo q (_root_.Metric.closedBall (0 : ℂ) 1 ∩ _root_.Metric.closedBall c s) (_root_.Metric.closedBall p η) →
      _root_.Set.EqOn (r ∘ q) (diskExtension u) (_root_.Metric.closedBall (0 : ℂ) 1 ∩ _root_.Metric.sphere c s) →
      ∀ (γ : freeLoop M) (τ : C(loopCircle, loopCircle)), IsWeaklyMonotoneOnce τ →
      (∀ θ, _root_.Dist.dist (diskBoundary θ : ℂ) c ≤ s → r (q (diskBoundary θ)) = γ (τ θ)) →
      (∀ θ, s ≤ _root_.Dist.dist (diskBoundary θ : ℂ) c → u (diskBoundary θ) = γ (τ θ)) →
      (∫ z in _root_.Metric.closedBall (0 : ℂ) 1 ∩ _root_.Metric.closedBall c s,
        diskMapEnergyDensity g (diskExtension u) z) ≤
        (C : ℝ) ^ 2 *
          (∫ z in _root_.Metric.closedBall (0 : ℂ) 1 ∩ _root_.Metric.closedBall c s,
            (‖fderiv ℝ q z 1‖ ^ 2 + ‖fderiv ℝ q z Complex.I‖ ^ 2) / 2) +
          (riemannianDiskEnergy g u -
            _root_.InfSet.sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
              weaklyMonotoneDiskCompetitors g γ)) := by
  let : MeasurableSpace F := borel F
  let : BorelSpace F := ⟨rfl⟩
  obtain ⟨η, C, hη, hlocal⟩ := exists_uniform_local_source_metric_bound_near_compact g hU hr hK hKU
  refine ⟨η, C, hη, ?_⟩
  intro p hp u q L Lq c s hu hq hqrange hseam γ τ hτ htraceIn htraceOut
  obtain ⟨hballU, hrlip, hrbound⟩ := hlocal p hp
  let A : Set ℂ := _root_.Metric.closedBall (0 : ℂ) 1 ∩ _root_.Metric.closedBall c s
  have hv : ∀ z ∈ A, ∀ w ∈ A, riemannianEDistOf g ((r ∘ q) z) ((r ∘ q) w) ≤
      ((C * Lq : ℝ≥0) : ℝ≥0∞) * _root_.EDist.edist z w := by
    intro z hz w hw
    apply (hrlip (q z) (hqrange hz) (q w) (hqrange hw)).trans
    rw [ENNReal.coe_mul, mul_assoc]
    exact mul_le_mul' le_rfl (hq z w)
  obtain ⟨_, _, _, _, hvint, _⟩ := exists_disk_cap_replacement_of_eqOn_sphere g u hu hv hseam
  have hc : (∫ z in A, diskMapEnergyDensity g (diskExtension u) z) ≤
      (∫ z in A, diskMapEnergyDensity g (r ∘ q) z) +
        (riemannianDiskEnergy g u -
          _root_.InfSet.sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
            weaklyMonotoneDiskCompetitors g γ)) :=
    disk_cap_energy_le_add_minimizing_defect g u hu hv hseam hτ htraceIn htraceOut
  have hdirint (v : ℂ) : _root_.MeasureTheory.IntegrableOn (fun z => ‖fderiv ℝ q z v‖ ^ 2) A := by
    apply (_root_.MeasureTheory.integrableOn_const (C := ((Lq : ℝ) * ‖v‖) ^ 2)
      ((_root_.ProperSpace.isCompact_closedBall (0 : ℂ) 1).inter_right _root_.Metric.isClosed_closedBall).measure_ne_top).mono'
    · have heval : Continuous (fun A : ℂ →L[ℝ] F => A v) := by fun_prop
      exact ((heval.measurable.comp (measurable_fderiv ℝ q)).norm.pow_const 2).aestronglyMeasurable
    · filter_upwards [] with z
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) ((fderiv ℝ q z).le_opNorm v |>.trans
        (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hq) (norm_nonneg v))) 2
  have hJint := ((hdirint 1).add (hdirint Complex.I)).div_const 2
  have hpoint : ∀ᵐ z ∂volume.restrict A,
      diskMapEnergyDensity g (r ∘ q) z ≤ (C : ℝ) ^ 2 *
        ((‖fderiv ℝ q z 1‖ ^ 2 + ‖fderiv ℝ q z Complex.I‖ ^ 2) / 2) := by
    filter_upwards [_root_.MeasureTheory.ae_restrict_of_ae (hq.ae_differentiableAt (μ := _root_.MeasureTheory.MeasureSpace.volume)),
      _root_.MeasureTheory.ae_restrict_mem (measurableSet_closedBall.inter measurableSet_closedBall)] with z hz hzA
    have hrz : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, E) r (q z) :=
      (hr.contMDiffAt (hU.mem_nhds (hballU (hqrange hzA)))).mdifferentiableAt one_ne_zero
    have hd := mfderiv_comp z hrz hz.mdifferentiableAt
    rw [mfderiv_eq_fderiv] at hd
    have hbound (v : ℂ) : g.inner (r (q z))
        (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) r (q z) (fderiv ℝ q z v))
        (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) r (q z) (fderiv ℝ q z v)) ≤
          (C : ℝ) ^ 2 * ‖fderiv ℝ q z v‖ ^ 2 := by
      have h := hrbound (q z) (hqrange hzA) (fderiv ℝ q z v)
      have hs := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
      rwa [Real.sq_sqrt (metric_inner_self_nonneg g _ _), mul_pow] at hs
    unfold diskMapEnergyDensity diskMapPartial
    rw [hd]
    have h1 := hbound 1
    have hI := hbound Complex.I
    change (g.inner (r (q z))
        (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) r (q z) (fderiv ℝ q z 1))
        (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) r (q z) (fderiv ℝ q z 1)) +
      g.inner (r (q z))
        (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) r (q z) (fderiv ℝ q z Complex.I))
        (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) r (q z) (fderiv ℝ q z Complex.I))) / 2 ≤ _
    nlinarith
  have hb := _root_.MeasureTheory.integral_mono_ae hvint (hJint.const_mul ((C : ℝ) ^ 2)) hpoint
  rw [_root_.MeasureTheory.integral_const_mul] at hb
  exact hc.trans (add_le_add (by simpa only [Pi.add_apply] using hb) le_rfl)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_local_reconstructed_disk_cap_energy_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_local_reconstructed_disk_cap_energy_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_local_reconstructed_disk_cap_energy_bound ``Submission.DifferentialGeometry.Geometry.exists_local_reconstructed_disk_cap_energy_bound

end DifferentialGeometry.Geometry

end

end

section

noncomputable section

open _root_.Set _root_.Filter _root_.Function _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Metric _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Topology _root_.Submission.DifferentialGeometry.Analysis
open scoped _root_.Topology _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Topology.Manifold _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

theorem exists_uniform_intrinsic_boundary_cap_energy_bound
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ : freeLoop M)
    (hγ : IsSmoothEmbeddedLoop (E := E) γ) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 ≤ C ∧ ∀ (u : C(closedDisk, M)) (L : ℝ≥0),
      (∀ z w : closedDisk, riemannianEDistOf g (u z) (u w) ≤
        (L : ℝ≥0∞) * _root_.EDist.edist z w) →
      ∀ ψ : CircleDeg1Lift, Continuous ψ →
      (∀ t : ℝ, u (diskBoundary (t : loopCircle)) = γ ((ψ t : ℝ) : loopCircle)) →
      ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      ψ (1 - Real.arccos (ρ / 2) / Real.pi) - ψ (Real.arccos (ρ / 2) / Real.pi) ≤ 2 / 3 →
      let α : ℝ → M := fun s => diskExtension u
        (circleMap (-1) ρ (-Real.arccos (ρ / 2) + 2 * Real.arccos (ρ / 2) * s))
      _root_.MeasureTheory.IntegrableOn (fun t => (riemannianCurveSpeed g α t) ^ 2) (_root_.Set.Icc (0 : ℝ) 1) →
      (∫ t in _root_.Set.Icc (0 : ℝ) 1, (riemannianCurveSpeed g α t) ^ 2) ≤ ε →
      (∫ z in boundaryLens ρ, diskMapEnergyDensity g (diskExtension u) z) ≤
        C * (∫ t in _root_.Set.Icc (0 : ℝ) 1, (riemannianCurveSpeed g α t) ^ 2) +
          (riemannianDiskEnergy g u -
            _root_.InfSet.sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
              weaklyMonotoneDiskCompetitors g γ)) := by
  obtain ⟨N, n, e, r, U, _, Cγ, J, hγN, he, hesupp, hU, heU, hr, hleft, _, hCγ, hJ⟩ :=
    exists_loop_neighborhood_embedding_retraction g γ hγ
  obtain ⟨Ce, hCe, heLip, hcurve⟩ := exists_curve_energy_bound_of_hasCompactSupport g
    (he.of_le (by simp)) hesupp
  let K := _root_.Set.range (fun θ : loopCircle => e (γ θ))
  have hK : IsCompact K := isCompact_range (he.continuous.comp γ.continuous)
  have hKU : K ⊆ U := by
    rintro _ ⟨θ, rfl⟩
    exact heU (_root_.Set.mem_image_of_mem e (hγN (_root_.Set.mem_range_self θ)))
  obtain ⟨η, Cr, hη, hlocal⟩ := exists_local_reconstructed_disk_cap_energy_bound g hU
    (hr.of_le (by simp)) hK hKU
  obtain ⟨ε₀, hε₀, htube⟩ := exists_energy_bound_curve_range_subset_of_isCompact g
    (isCompact_range γ.continuous) N.isOpen hγN
  let D : ℝ := 1 + 2 * (Cγ : ℝ) * (J : ℝ)
  have hD : 0 < D := by dsimp [D]; positivity
  let ε := _root_.Min.min ε₀ ((η / (D * Ce)) ^ 2)
  have hε : 0 < ε := lt_min hε₀ (sq_pos_of_pos (div_pos hη (by positivity)))
  let Q : ℝ := 2 * (144 * (16 * Real.pi + 1) * (18 * Real.pi ^ 2 + 1)) ^ 2 *
    ((Real.pi / 2) * D ^ 2 + (2 + 8 * (Cγ : ℝ) ^ 2 * (J : ℝ) ^ 2) / (8 * Real.pi))
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  refine ⟨ε, (Cr : ℝ) ^ 2 * Q * (Ce : ℝ) ^ 2, hε, by positivity, ?_⟩
  intro u L hu ψ hψ htrace ρ hρ hρ1 hshort α hαI hαE
  let a := Real.arccos (ρ / 2)
  let arc : ℝ → ℂ := fun s => circleMap (-1) ρ (-a + 2 * a * s)
  let f : ℂ → EuclideanSpace ℝ (Fin n) := e ∘ diskExtension u
  let Γ : ℝ → EuclideanSpace ℝ (Fin n) := fun t => e (γ (t : loopCircle))
  have hUlip := diskExtension_riemannian_lipschitz g hu
  have hf : LipschitzWith (Ce * L) f := by
    intro z w
    apply (heLip _ _).trans
    rw [ENNReal.coe_mul, mul_assoc]
    exact mul_le_mul' le_rfl (hUlip z w)
  have hparam : LipschitzWith (Real.nnabs (2 * a)) (fun s : ℝ => -a + 2 * a * s) := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    simp only [Real.dist_eq, add_sub_add_left_eq_sub, ← mul_sub, abs_mul, Real.coe_nnabs]
    exact le_rfl
  have harc := (lipschitzWith_circleMap (-1) ρ).comp hparam
  have hαlip (s t : ℝ) : riemannianEDistOf g (α s) (α t) ≤
      ((L * (Real.nnabs ρ * Real.nnabs (2 * a)) : ℝ≥0) : ℝ≥0∞) * _root_.EDist.edist s t := by
    apply (hUlip (arc s) (arc t)).trans
    rw [ENNReal.coe_mul, mul_assoc]
    exact mul_le_mul' le_rfl (harc s t)
  have hper : _root_.Function.Periodic Γ 1 := by
    intro t
    simp only [Γ, AddCircle.coe_add, AddCircle.coe_period, add_zero]
  have hInv : AntilipschitzWith J (hper.lift : loopCircle → EuclideanSpace ℝ (Fin n)) := by
    intro x y
    obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective x
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective y
    exact hJ (s : loopCircle) (t : loopCircle)
  have hftrace (t : ℝ) : f (circleMap 0 1 (2 * Real.pi * t)) = Γ (ψ t) := by
    have hz : circleMap 0 1 (2 * Real.pi * t) = (diskBoundary (t : loopCircle) : ℂ) := by
      simp only [diskBoundary_coe, circleMap, Complex.ofReal_one, one_mul, zero_add]
    change e (diskExtension u _) = e (γ _)
    rw [hz, diskExtension_coe, htrace]
  have hα0 : α 0 = γ ((ψ (1 - a / Real.pi) : ℝ) : loopCircle) := by
    have hArc : arc 0 = circleMap 0 1 (2 * Real.pi * (1 - a / Real.pi)) := by
      simp only [arc, _root_.MulZeroClass.mul_zero, add_zero]
      rw [circleMap_neg_one_neg_arccos (by linarith : -2 ≤ ρ) (by linarith : ρ ≤ 2)]
      congr 1
      dsimp [a]
      field_simp
    change diskExtension u (arc 0) = _
    rw [hArc]
    have hz : circleMap 0 1 (2 * Real.pi * (1 - a / Real.pi)) =
        (diskBoundary ((1 - a / Real.pi : ℝ) : loopCircle) : ℂ) := by
      simp only [diskBoundary_coe, circleMap, Complex.ofReal_one, one_mul, zero_add]
    rw [hz, diskExtension_coe, htrace]
  have hαrange : _root_.Set.MapsTo α (_root_.Set.Icc (0 : ℝ) 1) N :=
    htube α _ hαlip (hα0 ▸ _root_.Set.mem_range_self _) hαI (hαE.trans (min_le_left _ _))
  obtain ⟨_, hEa⟩ := hcurve α _ hαlip 0 1 hαI
  let Ea := ∫ t in _root_.Set.Icc (0 : ℝ) 1, ‖deriv (f ∘ arc) t‖ ^ 2
  have hEa' : Ea ≤ (Ce : ℝ) ^ 2 *
      ∫ t in _root_.Set.Icc (0 : ℝ) 1, (riemannianCurveSpeed g α t) ^ 2 := hEa
  have hEsq : Ea ≤ (η / D) ^ 2 := by
    apply (hEa'.trans (mul_le_mul_of_nonneg_left
      (hαE.trans (min_le_right _ _)) (sq_nonneg (Ce : ℝ)))).trans_eq
    field_simp
  have hsmall : D * Real.sqrt Ea ≤ η := by
    have hs := Real.sqrt_le_sqrt hEsq
    rw [Real.sqrt_sq (div_nonneg hη.le hD.le)] at hs
    exact (mul_le_mul_of_nonneg_left hs hD.le).trans_eq (mul_div_cancel₀ η hD.ne')
  obtain ⟨ψbar, h, q, hψbar, _, _, _, _, _, hqLip, hqrange, hseamF, hcaptrace, hqEnergy⟩ :=
    exists_boundary_cap_in_ball_of_short_lift_increment Γ hCγ hper hInv f hf ψ hψ hftrace
      hρ hρ1 hshort hsmall
  obtain ⟨Lq, hLq⟩ := hqLip
  have hseam : _root_.Set.EqOn (r ∘ q) (diskExtension u) (_root_.Metric.closedBall (0 : ℂ) 1 ∩ _root_.Metric.sphere (-1) ρ) := by
    intro z hz
    rw [Function.comp_apply, hseamF hz]
    apply hleft
    have hzArc : z ∈ circleMap (-1) ρ '' _root_.Set.Icc (-a) a := by
      rw [← sphere_inter_closedDisk_eq_inner_arc_image hρ (hρ1.le.trans (by norm_num))]
      exact ⟨hz.2, hz.1⟩
    obtain ⟨θ, hθ, rfl⟩ := hzArc
    have ha : 0 < a := Real.arccos_pos.mpr (by linarith)
    let t := (θ + a) / (2 * a)
    have ht : t ∈ _root_.Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg (by linarith [hθ.1]) (by positivity)
      · apply (div_le_one (by positivity : 0 < 2 * a)).mpr
        linarith [hθ.2]
    have heq : -a + 2 * a * t = θ := by dsimp [t]; field_simp; ring
    have hh := hαrange ht
    change diskExtension u (circleMap (-1) ρ (-a + 2 * a * t)) ∈ N at hh
    rwa [heq] at hh
  let τ := affineCircleMap ψbar hψbar ψbar.map_add_one
  have hτ : IsWeaklyMonotoneOnce τ :=
    ⟨ψbar, hψbar, fun _ => rfl, Or.inl ⟨ψbar.monotone, ψbar.map_add_one⟩⟩
  have hcap (θ : loopCircle) : attachBoundaryCap f q ρ (diskBoundary θ) = e (γ (τ θ)) := by
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
    simpa only [τ, affineCircleMap_coe, diskBoundary_coe, circleMap_zero,
      Complex.ofReal_one, one_mul, Γ] using hcaptrace t
  have hIn (θ : loopCircle) (hθ : _root_.Dist.dist (diskBoundary θ : ℂ) (-1) ≤ ρ) :
      r (q (diskBoundary θ)) = γ (τ θ) := by
    have heq := attachBoundaryCap_inner f q ρ
      (by simpa only [dist_eq_norm, sub_neg_eq_add] using hθ)
    rw [← heq, hcap]
    exact hleft _ (hγN (_root_.Set.mem_range_self _))
  have hOut (θ : loopCircle) (hθ : ρ ≤ _root_.Dist.dist (diskBoundary θ : ℂ) (-1)) :
      u (diskBoundary θ) = γ (τ θ) := by
    have heq := attachBoundaryCap_outer f q ρ hseamF (diskBoundary θ).property
      (by simpa only [dist_eq_norm, sub_neg_eq_add] using hθ)
    have hfval : r (f (diskBoundary θ)) = u (diskBoundary θ) := by
      change r (e (diskExtension u (diskBoundary θ))) = _
      rw [diskExtension_coe]
      obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
      rw [htrace]
      exact hleft _ (hγN (_root_.Set.mem_range_self _))
    rw [← hfval, ← heq, hcap]
    exact hleft _ (hγN (_root_.Set.mem_range_self _))
  have hpK : f (arc 0) ∈ K := by
    change e (α 0) ∈ _root_.Set.range (fun θ : loopCircle => e (γ θ))
    rw [hα0]
    exact _root_.Set.mem_range_self _
  have hqRange : _root_.Set.MapsTo q (_root_.Metric.closedBall (0 : ℂ) 1 ∩ _root_.Metric.closedBall (-1) ρ)
      (_root_.Metric.closedBall (f (arc 0)) η) := fun z hz => hqrange ⟨hz.2, hz.1⟩
  have hbound := hlocal (f (arc 0)) hpK u q L Lq (-1) ρ hu hLq hqRange hseam γ τ hτ hIn hOut
  rw [_root_.Set.inter_comm] at hbound
  have hqE : (∫ z in boundaryLens ρ,
      (‖fderiv ℝ q z 1‖ ^ 2 + ‖fderiv ℝ q z Complex.I‖ ^ 2) / 2) ≤ Q * Ea := hqEnergy
  have hb := mul_le_mul_of_nonneg_left hqE (sq_nonneg (Cr : ℝ))
  have hc := mul_le_mul_of_nonneg_left hEa' (mul_nonneg (sq_nonneg (Cr : ℝ)) hQ)
  calc
    _ ≤ _ := hbound
    _ ≤ (Cr : ℝ) ^ 2 * (Q * Ea) + _ := add_le_add hb le_rfl
    _ ≤ _ := by nlinarith only [hc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_uniform_intrinsic_boundary_cap_energy_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_uniform_intrinsic_boundary_cap_energy_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_uniform_intrinsic_boundary_cap_energy_bound ``Submission.DifferentialGeometry.Geometry.exists_uniform_intrinsic_boundary_cap_energy_bound

end DifferentialGeometry.Geometry

end

end
