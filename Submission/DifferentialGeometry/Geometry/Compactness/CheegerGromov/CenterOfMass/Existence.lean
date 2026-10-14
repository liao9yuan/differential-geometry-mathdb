import Submission.DifferentialGeometry.Geometry.Comparison.HalfSquaredDistance.Gradient


import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.CenterOfMass.StrictDistance.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open _root_.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian


attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [ConnectedSpace M] [T3Space M]

structure CenterOfMassConditions (g : SmoothRiemannianMetric I M)
    {ι : Type} [Fintype ι] (μ : ι → ℝ) (points : ι → M)
    (join : M → M → ℝ → M) (p : M) (r : ℝ) : Prop where
  complete :
    letI : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    CompleteSpace M
  enorm :
    letI : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v))
  r_pos : 0 < r
  points_mem :
    letI : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    ∀ i : ι, _root_.Dist.dist p (points i) < r
  μ_nonneg : ∀ i : ι, 0 ≤ μ i
  μ_pos : ∃ i : ι, 0 < μ i
  strict_distance : StrictDistanceConvexity (I := I) g points join p r

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.CenterOfMassConditions then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.CenterOfMassConditions"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.CenterOfMassConditions ``Submission.DifferentialGeometry.CheegerGromovCompactness.CenterOfMassConditions

namespace CenterOfMassConditions

variable {g : SmoothRiemannianMetric I M} {ι : Type} [Fintype ι]
  {μ : ι → ℝ} {points : ι → M} {join : M → M → ℝ → M} {p : M} {r : ℝ}

theorem exists_unique_minimizer (h : CenterOfMassConditions (I := I) g μ points join p r) :
    letI : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    ∃ q ∈ Metric.closedBall p (2 * r),
      (∀ y : M, CenterOfMass.centerEnergy (I := I) g μ points q ≤
        CenterOfMass.centerEnergy (I := I) g μ points y) ∧
      ∀ y : M,
        (∀ z : M, CenterOfMass.centerEnergy (I := I) g μ points y ≤
          CenterOfMass.centerEnergy (I := I) g μ points z) → y = q := by
  exact CenterOfMass.exists_unique_curve (I := I) g h.complete h.enorm μ points join
    h.r_pos h.points_mem h.μ_nonneg h.μ_pos h.strict_distance.mid h.strict_distance.zero
    h.strict_distance.one h.strict_distance.strict

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.CenterOfMassConditions.exists_unique_minimizer then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.CenterOfMassConditions.exists_unique_minimizer"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.CenterOfMassConditions.exists_unique_minimizer ``Submission.DifferentialGeometry.CheegerGromovCompactness.CenterOfMassConditions.exists_unique_minimizer

end CenterOfMassConditions

noncomputable def centerOfMass (g : SmoothRiemannianMetric I M)
    {ι : Type} [Fintype ι] (μ : ι → ℝ) (points : ι → M)
    (join : M → M → ℝ → M) (p : M) (r : ℝ)
    (h : CenterOfMassConditions (I := I) g μ points join p r) : M :=
  letI : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  Classical.choose h.exists_unique_minimizer

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.centerOfMass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.centerOfMass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.centerOfMass ``Submission.DifferentialGeometry.CheegerGromovCompactness.centerOfMass

namespace centerOfMass

variable {g : SmoothRiemannianMetric I M} {ι : Type} [Fintype ι]
  {μ : ι → ℝ} {points : ι → M} {join : M → M → ℝ → M} {p : M} {r : ℝ}
  (h : CenterOfMassConditions (I := I) g μ points join p r)

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] in
theorem grad_half_self (q : M)
    (hdiff :
      letI : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      MDifferentiableAt I 𝓘(ℝ, ℝ) (CenterOfMass.halfSqDist q) q) :
    letI : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    gradientFun (I := I) g (CenterOfMass.halfSqDist q) q =
      - (show TangentSpace I q from NormalCoordinates.normalChartAt (I := I) g q q) := by
  let : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  have hlocal : IsLocalMin (CenterOfMass.halfSqDist q) q := by
    unfold IsLocalMin IsMinFilter
    refine Filter.Eventually.of_forall ?_
    intro y
    unfold CenterOfMass.halfSqDist
    have hsq : 0 ≤ _root_.Dist.dist y q ^ 2 := sq_nonneg (_root_.Dist.dist y q)
    rw [dist_self]
    nlinarith
  have hgrad0 :
      gradientFun (I := I) g (CenterOfMass.halfSqDist q) q = 0 :=
    gradientFun_eq_zero_of_isLocalMin (I := I) g hlocal hdiff
  have hchart0 :
      (show TangentSpace I q from NormalCoordinates.normalChartAt (I := I) g q q) = 0 := by
    change NormalCoordinates.normalChartAt (I := I) g q q = (0 : E)
    exact NormalCoordinates.normalChartAt_centre (I := I) g q
  rw [hgrad0, hchart0, neg_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.centerOfMass.grad_half_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.centerOfMass.grad_half_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.centerOfMass.grad_half_self ``Submission.DifferentialGeometry.CheegerGromovCompactness.centerOfMass.grad_half_self

theorem mem :
    letI : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    centerOfMass (I := I) g μ points join p r h ∈ Metric.closedBall p (2 * r) := by
  let : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  exact (Classical.choose_spec h.exists_unique_minimizer).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.centerOfMass.mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.centerOfMass.mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.centerOfMass.mem ``Submission.DifferentialGeometry.CheegerGromovCompactness.centerOfMass.mem

theorem min :
    letI : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    ∀ y : M,
      CenterOfMass.centerEnergy (I := I) g μ points
          (centerOfMass (I := I) g μ points join p r h) ≤
        CenterOfMass.centerEnergy (I := I) g μ points y := by
  let : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  exact (Classical.choose_spec h.exists_unique_minimizer).2.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.centerOfMass.min then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.centerOfMass.min"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.centerOfMass.min ``Submission.DifferentialGeometry.CheegerGromovCompactness.centerOfMass.min

theorem unique :
    letI : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    ∀ y : M,
      (∀ z : M, CenterOfMass.centerEnergy (I := I) g μ points y ≤
        CenterOfMass.centerEnergy (I := I) g μ points z) →
      y = centerOfMass (I := I) g μ points join p r h := by
  let : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  exact (Classical.choose_spec h.exists_unique_minimizer).2.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.centerOfMass.unique then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.centerOfMass.unique"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.centerOfMass.unique ``Submission.DifferentialGeometry.CheegerGromovCompactness.centerOfMass.unique

theorem dist_le {qstar : M} {ε : ℝ} (hε : 0 ≤ ε)
    (hnear :
      letI : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ i : ι, _root_.Dist.dist qstar (points i) ≤ ε) :
    letI : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    dist (centerOfMass (I := I) g μ points join p r h) qstar ≤ 2 * ε := by
  let : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  obtain ⟨q, _hqmem, hqmin, hqdist, _hquniq⟩ :=
    CenterOfMass.exists_unique_curve_dist_le (I := I) g h.complete h.enorm μ points join
      h.r_pos h.points_mem hε hnear h.μ_nonneg h.μ_pos h.strict_distance.mid
      h.strict_distance.zero h.strict_distance.one h.strict_distance.strict
  have hq_eq : q = centerOfMass (I := I) g μ points join p r h := unique h q hqmin
  simpa [hq_eq] using hqdist

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.centerOfMass.dist_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.centerOfMass.dist_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.centerOfMass.dist_le ``Submission.DifferentialGeometry.CheegerGromovCompactness.centerOfMass.dist_le

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem centerEnergy_diff {x : M}
    (hdiffSummands :
      letI : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ i : ι, MDifferentiableAt I 𝓘(ℝ, ℝ) (CenterOfMass.halfSqDist (points i)) x) :
    letI : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    MDifferentiableAt I 𝓘(ℝ, ℝ) (CenterOfMass.centerEnergy (I := I) g μ points) x := by
  let : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  have hfun :
      CenterOfMass.centerEnergy (I := I) g μ points =
        (∑ i : ι, μ i • CenterOfMass.halfSqDist (points i)) := by
    funext q
    rw [CenterOfMass.centerEnergy_eq_dist (I := I) (ι := ι) g μ points q,
      CenterOfMass.metricEnergy_half (ι := ι)]
    simp [Pi.smul_apply, smul_eq_mul]
  rw [hfun]
  exact MDifferentiableAt.sum (𝕜 := ℝ) (I := I) (E' := ℝ)
    (t := Finset.univ)
    (f := fun i : ι => μ i • CenterOfMass.halfSqDist (points i)) (z := x)
    (by
      intro i _hi
      exact (hdiffSummands i).const_smul (μ i))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.centerOfMass.centerEnergy_diff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.centerOfMass.centerEnergy_diff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.centerOfMass.centerEnergy_diff ``Submission.DifferentialGeometry.CheegerGromovCompactness.centerOfMass.centerEnergy_diff

theorem expInv_equation
    (hdiffEnergy :
      letI : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      MDifferentiableAt I 𝓘(ℝ, ℝ) (CenterOfMass.centerEnergy (I := I) g μ points)
        (centerOfMass (I := I) g μ points join p r h))
    (hdiffSummands :
      letI : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ i : ι, MDifferentiableAt I 𝓘(ℝ, ℝ) (CenterOfMass.halfSqDist (points i))
        (centerOfMass (I := I) g μ points join p r h))
    (hgrad :
      letI : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ i : ι,
        gradientFun (I := I) g (CenterOfMass.halfSqDist (points i))
            (centerOfMass (I := I) g μ points join p r h) =
          - (show TangentSpace I (centerOfMass (I := I) g μ points join p r h) from
              NormalCoordinates.normalChartAt (I := I) g
                (centerOfMass (I := I) g μ points join p r h) (points i))) :
    letI : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    ∑ i : ι, μ i •
      (show TangentSpace I (centerOfMass (I := I) g μ points join p r h) from
        NormalCoordinates.normalChartAt (I := I) g
          (centerOfMass (I := I) g μ points join p r h) (points i)) = 0 := by
  let : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  exact CenterOfMass.sum_expInv_eq_zero (I := I) (κ := ι) g μ points
    (centerOfMass (I := I) g μ points join p r h) (min h) hdiffEnergy hdiffSummands hgrad

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.centerOfMass.expInv_equation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.centerOfMass.expInv_equation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.centerOfMass.expInv_equation ``Submission.DifferentialGeometry.CheegerGromovCompactness.centerOfMass.expInv_equation

theorem invB_equation
    (invB : ι → TangentSpace I (centerOfMass (I := I) g μ points join p r h))
    (hdiffSummands :
      letI : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ i : ι, MDifferentiableAt I 𝓘(ℝ, ℝ) (CenterOfMass.halfSqDist (points i))
        (centerOfMass (I := I) g μ points join p r h))
    (hgrad :
      letI : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ i : ι,
        gradientFun (I := I) g (CenterOfMass.halfSqDist (points i))
            (centerOfMass (I := I) g μ points join p r h) = -invB i) :
    letI : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    ∑ i : ι, μ i • invB i = 0 := by
  classical
  let : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  have hsum := CenterOfMass.sum_grad_eq_zero (I := I) (κ := ι) g μ points
    (centerOfMass (I := I) g μ points join p r h) (min h)
    (centerEnergy_diff (I := I) (g := g) hdiffSummands) hdiffSummands
  have hneg : ∑ i : ι, μ i • (-invB i) = 0 := by
    calc
      ∑ i : ι, μ i • (-invB i) =
          ∑ i : ι, μ i • gradientFun (I := I) g
            (CenterOfMass.halfSqDist (points i))
            (centerOfMass (I := I) g μ points join p r h) := by
              apply Finset.sum_congr rfl
              intro i _
              rw [hgrad i]
      _ = 0 := hsum
  have hsum_neg : -(∑ i : ι, μ i • invB i) = 0 := by
    simpa only [Finset.sum_neg_distrib, smul_neg] using hneg
  exact neg_eq_zero.mp hsum_neg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.centerOfMass.invB_equation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.centerOfMass.invB_equation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.centerOfMass.invB_equation ``Submission.DifferentialGeometry.CheegerGromovCompactness.centerOfMass.invB_equation

theorem expInv_equation_local
    (hdiffSummands :
      letI : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ i : ι, MDifferentiableAt I 𝓘(ℝ, ℝ) (CenterOfMass.halfSqDist (points i))
        (centerOfMass (I := I) g μ points join p r h))
    (hsrc :
      letI : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ i : ι, points i ∈
        (NormalCoordinates.normalChartAt (I := I) g
          (centerOfMass (I := I) g μ points join p r h)).source) :
    letI : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    ∃ ρ : ℝ, 0 < ρ ∧
      ((∀ i : ι, points i ≠ centerOfMass (I := I) g μ points join p r h →
        Real.sqrt
          (g.inner (centerOfMass (I := I) g μ points join p r h)
            (NormalCoordinates.normalChartAt (I := I) g
              (centerOfMass (I := I) g μ points join p r h) (points i) : E)
            (NormalCoordinates.normalChartAt (I := I) g
              (centerOfMass (I := I) g μ points join p r h) (points i) : E)) < ρ) →
        ∑ i : ι, μ i •
          (show TangentSpace I (centerOfMass (I := I) g μ points join p r h) from
            NormalCoordinates.normalChartAt (I := I) g
              (centerOfMass (I := I) g μ points join p r h) (points i)) = 0) := by
  let : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
  have : CompleteSpace M := h.complete
  let : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  set q := centerOfMass (I := I) g μ points join p r h
  obtain ⟨ρ, hρ, hgradρ⟩ := grad_halfSqDist (I := I) g h.enorm q
  refine ⟨ρ, hρ, ?_⟩
  intro hsmall
  refine expInv_equation h (centerEnergy_diff (I := I) (g := g) hdiffSummands)
    hdiffSummands ?_
  intro i
  by_cases hself : points i = q
  · rw [hself]
    have hdiffSelf :
        MDifferentiableAt I 𝓘(ℝ, ℝ) (CenterOfMass.halfSqDist q) q := by
      simpa [hself] using hdiffSummands i
    exact grad_half_self (I := I) (g := g) q hdiffSelf
  · exact hgradρ (hsrc i) hself (hsmall i hself) (hdiffSummands i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.centerOfMass.expInv_equation_local then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.centerOfMass.expInv_equation_local"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.centerOfMass.expInv_equation_local ``Submission.DifferentialGeometry.CheegerGromovCompactness.centerOfMass.expInv_equation_local

noncomputable def equationRadius : ℝ :=
  letI : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
  letI : CompleteSpace M := h.complete
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  Classical.choose (grad_halfSqDist (I := I) g h.enorm
    (centerOfMass (I := I) g μ points join p r h))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.centerOfMass.equationRadius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.centerOfMass.equationRadius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.centerOfMass.equationRadius ``Submission.DifferentialGeometry.CheegerGromovCompactness.centerOfMass.equationRadius

theorem equationRadius_pos : 0 < equationRadius (I := I) h := by
  let : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
  have : CompleteSpace M := h.complete
  let : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  exact (Classical.choose_spec (grad_halfSqDist (I := I) g h.enorm
    (centerOfMass (I := I) g μ points join p r h))).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.centerOfMass.equationRadius_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.centerOfMass.equationRadius_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.centerOfMass.equationRadius_pos ``Submission.DifferentialGeometry.CheegerGromovCompactness.centerOfMass.equationRadius_pos

theorem grad_eq_of_lt {pt : M}
    (hsrc : pt ∈ (NormalCoordinates.normalChartAt (I := I) g
      (centerOfMass (I := I) g μ points join p r h)).source)
    (hne : pt ≠ centerOfMass (I := I) g μ points join p r h)
    (hsmall : Real.sqrt
      (g.inner (centerOfMass (I := I) g μ points join p r h)
        (NormalCoordinates.normalChartAt (I := I) g
          (centerOfMass (I := I) g μ points join p r h) pt : E)
        (NormalCoordinates.normalChartAt (I := I) g
          (centerOfMass (I := I) g μ points join p r h) pt : E)) <
      equationRadius (I := I) h)
    (hdiff :
      letI : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      MDifferentiableAt I 𝓘(ℝ, ℝ) (CenterOfMass.halfSqDist pt)
        (centerOfMass (I := I) g μ points join p r h)) :
    letI : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    gradientFun (I := I) g (CenterOfMass.halfSqDist pt)
      (centerOfMass (I := I) g μ points join p r h) =
      -(show TangentSpace I (centerOfMass (I := I) g μ points join p r h) from
        NormalCoordinates.normalChartAt (I := I) g
          (centerOfMass (I := I) g μ points join p r h) pt) := by
  let : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
  have : CompleteSpace M := h.complete
  let : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  exact (Classical.choose_spec (grad_halfSqDist (I := I) g h.enorm
    (centerOfMass (I := I) g μ points join p r h))).2 hsrc hne hsmall hdiff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.centerOfMass.grad_eq_of_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.centerOfMass.grad_eq_of_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.centerOfMass.grad_eq_of_lt ``Submission.DifferentialGeometry.CheegerGromovCompactness.centerOfMass.grad_eq_of_lt

theorem expInv_equation_of_lt
    (hdiffSummands :
      letI : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ i : ι, MDifferentiableAt I 𝓘(ℝ, ℝ) (CenterOfMass.halfSqDist (points i))
        (centerOfMass (I := I) g μ points join p r h))
    (hsrc :
      letI : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ i : ι, points i ∈ (NormalCoordinates.normalChartAt (I := I) g
        (centerOfMass (I := I) g μ points join p r h)).source)
    (hsmall :
      letI : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ i : ι, points i ≠ centerOfMass (I := I) g μ points join p r h →
        Real.sqrt
          (g.inner (centerOfMass (I := I) g μ points join p r h)
            (NormalCoordinates.normalChartAt (I := I) g
              (centerOfMass (I := I) g μ points join p r h) (points i) : E)
            (NormalCoordinates.normalChartAt (I := I) g
              (centerOfMass (I := I) g μ points join p r h) (points i) : E)) <
          equationRadius (I := I) h) :
    letI : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    ∑ i : ι, μ i •
      (show TangentSpace I (centerOfMass (I := I) g μ points join p r h) from
        NormalCoordinates.normalChartAt (I := I) g
          (centerOfMass (I := I) g μ points join p r h) (points i)) = 0 := by
  let : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  refine expInv_equation h (centerEnergy_diff (I := I) (g := g) hdiffSummands)
    hdiffSummands ?_
  intro i
  by_cases hself : points i = centerOfMass (I := I) g μ points join p r h
  · rw [hself]
    have hdiffSelf :
        MDifferentiableAt I 𝓘(ℝ, ℝ)
          (CenterOfMass.halfSqDist (centerOfMass (I := I) g μ points join p r h))
          (centerOfMass (I := I) g μ points join p r h) := by
      simpa [hself] using hdiffSummands i
    exact grad_half_self (I := I) (g := g) _ hdiffSelf
  · exact grad_eq_of_lt h (hsrc i) hself (hsmall i hself) (hdiffSummands i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.centerOfMass.expInv_equation_of_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.centerOfMass.expInv_equation_of_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.centerOfMass.expInv_equation_of_lt ``Submission.DifferentialGeometry.CheegerGromovCompactness.centerOfMass.expInv_equation_of_lt

end centerOfMass

theorem centerOfMass_cont {P : Type*} [TopologicalSpace P] [FirstCountableTopology P]
    (g : SmoothRiemannianMetric I M) {ι : Type} [Fintype ι]
    (μ : P → ι → ℝ) (points : P → ι → M) (join : M → M → ℝ → M) (p : M) (r : ℝ) (p₀ : P)
    (H : ∀ a : P, CenterOfMassConditions (I := I) g (μ a) (points a) join p r)
    (hμ : Continuous μ) (hpts : Continuous points) :
    letI : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    Filter.Tendsto (fun a : P => centerOfMass (I := I) g (μ a) (points a) join p r (H a)) (nhds p₀)
      (nhds (centerOfMass (I := I) g (μ p₀) (points p₀) join p r (H p₀))) := by
  let : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  have : ProperSpace M :=
    HopfRinow.properSpace_riemMetric (I := I) (M := M) (H p₀).complete g (H p₀).enorm
  refine CenterOfMass.metricEnergy_argmin_stable (_root_.ProperSpace.isCompact_closedBall p (2 * r))
    μ points (fun a => centerOfMass (I := I) g (μ a) (points a) join p r (H a)) p₀ hμ hpts ?_ ?_ ?_
  · intro a y
    simp only [← CenterOfMass.centerEnergy_eq_dist (I := I) g (μ a) (points a)]
    exact centerOfMass.min (H a) y
  · intro a
    exact centerOfMass.mem (H a)
  · intro y hy
    refine centerOfMass.unique (H p₀) y (fun z => ?_)
    simp only [CenterOfMass.centerEnergy_eq_dist (I := I) g (μ p₀) (points p₀)]
    exact hy z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.centerOfMass_cont then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.centerOfMass_cont"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.centerOfMass_cont ``Submission.DifferentialGeometry.CheegerGromovCompactness.centerOfMass_cont

end CheegerGromovCompactness
end DifferentialGeometry
