import Mathlib.Topology.Order.IntermediateValue
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Tangent.NormDiamond
import Submission.DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic
import Submission.DifferentialGeometry.Geometry.Metric.Completeness
import Submission.DifferentialGeometry.Geometry.Metric.Exhaustion

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Submission.DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Function _root_.Filter _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry

namespace RiemannianMetricComplete

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem closedEBall_isCompact
    {g : SmoothRiemannianMetric I M}
    (hg : RiemannianMetricComplete (I := I) g)
    (O : M) (R : ℝ) :
    IsCompact
      {x : M |
        riemannianEDistOf (I := I) g O x ≤ ENNReal.ofReal R} := by
  let : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  let : TopologicalSpace.MetrizableSpace M :=
    Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E
      (fun x : M => TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : CompleteSpace M := hg.complete
  have hEnorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)) :=
    fun x v =>
      tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := I) g x v
  let ρ : ℝ := (ENNReal.ofReal R).toReal
  have : FiniteDimensional ℝ (TangentSpace I O) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  have : ProperSpace (TangentSpace I O) :=
    FiniteDimensional.proper_real (TangentSpace I O)
  have himg :
      IsCompact
        ((fun v => expMapIntrinsic (I := I) g hEnorm O v) ''
          Metric.closedBall (0 : TangentSpace I O) ρ) :=
    (_root_.ProperSpace.isCompact_closedBall (0 : TangentSpace I O) ρ).image
      (expMapIntrinsic_continuous (I := I) g hEnorm O)
  have hclosed :
      IsClosed
        {x : M |
          riemannianEDistOf (I := I) g O x ≤ ENNReal.ofReal R} := by
    have hset :
        {x : M |
          riemannianEDistOf (I := I) g O x ≤ ENNReal.ofReal R} =
          Metric.closedEBall O (ENNReal.ofReal R) := by
      ext x
      rw [Metric.mem_closedEBall',
        IsRiemannianManifold.out (I := I) O x]
      rfl
    rw [hset]
    exact Metric.isClosed_closedEBall
  refine himg.of_isClosed_subset hclosed ?_
  intro x hx
  have hfin :
      riemannianEDist I O x ≠ (⊤ : ℝ≥0∞) := by
    apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    change _root_.Manifold.riemannianEDist I O x ≤ ENNReal.ofReal R at hx
    exact hx
  obtain ⟨v, hv_exp, hv_len⟩ :=
    hopf_rinow_expMapIntrinsic_surjective_minimizing_of_ne_top
      (I := I) g hEnorm O x hfin
  refine ⟨v, ?_, hv_exp⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  have hnorm : ‖v‖ = Real.sqrt (g.inner O v v) := by
    have hv := hEnorm O v
    rw [← ofReal_norm] at hv
    exact (ENNReal.ofReal_eq_ofReal_iff
      (norm_nonneg v) (Real.sqrt_nonneg _)).mp hv
  rw [hnorm, hv_len]
  exact (ENNReal.toReal_le_toReal hfin ENNReal.ofReal_ne_top).2
    (by
      change _root_.Manifold.riemannianEDist I O x ≤ ENNReal.ofReal R at hx
      exact hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.RiemannianMetricComplete.closedEBall_isCompact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.RiemannianMetricComplete.closedEBall_isCompact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.RiemannianMetricComplete.closedEBall_isCompact ``Submission.DifferentialGeometry.RiemannianMetricComplete.closedEBall_isCompact

end RiemannianMetricComplete

namespace Geometry
namespace Riemannian
namespace HopfRinow

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [ConnectedSpace M] [T3Space M]
variable [RiemannianBundle (fun x : M => TangentSpace I x)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
@[reducible] noncomputable def riemMetricSpace
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] :
    MetricSpace M :=
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  EMetricSpace.toMetricSpace (fun x y : M => by
    rw [IsRiemannianManifold.out (I := I) x y]
    exact riemannianEDist_ne_top (I := I) x y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.HopfRinow.riemMetricSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.HopfRinow.riemMetricSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.HopfRinow.riemMetricSpace ``Submission.DifferentialGeometry.Geometry.Riemannian.HopfRinow.riemMetricSpace

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem riemMetric_realizes
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] :
    ∀ x y : M,
      (letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
       _root_.EDist.edist x y) =
      ENNReal.ofReal (letI : MetricSpace M := riemMetricSpace (I := I) (M := M)
       dist x y) := by
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : MetricSpace M := riemMetricSpace (I := I) (M := M)
  intro x y
  exact edist_dist x y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.HopfRinow.riemMetric_realizes then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.HopfRinow.riemMetric_realizes"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.HopfRinow.riemMetric_realizes ``Submission.DifferentialGeometry.Geometry.Riemannian.HopfRinow.riemMetric_realizes

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem riemMetric_dist_eq
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (x y : M) :
    letI : MetricSpace M := riemMetricSpace (I := I) (M := M)
    dist x y = (_root_.Manifold.riemannianEDist I x y).toReal := by
  let : MetricSpace M := riemMetricSpace (I := I) (M := M)
  have hreal := riemMetric_realizes (I := I) (M := M) x y
  have hfin : _root_.Manifold.riemannianEDist I x y ≠ (⊤ : ℝ≥0∞) :=
    riemannianEDist_ne_top (I := I) x y
  have hout :
      (letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
       edist x y) = _root_.Manifold.riemannianEDist I x y := by
    let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    exact IsRiemannianManifold.out (I := I) x y
  have hriem : _root_.Manifold.riemannianEDist I x y = ENNReal.ofReal (_root_.Dist.dist x y) := by
    rw [← hout]
    exact hreal
  rw [hriem, ENNReal.toReal_ofReal dist_nonneg]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.HopfRinow.riemMetric_dist_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.HopfRinow.riemMetric_dist_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.HopfRinow.riemMetric_dist_eq ``Submission.DifferentialGeometry.Geometry.Riemannian.HopfRinow.riemMetric_dist_eq

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [ConnectedSpace M] in
omit [T2Space (TangentBundle I M)] in
theorem expImageClosedBall_compact
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (hcomplete :
      letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
      CompleteSpace M)
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (R : ℝ) :
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    IsCompact ((fun v => expMapIntrinsic (I := I) g hEnorm p v) ''
      Metric.closedBall (0 : TangentSpace I p) R) := by
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  have : CompleteSpace M := hcomplete
  have : FiniteDimensional ℝ (TangentSpace I p) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  have : ProperSpace (TangentSpace I p) :=
    FiniteDimensional.proper_real (TangentSpace I p)
  exact (_root_.ProperSpace.isCompact_closedBall (0 : TangentSpace I p) R).image
    (expMapIntrinsic_continuous (I := I) g hEnorm p)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.HopfRinow.expImageClosedBall_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.HopfRinow.expImageClosedBall_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.HopfRinow.expImageClosedBall_compact ``Submission.DifferentialGeometry.Geometry.Riemannian.HopfRinow.expImageClosedBall_compact

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem closedBall_subset_expImage
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (hcomplete :
      letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
      CompleteSpace M)
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) {R : ℝ} :
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    (letI : MetricSpace M := riemMetricSpace (I := I) (M := M)
     Metric.closedBall p R) ⊆
      (fun v => expMapIntrinsic (I := I) g hEnorm p v) ''
        Metric.closedBall (0 : TangentSpace I p) R := by
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  have : CompleteSpace M := hcomplete
  let : MetricSpace M := riemMetricSpace (I := I) (M := M)
  intro y hy
  obtain ⟨v, hv_exp, hv_len⟩ :=
    hopf_rinow_expMapIntrinsic_surjective_minimizing (I := I) g hEnorm p y
  refine ⟨v, ?_, hv_exp⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  have hnorm : ‖v‖ = Real.sqrt (g.inner p v v) := by
    have hz := hEnorm p v
    rw [← ofReal_norm] at hz
    exact (ENNReal.ofReal_eq_ofReal_iff (norm_nonneg v) (Real.sqrt_nonneg _)).mp hz
  rw [hnorm, hv_len]
  have hy' : _root_.Dist.dist p y ≤ R := by
    simpa [Metric.mem_closedBall, dist_comm] using hy
  rw [riemMetric_dist_eq (I := I) (M := M) p y] at hy'
  exact hy'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.HopfRinow.closedBall_subset_expImage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.HopfRinow.closedBall_subset_expImage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.HopfRinow.closedBall_subset_expImage ``Submission.DifferentialGeometry.Geometry.Riemannian.HopfRinow.closedBall_subset_expImage

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem properSpace_riemMetric
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (hcomplete :
      letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
      CompleteSpace M)
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) :
    letI : MetricSpace M := riemMetricSpace (I := I) (M := M)
    ProperSpace M := by
  let : MetricSpace M := riemMetricSpace (I := I) (M := M)
  refine ProperSpace.of_isCompact_closedBall_of_le (α := M) 0 ?_
  intro p R hR
  have hsubset :=
    closedBall_subset_expImage (I := I) (M := M) hcomplete g hEnorm p (R := R)
  have himg :=
    expImageClosedBall_compact (I := I) (M := M) hcomplete g hEnorm p R
  have hclosed : IsClosed (Metric.closedBall p R) := by
    simpa [riemMetricSpace] using
      (Metric.isClosed_closedBall : IsClosed (Metric.closedBall p R))
  exact himg.of_isClosed_subset hclosed hsubset

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.HopfRinow.properSpace_riemMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.HopfRinow.properSpace_riemMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.HopfRinow.properSpace_riemMetric ``Submission.DifferentialGeometry.Geometry.Riemannian.HopfRinow.properSpace_riemMetric

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem intermediateDist_riemMetric
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (hcomplete :
      letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
      CompleteSpace M)
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (O : M) :
    letI : MetricSpace M := riemMetricSpace (I := I) (M := M)
    ∀ p : M, ∀ t : ℝ, 0 ≤ t → t ≤ _root_.Dist.dist p O →
      ∃ q : M, _root_.Dist.dist q O = t := by
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  have : CompleteSpace M := hcomplete
  let : MetricSpace M := riemMetricSpace (I := I) (M := M)
  intro p t ht0 htp
  obtain ⟨v, hv_exp, _hv_len⟩ :=
    hopf_rinow_expMapIntrinsic_surjective_minimizing (I := I) g hEnorm O p
  let γ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm O v
  let f : ℝ → ℝ := fun s => _root_.Dist.dist (γ s) O
  have hγ0 : γ 0 = O := intrinsicGeodesic_zero (I := I) g hEnorm O v
  have hγ1 : γ 1 = p := by
    simpa [γ, expMapIntrinsic_def] using hv_exp
  have hf_cont : ContinuousOn f (Set.Icc (0 : ℝ) 1) := by
    exact ((intrinsicGeodesic_continuous (I := I) g hEnorm O v).dist
      continuous_const).continuousOn
  have hmem : t ∈ Set.Icc (f 0) (f 1) := by
    rw [Set.mem_Icc]
    constructor
    · simpa [f, hγ0] using ht0
    · simpa [f, hγ1, dist_comm] using htp
  obtain ⟨s, hsIcc, hs⟩ :=
    intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num) hf_cont hmem
  exact ⟨γ s, by simpa [f] using hs⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.HopfRinow.intermediateDist_riemMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.HopfRinow.intermediateDist_riemMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.HopfRinow.intermediateDist_riemMetric ``Submission.DifferentialGeometry.Geometry.Riemannian.HopfRinow.intermediateDist_riemMetric

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [RiemannianBundle (fun x : M => TangentSpace I x)] in
theorem properSpace_riemMetric_of_complete_metric
    (g : SmoothRiemannianMetric I M)
    (hcomplete : RiemannianMetricComplete (I := I) g) :
    letI : IsManifold I 1 M :=
      IsManifold.of_le (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
        (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
    letI : TopologicalSpace.MetrizableSpace M :=
      Manifold.metrizableSpace I M
    letI : T3Space M := inferInstance
    letI : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    letI : PseudoEMetricSpace M :=
      (EMetricSpace.ofRiemannianMetric I M).toPseudoEMetricSpace
    letI : CompleteSpace M := hcomplete.complete
    letI : MetricSpace M := riemMetricSpace (I := I) (M := M)
    ProperSpace M := by
  let : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  let : TopologicalSpace.MetrizableSpace M :=
    Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : PseudoEMetricSpace M :=
    (EMetricSpace.ofRiemannianMetric I M).toPseudoEMetricSpace
  let : CompleteSpace M := hcomplete.complete
  have hEnorm : IsMetricNorm (I := I) (M := M) g := by
    intro x v
    exact tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g x v
  exact properSpace_riemMetric (I := I) (M := M) hcomplete.complete g hEnorm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.HopfRinow.properSpace_riemMetric_of_complete_metric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.HopfRinow.properSpace_riemMetric_of_complete_metric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.HopfRinow.properSpace_riemMetric_of_complete_metric ``Submission.DifferentialGeometry.Geometry.Riemannian.HopfRinow.properSpace_riemMetric_of_complete_metric

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
noncomputable def metricExhaustionOfCompleteMetric
    (g : SmoothRiemannianMetric I M)
    (hg : RiemannianMetricComplete (I := I) g)
    (x₀ : M) :
    letI : IsManifold I 1 M :=
      IsManifold.of_le (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
        (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
    letI : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
    letI : T3Space M := inferInstance
    letI : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    letI : PseudoEMetricSpace M :=
      (EMetricSpace.ofRiemannianMetric I M).toPseudoEMetricSpace
    letI : CompleteSpace M := hg.complete
    letI : MetricSpace M := riemMetricSpace (I := I) (M := M)
    letI : ProperSpace M := by
      exact properSpace_riemMetric_of_complete_metric (I := I) (M := M) g hg
    MetricExhaustion M := by
  let : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : PseudoEMetricSpace M :=
    (EMetricSpace.ofRiemannianMetric I M).toPseudoEMetricSpace
  let : CompleteSpace M := hg.complete
  let : MetricSpace M := riemMetricSpace (I := I) (M := M)
  let : ProperSpace M :=
    properSpace_riemMetric_of_complete_metric (I := I) (M := M) g hg
  exact MetricExhaustion.closedBall x₀

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.HopfRinow.metricExhaustionOfCompleteMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.HopfRinow.metricExhaustionOfCompleteMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.HopfRinow.metricExhaustionOfCompleteMetric ``Submission.DifferentialGeometry.Geometry.Riemannian.HopfRinow.metricExhaustionOfCompleteMetric

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [RiemannianBundle (fun x : M => TangentSpace I x)] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space (TangentBundle I M)] in
theorem riemMetric_dist_eq_of_complete_metric
    (g : SmoothRiemannianMetric I M)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (x y : M) :
    letI : IsManifold I 1 M :=
      IsManifold.of_le (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
        (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
    letI : TopologicalSpace.MetrizableSpace M :=
      Manifold.metrizableSpace I M
    letI : T3Space M := inferInstance
    letI : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    letI : PseudoEMetricSpace M :=
      (EMetricSpace.ofRiemannianMetric I M).toPseudoEMetricSpace
    letI : CompleteSpace M := hcomplete.complete
    letI : MetricSpace M := riemMetricSpace (I := I) (M := M)
    dist x y = (_root_.Manifold.riemannianEDist I x y).toReal := by
  let _ := hcomplete
  let : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  let : TopologicalSpace.MetrizableSpace M :=
    Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : PseudoEMetricSpace M :=
    (EMetricSpace.ofRiemannianMetric I M).toPseudoEMetricSpace
  let : CompleteSpace M := hcomplete.complete
  exact riemMetric_dist_eq (I := I) (M := M) x y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.HopfRinow.riemMetric_dist_eq_of_complete_metric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.HopfRinow.riemMetric_dist_eq_of_complete_metric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.HopfRinow.riemMetric_dist_eq_of_complete_metric ``Submission.DifferentialGeometry.Geometry.Riemannian.HopfRinow.riemMetric_dist_eq_of_complete_metric

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [RiemannianBundle (fun x : M => TangentSpace I x)] in
theorem intermediateDist_riemMetric_of_complete_metric
    (g : SmoothRiemannianMetric I M)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (O : M) :
    letI : IsManifold I 1 M :=
      IsManifold.of_le (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
        (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
    letI : TopologicalSpace.MetrizableSpace M :=
      Manifold.metrizableSpace I M
    letI : T3Space M := inferInstance
    letI : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    letI : PseudoEMetricSpace M :=
      (EMetricSpace.ofRiemannianMetric I M).toPseudoEMetricSpace
    letI : CompleteSpace M := hcomplete.complete
    letI : MetricSpace M := riemMetricSpace (I := I) (M := M)
    ∀ p : M, ∀ t : ℝ, 0 ≤ t → t ≤ _root_.Dist.dist p O →
      ∃ q : M, _root_.Dist.dist q O = t := by
  let : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  let : TopologicalSpace.MetrizableSpace M :=
    Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : PseudoEMetricSpace M :=
    (EMetricSpace.ofRiemannianMetric I M).toPseudoEMetricSpace
  let : CompleteSpace M := hcomplete.complete
  have hEnorm : IsMetricNorm (I := I) (M := M) g := by
    intro x v
    exact tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g x v
  exact intermediateDist_riemMetric (I := I) (M := M) hcomplete.complete g hEnorm O

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.HopfRinow.intermediateDist_riemMetric_of_complete_metric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.HopfRinow.intermediateDist_riemMetric_of_complete_metric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.HopfRinow.intermediateDist_riemMetric_of_complete_metric ``Submission.DifferentialGeometry.Geometry.Riemannian.HopfRinow.intermediateDist_riemMetric_of_complete_metric

end HopfRinow
end Riemannian
end Geometry
end DifferentialGeometry

end
