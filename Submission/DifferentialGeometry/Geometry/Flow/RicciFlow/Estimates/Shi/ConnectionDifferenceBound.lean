import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.TimeWeighted
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Connection.TimeIntegrability
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Connection.EndpointConvergence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Connection.DifferenceTimeDerivative
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.TimeIntegrability
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.InitialDistanceSupWeight
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.InitialDistanceLaplacian

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

theorem initialConnectionDifferenceBound_sqrt_of_complete_bounded_curvature
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) {T K : ℝ} (hT : 0 < T)
    (hcarrier : _root_.Set.Icc (0 : ℝ) T ⊆ D.carrier)
    (hregular : _root_.Set.Ioc (0 : ℝ) T ⊆ D.regular)
    (hcomplete : RiemannianMetricComplete (I := I) (S.base.metric 0))
    (hK : 0 ≤ K)
    (hcurv : ∀ t ∈ _root_.Set.Icc (0 : ℝ) T, ∀ x : M,
      nablaKRm04NormSqIntrinsic S 0 t x ≤ K) :
    InitialConnectionDifferenceBound S T _root_.Set.univ
      ((3 * Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 5) *
        Real.exp (3 * ((Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt K) * T)) *
          (2 * Real.sqrt ((2 : ℝ) ^ 1 *
      (towerConst (_root_.Max.max 0 (∑ j ∈ Finset.range 3, rmTowerCost (Module.finrank ℝ E) j))
        (_root_.Max.max 1 K * T) 1) ^ 2 * (_root_.Max.max 1 K) ^ 2))) (fun t _ => Real.sqrt t) := by
  have hcurvNorm : ∀ t ∈ _root_.Set.Icc (0 : ℝ) T, ∀ x : M,
      Tensor0SBundle.normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ K := by
    intro t ht x
    simpa only [nablaKRm04NormSqIntrinsic, nablaKRm04Field_zero, Nat.add_zero]
      using hcurv t ht x
  have hinitial : ∀ (x : M) (u w v : TangentSpace I x),
      ContinuousWithinAt
        (fun r : ℝ => (S.base.metric 0).inner x
          (CovariantDerivative.difference
            (LeviCivita (I := I) (S.base.metric r))
            (LeviCivita (I := I) (S.base.metric 0)) x u w) v)
        (_root_.Set.Icc (0 : ℝ) T) 0 :=
    continuousWithinAt_initial_connection_pairing_of_complete_bounded_curvature
      S hS hT hcarrier hregular hcomplete hK hcurvNorm
  let A : ℝ := ((2 : ℝ) ^ 1 *
      (towerConst (_root_.Max.max 0 (∑ j ∈ Finset.range 3, rmTowerCost (Module.finrank ℝ E) j))
        (_root_.Max.max 1 K * T) 1) ^ 2 * (_root_.Max.max 1 K) ^ 2)
  have hweighted := time_weighted_curvature_derivative_bound_of_complete
    S hS hcarrier hregular hcomplete hK hcurvNorm 1
  have hbound : ∀ t ∈ _root_.Set.Ioc (0 : ℝ) T, ∀ x : M,
      (t - 0) * nablaKRm04NormSqIntrinsic S 1 t x ≤ A := by
    intro t ht x
    simpa only [A, pow_one, sub_zero] using hweighted t ht x
  have hint : ∀ t ∈ _root_.Set.Ioc (0 : ℝ) T, ∀ x : M,
      IntervalIntegrable (fun s => Real.sqrt (nablaKRm04NormSqIntrinsic S 1 s x))
        volume 0 t := by
    intro t ht x
    exact intervalIntegrable_sqrt_nablaKRm04NormSqIntrinsic_of_sub_mul_le
      S hS ht.1.le (fun _ hs => hregular ⟨hs.1, hs.2.trans ht.2⟩) 1 x
      (fun s hs => hbound s ⟨hs.1, hs.2.trans ht.2⟩ x)
  have hspeed : ∀ (x : M) (u w v : TangentSpace I x),
      IntervalIntegrable
        (fun s => (S.base.metric 0).inner x (connectionVariationSpeed S s x u w) v)
        volume 0 T := by
    intro x u w v
    exact intervalIntegrable_connectionVariationSpeed_pairing_of_curvature_bound
      S hS hT.le hcarrier hregular x u w v (fun s hs => hcurv s hs x)
      (hint T ⟨hT, le_rfl⟩ x)
  have hrep := connectionDifferenceTimeIntegralOn_of_initial_continuity
    S hS hcarrier hregular hinitial hspeed
  let C₀ : ℝ := 3 * Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 5) *
    Real.exp (3 * ((Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt K) * T)
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  have hconn : InitialConnectionDifferenceBound S T _root_.Set.univ C₀
      (nablaRmTimeIntegral S) :=
    initialConnectionDifferenceBound_of_connectionVariation S hS hT hcarrier hregular
      (fun s hs y _ => hcurv s hs y) (Real.sqrt_nonneg _)
      (connectionVariationKoszulOn_connectionVariationSpeed S T)
      (nablaRicciNormBoundOn_nablaRicci S T) hrep hint
  have hintegral : ∀ t ∈ _root_.Set.Ioc (0 : ℝ) T, ∀ x : M,
      nablaRmTimeIntegral S t x ≤ 2 * Real.sqrt A * Real.sqrt t := by
    intro t ht x
    have h := integral_sqrt_nablaKRm04NormSqIntrinsic_le_of_sub_mul_le
      S hS ht.1.le (fun _ hs => hregular ⟨hs.1, hs.2.trans ht.2⟩) 1 x
      (fun s hs => hbound s ⟨hs.1, hs.2.trans ht.2⟩ x)
    simpa only [sub_zero, nablaRmTimeIntegral] using h
  intro t ht x hx u w
  have h := hconn.mono hC₀ hintegral t ht x hx u w
  dsimp at h ⊢
  convert h using 1
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.initialConnectionDifferenceBound_sqrt_of_complete_bounded_curvature then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.initialConnectionDifferenceBound_sqrt_of_complete_bounded_curvature"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.initialConnectionDifferenceBound_sqrt_of_complete_bounded_curvature ``Submission.DifferentialGeometry.PDE.RicciFlow.initialConnectionDifferenceBound_sqrt_of_complete_bounded_curvature

theorem exists_initialConnectionDifferenceBound_sqrt_of_complete_bounded_curvature
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) {T K : ℝ} (hT : 0 < T)
    (hcarrier : _root_.Set.Icc (0 : ℝ) T ⊆ D.carrier)
    (hregular : _root_.Set.Ioc (0 : ℝ) T ⊆ D.regular)
    (hcomplete : RiemannianMetricComplete (I := I) (S.base.metric 0))
    (hK : 0 ≤ K)
    (hcurv : ∀ t ∈ _root_.Set.Icc (0 : ℝ) T, ∀ x : M,
      nablaKRm04NormSqIntrinsic S 0 t x ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧
      InitialConnectionDifferenceBound S T _root_.Set.univ C (fun t _ => Real.sqrt t) := by
  refine ⟨(3 * Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 5) *
        Real.exp (3 * ((Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt K) * T)) *
          (2 * Real.sqrt ((2 : ℝ) ^ 1 *
      (towerConst (_root_.Max.max 0 (∑ j ∈ Finset.range 3, rmTowerCost (Module.finrank ℝ E) j))
        (_root_.Max.max 1 K * T) 1) ^ 2 * (_root_.Max.max 1 K) ^ 2)), by positivity, ?_⟩
  exact initialConnectionDifferenceBound_sqrt_of_complete_bounded_curvature
    S hS hT hcarrier hregular hcomplete hK hcurv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.exists_initialConnectionDifferenceBound_sqrt_of_complete_bounded_curvature then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.exists_initialConnectionDifferenceBound_sqrt_of_complete_bounded_curvature"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.exists_initialConnectionDifferenceBound_sqrt_of_complete_bounded_curvature ``Submission.DifferentialGeometry.PDE.RicciFlow.exists_initialConnectionDifferenceBound_sqrt_of_complete_bounded_curvature

end DifferentialGeometry.PDE.RicciFlow

end

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem InitialConnectionDifferenceBound.timeShift
    {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D}
    {a b C : ℝ} {B : Set M} {Theta : ℝ → M → ℝ}
    (h : InitialConnectionDifferenceBound (S.timeShift a) (b - a) B C Theta) :
    ∀ t ∈ _root_.Set.Ioc a b, ∀ x ∈ B, ∀ u w : TangentSpace I x,
      Real.sqrt ((S.base.metric a).inner x
        (CovariantDerivative.difference
          (LeviCivita (S.base.metric t)) (LeviCivita (S.base.metric a)) x u w)
        (CovariantDerivative.difference
          (LeviCivita (S.base.metric t)) (LeviCivita (S.base.metric a)) x u w)) ≤
        C * Theta (t - a) x *
          Real.sqrt ((S.base.metric a).inner x u u) *
          Real.sqrt ((S.base.metric a).inner x w w) := by
  intro t ht x hx u w
  have htshift : t - a ∈ _root_.Set.Ioc (0 : ℝ) (b - a) := by
    constructor <;> linarith [ht.1, ht.2]
  have hbound := h (t - a) htshift x hx u w
  simpa only [SolutionOn.timeShift_base_metric, zero_add, sub_add_cancel] using hbound

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.InitialConnectionDifferenceBound.timeShift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.InitialConnectionDifferenceBound.timeShift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.InitialConnectionDifferenceBound.timeShift ``Submission.DifferentialGeometry.PDE.RicciFlow.InitialConnectionDifferenceBound.timeShift

end DifferentialGeometry.PDE.RicciFlow

end

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

theorem exists_connection_difference_sqrt_bound_of_complete_bounded_curvature
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) {a b K : ℝ} (hab : a < b)
    (hcarrier : _root_.Set.Icc a b ⊆ D.carrier)
    (hregular : _root_.Set.Ioc a b ⊆ D.regular)
    (hcomplete : RiemannianMetricComplete (I := I) (S.base.metric a))
    (hK : 0 ≤ K)
    (hcurv : ∀ t ∈ _root_.Set.Icc a b, ∀ x : M, nablaKRm04NormSqIntrinsic S 0 t x ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ _root_.Set.Ioc a b, ∀ x : M, ∀ u w : TangentSpace I x,
      Real.sqrt ((S.base.metric a).inner x
        (CovariantDerivative.difference
          (LeviCivita (S.base.metric t)) (LeviCivita (S.base.metric a)) x u w)
        (CovariantDerivative.difference
          (LeviCivita (S.base.metric t)) (LeviCivita (S.base.metric a)) x u w)) ≤
        C * Real.sqrt (t - a) *
          Real.sqrt ((S.base.metric a).inner x u u) *
          Real.sqrt ((S.base.metric a).inner x w w) := by
  have hcarrier' : _root_.Set.Icc (0 : ℝ) (b - a) ⊆ (D.timeShift a).carrier := by
    intro s hs
    change s + a ∈ D.carrier
    apply hcarrier
    constructor <;> linarith [hs.1, hs.2]
  have hregular' : _root_.Set.Ioc (0 : ℝ) (b - a) ⊆ (D.timeShift a).regular := by
    intro s hs
    change s + a ∈ D.regular
    apply hregular
    constructor <;> linarith [hs.1, hs.2]
  have hcomplete' : RiemannianMetricComplete (I := I) ((S.timeShift a).base.metric 0) := by
    simpa only [SolutionOn.timeShift_base_metric, zero_add] using hcomplete
  have hcurv' : ∀ s ∈ _root_.Set.Icc (0 : ℝ) (b - a), ∀ x : M,
      nablaKRm04NormSqIntrinsic (S.timeShift a) 0 s x ≤ K := by
    intro s hs x
    change nablaKRm04NormSqIntrinsic S 0 (s + a) x ≤ K
    apply hcurv (s + a) _ x
    constructor <;> linarith [hs.1, hs.2]
  obtain ⟨C, hC, hbound⟩ :=
    exists_initialConnectionDifferenceBound_sqrt_of_complete_bounded_curvature
      (S.timeShift a) (isSolutionOn_timeShift hS a) (sub_pos.mpr hab)
      hcarrier' hregular' hcomplete' hK hcurv'
  refine ⟨C, hC, ?_⟩
  intro t ht x u w
  exact hbound.timeShift (S := S) (a := a) (b := b) t ht x (_root_.Set.mem_univ _) u w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.exists_connection_difference_sqrt_bound_of_complete_bounded_curvature then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.exists_connection_difference_sqrt_bound_of_complete_bounded_curvature"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.exists_connection_difference_sqrt_bound_of_complete_bounded_curvature ``Submission.DifferentialGeometry.PDE.RicciFlow.exists_connection_difference_sqrt_bound_of_complete_bounded_curvature

end DifferentialGeometry.PDE.RicciFlow
