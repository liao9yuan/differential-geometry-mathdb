import Mathlib.Data.ENNReal.Real
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Restriction
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.InitialMetricDerivative

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Manifold _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open scoped _root_.Manifold _root_.ContDiff _root_.Topology _root_.ENNReal
namespace DifferentialGeometry.PDE.RicciFlow

def lifetimeInterval (T : ℝ≥0∞) (hT : 0 < T) : RealTimeInterval :=
  if htop : T = ⊤ then RealTimeInterval.closedInfinite 0
  else RealTimeInterval.closedOpen 0 T.toReal (ENNReal.toReal_pos hT.ne' htop)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.lifetimeInterval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.lifetimeInterval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.lifetimeInterval ``Submission.DifferentialGeometry.PDE.RicciFlow.lifetimeInterval

theorem lifetimeInterval_top :
    lifetimeInterval ⊤ (by simp) = RealTimeInterval.closedInfinite 0 := by
  simp only [lifetimeInterval, dite_true]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.lifetimeInterval_top then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.lifetimeInterval_top"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.lifetimeInterval_top ``Submission.DifferentialGeometry.PDE.RicciFlow.lifetimeInterval_top

theorem lifetimeInterval_ofReal (T : ℝ) (hT : 0 < T) :
    lifetimeInterval (ENNReal.ofReal T) (ENNReal.ofReal_pos.mpr hT) =
      RealTimeInterval.closedOpen 0 T hT := by
  simp only [lifetimeInterval, ENNReal.ofReal_ne_top, dite_false,
    ENNReal.toReal_ofReal hT.le]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.lifetimeInterval_ofReal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.lifetimeInterval_ofReal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.lifetimeInterval_ofReal ``Submission.DifferentialGeometry.PDE.RicciFlow.lifetimeInterval_ofReal

theorem lifetimeInterval_initial (T : ℝ≥0∞) (hT : 0 < T) :
    (lifetimeInterval T hT).initial = 0 := by
  by_cases htop : T = ⊤ <;> simp only [lifetimeInterval, htop, ↓reduceDIte,
    RealTimeInterval.closedInfinite, RealTimeInterval.closedOpen]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.lifetimeInterval_initial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.lifetimeInterval_initial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.lifetimeInterval_initial ``Submission.DifferentialGeometry.PDE.RicciFlow.lifetimeInterval_initial

theorem mem_lifetimeInterval_carrier (T : ℝ≥0∞) (hT : 0 < T) (t : ℝ) :
    t ∈ (lifetimeInterval T hT).carrier ↔ 0 ≤ t ∧ ENNReal.ofReal t < T := by
  by_cases htop : T = ⊤
  · subst T
    simp [lifetimeInterval_top, RealTimeInterval.closedInfinite]
  · simp only [lifetimeInterval, htop, dite_false, RealTimeInterval.closedOpen, _root_.Set.mem_Ico]
    constructor
    · intro ht
      exact ⟨ht.1, (ENNReal.ofReal_lt_iff_lt_toReal ht.1 htop).mpr ht.2⟩
    · intro ht
      exact ⟨ht.1, (ENNReal.ofReal_lt_iff_lt_toReal ht.1 htop).mp ht.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.mem_lifetimeInterval_carrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.mem_lifetimeInterval_carrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.mem_lifetimeInterval_carrier ``Submission.DifferentialGeometry.PDE.RicciFlow.mem_lifetimeInterval_carrier

theorem mem_lifetimeInterval_regular (T : ℝ≥0∞) (hT : 0 < T) (t : ℝ) :
    t ∈ (lifetimeInterval T hT).regular ↔ 0 < t ∧ ENNReal.ofReal t < T := by
  by_cases htop : T = ⊤
  · subst T
    simp [lifetimeInterval_top, RealTimeInterval.closedInfinite]
  · simp only [lifetimeInterval, htop, dite_false, RealTimeInterval.closedOpen, _root_.Set.mem_Ioo]
    constructor
    · intro ht
      exact ⟨ht.1, (ENNReal.ofReal_lt_iff_lt_toReal ht.1.le htop).mpr ht.2⟩
    · intro ht
      exact ⟨ht.1, (ENNReal.ofReal_lt_iff_lt_toReal ht.1.le htop).mp ht.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.mem_lifetimeInterval_regular then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.mem_lifetimeInterval_regular"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.mem_lifetimeInterval_regular ``Submission.DifferentialGeometry.PDE.RicciFlow.mem_lifetimeInterval_regular

theorem lifetimeInterval_carrier_mono {T T' : ℝ≥0∞} (hT : 0 < T) (hT' : 0 < T')
    (h : T ≤ T') : (lifetimeInterval T hT).carrier ⊆ (lifetimeInterval T' hT').carrier := by
  intro t ht
  rw [mem_lifetimeInterval_carrier] at ht ⊢
  exact ⟨ht.1, ht.2.trans_le h⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.lifetimeInterval_carrier_mono then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.lifetimeInterval_carrier_mono"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.lifetimeInterval_carrier_mono ``Submission.DifferentialGeometry.PDE.RicciFlow.lifetimeInterval_carrier_mono

theorem lifetimeInterval_regular_mono {T T' : ℝ≥0∞} (hT : 0 < T) (hT' : 0 < T')
    (h : T ≤ T') : (lifetimeInterval T hT).regular ⊆ (lifetimeInterval T' hT').regular := by
  intro t ht
  rw [mem_lifetimeInterval_regular] at ht ⊢
  exact ⟨ht.1, ht.2.trans_le h⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.lifetimeInterval_regular_mono then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.lifetimeInterval_regular_mono"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.lifetimeInterval_regular_mono ``Submission.DifferentialGeometry.PDE.RicciFlow.lifetimeInterval_regular_mono

theorem Icc_subset_lifetimeInterval_iff (T : ℝ≥0∞) (hT : 0 < T)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    Icc 0 θ ⊆ (lifetimeInterval T hT).carrier ↔ ENNReal.ofReal θ < T := by
  constructor
  · intro h
    exact ((mem_lifetimeInterval_carrier T hT θ).mp (h ⟨hθ, le_rfl⟩)).2
  · intro h t ht
    exact (mem_lifetimeInterval_carrier T hT t).mpr
      ⟨ht.1, (ENNReal.ofReal_le_ofReal ht.2).trans_lt h⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Icc_subset_lifetimeInterval_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Icc_subset_lifetimeInterval_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Icc_subset_lifetimeInterval_iff ``Submission.DifferentialGeometry.PDE.RicciFlow.Icc_subset_lifetimeInterval_iff

theorem exists_finite_lifetime_window (T : ℝ≥0∞) (hT : 0 < T) :
    ∃ b : ℝ, 0 < b ∧ ENNReal.ofReal b < T := by
  obtain ⟨b, _, hb, hbT⟩ := ENNReal.lt_iff_exists_real_btwn.mp hT
  exact ⟨b, ENNReal.ofReal_pos.mp hb, hbT⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.exists_finite_lifetime_window then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.exists_finite_lifetime_window"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.exists_finite_lifetime_window ``Submission.DifferentialGeometry.PDE.RicciFlow.exists_finite_lifetime_window

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [CompleteSpace E]

theorem isSolutionOn_lifetime_restrict {T T' : ℝ≥0∞} (hT : 0 < T) (hT' : 0 < T')
    (h : T ≤ T') (S : SolutionOn (I := I) (M := M) (lifetimeInterval T' hT'))
    (hS : IsSolutionOn S) :
    IsSolutionOn (S.timeRestrict (lifetimeInterval T hT)) ∧
      (S.timeRestrict (lifetimeInterval T hT)).base.metric = S.base.metric := by
  exact ⟨isSolutionOn_timeRestrict hS (lifetimeInterval_carrier_mono hT hT' h)
    (lifetimeInterval_regular_mono hT hT' h), rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.isSolutionOn_lifetime_restrict then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.isSolutionOn_lifetime_restrict"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.isSolutionOn_lifetime_restrict ``Submission.DifferentialGeometry.PDE.RicciFlow.isSolutionOn_lifetime_restrict

variable [BoundarylessManifold I M]

theorem initial_metric_derivative_lifetime (T : ℝ≥0∞) (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (lifetimeInterval T hT)) (hS : IsSolutionOn S)
    (x : M) (v w : TangentSpace I x) :
    HasDerivWithinAt (fun t => (S.base.metric t).inner x v w)
      (-2 * ricciTensor (S.base.metric 0) x v w) (_root_.Set.Ici 0) 0 := by
  obtain ⟨b, hb, hbT⟩ := exists_finite_lifetime_window T hT
  have hcar : _root_.Set.Ico 0 b ⊆ (lifetimeInterval T hT).carrier := by
    intro t ht
    exact (mem_lifetimeInterval_carrier T hT t).mpr
      ⟨ht.1, (ENNReal.ofReal_le_ofReal ht.2.le).trans_lt hbT⟩
  have hreg : _root_.Set.Ioo 0 b ⊆ (lifetimeInterval T hT).regular := by
    intro t ht
    exact (mem_lifetimeInterval_regular T hT t).mpr
      ⟨ht.1, (ENNReal.ofReal_le_ofReal ht.2.le).trans_lt hbT⟩
  exact initial_metric_derivative hb (S.timeRestrict (RealTimeInterval.closedOpen 0 b hb))
    (isSolutionOn_timeRestrict hS hcar hreg) x v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.initial_metric_derivative_lifetime then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.initial_metric_derivative_lifetime"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.initial_metric_derivative_lifetime ``Submission.DifferentialGeometry.PDE.RicciFlow.initial_metric_derivative_lifetime
end DifferentialGeometry.PDE.RicciFlow
