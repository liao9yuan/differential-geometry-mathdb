import Submission.DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Continuity
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Arity
import Mathlib.Data.ENNReal.Real

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold _root_.ContDiff _root_.ENNReal
namespace DifferentialGeometry.Geometry.Metric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

def metricDerivENormSupOn (K : Set M) (p : ℕ)
    (gk gInf gRef : SmoothRiemannianMetric I M) : ℝ≥0∞ :=
  ⨆ (j : ℕ) (_ : j ≤ p) (x : M) (_ : x ∈ K),
    ENNReal.ofReal (metricDerivNorm j gk gInf gRef x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.metricDerivENormSupOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.metricDerivENormSupOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.metricDerivENormSupOn ``Submission.DifferentialGeometry.Geometry.Metric.metricDerivENormSupOn

theorem ofReal_metricDerivNorm_le_sup (K : Set M) (p : ℕ)
    (gk gInf gRef : SmoothRiemannianMetric I M) {j : ℕ} (hj : j ≤ p)
    {x : M} (hx : x ∈ K) :
    ENNReal.ofReal (metricDerivNorm j gk gInf gRef x) ≤
      metricDerivENormSupOn K p gk gInf gRef :=
  le_iSup_of_le j (le_iSup_of_le hj (le_iSup_of_le x (le_iSup_of_le hx le_rfl)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.ofReal_metricDerivNorm_le_sup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.ofReal_metricDerivNorm_le_sup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.ofReal_metricDerivNorm_le_sup ``Submission.DifferentialGeometry.Geometry.Metric.ofReal_metricDerivNorm_le_sup

theorem metricDerivENormSupOn_le_iff (K : Set M) (p : ℕ)
    (gk gInf gRef : SmoothRiemannianMetric I M) (C : ℝ≥0∞) :
    metricDerivENormSupOn K p gk gInf gRef ≤ C ↔
      ∀ j ≤ p, ∀ x ∈ K, ENNReal.ofReal (metricDerivNorm j gk gInf gRef x) ≤ C := by
  simp only [metricDerivENormSupOn, iSup_le_iff]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.metricDerivENormSupOn_le_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.metricDerivENormSupOn_le_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.metricDerivENormSupOn_le_iff ``Submission.DifferentialGeometry.Geometry.Metric.metricDerivENormSupOn_le_iff

theorem metricDerivNorm_lt_of_sup_lt (K : Set M) (p : ℕ)
    (gk gInf gRef : SmoothRiemannianMetric I M) {ε : ℝ}
    (hsmall : metricDerivENormSupOn K p gk gInf gRef < ENNReal.ofReal ε)
    {j : ℕ} (hj : j ≤ p) {x : M} (hx : x ∈ K) :
    metricDerivNorm j gk gInf gRef x < ε := by
  have h := (ofReal_metricDerivNorm_le_sup K p gk gInf gRef hj hx).trans_lt hsmall
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (Real.sqrt_nonneg _)).mp h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.metricDerivNorm_lt_of_sup_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.metricDerivNorm_lt_of_sup_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.metricDerivNorm_lt_of_sup_lt ``Submission.DifferentialGeometry.Geometry.Metric.metricDerivNorm_lt_of_sup_lt

theorem metricDerivENormSupOn_mono {K L : Set M} (hKL : K ⊆ L)
    {p q : ℕ} (hpq : p ≤ q) (gk gInf gRef : SmoothRiemannianMetric I M) :
    metricDerivENormSupOn K p gk gInf gRef ≤ metricDerivENormSupOn L q gk gInf gRef := by
  apply (metricDerivENormSupOn_le_iff _ _ _ _ _ _).mpr
  intro j hj x hx
  exact ofReal_metricDerivNorm_le_sup L q gk gInf gRef (hj.trans hpq) (hKL hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.metricDerivENormSupOn_mono then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.metricDerivENormSupOn_mono"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.metricDerivENormSupOn_mono ``Submission.DifferentialGeometry.Geometry.Metric.metricDerivENormSupOn_mono

@[simp] theorem metricDerivENormSupOn_empty (p : ℕ)
    (gk gInf gRef : SmoothRiemannianMetric I M) :
    metricDerivENormSupOn ∅ p gk gInf gRef = 0 := by
  simp [metricDerivENormSupOn]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.metricDerivENormSupOn_empty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.metricDerivENormSupOn_empty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.metricDerivENormSupOn_empty ``Submission.DifferentialGeometry.Geometry.Metric.metricDerivENormSupOn_empty

@[simp] theorem metricDerivENormSupOn_self (K : Set M) (p : ℕ)
    (g gRef : SmoothRiemannianMetric I M) :
    metricDerivENormSupOn K p g g gRef = 0 := by
  simp [metricDerivENormSupOn, metricDerivNorm_self]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.metricDerivENormSupOn_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.metricDerivENormSupOn_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.metricDerivENormSupOn_self ``Submission.DifferentialGeometry.Geometry.Metric.metricDerivENormSupOn_self

theorem metricDerivENormSupOn_eq_ofReal_of_bddAbove (K : Set M) (p : ℕ)
    (gk gInf gRef : SmoothRiemannianMetric I M)
    (hbounded : BddAbove {r : ℝ | ∃ j : ℕ, j ≤ p ∧ ∃ x : M, x ∈ K ∧
      metricDerivNorm j gk gInf gRef x = r}) :
    metricDerivENormSupOn K p gk gInf gRef =
      ENNReal.ofReal (metricDerivNormSupOn K p gk gInf gRef) := by
  classical
  rcases K.eq_empty_or_nonempty with rfl | hK
  · simp [metricDerivNormSupOn]
  let S := {r : ℝ | ∃ j : ℕ, j ≤ p ∧ ∃ x : M, x ∈ K ∧
    metricDerivNorm j gk gInf gRef x = r}
  have hS : S.Nonempty := by
    obtain ⟨x, hx⟩ := hK
    exact ⟨_, 0, Nat.zero_le p, x, hx, rfl⟩
  have hle : metricDerivENormSupOn K p gk gInf gRef ≤
      ENNReal.ofReal (metricDerivNormSupOn K p gk gInf gRef) := by
    apply (metricDerivENormSupOn_le_iff _ _ _ _ _ _).mpr
    intro j hj x hx
    exact ENNReal.ofReal_le_ofReal (le_csSup hbounded ⟨j, hj, x, hx, rfl⟩)
  have hfinite : metricDerivENormSupOn K p gk gInf gRef ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  apply le_antisymm hle
  apply (ENNReal.ofReal_le_iff_le_toReal hfinite).mpr
  apply csSup_le hS
  rintro r ⟨j, hj, x, hx, rfl⟩
  exact (ENNReal.ofReal_le_iff_le_toReal hfinite).mp
    (ofReal_metricDerivNorm_le_sup K p gk gInf gRef hj hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.metricDerivENormSupOn_eq_ofReal_of_bddAbove then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.metricDerivENormSupOn_eq_ofReal_of_bddAbove"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.metricDerivENormSupOn_eq_ofReal_of_bddAbove ``Submission.DifferentialGeometry.Geometry.Metric.metricDerivENormSupOn_eq_ofReal_of_bddAbove

theorem metricDerivENormSupOn_eq_ofReal_of_isCompact {K : Set M} (hK : IsCompact K)
    (p : ℕ) (gk gInf gRef : SmoothRiemannianMetric I M) :
    metricDerivENormSupOn K p gk gInf gRef =
      ENNReal.ofReal (metricDerivNormSupOn K p gk gInf gRef) := by
  obtain ⟨C, _, hC⟩ := metricDerivNorm_bddOn hK p gk gInf gRef
  apply metricDerivENormSupOn_eq_ofReal_of_bddAbove
  refine ⟨C, ?_⟩
  rintro r ⟨j, hj, x, hx, rfl⟩
  exact hC j hj x hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.metricDerivENormSupOn_eq_ofReal_of_isCompact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.metricDerivENormSupOn_eq_ofReal_of_isCompact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.metricDerivENormSupOn_eq_ofReal_of_isCompact ``Submission.DifferentialGeometry.Geometry.Metric.metricDerivENormSupOn_eq_ofReal_of_isCompact

end DifferentialGeometry.Geometry.Metric
