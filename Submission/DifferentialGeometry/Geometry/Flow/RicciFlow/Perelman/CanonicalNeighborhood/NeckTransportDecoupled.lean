import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BackgroundJetTransfer

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

universe u


section Threshold

variable (E' : Type*) [NormedAddCommGroup E'] [NormedSpace ℝ E']


theorem two_mul_sq_le_three_halves_pow {n : ℕ} (hn : 16 ≤ n) :
    2 * (n : ℝ) ^ 2 ≤ (3 / 2 : ℝ) ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hn0 : (16 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hstep : 2 * ((n : ℝ) + 1) ^ 2 ≤ 3 / 2 * (2 * (n : ℝ) ^ 2) := by nlinarith
    have hmul : 3 / 2 * (2 * (n : ℝ) ^ 2) ≤ 3 / 2 * (3 / 2 : ℝ) ^ n :=
      mul_le_mul_of_nonneg_left ih (by norm_num)
    have hpow : (3 / 2 : ℝ) ^ (n + 1) = 3 / 2 * (3 / 2 : ℝ) ^ n := by ring
    push_cast
    rw [hpow]
    linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.two_mul_sq_le_three_halves_pow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.two_mul_sq_le_three_halves_pow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.two_mul_sq_le_three_halves_pow ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.two_mul_sq_le_three_halves_pow


theorem sqrt_add_two_le_backgroundJetBudget (order : ℕ) :
    Real.sqrt ((3 / 2 : ℝ) ^ (2 + order)) + 2 ≤ backgroundJetBudget E' order := by
  have hCc : (0 : ℝ) ≤ metricCovariantDerivativeComparisonConstant (E := E') 2 order :=
    metric_covariant_derivative_comparison_constant_nonneg (E := E') 2 order
  have hord : (0 : ℝ) ≤ (order : ℝ) := Nat.cast_nonneg order
  have hs : (0 : ℝ) ≤ Real.sqrt ((3 / 2 : ℝ) ^ (2 + order)) := Real.sqrt_nonneg _
  have heq : backgroundJetBudget E' order =
      Real.sqrt ((3 / 2 : ℝ) ^ (2 + order)) *
        (1 + metricCovariantDerivativeComparisonConstant (E := E') 2 order * (order : ℝ)) + 2 :=
    rfl
  rw [heq]
  nlinarith [mul_nonneg (mul_nonneg hs hCc) hord]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.sqrt_add_two_le_backgroundJetBudget then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.sqrt_add_two_le_backgroundJetBudget"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.sqrt_add_two_le_backgroundJetBudget ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.sqrt_add_two_le_backgroundJetBudget


theorem backgroundJetSmallness_le_inv_sqrt (order : ℕ) :
    backgroundJetSmallness E' order ≤ (Real.sqrt ((3 / 2 : ℝ) ^ (2 + order)))⁻¹ := by
  have hpos : (0 : ℝ) < Real.sqrt ((3 / 2 : ℝ) ^ (2 + order)) :=
    Real.sqrt_pos.mpr (by positivity)
  refine le_trans (backgroundJetSmallness_le_inv E' order) (inv_anti₀ hpos ?_)
  have h := sqrt_add_two_le_backgroundJetBudget E' order
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.backgroundJetSmallness_le_inv_sqrt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.backgroundJetSmallness_le_inv_sqrt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.backgroundJetSmallness_le_inv_sqrt ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.backgroundJetSmallness_le_inv_sqrt


theorem backgroundJetSmallness_lt_of_inv_le {alpha : ℝ} (halpha : 0 < alpha) {n : ℕ}
    (h16 : 16 ≤ n) (hn : (2 * alpha)⁻¹ ≤ (n : ℝ)) :
    backgroundJetSmallness E' n < alpha := by
  have h2 : (0 : ℝ) < 2 * alpha := by linarith
  have hone : (1 : ℝ) ≤ 2 * alpha * (n : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hn h2.le
    rwa [mul_inv_cancel₀ h2.ne'] at h
  have hpow : 2 * (n : ℝ) ^ 2 ≤ (3 / 2 : ℝ) ^ n := two_mul_sq_le_three_halves_pow h16
  have hn0 : (0 : ℝ) ≤ 2 * (n : ℝ) := by positivity
  have hsq : (2 * (n : ℝ)) ^ 2 ≤ (3 / 2 : ℝ) ^ (2 + n) := by
    have hexp : (3 / 2 : ℝ) ^ (2 + n) = 9 / 4 * (3 / 2 : ℝ) ^ n := by
      rw [pow_add]; norm_num
    rw [hexp]
    nlinarith [sq_nonneg ((n : ℝ))]
  have hsqrt : 2 * (n : ℝ) ≤ Real.sqrt ((3 / 2 : ℝ) ^ (2 + n)) := by
    calc 2 * (n : ℝ) = Real.sqrt ((2 * (n : ℝ)) ^ 2) := (Real.sqrt_sq hn0).symm
      _ ≤ Real.sqrt ((3 / 2 : ℝ) ^ (2 + n)) := Real.sqrt_le_sqrt hsq
  have hb : 2 * (n : ℝ) + 2 ≤ backgroundJetBudget E' n := by
    have h := sqrt_add_two_le_backgroundJetBudget E' n
    linarith
  have hbudpos : 0 < backgroundJetBudget E' n := backgroundJetBudget_pos E' n
  have hprod : alpha * (2 * (n : ℝ) + 2) ≤ alpha * backgroundJetBudget E' n :=
    mul_le_mul_of_nonneg_left hb halpha.le
  have hmul : 1 < alpha * backgroundJetBudget E' n := by nlinarith [hone, hprod, halpha]
  have hfin : (backgroundJetBudget E' n)⁻¹ < alpha := by
    have h3 := mul_lt_mul_of_pos_left hmul (inv_pos.mpr hbudpos)
    rw [mul_one] at h3
    have hassoc : (backgroundJetBudget E' n)⁻¹ * (alpha * backgroundJetBudget E' n)
        = ((backgroundJetBudget E' n)⁻¹ * backgroundJetBudget E' n) * alpha := by ring
    have heq : (backgroundJetBudget E' n)⁻¹ * (alpha * backgroundJetBudget E' n) = alpha := by
      rw [hassoc, inv_mul_cancel₀ hbudpos.ne', one_mul]
    rw [heq] at h3
    exact h3
  exact lt_of_le_of_lt (backgroundJetSmallness_le_inv E' n) hfin

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.backgroundJetSmallness_lt_of_inv_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.backgroundJetSmallness_lt_of_inv_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.backgroundJetSmallness_lt_of_inv_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.backgroundJetSmallness_lt_of_inv_le


theorem backgroundJetSmallness_ceil_lt_self {alpha : ℝ} (halpha : 0 < alpha)
    (hsmall : alpha < 1 / 32) :
    backgroundJetSmallness E' ⌈(2 * alpha)⁻¹⌉₊ < alpha := by
  have h2 : (0 : ℝ) < 2 * alpha := by linarith
  have h16 : (16 : ℝ) ≤ (2 * alpha)⁻¹ := by
    have hle : 2 * alpha ≤ 1 / 16 := by linarith
    have hinv : ((1 : ℝ) / 16)⁻¹ = 16 := by norm_num
    have h := inv_anti₀ h2 hle
    rw [hinv] at h
    exact h
  refine backgroundJetSmallness_lt_of_inv_le E' halpha ?_ (Nat.le_ceil _)
  have hcast : (16 : ℝ) ≤ ((⌈(2 * alpha)⁻¹⌉₊ : ℕ) : ℝ) := le_trans h16 (Nat.le_ceil _)
  exact_mod_cast hcast

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.backgroundJetSmallness_ceil_lt_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.backgroundJetSmallness_ceil_lt_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.backgroundJetSmallness_ceil_lt_self ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.backgroundJetSmallness_ceil_lt_self


theorem not_le_backgroundJetSmallness_ceil {alpha : ℝ} (halpha : 0 < alpha)
    (hsmall : alpha < 1 / 32) :
    ¬ alpha ≤ backgroundJetSmallness E' ⌈(2 * alpha)⁻¹⌉₊ :=
  not_le.mpr (backgroundJetSmallness_ceil_lt_self E' halpha hsmall)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.not_le_backgroundJetSmallness_ceil then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.not_le_backgroundJetSmallness_ceil"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.not_le_backgroundJetSmallness_ceil ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.not_le_backgroundJetSmallness_ceil

end Threshold


section Tolerances


def neckModelTolerance (alpha : ℝ) : ℝ :=
  _root_.Min.min alpha (backgroundJetSmallness (EuclideanSpace ℝ (Fin 2) × ℝ) ⌈(2 * alpha)⁻¹⌉₊)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neckModelTolerance then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neckModelTolerance"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neckModelTolerance ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neckModelTolerance


def neckSourceTolerance (alpha : ℝ) : ℝ :=
  alpha / (backgroundJetConstant (EuclideanSpace ℝ (Fin 2) × ℝ) ⌈(2 * alpha)⁻¹⌉₊ *
    ((⌈(2 * alpha)⁻¹⌉₊ : ℝ) + 1))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neckSourceTolerance then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neckSourceTolerance"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neckSourceTolerance ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neckSourceTolerance

theorem neckModelTolerance_pos {alpha : ℝ} (ha : 0 < alpha) : 0 < neckModelTolerance alpha :=
  lt_min ha (backgroundJetSmallness_pos _ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neckModelTolerance_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neckModelTolerance_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neckModelTolerance_pos ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neckModelTolerance_pos

theorem neckModelTolerance_le (alpha : ℝ) : neckModelTolerance alpha ≤ alpha :=
  min_le_left _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neckModelTolerance_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neckModelTolerance_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neckModelTolerance_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neckModelTolerance_le

theorem neckModelTolerance_le_smallness (alpha : ℝ) :
    neckModelTolerance alpha ≤
      backgroundJetSmallness (EuclideanSpace ℝ (Fin 2) × ℝ) ⌈(2 * alpha)⁻¹⌉₊ :=
  min_le_right _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neckModelTolerance_le_smallness then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neckModelTolerance_le_smallness"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neckModelTolerance_le_smallness ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neckModelTolerance_le_smallness

theorem neckSourceTolerance_pos {alpha : ℝ} (ha : 0 < alpha) : 0 < neckSourceTolerance alpha := by
  have hK : 0 < backgroundJetConstant (EuclideanSpace ℝ (Fin 2) × ℝ) ⌈(2 * alpha)⁻¹⌉₊ :=
    backgroundJetConstant_pos _ _
  have hfac : 0 < backgroundJetConstant (EuclideanSpace ℝ (Fin 2) × ℝ) ⌈(2 * alpha)⁻¹⌉₊ *
      ((⌈(2 * alpha)⁻¹⌉₊ : ℝ) + 1) := by positivity
  exact div_pos ha hfac

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neckSourceTolerance_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neckSourceTolerance_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neckSourceTolerance_pos ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neckSourceTolerance_pos


theorem backgroundJetConstant_mul_le_of_le_neckSourceTolerance {alpha eps : ℝ} (ha : 0 < alpha)
    (heps : eps ≤ neckSourceTolerance alpha) :
    backgroundJetConstant (EuclideanSpace ℝ (Fin 2) × ℝ) ⌈(2 * alpha)⁻¹⌉₊ *
      ((⌈(2 * alpha)⁻¹⌉₊ : ℝ) + 1) * eps ≤ alpha := by
  have hK : 0 < backgroundJetConstant (EuclideanSpace ℝ (Fin 2) × ℝ) ⌈(2 * alpha)⁻¹⌉₊ :=
    backgroundJetConstant_pos _ _
  have hfac : 0 < backgroundJetConstant (EuclideanSpace ℝ (Fin 2) × ℝ) ⌈(2 * alpha)⁻¹⌉₊ *
      ((⌈(2 * alpha)⁻¹⌉₊ : ℝ) + 1) := by positivity
  have hmono := mul_le_mul_of_nonneg_left heps hfac.le
  have heq : backgroundJetConstant (EuclideanSpace ℝ (Fin 2) × ℝ) ⌈(2 * alpha)⁻¹⌉₊ *
      ((⌈(2 * alpha)⁻¹⌉₊ : ℝ) + 1) * neckSourceTolerance alpha = alpha := by
    rw [neckSourceTolerance, mul_div_cancel₀ _ hfac.ne']
  rw [heq] at hmono
  exact hmono

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.backgroundJetConstant_mul_le_of_le_neckSourceTolerance then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.backgroundJetConstant_mul_le_of_le_neckSourceTolerance"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.backgroundJetConstant_mul_le_of_le_neckSourceTolerance ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.backgroundJetConstant_mul_le_of_le_neckSourceTolerance


theorem exists_model_tolerance (alpha : ℝ) (ha : 0 < alpha) (hsmall : 2 * alpha < 1 / 11) :
    ∃ beta : ℝ, 0 < beta ∧ beta ≤ alpha ∧ beta < 1 / 11 ∧
      beta ≤ backgroundJetSmallness (EuclideanSpace ℝ (Fin 2) × ℝ) ⌈(2 * alpha)⁻¹⌉₊ :=
  ⟨neckModelTolerance alpha, neckModelTolerance_pos ha, neckModelTolerance_le alpha,
    lt_of_le_of_lt (neckModelTolerance_le alpha) (by linarith),
    neckModelTolerance_le_smallness alpha⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_model_tolerance then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_model_tolerance"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_model_tolerance ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_model_tolerance


theorem exists_source_tolerance (alpha : ℝ) (ha : 0 < alpha) :
    ∃ eps₀ : ℝ, 0 < eps₀ ∧ ∀ eps, 0 ≤ eps → eps ≤ eps₀ →
      backgroundJetConstant (EuclideanSpace ℝ (Fin 2) × ℝ) ⌈(2 * alpha)⁻¹⌉₊ *
        ((⌈(2 * alpha)⁻¹⌉₊ : ℝ) + 1) * eps ≤ alpha :=
  ⟨neckSourceTolerance alpha, neckSourceTolerance_pos ha,
    fun _ _ heps => backgroundJetConstant_mul_le_of_le_neckSourceTolerance ha heps⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_source_tolerance then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_source_tolerance"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_source_tolerance ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_source_tolerance

end Tolerances


def StrongNeck.mono {D : RealTimeInterval} {M : Type u} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    {S : SolutionOn (I := I3) (M := M) D} {eps eps' : ℝ} {x : M} {t : ℝ}
    (neck : StrongNeck S eps x t) (heps : eps ≤ eps') (hsmall : eps' < 1 / 11) :
    StrongNeck S eps' x t where
  eps_pos := lt_of_lt_of_le neck.eps_pos heps
  eps_small := hsmall
  Q_pos := neck.Q_pos
  cylinder := neck.cylinder
  map := neck.map
  center := neck.center
  center_eq := neck.center_eq
  domain := by
    have hle : eps'⁻¹ ≤ eps⁻¹ := inv_anti₀ neck.eps_pos heps
    exact fun y hy => neck.domain (Set.prod_mono (subset_refl _)
      (Set.Ioo_subset_Ioo (neg_le_neg hle) hle) hy)
  time_domain := neck.time_domain
  comparison := by
    have hle : eps'⁻¹ ≤ eps⁻¹ := inv_anti₀ neck.eps_pos heps
    exact neck.comparison.mono (Set.prod_mono (subset_refl _)
      (Set.Ioo_subset_Ioo (neg_le_neg hle) hle)) (Nat.ceil_mono hle) heps

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.mono then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.mono"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.mono ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.mono


theorem neck_window_subset_of_le {alpha beta : ℝ} (hbeta : 0 < beta) (hle : beta ≤ alpha) :
    (Set.univ ×ˢ Set.Ioo (-(2 * alpha)⁻¹) (2 * alpha)⁻¹ : Set Cylinder) ⊆
      Set.univ ×ˢ Set.Ioo (-beta⁻¹) beta⁻¹ := by
  have hinv : (2 * alpha)⁻¹ ≤ beta⁻¹ := inv_anti₀ hbeta (by linarith)
  exact Set.prod_mono (subset_refl _) (Set.Ioo_subset_Ioo (by linarith) hinv)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neck_window_subset_of_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neck_window_subset_of_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neck_window_subset_of_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neck_window_subset_of_le


section NeckTransport

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
  [T2Space M] [SigmaCompactSpace M]
  {P : Type u} [TopologicalSpace P] [ChartedSpace ThreeSpace P] [IsManifold I3 ∞ P]
  [T2Space P] [SigmaCompactSpace P]


def StrongNeck.transport' {Dm : RealTimeInterval} {Sm : SolutionOn (I := I3) (M := P) Dm}
    {p : P} {t₀ : ℝ} {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D} {x : M}
    {t : ℝ} {alpha beta eps K : ℝ} {V : Set P} {times' : Set ℝ} {order' : ℕ}
    (nk : StrongNeck Sm beta p t₀) (hQ : 0 < S.scalar t x)
    (Fmap : PartialDiffeomorph I3 I3 P M ∞)
    (cmp : MetricComparisonOn (rescaledMetric Sm t₀ (Sm.scalar t₀ p) nk.Q_pos)
      (rescaledMetric S t (S.scalar t x) hQ) Fmap V times' order' eps)
    (T : TransportedErrorTower cmp nk.cylinder.metric nk.map
      (Set.univ ×ˢ Set.Ioo (-(2 * alpha)⁻¹) (2 * alpha)⁻¹) (Set.Icc (-1) 0)
      ⌈(2 * alpha)⁻¹⌉₊ K)
    (hsmall : 2 * alpha < 1 / 11) (hbeta_le : beta ≤ alpha) (hKeps : K * eps ≤ alpha)
    (hbase : Fmap p = x)
    (hcore : ∀ y ∈ Set.univ ×ˢ Set.Ioo (-(2 * alpha)⁻¹) (2 * alpha)⁻¹, nk.map y ∈ V)
    (hVsource : V ⊆ Fmap.source)
    (htime : Set.Icc (t - (S.scalar t x)⁻¹) t ⊆ D.carrier)
    (hjet : ∀ b s, s ∈ Set.Icc (-1 : ℝ) 0 → UniqueDiffWithinAt ℝ (Set.Icc (-1 : ℝ) 0) s →
      ∀ y ∈ Set.univ ×ˢ Set.Ioo (-(2 * alpha)⁻¹) (2 * alpha)⁻¹,
        ∀ v : Fin 2 → TangentSpace IC y,
          DifferentiableWithinAt ℝ (fun a => nk.comparison.jet b a y v)
            (Set.Icc (-1 : ℝ) 0) s) :
    StrongNeck S (2 * alpha) x t where
  eps_pos := by have := nk.eps_pos; linarith
  eps_small := hsmall
  Q_pos := hQ
  cylinder := nk.cylinder
  map := partialDiffeomorphTransMixed nk.map Fmap
  center := nk.center
  center_eq := by
    change Fmap (nk.map (nk.center, 0)) = x
    rw [nk.center_eq, hbase]
  domain := by
    intro y hy
    refine Set.mem_inter (nk.domain (neck_window_subset_of_le nk.eps_pos hbeta_le hy)) ?_
    exact hVsource (hcore y hy)
  time_domain := htime
  comparison := by
    have hb : (0 : ℝ) < beta := nk.eps_pos
    have hsub := neck_window_subset_of_le (alpha := alpha) hb hbeta_le
    have horder : ⌈(2 * alpha)⁻¹⌉₊ ≤ ⌈beta⁻¹⌉₊ :=
      Nat.ceil_mono (inv_anti₀ hb (by linarith))
    have hmapdiff : ∀ y ∈ Set.univ ×ˢ Set.Ioo (-(2 * alpha)⁻¹) (2 * alpha)⁻¹,
        MDifferentiableAt IC I3 (nk.map : Cylinder → P) y := fun y hy =>
      nk.map.mdifferentiableAt (by simp) (nk.domain (hsub hy))
    exact ((nk.comparison.mono hsub horder le_rfl).trans cmp T hcore hmapdiff
      (fun y hy => Fmap.mdifferentiableAt (by simp) (hVsource (hcore y hy))) hjet).mono
      (subset_refl _) le_rfl (by linarith)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.transport' then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.transport'"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.transport' ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.transport'


def SpatialNeck.transport' {gm : SmoothRiemannianMetric I3 P} {p : P}
    {g : SmoothRiemannianMetric I3 M} {x : M} {alpha beta eps K : ℝ} {V : Set P}
    {times' : Set ℝ} {order' : ℕ}
    (nk : SpatialNeck gm beta p) (hQ : 0 < metricScalarAt g x)
    (Fmap : PartialDiffeomorph I3 I3 P M ∞)
    (cmp : MetricComparisonOn (fun _ => DifferentialGeometry.scaleMetric (metricScalarAt gm p) nk.Q_pos gm)
      (fun _ => DifferentialGeometry.scaleMetric (metricScalarAt g x) hQ g) Fmap V times' order' eps)
    (T : TransportedErrorTower cmp (fun _ => nk.cylinder.metric 0) nk.map
      (Set.univ ×ˢ Set.Ioo (-(2 * alpha)⁻¹) (2 * alpha)⁻¹) {0} ⌈(2 * alpha)⁻¹⌉₊ K)
    (hsmall : 2 * alpha < 1 / 11) (hbeta_le : beta ≤ alpha) (hKeps : K * eps ≤ alpha)
    (hbase : Fmap p = x)
    (hcore : ∀ y ∈ Set.univ ×ˢ Set.Ioo (-(2 * alpha)⁻¹) (2 * alpha)⁻¹, nk.map y ∈ V)
    (hVsource : V ⊆ Fmap.source) :
    SpatialNeck g (2 * alpha) x where
  eps_pos := by have := nk.eps_pos; linarith
  eps_small := hsmall
  Q_pos := hQ
  cylinder := nk.cylinder
  map := partialDiffeomorphTransMixed nk.map Fmap
  center := nk.center
  center_eq := by
    change Fmap (nk.map (nk.center, 0)) = x
    rw [nk.center_eq, hbase]
  domain := by
    intro y hy
    refine Set.mem_inter (nk.domain (neck_window_subset_of_le nk.eps_pos hbeta_le hy)) ?_
    exact hVsource (hcore y hy)
  comparison := by
    have hb : (0 : ℝ) < beta := nk.eps_pos
    have hsub := neck_window_subset_of_le (alpha := alpha) hb hbeta_le
    have horder : ⌈(2 * alpha)⁻¹⌉₊ ≤ ⌈beta⁻¹⌉₊ :=
      Nat.ceil_mono (inv_anti₀ hb (by linarith))
    have hmapdiff : ∀ y ∈ Set.univ ×ˢ Set.Ioo (-(2 * alpha)⁻¹) (2 * alpha)⁻¹,
        MDifferentiableAt IC I3 (nk.map : Cylinder → P) y := fun y hy =>
      nk.map.mdifferentiableAt (by simp) (nk.domain (hsub hy))
    exact ((nk.comparison.mono hsub horder le_rfl).trans cmp T hcore hmapdiff
      (fun y hy => Fmap.mdifferentiableAt (by simp) (hVsource (hcore y hy)))
      (fun _ _ _ _ _ _ _ => DifferentiableWithinAt.singleton)).mono
      (subset_refl _) le_rfl (by linarith)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.transport' then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.transport'"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.transport' ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.transport'


def StrongNeck.transportOfComparisons' {Dm : RealTimeInterval}
    {Sm : SolutionOn (I := I3) (M := P) Dm} {p : P} {D : RealTimeInterval}
    {S : SolutionOn (I := I3) (M := M) D} {x : M} {t : ℝ} {alpha beta eps : ℝ} {V : Set P}
    {order' : ℕ}
    (nk : StrongNeck Sm beta p 0) (hQ : 0 < S.scalar t x)
    (Fmap : PartialDiffeomorph I3 I3 P M ∞)
    (cmp : MetricComparisonOn (rescaledMetric Sm 0 (Sm.scalar 0 p) nk.Q_pos)
      (rescaledMetric S t (S.scalar t x) hQ) Fmap V (Set.Icc (-1) 0) order' eps)
    (Phi : Cylinder ≃ₘ⟮IC, I3⟯ P) (hPhi : ∀ y, Phi y = nk.map y)
    (hsmall : 2 * alpha < 1 / 11) (heps : 0 ≤ eps)
    (hbeta_pos : 0 < beta) (hbeta_le : beta ≤ alpha)
    (hbeta_small : beta ≤
      backgroundJetSmallness (EuclideanSpace ℝ (Fin 2) × ℝ) ⌈(2 * alpha)⁻¹⌉₊)
    (hKeps : backgroundJetConstant (EuclideanSpace ℝ (Fin 2) × ℝ) ⌈(2 * alpha)⁻¹⌉₊ *
      ((⌈(2 * alpha)⁻¹⌉₊ : ℝ) + 1) * eps ≤ alpha)
    (horder : ⌈(2 * alpha)⁻¹⌉₊ ≤ order')
    (hbase : Fmap p = x)
    (hcore : ∀ y ∈ Set.univ ×ˢ Set.Ioo (-(2 * alpha)⁻¹) (2 * alpha)⁻¹, nk.map y ∈ V)
    (hVsource : V ⊆ Fmap.source)
    (htime : Set.Icc (t - (S.scalar t x)⁻¹) t ⊆ D.carrier)
    (hdiff : ∀ b s, s ∈ Set.Icc (-1 : ℝ) 0 → UniqueDiffWithinAt ℝ (Set.Icc (-1 : ℝ) 0) s →
      ∀ y ∈ Set.univ ×ˢ Set.Ioo (-(2 * alpha)⁻¹) (2 * alpha)⁻¹,
        ∀ v : Fin 2 → TangentSpace IC y,
          DifferentiableWithinAt ℝ
            (fun a => cmp.jet b a (Phi y) (fun q => mfderiv IC I3 Phi y (v q)))
            (Set.Icc (-1 : ℝ) 0) s)
    (hjet : ∀ b s, s ∈ Set.Icc (-1 : ℝ) 0 → UniqueDiffWithinAt ℝ (Set.Icc (-1 : ℝ) 0) s →
      ∀ y ∈ Set.univ ×ˢ Set.Ioo (-(2 * alpha)⁻¹) (2 * alpha)⁻¹,
        ∀ v : Fin 2 → TangentSpace IC y,
          DifferentiableWithinAt ℝ (fun a => nk.comparison.jet b a y v)
            (Set.Icc (-1 : ℝ) 0) s) :
    StrongNeck S (2 * alpha) x t := by
  have hsub := neck_window_subset_of_le (alpha := alpha) hbeta_pos hbeta_le
  have horder2 : ⌈(2 * alpha)⁻¹⌉₊ ≤ ⌈beta⁻¹⌉₊ :=
    Nat.ceil_mono (inv_anti₀ hbeta_pos (by linarith))
  have hUopen : IsOpen (Set.univ ×ˢ Set.Ioo (-(2 * alpha)⁻¹) (2 * alpha)⁻¹ : Set Cylinder) :=
    isOpen_univ.prod isOpen_Ioo
  have hV : ∀ y ∈ (Set.univ ×ˢ Set.Ioo (-(2 * alpha)⁻¹) (2 * alpha)⁻¹ : Set Cylinder),
      Phi y ∈ V := by
    intro y hy
    rw [hPhi y]
    exact hcore y hy
  exact StrongNeck.transport' nk hQ Fmap cmp
    (TransportedErrorTower.ofPullbackCross_of_close cmp nk.cylinder.metric Phi
      (nk.map : Cylinder → P) (fun y => (hPhi y).symm)
      (nk.comparison.mono hsub horder2 le_rfl) hUopen hV horder heps hbeta_pos hbeta_small hdiff)
    hsmall hbeta_le hKeps hbase hcore hVsource htime hjet

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.transportOfComparisons' then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.transportOfComparisons'"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.transportOfComparisons' ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.transportOfComparisons'


def SpatialNeck.transportOfComparisons' {gm : SmoothRiemannianMetric I3 P} {p : P}
    {g : SmoothRiemannianMetric I3 M} {x : M} {alpha beta eps : ℝ} {V : Set P} {order' : ℕ}
    (nk : SpatialNeck gm beta p) (hQ : 0 < metricScalarAt g x)
    (Fmap : PartialDiffeomorph I3 I3 P M ∞)
    (cmp : MetricComparisonOn (fun _ => DifferentialGeometry.scaleMetric (metricScalarAt gm p) nk.Q_pos gm)
      (fun _ => DifferentialGeometry.scaleMetric (metricScalarAt g x) hQ g) Fmap V {0} order' eps)
    (Phi : Cylinder ≃ₘ⟮IC, I3⟯ P) (hPhi : ∀ y, Phi y = nk.map y)
    (hsmall : 2 * alpha < 1 / 11) (heps : 0 ≤ eps)
    (hbeta_pos : 0 < beta) (hbeta_le : beta ≤ alpha)
    (hbeta_small : beta ≤
      backgroundJetSmallness (EuclideanSpace ℝ (Fin 2) × ℝ) ⌈(2 * alpha)⁻¹⌉₊)
    (hKeps : backgroundJetConstant (EuclideanSpace ℝ (Fin 2) × ℝ) ⌈(2 * alpha)⁻¹⌉₊ *
      ((⌈(2 * alpha)⁻¹⌉₊ : ℝ) + 1) * eps ≤ alpha)
    (horder : ⌈(2 * alpha)⁻¹⌉₊ ≤ order')
    (hbase : Fmap p = x)
    (hcore : ∀ y ∈ Set.univ ×ˢ Set.Ioo (-(2 * alpha)⁻¹) (2 * alpha)⁻¹, nk.map y ∈ V)
    (hVsource : V ⊆ Fmap.source) :
    SpatialNeck g (2 * alpha) x := by
  have hsub := neck_window_subset_of_le (alpha := alpha) hbeta_pos hbeta_le
  have horder2 : ⌈(2 * alpha)⁻¹⌉₊ ≤ ⌈beta⁻¹⌉₊ :=
    Nat.ceil_mono (inv_anti₀ hbeta_pos (by linarith))
  have hUopen : IsOpen (Set.univ ×ˢ Set.Ioo (-(2 * alpha)⁻¹) (2 * alpha)⁻¹ : Set Cylinder) :=
    isOpen_univ.prod isOpen_Ioo
  have hV : ∀ y ∈ (Set.univ ×ˢ Set.Ioo (-(2 * alpha)⁻¹) (2 * alpha)⁻¹ : Set Cylinder),
      Phi y ∈ V := by
    intro y hy
    rw [hPhi y]
    exact hcore y hy
  exact SpatialNeck.transport' nk hQ Fmap cmp
    (TransportedErrorTower.ofPullbackCross_of_close cmp (fun _ => nk.cylinder.metric 0) Phi
      (nk.map : Cylinder → P) (fun y => (hPhi y).symm)
      (nk.comparison.mono hsub horder2 le_rfl) hUopen hV horder heps hbeta_pos hbeta_small
      (fun _ _ _ _ _ _ _ => DifferentiableWithinAt.singleton))
    hsmall hbeta_le hKeps hbase hcore hVsource

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.transportOfComparisons' then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.transportOfComparisons'"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.transportOfComparisons' ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.transportOfComparisons'


def StrongNeck.transportOfComparisonsOfTolerances {Dm : RealTimeInterval}
    {Sm : SolutionOn (I := I3) (M := P) Dm} {p : P} {D : RealTimeInterval}
    {S : SolutionOn (I := I3) (M := M) D} {x : M} {t : ℝ} {alpha eps : ℝ} {V : Set P}
    {order' : ℕ}
    (nk : StrongNeck Sm (neckModelTolerance alpha) p 0) (hQ : 0 < S.scalar t x)
    (Fmap : PartialDiffeomorph I3 I3 P M ∞)
    (cmp : MetricComparisonOn (rescaledMetric Sm 0 (Sm.scalar 0 p) nk.Q_pos)
      (rescaledMetric S t (S.scalar t x) hQ) Fmap V (Set.Icc (-1) 0) order' eps)
    (Phi : Cylinder ≃ₘ⟮IC, I3⟯ P) (hPhi : ∀ y, Phi y = nk.map y)
    (ha : 0 < alpha) (hsmall : 2 * alpha < 1 / 11)
    (heps : 0 ≤ eps) (heps' : eps ≤ neckSourceTolerance alpha)
    (horder : ⌈(2 * alpha)⁻¹⌉₊ ≤ order')
    (hbase : Fmap p = x)
    (hcore : ∀ y ∈ Set.univ ×ˢ Set.Ioo (-(2 * alpha)⁻¹) (2 * alpha)⁻¹, nk.map y ∈ V)
    (hVsource : V ⊆ Fmap.source)
    (htime : Set.Icc (t - (S.scalar t x)⁻¹) t ⊆ D.carrier)
    (hdiff : ∀ b s, s ∈ Set.Icc (-1 : ℝ) 0 → UniqueDiffWithinAt ℝ (Set.Icc (-1 : ℝ) 0) s →
      ∀ y ∈ Set.univ ×ˢ Set.Ioo (-(2 * alpha)⁻¹) (2 * alpha)⁻¹,
        ∀ v : Fin 2 → TangentSpace IC y,
          DifferentiableWithinAt ℝ
            (fun a => cmp.jet b a (Phi y) (fun q => mfderiv IC I3 Phi y (v q)))
            (Set.Icc (-1 : ℝ) 0) s)
    (hjet : ∀ b s, s ∈ Set.Icc (-1 : ℝ) 0 → UniqueDiffWithinAt ℝ (Set.Icc (-1 : ℝ) 0) s →
      ∀ y ∈ Set.univ ×ˢ Set.Ioo (-(2 * alpha)⁻¹) (2 * alpha)⁻¹,
        ∀ v : Fin 2 → TangentSpace IC y,
          DifferentiableWithinAt ℝ (fun a => nk.comparison.jet b a y v)
            (Set.Icc (-1 : ℝ) 0) s) :
    StrongNeck S (2 * alpha) x t :=
  StrongNeck.transportOfComparisons' nk hQ Fmap cmp Phi hPhi hsmall heps
    (neckModelTolerance_pos ha) (neckModelTolerance_le alpha)
    (neckModelTolerance_le_smallness alpha)
    (backgroundJetConstant_mul_le_of_le_neckSourceTolerance ha heps') horder hbase hcore hVsource
    htime hdiff hjet

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.transportOfComparisonsOfTolerances then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.transportOfComparisonsOfTolerances"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.transportOfComparisonsOfTolerances ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.transportOfComparisonsOfTolerances


def SpatialNeck.transportOfComparisonsOfTolerances {gm : SmoothRiemannianMetric I3 P} {p : P}
    {g : SmoothRiemannianMetric I3 M} {x : M} {alpha eps : ℝ} {V : Set P} {order' : ℕ}
    (nk : SpatialNeck gm (neckModelTolerance alpha) p) (hQ : 0 < metricScalarAt g x)
    (Fmap : PartialDiffeomorph I3 I3 P M ∞)
    (cmp : MetricComparisonOn (fun _ => DifferentialGeometry.scaleMetric (metricScalarAt gm p) nk.Q_pos gm)
      (fun _ => DifferentialGeometry.scaleMetric (metricScalarAt g x) hQ g) Fmap V {0} order' eps)
    (Phi : Cylinder ≃ₘ⟮IC, I3⟯ P) (hPhi : ∀ y, Phi y = nk.map y)
    (ha : 0 < alpha) (hsmall : 2 * alpha < 1 / 11)
    (heps : 0 ≤ eps) (heps' : eps ≤ neckSourceTolerance alpha)
    (horder : ⌈(2 * alpha)⁻¹⌉₊ ≤ order')
    (hbase : Fmap p = x)
    (hcore : ∀ y ∈ Set.univ ×ˢ Set.Ioo (-(2 * alpha)⁻¹) (2 * alpha)⁻¹, nk.map y ∈ V)
    (hVsource : V ⊆ Fmap.source) :
    SpatialNeck g (2 * alpha) x :=
  SpatialNeck.transportOfComparisons' nk hQ Fmap cmp Phi hPhi hsmall heps
    (neckModelTolerance_pos ha) (neckModelTolerance_le alpha)
    (neckModelTolerance_le_smallness alpha)
    (backgroundJetConstant_mul_le_of_le_neckSourceTolerance ha heps') horder hbase hcore hVsource

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.transportOfComparisonsOfTolerances then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.transportOfComparisonsOfTolerances"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.transportOfComparisonsOfTolerances ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.transportOfComparisonsOfTolerances

end NeckTransport

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
