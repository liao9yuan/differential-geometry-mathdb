import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.ConstantMonotonicity
import Submission.DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.MetricComparison
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.Estimate.QuadraticForm

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Analysis
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.BigOperators

section ScalarMonotonicity

private theorem sqrt_le_div_of_weighted (m : ℕ) {a N C : Real} (ha : 0 < a)
    (h : Real.sqrt (a ^ m * N) ≤ C) :
    Real.sqrt N ≤ C / Real.sqrt a ^ m := by
  have hpow : (0 : Real) < Real.sqrt a ^ m := pow_pos (Real.sqrt_pos.mpr ha) m
  rw [Real.sqrt_mul (pow_nonneg ha.le m), sqrt_pow_of_nonneg ha.le m] at h
  rw [le_div_iff₀ hpow, mul_comm]
  exact h

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.sqrt_le_div_of_weighted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.sqrt_le_div_of_weighted target :: scope.openDecls } }

end ScalarMonotonicity

section Shift

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M]
variable [SigmaCompactSpace M] [T2Space M]

omit [I.Boundaryless] [IsManifold I 2 M] [SigmaCompactSpace M] [T2Space M] in
private theorem timeShift_family_connection
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (τ s : Real) :
    (S.timeShift τ).family.connection s = S.family.connection (s + τ) := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.timeShift_family_connection
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.timeShift_family_connection target :: scope.openDecls } }

omit [I.Boundaryless] [SigmaCompactSpace M] in
private theorem nablaKRm04Field_timeShift
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (τ s : Real) (k : ℕ) :
    nablaKRm04Field (I := I) (S.timeShift τ) s k =
      nablaKRm04Field (I := I) S (s + τ) k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [nablaKRm04Field_succ, ih, timeShift_family_connection]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.nablaKRm04Field_timeShift
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.nablaKRm04Field_timeShift target :: scope.openDecls } }

omit [I.Boundaryless] [SigmaCompactSpace M] in
private theorem nablaKRm04NormSqIntrinsic_timeShift
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (τ : Real) (k : ℕ)
    (s : Real) (x : M) :
    nablaKRm04NormSqIntrinsic (I := I) (S.timeShift τ) k s x =
      nablaKRm04NormSqIntrinsic (I := I) S k (s + τ) x := by
  unfold nablaKRm04NormSqIntrinsic
  rw [nablaKRm04Field_timeShift]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.nablaKRm04NormSqIntrinsic_timeShift
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.nablaKRm04NormSqIntrinsic_timeShift target :: scope.openDecls } }

def timeShiftSolution
    {alpha omega : Real} {halphaomega : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega halphaomega)) (τ : Real) :
    SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen (alpha - τ) (omega - τ)
        (sub_lt_sub_right halphaomega τ)) :=
  (S.timeShift τ).cast _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.timeShiftSolution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.timeShiftSolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.timeShiftSolution ``Submission.DifferentialGeometry.PDE.RicciFlow.timeShiftSolution

omit [FiniteDimensional Real E] [CompleteSpace E] [I.Boundaryless] [IsManifold I 1 M]
  [IsManifold I 2 M] [SigmaCompactSpace M] [T2Space M] in
theorem timeShiftSolution_metric
    {alpha omega : Real} {halphaomega : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega halphaomega)) (τ s : Real) :
    (timeShiftSolution (I := I) S τ).base.metric s = S.base.metric (s + τ) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.timeShiftSolution_metric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.timeShiftSolution_metric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.timeShiftSolution_metric ``Submission.DifferentialGeometry.PDE.RicciFlow.timeShiftSolution_metric

omit [I.Boundaryless] [IsManifold I 2 M] [SigmaCompactSpace M] in
theorem isSolutionOn_timeShiftSolution
    {alpha omega : Real} {halphaomega : alpha < omega}
    {S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega halphaomega)}
    (hS : IsSolutionOn (I := I) S) (τ : Real) :
    IsSolutionOn (I := I) (timeShiftSolution (I := I) S τ) := by
  refine isSolutionOn_cast (isSolutionOn_timeShift (I := I) hS τ) ?_ ?_
  · ext s
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
  · ext s
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.isSolutionOn_timeShiftSolution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.isSolutionOn_timeShiftSolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.isSolutionOn_timeShiftSolution ``Submission.DifferentialGeometry.PDE.RicciFlow.isSolutionOn_timeShiftSolution

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem nablaKRm04NormSqIntrinsic_timeShiftSolution
    {alpha omega : Real} {halphaomega : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega halphaomega)) (τ : Real) (k : ℕ)
    (s : Real) (x : M) :
    nablaKRm04NormSqIntrinsic (I := I) (timeShiftSolution (I := I) S τ) k s x =
      nablaKRm04NormSqIntrinsic (I := I) S k (s + τ) x := by
  unfold timeShiftSolution
  rw [nablaKRm04NormSqIntrinsic_cast, nablaKRm04NormSqIntrinsic_timeShift]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.nablaKRm04NormSqIntrinsic_timeShiftSolution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.nablaKRm04NormSqIntrinsic_timeShiftSolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.nablaKRm04NormSqIntrinsic_timeShiftSolution ``Submission.DifferentialGeometry.PDE.RicciFlow.nablaKRm04NormSqIntrinsic_timeShiftSolution

end Shift



section Global

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable [I.Boundaryless]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
variable [VectorBundle Real E (TangentSpace I : M → Type _)]

def shiCompleteGlobalBound (d m : ℕ) : Real := shiLocalUniformBound d m 1 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.shiCompleteGlobalBound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.shiCompleteGlobalBound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.shiCompleteGlobalBound ``Submission.DifferentialGeometry.PDE.RicciFlow.shiCompleteGlobalBound


theorem shiCompleteGlobalBound_nonneg (d m : ℕ) : 0 ≤ shiCompleteGlobalBound d m :=
  shiLocalUniformBound_nonneg _ _ _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.shiCompleteGlobalBound_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.shiCompleteGlobalBound_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.shiCompleteGlobalBound_nonneg ``Submission.DifferentialGeometry.PDE.RicciFlow.shiCompleteGlobalBound_nonneg

private theorem shi_centre_bound_of_solution
    {alpha omega : Real} {halphaomega : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega halphaomega))
    (hS : IsSolutionOn (I := I) S) {T K : Real} (x : M)
    (halpha : alpha < 0) (hT : 0 < T) (hTomega : T < omega) (hK : 0 < K)
    (hKT : K * T ≤ 1)
    (hcomplete : RiemannianMetricComplete (I := I) (S.base.metric 0))
    (hcurv : ∀ s ∈ Set.Icc (0 : Real) T, ∀ y : M,
      nablaKRm04NormSqIntrinsic (I := I) S 0 s y ≤ K ^ 2) (m : ℕ) :
    Real.sqrt (T ^ m * nablaKRm04NormSqIntrinsic (I := I) S m T x) ≤
      shiCompleteGlobalBound (Module.finrank Real E) m * K := by
  have h0 : (0 : Real) ∈
      (RealTimeInterval.closedOpen alpha omega halphaomega).carrier :=
    ⟨halpha.le, lt_trans hT hTomega⟩
  have hball : IsCompact {y : M |
      riemannianEDistOf (I := I) (S.base.metric 0) x y ≤
        ENNReal.ofReal (1 / Real.sqrt K)} :=
    RiemannianMetricComplete.closedEBall_isCompact (I := I) hcomplete x (1 / Real.sqrt K)
  have hcentre : riemannianEDistOf (I := I) (S.base.metric 0) x x ≤
      ENNReal.ofReal (1 / (2 * Real.sqrt K)) := by
    rw [riemannianEDistOf_self]
    simp
  have hlocal := (shi_local_all_orders_curvature_scale_of_solution_uniform (I := I) S hS
    (R := 1) x halpha hK hT hTomega one_pos h0 hball
    (fun s hs y _ => hcurv s hs y) m T ⟨hT, le_rfl⟩ x hcentre).1
  have hmono : shiLocalUniformBound (Module.finrank Real E) m (K * T) 1 ≤
      shiCompleteGlobalBound (Module.finrank Real E) m :=
    shiLocalUniformBound_mono _ _ one_pos (mul_nonneg hK.le hT.le) hKT
  exact le_trans hlocal (mul_le_mul_of_nonneg_right hmono hK.le)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.shi_centre_bound_of_solution
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.shi_centre_bound_of_solution target :: scope.openDecls } }

theorem shi_complete_global_of_solution
    {alpha omega : Real} {halphaomega : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega halphaomega))
    (hS : IsSolutionOn (I := I) S) {T K : Real}
    (halpha : alpha < 0) (hTomega : T < omega) (hK : 0 < K)
    (hcomplete : RiemannianMetricComplete (I := I) (S.base.metric 0))
    (hcurv : ∀ s ∈ Set.Icc (0 : Real) T, ∀ y : M,
      nablaKRm04NormSqIntrinsic (I := I) S 0 s y ≤ K ^ 2) :
    ∀ m : ℕ, ∀ t ∈ Set.Ioc (0 : Real) T, ∀ x : M,
      Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S m t x) ≤
        shiCompleteGlobalBound (Module.finrank Real E) m * K /
          Real.sqrt (_root_.Min.min t K⁻¹) ^ m := by
  intro m t ht x
  have hKinv : (0 : Real) < K⁻¹ := inv_pos.mpr hK
  have htomega : t < omega := lt_of_le_of_lt ht.2 hTomega
  rcases le_total t K⁻¹ with hle | hle
  · rw [min_eq_left hle]
    refine sqrt_le_div_of_weighted m ht.1 ?_
    refine shi_centre_bound_of_solution (I := I) S hS x halpha ht.1 htomega hK ?_
      hcomplete ?_ m
    · calc K * t ≤ K * K⁻¹ := mul_le_mul_of_nonneg_left hle hK.le
        _ = 1 := mul_inv_cancel₀ (ne_of_gt hK)
    · exact fun s hs y => hcurv s ⟨hs.1, le_trans hs.2 ht.2⟩ y
  · rw [min_eq_right hle]
    have hτ0 : 0 ≤ t - K⁻¹ := by linarith
    have hτt : t - K⁻¹ ≤ t := by linarith
    have hslab : Set.Icc (0 : Real) (t - K⁻¹) ⊆
        (RealTimeInterval.closedOpen alpha omega halphaomega).carrier := by
      intro s hs
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hreg : Set.Ioc (0 : Real) (t - K⁻¹) ⊆
        (RealTimeInterval.closedOpen alpha omega halphaomega).regular := by
      intro s hs
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hric : ∀ s ∈ Set.Icc (0 : Real) (t - K⁻¹), ∀ y : M, ∀ v : TangentSpace I y,
        |ricciTensor (I := I) (S.base.metric s) y v v| ≤
          ((Module.finrank Real E : Real) ^ 2 * K) * (S.base.metric s).inner y v v := by
      intro s hs y v
      have hsT : s ∈ Set.Icc (0 : Real) T :=
        ⟨hs.1, by linarith [hs.2, ht.2]⟩
      have hcurv0 : normSq0S (I := I) (S.base.metric s) y 4 (S.base.rm04 s y) ≤ K ^ 2 := by
        simpa only [nablaKRm04NormSqIntrinsic, nablaKRm04Field_zero, Nat.add_zero] using
          hcurv s hsT y
      have hb := ricci_quadratic_form_bound_of_solution_curvature_bound (I := I) S y v hcurv0
      rwa [Real.sqrt_sq hK.le] at hb
    have hcompleteτ : RiemannianMetricComplete (I := I) (S.base.metric (t - K⁻¹)) :=
      complete_of_ricBound (I := I) S hS hslab hreg (by positivity) hric hcomplete
        ⟨hτ0, le_rfl⟩
    have hshiftcomplete : RiemannianMetricComplete (I := I)
        ((timeShiftSolution (I := I) S (t - K⁻¹)).base.metric 0) := by
      rw [timeShiftSolution_metric, zero_add]
      exact hcompleteτ
    have hcurvshift : ∀ s ∈ Set.Icc (0 : Real) K⁻¹, ∀ y : M,
        nablaKRm04NormSqIntrinsic (I := I)
          (timeShiftSolution (I := I) S (t - K⁻¹)) 0 s y ≤ K ^ 2 := by
      intro s hs y
      rw [nablaKRm04NormSqIntrinsic_timeShiftSolution]
      exact hcurv (s + (t - K⁻¹)) ⟨by linarith [hs.1], by linarith [hs.2, ht.2]⟩ y
    have hcore := shi_centre_bound_of_solution (I := I)
      (timeShiftSolution (I := I) S (t - K⁻¹))
      (isSolutionOn_timeShiftSolution (I := I) hS (t - K⁻¹)) x (by linarith) hKinv
      (by linarith) hK (le_of_eq (mul_inv_cancel₀ (ne_of_gt hK))) hshiftcomplete
      hcurvshift m
    rw [nablaKRm04NormSqIntrinsic_timeShiftSolution] at hcore
    have hsum : K⁻¹ + (t - K⁻¹) = t := by ring
    rw [hsum] at hcore
    exact sqrt_le_div_of_weighted m hKinv hcore

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.shi_complete_global_of_solution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.shi_complete_global_of_solution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.shi_complete_global_of_solution ``Submission.DifferentialGeometry.PDE.RicciFlow.shi_complete_global_of_solution

theorem shi_complete_global_sum_of_solution
    {alpha omega : Real} {halphaomega : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega halphaomega))
    (hS : IsSolutionOn (I := I) S) {T K : Real}
    (halpha : alpha < 0) (hTomega : T < omega) (hK : 0 < K)
    (hcomplete : RiemannianMetricComplete (I := I) (S.base.metric 0))
    (hcurv : ∀ s ∈ Set.Icc (0 : Real) T, ∀ y : M,
      nablaKRm04NormSqIntrinsic (I := I) S 0 s y ≤ K ^ 2) :
    ∀ m : ℕ, ∀ t ∈ Set.Ioc (0 : Real) T, ∀ x : M,
      Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S m t x) ≤
        shiCompleteGlobalBound (Module.finrank Real E) m * K *
          (1 / Real.sqrt t ^ m + Real.sqrt K ^ m) := by
  intro m t ht x
  have hKinv : (0 : Real) < K⁻¹ := inv_pos.mpr hK
  have hCK : (0 : Real) ≤ shiCompleteGlobalBound (Module.finrank Real E) m * K :=
    mul_nonneg (shiCompleteGlobalBound_nonneg _ _) hK.le
  have hmain := shi_complete_global_of_solution (I := I) S hS halpha hTomega hK
    hcomplete hcurv m t ht x
  have hsplit : 1 / Real.sqrt (_root_.Min.min t K⁻¹) ^ m ≤
      1 / Real.sqrt t ^ m + Real.sqrt K ^ m := by
    have hpt : (0 : Real) ≤ 1 / Real.sqrt t ^ m := by positivity
    have hpK : (0 : Real) ≤ Real.sqrt K ^ m := by positivity
    rcases le_total t K⁻¹ with hle | hle
    · rw [min_eq_left hle]
      linarith
    · rw [min_eq_right hle, Real.sqrt_inv, inv_pow, one_div, inv_inv]
      linarith
  calc Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S m t x)
      ≤ shiCompleteGlobalBound (Module.finrank Real E) m * K /
          Real.sqrt (_root_.Min.min t K⁻¹) ^ m := hmain
    _ = shiCompleteGlobalBound (Module.finrank Real E) m * K *
          (1 / Real.sqrt (_root_.Min.min t K⁻¹) ^ m) := by
        rw [div_eq_mul_one_div]
    _ ≤ shiCompleteGlobalBound (Module.finrank Real E) m * K *
          (1 / Real.sqrt t ^ m + Real.sqrt K ^ m) :=
        mul_le_mul_of_nonneg_left hsplit hCK

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.shi_complete_global_sum_of_solution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.shi_complete_global_sum_of_solution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.shi_complete_global_sum_of_solution ``Submission.DifferentialGeometry.PDE.RicciFlow.shi_complete_global_sum_of_solution

theorem shi_positive_slab_of_solution
    {alpha omega : Real} {halphaomega : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega halphaomega))
    (hS : IsSolutionOn (I := I) S) {a₀ a b K : Real}
    (halpha : alpha < a₀) (ha₀ : a₀ < a) (hb : b < omega) (hK : 0 < K)
    (hcomplete : RiemannianMetricComplete (I := I) (S.base.metric a₀))
    (hcurv : ∀ s ∈ Set.Icc a₀ b, ∀ y : M,
      nablaKRm04NormSqIntrinsic (I := I) S 0 s y ≤ K ^ 2) :
    ∀ m : ℕ, ∀ t ∈ Set.Icc a b, ∀ x : M,
      Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S m t x) ≤
        shiCompleteGlobalBound (Module.finrank Real E) m * K *
          (1 / Real.sqrt (a - a₀) + Real.sqrt K) ^ m := by
  intro m t ht x
  have hKinv : (0 : Real) < K⁻¹ := inv_pos.mpr hK
  have haa : (0 : Real) < a - a₀ := by linarith
  have hCK : (0 : Real) ≤ shiCompleteGlobalBound (Module.finrank Real E) m * K :=
    mul_nonneg (shiCompleteGlobalBound_nonneg _ _) hK.le
  have hshiftcomplete : RiemannianMetricComplete (I := I)
      ((timeShiftSolution (I := I) S a₀).base.metric 0) := by
    rw [timeShiftSolution_metric, zero_add]
    exact hcomplete
  have hcurvshift : ∀ s ∈ Set.Icc (0 : Real) (b - a₀), ∀ y : M,
      nablaKRm04NormSqIntrinsic (I := I)
        (timeShiftSolution (I := I) S a₀) 0 s y ≤ K ^ 2 := by
    intro s hs y
    rw [nablaKRm04NormSqIntrinsic_timeShiftSolution]
    exact hcurv (s + a₀) ⟨by linarith [hs.1], by linarith [hs.2]⟩ y
  have hmain := shi_complete_global_of_solution (I := I) (timeShiftSolution (I := I) S a₀)
    (isSolutionOn_timeShiftSolution (I := I) hS a₀) (by linarith) (by linarith) hK
    hshiftcomplete hcurvshift m (t - a₀)
    ⟨by linarith [ht.1], by linarith [ht.2]⟩ x
  rw [nablaKRm04NormSqIntrinsic_timeShiftSolution, sub_add_cancel] at hmain
  have hstep : 1 / Real.sqrt (_root_.Min.min (t - a₀) K⁻¹) ≤ 1 / Real.sqrt (a - a₀) + Real.sqrt K := by
    have hsqa : (0 : Real) < Real.sqrt (a - a₀) := Real.sqrt_pos.mpr haa
    have hsqK : (0 : Real) ≤ Real.sqrt K := Real.sqrt_nonneg K
    rcases le_total (a - a₀) K⁻¹ with hle | hle
    · have hmin : a - a₀ ≤ _root_.Min.min (t - a₀) K⁻¹ := le_min (by linarith [ht.1]) hle
      have h1 : 1 / Real.sqrt (_root_.Min.min (t - a₀) K⁻¹) ≤ 1 / Real.sqrt (a - a₀) :=
        one_div_le_one_div_of_le hsqa (Real.sqrt_le_sqrt hmin)
      linarith
    · have hmin : K⁻¹ ≤ _root_.Min.min (t - a₀) K⁻¹ := le_min (by linarith [ht.1]) le_rfl
      have h1 : 1 / Real.sqrt (_root_.Min.min (t - a₀) K⁻¹) ≤ 1 / Real.sqrt K⁻¹ :=
        one_div_le_one_div_of_le (Real.sqrt_pos.mpr hKinv) (Real.sqrt_le_sqrt hmin)
      have hinvK : 1 / Real.sqrt K⁻¹ = Real.sqrt K := by
        rw [Real.sqrt_inv, one_div, inv_inv]
      rw [hinvK] at h1
      have hpos : (0 : Real) ≤ 1 / Real.sqrt (a - a₀) := by positivity
      linarith
  have hpow : (1 / Real.sqrt (_root_.Min.min (t - a₀) K⁻¹)) ^ m ≤
      (1 / Real.sqrt (a - a₀) + Real.sqrt K) ^ m :=
    pow_le_pow_left₀ (by positivity) hstep m
  calc Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S m t x)
      ≤ shiCompleteGlobalBound (Module.finrank Real E) m * K /
          Real.sqrt (_root_.Min.min (t - a₀) K⁻¹) ^ m := hmain
    _ = shiCompleteGlobalBound (Module.finrank Real E) m * K *
          (1 / Real.sqrt (_root_.Min.min (t - a₀) K⁻¹)) ^ m := by
        rw [div_pow, one_pow, div_eq_mul_one_div]
    _ ≤ shiCompleteGlobalBound (Module.finrank Real E) m * K *
          (1 / Real.sqrt (a - a₀) + Real.sqrt K) ^ m :=
        mul_le_mul_of_nonneg_left hpow hCK

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.shi_positive_slab_of_solution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.shi_positive_slab_of_solution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.shi_positive_slab_of_solution ``Submission.DifferentialGeometry.PDE.RicciFlow.shi_positive_slab_of_solution

private theorem eq_zero_of_le_mul_of_pos_le_one {v A : Real} (hv : 0 ≤ v) (hA : 0 ≤ A)
    (h : ∀ K : Real, 0 < K → K ≤ 1 → v ≤ A * K) : v = 0 := by
  refine le_antisymm (le_of_forall_pos_lt_add ?_) hv
  intro ε hε
  set K : Real := _root_.Min.min 1 (ε / (2 * (A + 1))) with hKdef
  have hApos : (0 : Real) < A + 1 := by linarith
  have hKpos : 0 < K := lt_min one_pos (by positivity)
  have hK1 : K ≤ 1 := min_le_left _ _
  have hKle : K ≤ ε / (2 * (A + 1)) := min_le_right _ _
  calc v ≤ A * K := h K hKpos hK1
    _ ≤ A * (ε / (2 * (A + 1))) := by gcongr
    _ < 0 + ε := by
        rw [zero_add, mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.eq_zero_of_le_mul_of_pos_le_one
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.eq_zero_of_le_mul_of_pos_le_one target :: scope.openDecls } }

theorem shi_complete_global_flat_of_solution
    {alpha omega : Real} {halphaomega : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega halphaomega))
    (hS : IsSolutionOn (I := I) S) {T : Real}
    (halpha : alpha < 0) (hTomega : T < omega)
    (hcomplete : RiemannianMetricComplete (I := I) (S.base.metric 0))
    (hflat : ∀ s ∈ Set.Icc (0 : Real) T, ∀ y : M,
      nablaKRm04NormSqIntrinsic (I := I) S 0 s y ≤ 0) :
    ∀ m : ℕ, ∀ t ∈ Set.Ioc (0 : Real) T, ∀ x : M,
      nablaKRm04NormSqIntrinsic (I := I) S m t x = 0 := by
  intro m t ht x
  have hv0 : 0 ≤ nablaKRm04NormSqIntrinsic (I := I) S m t x :=
    nablaKRm04NormSqIntrinsic_nonneg (I := I) S m t x
  have hC0 : 0 ≤ shiCompleteGlobalBound (Module.finrank Real E) m :=
    shiCompleteGlobalBound_nonneg _ _
  have hsqrt : Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S m t x) = 0 := by
    refine eq_zero_of_le_mul_of_pos_le_one (Real.sqrt_nonneg _)
      (A := shiCompleteGlobalBound (Module.finrank Real E) m * (1 / Real.sqrt t ^ m + 1))
      (by positivity) ?_
    intro K hK hK1
    have hcurv : ∀ s ∈ Set.Icc (0 : Real) T, ∀ y : M,
        nablaKRm04NormSqIntrinsic (I := I) S 0 s y ≤ K ^ 2 :=
      fun s hs y => (hflat s hs y).trans (by positivity)
    have h := shi_complete_global_sum_of_solution (I := I) S hS halpha hTomega hK hcomplete
      hcurv m t ht x
    have hsqK : Real.sqrt K ^ m ≤ 1 := by
      have h1 : Real.sqrt K ≤ 1 := by simpa using Real.sqrt_le_sqrt hK1
      exact pow_le_one₀ (Real.sqrt_nonneg K) h1
    calc Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S m t x)
        ≤ shiCompleteGlobalBound (Module.finrank Real E) m * K *
            (1 / Real.sqrt t ^ m + Real.sqrt K ^ m) := h
      _ ≤ shiCompleteGlobalBound (Module.finrank Real E) m * K *
            (1 / Real.sqrt t ^ m + 1) := by gcongr
      _ = shiCompleteGlobalBound (Module.finrank Real E) m *
            (1 / Real.sqrt t ^ m + 1) * K := by ring
  exact le_antisymm (Real.sqrt_eq_zero'.mp hsqrt) hv0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.shi_complete_global_flat_of_solution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.shi_complete_global_flat_of_solution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.shi_complete_global_flat_of_solution ``Submission.DifferentialGeometry.PDE.RicciFlow.shi_complete_global_flat_of_solution

theorem shi_positive_slab_flat_of_solution
    {alpha omega : Real} {halphaomega : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega halphaomega))
    (hS : IsSolutionOn (I := I) S) {a₀ a b : Real}
    (halpha : alpha < a₀) (ha₀ : a₀ < a) (hb : b < omega)
    (hcomplete : RiemannianMetricComplete (I := I) (S.base.metric a₀))
    (hflat : ∀ s ∈ Set.Icc a₀ b, ∀ y : M,
      nablaKRm04NormSqIntrinsic (I := I) S 0 s y ≤ 0) :
    ∀ m : ℕ, ∀ t ∈ Set.Icc a b, ∀ x : M,
      nablaKRm04NormSqIntrinsic (I := I) S m t x = 0 := by
  intro m t ht x
  have hv0 : 0 ≤ nablaKRm04NormSqIntrinsic (I := I) S m t x :=
    nablaKRm04NormSqIntrinsic_nonneg (I := I) S m t x
  have hC0 : 0 ≤ shiCompleteGlobalBound (Module.finrank Real E) m :=
    shiCompleteGlobalBound_nonneg _ _
  have hsqrt : Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S m t x) = 0 := by
    refine eq_zero_of_le_mul_of_pos_le_one (Real.sqrt_nonneg _)
      (A := shiCompleteGlobalBound (Module.finrank Real E) m *
        (1 / Real.sqrt (a - a₀) + 1) ^ m)
      (by positivity) ?_
    intro K hK hK1
    have hcurv : ∀ s ∈ Set.Icc a₀ b, ∀ y : M,
        nablaKRm04NormSqIntrinsic (I := I) S 0 s y ≤ K ^ 2 :=
      fun s hs y => (hflat s hs y).trans (by positivity)
    have h := shi_positive_slab_of_solution (I := I) S hS halpha ha₀ hb hK hcomplete
      hcurv m t ht x
    have hsqK : Real.sqrt K ≤ 1 := by simpa using Real.sqrt_le_sqrt hK1
    have hpow : (1 / Real.sqrt (a - a₀) + Real.sqrt K) ^ m ≤
        (1 / Real.sqrt (a - a₀) + 1) ^ m := by
      gcongr
    calc Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S m t x)
        ≤ shiCompleteGlobalBound (Module.finrank Real E) m * K *
            (1 / Real.sqrt (a - a₀) + Real.sqrt K) ^ m := h
      _ ≤ shiCompleteGlobalBound (Module.finrank Real E) m * K *
            (1 / Real.sqrt (a - a₀) + 1) ^ m := by gcongr
      _ = shiCompleteGlobalBound (Module.finrank Real E) m *
            (1 / Real.sqrt (a - a₀) + 1) ^ m * K := by ring
  exact le_antisymm (Real.sqrt_eq_zero'.mp hsqrt) hv0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.shi_positive_slab_flat_of_solution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.shi_positive_slab_flat_of_solution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.shi_positive_slab_flat_of_solution ``Submission.DifferentialGeometry.PDE.RicciFlow.shi_positive_slab_flat_of_solution

end Global

end DifferentialGeometry.PDE.RicciFlow

end
