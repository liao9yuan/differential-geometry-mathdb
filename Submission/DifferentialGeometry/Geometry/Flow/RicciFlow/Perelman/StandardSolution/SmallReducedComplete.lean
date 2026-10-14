import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ShortTime.ReducedLengthLimit
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ShortTime.JacobianLimit
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.MinPrefix
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.MinNonconjugacy
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.RedJacobian
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ReducedVolumeComplete
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Length

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Set
open _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.Submission.Topology _root_.Submission.DifferentialGeometry.Topology

namespace DifferentialGeometry.PDE.RicciFlow

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

private theorem original_min_terminal_regular
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (x : M)
    (Z : TangentSpace I x) {sigma : ℝ}
    (hmin : (Z, sigma) ∈ lMinDomain S T x) :
    T ∈ D.regular := by
  have hdom : (Z, sigma) ∈ lExpPosDom S T x :=
    ((mem_lMinDomain S T x Z sigma).mp hmin).1
  have hclock := lExpPosDom_regularity S T x Z hdom
    (show (0 : ℝ) ∈ _root_.Set.Icc (0 : ℝ) (Real.sqrt sigma) from
      ⟨le_rfl, Real.sqrt_nonneg sigma⟩)
  simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero] using hclock

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.original_min_terminal_regular
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.original_min_terminal_regular target :: scope.openDecls } }

theorem lRedLen_sq_lim_of_rm
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (K T : ℝ) (x : M)
    (Z : TangentSpace I x) {sigma : ℝ}
    (hmin : (Z, sigma) ∈ lMinDomain S T x)
    (hRm : ∀ t ∈ _root_.Set.Icc (T - sigma) T, ∀ y : M,
      normSq0S (I := I) (S.base.metric t) y 4
        (S.base.rm04 t y) ≤ K) :
    _root_.Filter.Tendsto
      (fun s : ℝ ↦ redLength S T x (lExp S T x Z (s ^ 2)) (s ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝 ((S.base.metric T).inner x Z Z)) := by
  have hsigma : 0 < sigma := lMinDomain_pos S T x Z sigma hmin
  have hT : T ∈ D.regular := original_min_terminal_regular S T x Z hmin
  have hsToZero : _root_.Filter.Tendsto (fun s : Real ↦ s ^ 2)
      (𝓝[>] (0 : Real)) (𝓝 (0 : Real)) := by
    have hid : _root_.Filter.Tendsto (fun s : Real ↦ s) (𝓝[>] (0 : Real))
        (𝓝 (0 : Real)) :=
      tendsto_id.mono_left inf_le_left
    simpa only [zero_pow (by norm_num : (2 : Nat) ≠ 0)] using hid.pow 2
  have hsLt : ∀ᶠ s in 𝓝[>] (0 : Real), s ^ 2 < sigma :=
    hsToZero.eventually (Iio_mem_nhds hsigma)
  have hEq :
      (fun s : Real ↦
        lRegularizedAction S T (lRegularizedCurve S T x Z) 0 s / (2 * s)) =ᶠ[𝓝[>] (0 : Real)]
      fun s : Real ↦
        redLength (I := I) S T x (lExp (I := I) S T x Z (s ^ 2))
          (s ^ 2) := by
    filter_upwards [self_mem_nhdsWithin, hsLt] with s hs hsSq
    have hs0 : 0 < s ^ 2 := sq_pos_of_pos hs
    have hminSq : (Z, s ^ 2) ∈ lMinDomain S T x :=
      lMinDomain_down_of_rm S hS K T x Z hmin hs0 hsSq.le hRm
    have hcost := ((mem_lMinDomain S T x Z (s ^ 2)).1 hminSq).2
    have hlen :
        lLength S T (fun r : Real ↦ lExp S T x Z r) 0 (s ^ 2) =
          lRegularizedAction S T (lRegularizedCurve S T x Z) 0 s := by
      change lLength S T (squareRootReparametrization (lRegularizedCurve S T x Z)) 0 (s ^ 2) = _
      have hlenSq := lLength_squareRootReparametrization_eq_lRegularizedAction (I := I) S T
        (lRegularizedCurve S T x Z) (s ^ 2) hs0.le
      rw [Real.sqrt_sq hs.le] at hlenSq
      exact hlenSq
    change lRegularizedAction S T (lRegularizedCurve S T x Z) 0 s / (2 * s) =
      lCost S T x (lExp S T x Z (s ^ 2)) (s ^ 2) /
        (2 * Real.sqrt (s ^ 2))
    rw [Real.sqrt_sq hs.le]
    exact congrArg (fun q : Real ↦ q / (2 * s)) (hlen.symm.trans hcost)
  exact (tendsto_lRegularizedAction_div_at_zero S hS T x Z hT).congr' hEq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.lRedLen_sq_lim_of_rm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.lRedLen_sq_lim_of_rm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.lRedLen_sq_lim_of_rm ``Submission.DifferentialGeometry.PDE.RicciFlow.lRedLen_sq_lim_of_rm

theorem lRedJac_zero_lim_of_rm
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (K T : ℝ) (x : M)
    (Z : TangentSpace I x) {sigma : ℝ}
    (hmin : (Z, sigma) ∈ lMinDomain S T x)
    (hRm : ∀ t ∈ _root_.Set.Icc (T - sigma) T, ∀ y : M,
      normSq0S (I := I) (S.base.metric t) y 4
        (S.base.rm04 t y) ≤ K) :
    _root_.Filter.Tendsto (fun s : ℝ ↦ lReducedJacobian S T x Z (s ^ 2))
      (𝓝[>] (0 : ℝ))
      (𝓝 (((Real.pi : ℝ) ^ ((Module.finrank ℝ E : ℝ) / 2))⁻¹ *
        Real.exp (-(S.base.metric T).inner x Z Z))) := by
  have hsigma : 0 < sigma := lMinDomain_pos S T x Z sigma hmin
  have hT : T ∈ D.regular := original_min_terminal_regular S T x Z hmin
  have hden := tendsto_normalized_lExpDensity_at_zero S hS T x Z hT
  have hlen := lRedLen_sq_lim_of_rm S hS K T x Z hmin hRm
  have hexp : _root_.Filter.Tendsto
      (fun s : Real ↦ Real.exp
        (-redLength S T x (lExp S T x Z (s ^ 2)) (s ^ 2)))
      (𝓝[>] (0 : Real))
      (𝓝 (Real.exp (-(S.base.metric T).inner x Z Z))) :=
    by simpa only [Real.exp_eq_exp_ℝ] using hlen.neg.exp
  have hpi : _root_.Filter.Tendsto
      (fun _ : Real ↦ ((Real.pi : Real) ^
        ((Module.finrank Real E : Real) / 2))⁻¹)
      (𝓝[>] (0 : Real))
      (𝓝 (((Real.pi : Real) ^
        ((Module.finrank Real E : Real) / 2))⁻¹)) :=
    tendsto_const_nhds
  have hcore : _root_.Filter.Tendsto
      (fun s : Real ↦
        (lExpDensity S T x Z (s ^ 2) /
            (2 * s) ^ (Module.finrank Real E)) *
          ((Real.pi : Real) ^
            ((Module.finrank Real E : Real) / 2))⁻¹ *
          Real.exp
            (-redLength S T x (lExp S T x Z (s ^ 2)) (s ^ 2)))
      (𝓝[>] (0 : Real))
      (𝓝 (lSourceDensity S T x *
        ((Real.pi : Real) ^
          ((Module.finrank Real E : Real) / 2))⁻¹ *
        Real.exp (-(S.base.metric T).inner x Z Z))) :=
    (hden.mul hpi).mul hexp
  have hsToZero : _root_.Filter.Tendsto (fun s : Real ↦ s ^ 2)
      (𝓝[>] (0 : Real)) (𝓝 (0 : Real)) := by
    have hid : _root_.Filter.Tendsto (fun s : Real ↦ s) (𝓝[>] (0 : Real))
        (𝓝 (0 : Real)) :=
      tendsto_id.mono_left inf_le_left
    simpa only [zero_pow (by norm_num : (2 : Nat) ≠ 0)] using hid.pow 2
  have hsLt : ∀ᶠ s in 𝓝[>] (0 : Real), s ^ 2 < sigma :=
    hsToZero.eventually (Iio_mem_nhds hsigma)
  have heq :
      (fun s : Real ↦ lReducedJacobian S T x Z (s ^ 2) * lSourceDensity S T x) =ᶠ[𝓝[>] (0 : Real)]
      fun s : Real ↦
        (lExpDensity S T x Z (s ^ 2) /
            (2 * s) ^ (Module.finrank Real E)) *
          ((Real.pi : Real) ^
            ((Module.finrank Real E : Real) / 2))⁻¹ *
          Real.exp
            (-redLength S T x (lExp S T x Z (s ^ 2)) (s ^ 2)) := by
    filter_upwards [self_mem_nhdsWithin, hsLt] with s hs hsSq
    have hs0 : s ≠ 0 := ne_of_gt hs
    have hsSq0 : 0 < s ^ 2 := sq_pos_of_pos hs
    have hdomSq : (Z, s ^ 2) ∈ lExpPosDom S T x :=
      lExpPosDom_down S T x Z
        (((mem_lMinDomain S T x Z sigma).mp hmin).1) hsSq0 hsSq.le
    have hnconjSq : ¬ IsLConjugate S T x Z (s ^ 2) :=
      lMinVec_nconj_lt_of_rm S hS K T x hmin hsSq hRm
    have hsPow : Real.exp
        ((Module.finrank Real E : Real) / 2 * Real.log (s ^ 2)) =
        s ^ (Module.finrank Real E) := by
      rw [mul_comm, ← Real.rpow_def_of_pos hsSq0, ← Real.rpow_two s,
        ← Real.rpow_mul hs.le]
      rw [show (2 : Real) * ((Module.finrank Real E : Real) / 2) =
          (Module.finrank Real E : Real) by ring, Real.rpow_natCast]
    have hfourPi : 0 < (4 : Real) * Real.pi :=
      mul_pos (by norm_num) Real.pi_pos
    have hfourPow : Real.exp
        ((Module.finrank Real E : Real) / 2 * Real.log (4 * Real.pi)) =
        (2 : Real) ^ (Module.finrank Real E) *
          (Real.pi : Real) ^ ((Module.finrank Real E : Real) / 2) := by
      rw [mul_comm, ← Real.rpow_def_of_pos hfourPi]
      rw [show (4 : Real) * Real.pi = (2 : Real) ^ 2 * Real.pi by ring,
        Real.mul_rpow (sq_nonneg (2 : Real)) Real.pi_pos.le,
        ← Real.rpow_two (2 : Real),
        ← Real.rpow_mul (by norm_num : (0 : Real) ≤ 2)]
      rw [show (2 : Real) * ((Module.finrank Real E : Real) / 2) =
          (Module.finrank Real E : Real) by ring, Real.rpow_natCast]
    have hpi0 : (Real.pi : Real) ^
        ((Module.finrank Real E : Real) / 2) ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos Real.pi_pos _)
    rw [lRedJac_mul_src_of_nonconj S T x Z (s ^ 2) hdomSq hnconjSq]
    unfold DifferentialGeometry.PDE.RicciFlow.Perelman.redDensity
    rw [Real.exp_sub, Real.exp_sub, hsPow, hfourPow]
    field_simp [hs0, hpi0]
    ring
  have hprod : _root_.Filter.Tendsto
      (fun s : Real ↦ lReducedJacobian S T x Z (s ^ 2) * lSourceDensity S T x)
      (𝓝[>] (0 : Real))
      (𝓝 (lSourceDensity S T x *
        ((Real.pi : Real) ^
          ((Module.finrank Real E : Real) / 2))⁻¹ *
        Real.exp (-(S.base.metric T).inner x Z Z))) :=
    hcore.congr' heq.symm
  have hsrc0 : lSourceDensity S T x ≠ 0 :=
    ne_of_gt (lSourceDensity_pos S T x)
  have hdiv := hprod.div_const (lSourceDensity S T x)
  have hfun :
      (fun s : Real ↦
        (lReducedJacobian S T x Z (s ^ 2) * lSourceDensity S T x) /
          lSourceDensity S T x) =
      (fun s : Real ↦ lReducedJacobian S T x Z (s ^ 2)) := by
    funext s
    exact mul_div_cancel_right₀ _ hsrc0
  have htarget :
      (lSourceDensity S T x *
          ((Real.pi : Real) ^
            ((Module.finrank Real E : Real) / 2))⁻¹ *
          Real.exp (-(S.base.metric T).inner x Z Z)) /
        lSourceDensity S T x =
      ((Real.pi : Real) ^
          ((Module.finrank Real E : Real) / 2))⁻¹ *
        Real.exp (-(S.base.metric T).inner x Z Z) := by
    field_simp [hsrc0]
  rw [hfun, htarget] at hdiv
  exact hdiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.lRedJac_zero_lim_of_rm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.lRedJac_zero_lim_of_rm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.lRedJac_zero_lim_of_rm ``Submission.DifferentialGeometry.PDE.RicciFlow.lRedJac_zero_lim_of_rm

theorem lRedJac_tau_lim_of_rm
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (K T : ℝ) (x : M)
    (Z : TangentSpace I x) {sigma : ℝ}
    (hmin : (Z, sigma) ∈ lMinDomain S T x)
    (hRm : ∀ t ∈ _root_.Set.Icc (T - sigma) T, ∀ y : M,
      normSq0S (I := I) (S.base.metric t) y 4
        (S.base.rm04 t y) ≤ K) :
    _root_.Filter.Tendsto (fun tau : ℝ ↦ lReducedJacobian S T x Z tau)
      (𝓝[>] (0 : ℝ))
      (𝓝 (((Real.pi : ℝ) ^ ((Module.finrank ℝ E : ℝ) / 2))⁻¹ *
        Real.exp (-(S.base.metric T).inner x Z Z))) := by
  have hsqrt : _root_.Filter.Tendsto Real.sqrt
      (𝓝[>] (0 : Real)) (𝓝[>] (0 : Real)) :=
    tendsto_nhdsWithin_iff.mpr ⟨
      by
        simpa only [Real.sqrt_zero] using
          (Real.continuous_sqrt.tendsto (0 : Real)).mono_left nhdsWithin_le_nhds,
      by
        filter_upwards [self_mem_nhdsWithin] with tau htau
        exact Real.sqrt_pos.2 htau⟩
  have hlim := (lRedJac_zero_lim_of_rm S hS K T x Z hmin hRm).comp hsqrt
  have heq :
      (fun tau : Real ↦ lReducedJacobian S T x Z tau) =ᶠ[𝓝[>] (0 : Real)]
        (fun tau : Real ↦ lReducedJacobian S T x Z (Real.sqrt tau ^ 2)) := by
    filter_upwards [self_mem_nhdsWithin] with tau htau
    rw [Real.sq_sqrt htau.le]
  exact hlim.congr' heq.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.lRedJac_tau_lim_of_rm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.lRedJac_tau_lim_of_rm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.lRedJac_tau_lim_of_rm ``Submission.DifferentialGeometry.PDE.RicciFlow.lRedJac_tau_lim_of_rm

variable [NeZero (Module.finrank ℝ E)]

theorem lRedJac_le_gauss_of_rm
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (K T : ℝ) (x : M)
    {Z : TangentSpace I x} {sigma tau : ℝ}
    (hmin : (Z, sigma) ∈ lMinDomain S T x)
    (htau : 0 < tau) (hlt : tau < sigma)
    (hRm : ∀ t ∈ _root_.Set.Icc (T - sigma) T, ∀ y : M,
      normSq0S (I := I) (S.base.metric t) y 4
        (S.base.rm04 t y) ≤ K) :
    lReducedJacobian S T x Z tau ≤
      ((Real.pi : ℝ) ^ ((Module.finrank ℝ E : ℝ) / 2))⁻¹ *
        Real.exp (-(S.base.metric T).inner x Z Z) := by
  have hclock : _root_.Filter.Tendsto (fun r : ℝ ↦ r)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < tau :=
    hclock.eventually (Iio_mem_nhds htau)
  have hanti := lRedJac_antitoneOn_of_rm S hS K T x hmin hRm
  have hle : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      lReducedJacobian S T x Z tau ≤ lReducedJacobian S T x Z r := by
    filter_upwards [self_mem_nhdsWithin, hsmall] with r hr hrt
    exact hanti ⟨hr, hrt.trans hlt⟩ ⟨htau, hlt⟩ hrt.le
  exact ge_of_tendsto
    (lRedJac_tau_lim_of_rm S hS K T x Z hmin hRm) hle

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.lRedJac_le_gauss_of_rm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.lRedJac_le_gauss_of_rm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.lRedJac_le_gauss_of_rm ``Submission.DifferentialGeometry.PDE.RicciFlow.lRedJac_le_gauss_of_rm

end DifferentialGeometry.PDE.RicciFlow

end
