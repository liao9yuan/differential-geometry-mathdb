import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.OriginalRayLocalization
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.GaussianTailRate
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.InitialVolumeHorizon
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.InitialVolumeEndpoint

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open scoped _root_.ContDiff _root_.ENNReal _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.Submission.Topology _root_.Submission.DifferentialGeometry.Topology

namespace DifferentialGeometry.PDE.RicciFlow

def boundedGeometryNoncollapseEpsilon (n : ℕ) (H K c : ℝ) : ℝ :=
  _root_.Min.min (originalRayLocalizationEpsilon n / 2)
    (_root_.Min.min (1 / 2)
      (initialReducedVolumeLowerCoeff n H K c / (2 * reducedSourceGaussianTailRate n)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.boundedGeometryNoncollapseEpsilon then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.boundedGeometryNoncollapseEpsilon"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.boundedGeometryNoncollapseEpsilon ``Submission.DifferentialGeometry.PDE.RicciFlow.boundedGeometryNoncollapseEpsilon

def boundedGeometryNoncollapseCoeff (n : ℕ) (H K c : ℝ) : ℝ :=
  initialReducedVolumeLowerCoeff n H K c *
      boundedGeometryNoncollapseEpsilon n H K c ^ ((n : ℝ) / 2) /
    (2 * Real.exp ((n : ℝ) ^ 2 + (n : ℝ) ^ 3) *
      (4 * Real.pi) ^ (-(n : ℝ) / 2))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.boundedGeometryNoncollapseCoeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.boundedGeometryNoncollapseCoeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.boundedGeometryNoncollapseCoeff ``Submission.DifferentialGeometry.PDE.RicciFlow.boundedGeometryNoncollapseCoeff

private theorem noncollapseEpsilon_bounds (n : ℕ) (H K c : ℝ)
    (hH : 0 < H) (hK : 0 < K) (hc : 0 < c) :
    0 < boundedGeometryNoncollapseEpsilon n H K c ∧
      boundedGeometryNoncollapseEpsilon n H K c ≤ originalRayLocalizationEpsilon n ∧
      boundedGeometryNoncollapseEpsilon n H K c < 1 ∧
      reducedSourceGaussianTailRate n * boundedGeometryNoncollapseEpsilon n H K c ≤
        initialReducedVolumeLowerCoeff n H K c / 2 := by
  let eps := boundedGeometryNoncollapseEpsilon n H K c
  have hloc := originalRayLocalizationEpsilon_pos n
  have hnu := initialReducedVolumeLowerCoeff_pos n H K c hH hK hc
  have hrate := reducedSourceGaussianTailRate_pos n
  have heps : 0 < eps :=
    lt_min (half_pos hloc)
      (lt_min (by norm_num) (div_pos hnu (mul_pos (by norm_num) hrate)))
  have hlocHalf : eps ≤ originalRayLocalizationEpsilon n / 2 := min_le_left _ _
  have hhalf : eps ≤ (1 / 2 : ℝ) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hratio : eps ≤ initialReducedVolumeLowerCoeff n H K c /
      (2 * reducedSourceGaussianTailRate n) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hprod := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hrate)).mp hratio
  exact ⟨heps, by linarith only [hlocHalf, hloc], by linarith only [hhalf],
    by nlinarith only [hprod]⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.noncollapseEpsilon_bounds
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.noncollapseEpsilon_bounds target :: scope.openDecls } }

theorem boundedGeometryNoncollapseCoeff_pos (n : ℕ) (H K c : ℝ)
    (hH : 0 < H) (hK : 0 < K) (hc : 0 < c) :
    0 < boundedGeometryNoncollapseCoeff n H K c := by
  have heps := (noncollapseEpsilon_bounds n H K c hH hK hc).1
  unfold boundedGeometryNoncollapseCoeff
  exact div_pos
    (mul_pos (initialReducedVolumeLowerCoeff_pos n H K c hH hK hc)
      (Real.rpow_pos_of_pos heps _))
    (mul_pos (mul_pos (by norm_num) (Real.exp_pos _))
      (Real.rpow_pos_of_pos (by positivity) _))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.boundedGeometryNoncollapseCoeff_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.boundedGeometryNoncollapseCoeff_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.boundedGeometryNoncollapseCoeff_pos ``Submission.DifferentialGeometry.PDE.RicciFlow.boundedGeometryNoncollapseCoeff_pos

theorem boundedGeometryNoncollapseCoeff_antitoneOn (n : ℕ) (K c : ℝ)
    (hK : 0 < K) (hc : 0 < c) :
    AntitoneOn (fun H : ℝ ↦ boundedGeometryNoncollapseCoeff n H K c) (_root_.Set.Ioi 0) := by
  intro H₁ hH₁ H₂ hH₂ hH
  have hnu := initialReducedVolumeLowerCoeff_antitoneOn n K c hK hc hH₁ hH₂ hH
  have hnu₁ := initialReducedVolumeLowerCoeff_pos n H₁ K c hH₁ hK hc
  have heps₂ := (noncollapseEpsilon_bounds n H₂ K c hH₂ hK hc).1
  have heps : boundedGeometryNoncollapseEpsilon n H₂ K c ≤
      boundedGeometryNoncollapseEpsilon n H₁ K c := by
    unfold boundedGeometryNoncollapseEpsilon
    exact min_le_min le_rfl (min_le_min le_rfl
      (div_le_div_of_nonneg_right hnu
        (mul_pos (by norm_num) (reducedSourceGaussianTailRate_pos n)).le))
  unfold boundedGeometryNoncollapseCoeff
  apply div_le_div_of_nonneg_right ?_ (by positivity)
  exact mul_le_mul hnu
    (Real.rpow_le_rpow heps₂.le heps (by positivity))
    (Real.rpow_nonneg heps₂.le _) hnu₁.le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.boundedGeometryNoncollapseCoeff_antitoneOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.boundedGeometryNoncollapseCoeff_antitoneOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.boundedGeometryNoncollapseCoeff_antitoneOn ``Submission.DifferentialGeometry.PDE.RicciFlow.boundedGeometryNoncollapseCoeff_antitoneOn

private theorem originalSplit_factor_le (n : ℕ) (eps r : ℝ)
    (heps : 0 < eps) (heps1 : eps < 1) (hr : 0 < r) :
    Real.exp (((n : ℝ) ^ 2 + (n : ℝ) ^ 3) * eps -
        ((n : ℝ) / 2) * Real.log (eps * r ^ 2) -
        ((n : ℝ) / 2) * Real.log (4 * Real.pi)) ≤
      (Real.exp ((n : ℝ) ^ 2 + (n : ℝ) ^ 3) *
          (4 * Real.pi) ^ (-(n : ℝ) / 2)) /
        (eps ^ ((n : ℝ) / 2) * r ^ n) := by
  have htau : 0 < eps * r ^ 2 := mul_pos heps (sq_pos_of_pos hr)
  have hpi : 0 < 4 * Real.pi := by positivity
  have htauPow : (eps * r ^ 2) ^ ((n : ℝ) / 2) =
      eps ^ ((n : ℝ) / 2) * r ^ n := by
    rw [Real.mul_rpow heps.le (sq_nonneg r)]
    congr 1
    calc
      (r ^ 2) ^ ((n : ℝ) / 2) = r ^ ((2 : ℝ) * ((n : ℝ) / 2)) := by
        rw [Real.rpow_mul hr.le, Real.rpow_two]
      _ = r ^ (n : ℝ) := by congr 1; ring
      _ = r ^ n := Real.rpow_natCast r n
  have hlogTau : Real.exp (((n : ℝ) / 2) * Real.log (eps * r ^ 2)) =
      eps ^ ((n : ℝ) / 2) * r ^ n := by
    rw [mul_comm, ← Real.rpow_def_of_pos htau]
    exact htauPow
  have hlogPi : Real.exp (((n : ℝ) / 2) * Real.log (4 * Real.pi)) =
      (4 * Real.pi) ^ ((n : ℝ) / 2) := by
    rw [mul_comm, ← Real.rpow_def_of_pos hpi]
  have hexp : Real.exp (((n : ℝ) ^ 2 + (n : ℝ) ^ 3) * eps) ≤
      Real.exp ((n : ℝ) ^ 2 + (n : ℝ) ^ 3) := by
    apply Real.exp_le_exp.mpr
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left heps1.le
        (by positivity : 0 ≤ (n : ℝ) ^ 2 + (n : ℝ) ^ 3)
  calc
    _ = Real.exp (((n : ℝ) ^ 2 + (n : ℝ) ^ 3) * eps) /
        (eps ^ ((n : ℝ) / 2) * r ^ n) / (4 * Real.pi) ^ ((n : ℝ) / 2) := by
      rw [Real.exp_sub, Real.exp_sub, hlogTau, hlogPi]
    _ ≤ Real.exp ((n : ℝ) ^ 2 + (n : ℝ) ^ 3) /
        (eps ^ ((n : ℝ) / 2) * r ^ n) / (4 * Real.pi) ^ ((n : ℝ) / 2) :=
      div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_right hexp (by positivity)) (by positivity)
    _ = _ := by
      rw [show -(n : ℝ) / 2 = -((n : ℝ) / 2) by ring, Real.rpow_neg hpi.le]
      ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.originalSplit_factor_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.originalSplit_factor_le target :: scope.openDecls } }

variable {E F M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace F] {I : ModelWithCorners ℝ E F} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace F M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [ConnectedSpace M] {D : RealTimeInterval}

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem fixed_terminal_ball_noncollapsed_connected
    (H K c : ℝ) (hH : 0 < H) (hK : 0 < K) (hc : 0 < c)
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (time : RealTimeInterval.FlowTime D) (hT : 0 < (time : ℝ)) (hTH : (time : ℝ) ≤ H)
    (hnonneg : D.carrier ⊆ _root_.Set.Ici (0 : ℝ))
    (hcarrier : _root_.Set.Icc (0 : ℝ) (time : ℝ) ⊆ D.carrier)
    (hregular : _root_.Set.Ioc (0 : ℝ) (time : ℝ) ⊆ D.regular)
    (hcomplete : ∀ t ∈ _root_.Set.Icc (0 : ℝ) (time : ℝ),
      RiemannianMetricComplete (I := I) (S.base.metric t))
    (hbounded : ∃ Q : ℝ, ∀ t ∈ _root_.Set.Icc (0 : ℝ) (time : ℝ), ∀ z : M,
      normSq0S (I := I) (S.base.metric t) z 4 (S.base.rm04 t z) ≤ Q)
    (hinit : ∀ z : M,
      Real.sqrt (normSq0S (I := I) (S.base.metric 0) z 4 (S.base.rm04 0 z)) ≤ K)
    (hInj : ∀ p : M, ENNReal.ofReal c ≤
      intrinsicInjectivityRadiusOf (I := I) (S.base.metric 0)
        (hcomplete 0 ⟨le_rfl, hT.le⟩) p)
    (B : FlowMetricBall S time)
    (hballSlab : _root_.Set.Icc ((time : ℝ) - B.radius ^ 2) (time : ℝ) ⊆ D.carrier)
    (hRm : ∀ t ∈ _root_.Set.Icc ((time : ℝ) - B.radius ^ 2) (time : ℝ), ∀ z ∈ B.set,
      B.radius ^ 4 * FlowMetricBall.rmNormSq S t z ≤ 1) :
    B.IsKappaNoncollapsed
      (boundedGeometryNoncollapseCoeff (Module.finrank ℝ E) H K c) := by
  let n := Module.finrank ℝ E
  let T : ℝ := time
  let r := B.radius
  let nu := initialReducedVolumeLowerCoeff n H K c
  let eps := boundedGeometryNoncollapseEpsilon n H K c
  let tau := eps * r ^ 2
  have hr : 0 < r := B.radius_pos
  have hnu : 0 < nu := initialReducedVolumeLowerCoeff_pos n H K c hH hK hc
  obtain ⟨heps, hepsLoc, heps1, hrate⟩ := noncollapseEpsilon_bounds n H K c hH hK hc
  have hleft : 0 ≤ T - r ^ 2 :=
    hnonneg (hballSlab ⟨le_rfl, sub_le_self _ (sq_nonneg _)⟩)
  have hrT : r ^ 2 ≤ T := by linarith only [hleft]
  have htau : 0 < tau := mul_pos heps (sq_pos_of_pos hr)
  have htauT : tau < T := by
    have hshort : tau < r ^ 2 := by
      simpa only [tau, one_mul] using mul_lt_mul_of_pos_right heps1 (sq_pos_of_pos hr)
    exact hshort.trans_le hrT
  have hballTimes : _root_.Set.Icc (T - r ^ 2) T ⊆ _root_.Set.Icc (0 : ℝ) T :=
    fun _ ht ↦ ⟨hleft.trans ht.1, ht.2⟩
  have hballReg : _root_.Set.Ioc (T - r ^ 2) T ⊆ D.regular :=
    fun _ ht ↦ hregular ⟨hleft.trans_lt ht.1, ht.2⟩
  have hballComplete : ∀ t ∈ _root_.Set.Icc (T - r ^ 2) T,
      RiemannianMetricComplete (I := I) (S.base.metric t) :=
    fun t ht ↦ hcomplete t (hballTimes ht)
  have hgT := hcomplete T ⟨hT.le, le_rfl⟩
  have hg0 := hcomplete 0 ⟨le_rfl, hT.le⟩
  obtain ⟨Q, hQ⟩ := hbounded
  have hqual : ∃ Q' : ℝ, 0 ≤ Q' ∧ ∀ t ∈ _root_.Set.Icc (T - r ^ 2) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric t) z 4 (S.base.rm04 t z) ≤ Q' :=
    ⟨max Q 0, le_max_right _ _, fun t ht z ↦ (hQ t (hballTimes ht) z).trans (le_max_left _ _)⟩
  have hRmQual : ∀ sigma : ℝ, 0 < sigma → _root_.Set.Icc (T - sigma) T ⊆ D.regular →
      ∃ Q' : ℝ, ∀ t ∈ _root_.Set.Icc (T - sigma) T, ∀ z : M,
        normSq0S (I := I) (S.base.metric t) z 4 (S.base.rm04 t z) ≤ Q' := by
    intro sigma _hsigma hslab
    exact ⟨Q, fun t ht z ↦ hQ t
      ⟨hnonneg (D.regular_subset (hslab ht)), ht.2⟩ z⟩
  have hcontain : ∀ Z : E, Z ∈ lInjDomain S T B.center tau →
      Real.sqrt ((S.base.metric T).inner B.center Z Z) ≤ 1 / (10 * Real.sqrt eps) →
      ∀ s ∈ _root_.Set.Icc (0 : ℝ) (Real.sqrt tau), lRegularizedCurve S T B.center Z s ∈ B.set := by
    intro Z hZ hnorm s hs
    have hloc := lRegCurve_mem_terminal_third_ball_of_fixed_rm S hS B
      hballSlab hballReg hRm hballComplete hqual eps heps hepsLoc Z hnorm hZ s hs
    change riemannianEDistOf (I := I) (S.base.metric T) B.center
      (lRegularizedCurve S T B.center Z s) < ENNReal.ofReal r
    exact hloc.2.trans_le (ENNReal.ofReal_le_ofReal (by linarith only [hr] : r / 3 ≤ r))
  have hinitial : ENNReal.ofReal nu ≤ DifferentialGeometry.PDE.RicciFlow.redVolume S T B.center T :=
    initial_reducedVolume_lower_connected H K c hH hK hc S hS T hT hTH
      hg0 hcarrier hregular ⟨Q, hQ⟩ hinit hInj B.center
  have htransfer : DifferentialGeometry.PDE.RicciFlow.redVolume S T B.center T ≤
      DifferentialGeometry.PDE.RicciFlow.redVolume S T B.center tau :=
    redVolume_initial_le_of_bounded_rm_on_nonnegative_carrier S hS T hgT B.center
      hnonneg hcarrier hregular ⟨Q, hQ⟩ tau htau htauT
  have hsplit := redVolume_fixed_terminal_ball_split S hS time hgT B
    hRmQual hballSlab hballReg hRm heps heps1 hcontain
  have htail : reducedSourceGaussianTail n (1 / (10 * Real.sqrt eps)) ≤
      ENNReal.ofReal (nu / 2) :=
    (reducedSourceGaussianTail_le_rate_mul n eps heps).trans
      (ENNReal.ofReal_le_ofReal hrate)
  let A := Real.exp (((n : ℝ) ^ 2 + (n : ℝ) ^ 3) * eps -
    ((n : ℝ) / 2) * Real.log tau - ((n : ℝ) / 2) * Real.log (4 * Real.pi))
  have hcombined : ENNReal.ofReal nu ≤ ENNReal.ofReal A * B.volume + ENNReal.ofReal (nu / 2) :=
    ((hinitial.trans htransfer).trans hsplit).trans (add_le_add le_rfl htail)
  have hkappa := boundedGeometryNoncollapseCoeff_pos n H K c hH hK hc
  refine ⟨hkappa, ?_⟩
  by_cases htop : B.volume = ⊤
  · rw [htop]
    exact le_top
  have hA : 0 < A := Real.exp_pos _
  have hreal := ENNReal.toReal_le_add hcombined
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top htop) ENNReal.ofReal_ne_top
  rw [ENNReal.toReal_ofReal hnu.le, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hA.le, ENNReal.toReal_ofReal (half_pos hnu).le] at hreal
  let d := Real.exp ((n : ℝ) ^ 2 + (n : ℝ) ^ 3) * (4 * Real.pi) ^ (-(n : ℝ) / 2)
  let u := eps ^ ((n : ℝ) / 2)
  let a := d / (u * r ^ n)
  have hd : 0 < d := mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (by positivity) _)
  have hu : 0 < u := Real.rpow_pos_of_pos heps _
  have hrpow : 0 < r ^ n := pow_pos hr n
  have ha : 0 < a := div_pos hd (mul_pos hu hrpow)
  have hfactor : A ≤ a := originalSplit_factor_le n eps r heps heps1 hr
  have hhalf : nu / 2 ≤ a * B.volume.toReal := by
    have hmul : A * B.volume.toReal ≤ a * B.volume.toReal :=
      mul_le_mul_of_nonneg_right hfactor ENNReal.toReal_nonneg
    linarith only [hreal, hmul]
  have hkappaEq : boundedGeometryNoncollapseCoeff n H K c = nu * u / (2 * d) := by
    change nu * u /
        (2 * Real.exp ((n : ℝ) ^ 2 + (n : ℝ) ^ 3) *
          (4 * Real.pi) ^ (-(n : ℝ) / 2)) =
      nu * u / (2 * (Real.exp ((n : ℝ) ^ 2 + (n : ℝ) ^ 3) *
          (4 * Real.pi) ^ (-(n : ℝ) / 2)))
    rw [mul_assoc]
  have hproduct : a * (boundedGeometryNoncollapseCoeff n H K c * r ^ n) = nu / 2 := by
    rw [hkappaEq]
    change (d / (u * r ^ n)) * ((nu * u / (2 * d)) * r ^ n) = nu / 2
    field_simp [hd.ne', hu.ne', hrpow.ne']
  have hmass : boundedGeometryNoncollapseCoeff n H K c * r ^ n ≤ B.volume.toReal := by
    apply (mul_le_mul_iff_right₀ ha).mp
    rw [hproduct]
    exact hhalf
  calc
    ENNReal.ofReal (boundedGeometryNoncollapseCoeff n H K c) * ENNReal.ofReal r ^ n =
        ENNReal.ofReal (boundedGeometryNoncollapseCoeff n H K c * r ^ n) := by
      rw [ENNReal.ofReal_mul hkappa.le, ENNReal.ofReal_pow hr.le]
    _ ≤ ENNReal.ofReal B.volume.toReal := ENNReal.ofReal_le_ofReal hmass
    _ ≤ B.volume := ENNReal.ofReal_toReal_le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.fixed_terminal_ball_noncollapsed_connected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.fixed_terminal_ball_noncollapsed_connected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.fixed_terminal_ball_noncollapsed_connected ``Submission.DifferentialGeometry.PDE.RicciFlow.fixed_terminal_ball_noncollapsed_connected

end DifferentialGeometry.PDE.RicciFlow

end
