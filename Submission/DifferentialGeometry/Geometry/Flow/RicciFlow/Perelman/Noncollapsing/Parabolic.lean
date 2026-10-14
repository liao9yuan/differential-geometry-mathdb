import Submission.DifferentialGeometry.Topology.Compactness.ProductNeighborhood
import Submission.DifferentialGeometry.Topology.Compactness.ExtremumNeighborhood
import Submission.DifferentialGeometry.Geometry.Metric.Distance.LocalBall
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.CurvatureContinuity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.Predicates

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

namespace FlowMetricBall

variable {S : SolutionOn (I := I) (M := M) D} {time : D.FlowTime}

def IsParabolicallyRmControlled (B : FlowMetricBall S time) : Prop :=
  Set.Icc ((time : Real) - B.radius ^ 2) (time : Real) ⊆ D.carrier ∧
    ∀ s ∈ Set.Icc ((time : Real) - B.radius ^ 2) (time : Real),
      ∀ x ∈ B.set, B.radius ^ 4 * rmNormSq S s x ≤ 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.IsParabolicallyRmControlled then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.IsParabolicallyRmControlled"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.IsParabolicallyRmControlled ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.IsParabolicallyRmControlled

omit [SigmaCompactSpace M] in
theorem isSpatiallyRmControlled_of_isParabolicallyRmControlled
    {B : FlowMetricBall S time} (hB : B.IsParabolicallyRmControlled) :
    B.IsSpatiallyRmControlled :=
  hB.2 time ⟨sub_le_self _ (sq_nonneg _), le_rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.isSpatiallyRmControlled_of_isParabolicallyRmControlled then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.isSpatiallyRmControlled_of_isParabolicallyRmControlled"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.isSpatiallyRmControlled_of_isParabolicallyRmControlled ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.isSpatiallyRmControlled_of_isParabolicallyRmControlled

end FlowMetricBall

def ParabolicallyKappaNoncollapsedBelowScale
    (S : SolutionOn (I := I) (M := M) D) (kappa rho : Real) : Prop :=
  0 < rho ∧ ∀ (t : D.FlowTime) (B : FlowMetricBall S t), B.radius ≤ rho →
    B.IsParabolicallyRmControlled → B.IsKappaNoncollapsed kappa

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.ParabolicallyKappaNoncollapsedBelowScale then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.ParabolicallyKappaNoncollapsedBelowScale"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.ParabolicallyKappaNoncollapsedBelowScale ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.ParabolicallyKappaNoncollapsedBelowScale

def ParabolicNoLocalCollapsing
    (S : SolutionOn (I := I) (M := M) D) (rho : Real) : Prop :=
  ∃ kappa : Real, 0 < kappa ∧ ParabolicallyKappaNoncollapsedBelowScale S kappa rho

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.ParabolicNoLocalCollapsing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.ParabolicNoLocalCollapsing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.ParabolicNoLocalCollapsing ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.ParabolicNoLocalCollapsing

theorem parabolicallyKappaNoncollapsedBelowScale_of_spatially
    {S : SolutionOn (I := I) (M := M) D} {kappa rho : Real}
    (h : SpatiallyKappaNoncollapsedBelowScale S kappa rho) :
    ParabolicallyKappaNoncollapsedBelowScale S kappa rho :=
  ⟨h.1, fun t B hr hB =>
    h.2 t B hr (FlowMetricBall.isSpatiallyRmControlled_of_isParabolicallyRmControlled hB)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicallyKappaNoncollapsedBelowScale_of_spatially then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicallyKappaNoncollapsedBelowScale_of_spatially"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicallyKappaNoncollapsedBelowScale_of_spatially ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicallyKappaNoncollapsedBelowScale_of_spatially

theorem parabolicNoLocalCollapsing_of_spatial
    {S : SolutionOn (I := I) (M := M) D} {rho : Real}
    (h : SpatialNoLocalCollapsing S rho) : ParabolicNoLocalCollapsing S rho := by
  obtain ⟨kappa, hkappa, hbelow⟩ := h
  exact ⟨kappa, hkappa, parabolicallyKappaNoncollapsedBelowScale_of_spatially hbelow⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicNoLocalCollapsing_of_spatial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicNoLocalCollapsing_of_spatial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicNoLocalCollapsing_of_spatial ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicNoLocalCollapsing_of_spatial

private theorem parabolicControlWindow
    (tau R : Real) (hR : 0 < R) (s q r : Real)
    (hq : q ∈ Set.Icc (s - (Real.sqrt R * r) ^ 2) s) :
    parabolicTime tau R q ∈
      Set.Icc (parabolicTime tau R s - r ^ 2) (parabolicTime tau R s) := by
  have hrad : (Real.sqrt R * r) ^ 2 = R * r ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hR.le]
  have hlo : s - R * r ^ 2 ≤ q := by simpa only [hrad] using hq.1
  have hlo_div : (s - R * r ^ 2) / R ≤ q / R :=
    (div_le_div_iff_of_pos_right hR).2 hlo
  have hsplit : (s - R * r ^ 2) / R = s / R - r ^ 2 := by
    field_simp [ne_of_gt hR]
  rw [hsplit] at hlo_div
  have hhi_div : q / R ≤ s / R := (div_le_div_iff_of_pos_right hR).2 hq.2
  unfold parabolicTime
  constructor <;> linarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicControlWindow
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicControlWindow target :: scope.openDecls } }

private theorem backwardControlWindow
    (tau R : Real) (hR : 0 < R) (s q r : Real)
    (hq : q ∈ Set.Icc
      (parabolicTime tau R s - (r / Real.sqrt R) ^ 2) (parabolicTime tau R s)) :
    parabolicBackward tau R q ∈ Set.Icc (s - r ^ 2) s := by
  have hrad : (r / Real.sqrt R) ^ 2 = r ^ 2 / R := by
    rw [div_pow, Real.sq_sqrt hR.le]
  have hlo0 := hq.1
  rw [hrad] at hlo0
  unfold parabolicTime at hlo0
  have hlo_div : (s - r ^ 2) / R ≤ q - tau := by
    rw [sub_div]
    linarith
  have hlo := (div_le_iff₀ hR).1 hlo_div
  have hhi0 := hq.2
  unfold parabolicTime at hhi0
  have hhi_div : q - tau ≤ s / R := by linarith
  have hhi := (le_div_iff₀ hR).1 hhi_div
  constructor
  · simpa [parabolicBackward, mul_comm] using hlo
  · simpa [parabolicBackward, mul_comm] using hhi

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.backwardControlWindow
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.backwardControlWindow target :: scope.openDecls } }

section Scaling

variable [CompleteSpace E]

omit [SigmaCompactSpace M] in
theorem parabolicBall_isParabolicallyRmControlled
    (S : SolutionOn (I := I) (M := M) D)
    (tau R : Real) (hR : 0 < R) (htau : tau ∈ D.carrier)
    (s : (parabolicInterval D tau R htau).FlowTime)
    (B : FlowMetricBall S (parabolicFlowTime tau R htau s))
    (hB : B.IsParabolicallyRmControlled) :
    (parabolicBall S tau R hR htau s B).IsParabolicallyRmControlled := by
  rcases hB with ⟨hwindow, hcurv⟩
  constructor
  · intro q hq
    exact hwindow (parabolicControlWindow tau R hR (s : Real) q B.radius hq)
  · intro q hq x hx
    have hq_old := parabolicControlWindow tau R hR (s : Real) q B.radius hq
    have hx_old : x ∈ B.set := by
      rwa [parabolicBall_set] at hx
    have hold := hcurv (parabolicTime tau R q) hq_old x hx_old
    unfold FlowMetricBall.rmNormSq
    rw [parabolicRmNormSq]
    have hscale : (Real.sqrt R * B.radius) ^ 4 * R⁻¹ ^ 2 = B.radius ^ 4 := by
      rw [mul_pow]
      calc
        Real.sqrt R ^ 4 * B.radius ^ 4 * R⁻¹ ^ 2 =
            (Real.sqrt R ^ 2) ^ 2 * B.radius ^ 4 * R⁻¹ ^ 2 := by ring
        _ = R ^ 2 * B.radius ^ 4 * R⁻¹ ^ 2 := by rw [Real.sq_sqrt hR.le]
        _ = B.radius ^ 4 := by field_simp [ne_of_gt hR]
    change (Real.sqrt R * B.radius) ^ 4 * (R⁻¹ ^ 2 *
      Tensor0SBundle.normSq0S (I := I) (S.base.metric (parabolicTime tau R q)) x 4
        (S.base.rm04 (parabolicTime tau R q) x)) ≤ 1
    rw [← mul_assoc, hscale]
    exact hold

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicBall_isParabolicallyRmControlled then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicBall_isParabolicallyRmControlled"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicBall_isParabolicallyRmControlled ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicBall_isParabolicallyRmControlled

omit [SigmaCompactSpace M] in
theorem backBall_isParabolicallyRmControlled
    (S : SolutionOn (I := I) (M := M) D)
    (tau R : Real) (hR : 0 < R) (htau : tau ∈ D.carrier)
    (s : (parabolicInterval D tau R htau).FlowTime)
    (B : FlowMetricBall (parabolicSolution (I := I) S tau R hR htau) s)
    (hB : B.IsParabolicallyRmControlled) :
    (backBall S tau R hR htau s B).IsParabolicallyRmControlled := by
  rcases hB with ⟨hwindow, hcurv⟩
  constructor
  · intro q hq
    let q' : Real := parabolicBackward tau R q
    have hq_new : q' ∈ Set.Icc (s - B.radius ^ 2) (s : Real) :=
      backwardControlWindow tau R hR (s : Real) q B.radius hq
    have hmem := hwindow hq_new
    change parabolicTime tau R q' ∈ D.carrier at hmem
    simpa only [q', parabolicTime_back (ne_of_gt hR)] using hmem
  · intro q hq x hx
    let q' : Real := parabolicBackward tau R q
    have hq_new : q' ∈ Set.Icc (s - B.radius ^ 2) (s : Real) :=
      backwardControlWindow tau R hR (s : Real) q B.radius hq
    have hset := parabolicBall_set (I := I) S tau R hR htau s
      (backBall S tau R hR htau s B)
    rw [parabolicBall_back] at hset
    have hx_new : x ∈ B.set := by rwa [hset]
    have hold := hcurv q' hq_new x hx_new
    unfold FlowMetricBall.rmNormSq at hold ⊢
    rw [parabolicRmNormSq, parabolicTime_back (ne_of_gt hR)] at hold
    change (B.radius / Real.sqrt R) ^ 4 *
      Tensor0SBundle.normSq0S (I := I) (S.base.metric q) x 4
        (S.base.rm04 q x) ≤ 1
    have hscale : (B.radius / Real.sqrt R) ^ 4 = B.radius ^ 4 * R⁻¹ ^ 2 := by
      rw [div_pow]
      have hsqrt : Real.sqrt R ^ 4 = R ^ 2 := by
        calc
          Real.sqrt R ^ 4 = (Real.sqrt R ^ 2) ^ 2 := by ring
          _ = R ^ 2 := by rw [Real.sq_sqrt hR.le]
      rw [hsqrt, div_eq_mul_inv, inv_pow]
    rw [hscale]
    simpa only [mul_assoc] using hold

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.backBall_isParabolicallyRmControlled then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.backBall_isParabolicallyRmControlled"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.backBall_isParabolicallyRmControlled ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.backBall_isParabolicallyRmControlled

omit [SigmaCompactSpace M] in
theorem parabolicBall_isParabolicallyRmControlled_iff
    (S : SolutionOn (I := I) (M := M) D)
    (tau R : Real) (hR : 0 < R) (htau : tau ∈ D.carrier)
    (s : (parabolicInterval D tau R htau).FlowTime)
    (B : FlowMetricBall S (parabolicFlowTime tau R htau s)) :
    (parabolicBall S tau R hR htau s B).IsParabolicallyRmControlled ↔
      B.IsParabolicallyRmControlled := by
  constructor
  · intro h
    have hback := backBall_isParabolicallyRmControlled (I := I) S tau R hR htau s
      (parabolicBall S tau R hR htau s B) h
    rwa [backBall_parabolic] at hback
  · exact parabolicBall_isParabolicallyRmControlled (I := I) S tau R hR htau s B

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicBall_isParabolicallyRmControlled_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicBall_isParabolicallyRmControlled_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicBall_isParabolicallyRmControlled_iff ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicBall_isParabolicallyRmControlled_iff

theorem parabolicallyKappaNoncollapsedBelowScale_parabolicSolution
    (S : SolutionOn (I := I) (M := M) D)
    (tau R : Real) (hR : 0 < R) (htau : tau ∈ D.carrier)
    (kappa rho : Real)
    (hS : ParabolicallyKappaNoncollapsedBelowScale S kappa rho) :
    ParabolicallyKappaNoncollapsedBelowScale
      (parabolicSolution (I := I) S tau R hR htau) kappa (Real.sqrt R * rho) := by
  refine ⟨mul_pos (Real.sqrt_pos.2 hR) hS.1, ?_⟩
  intro s B hscale hRm
  let B₀ := backBall S tau R hR htau s B
  have hradius : B₀.radius ≤ rho := by
    dsimp [B₀, backBall]
    apply (div_le_iff₀ (Real.sqrt_pos.2 hR)).2
    simpa only [mul_comm] using hscale
  have hRm₀ : B₀.IsParabolicallyRmControlled :=
    backBall_isParabolicallyRmControlled (I := I) S tau R hR htau s B hRm
  have hk₀ := hS.2 (parabolicFlowTime tau R htau s) B₀ hradius hRm₀
  have hk := parabolicBall_kappa (I := I) S tau R hR htau s B₀ kappa hk₀
  rwa [parabolicBall_back] at hk

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicallyKappaNoncollapsedBelowScale_parabolicSolution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicallyKappaNoncollapsedBelowScale_parabolicSolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicallyKappaNoncollapsedBelowScale_parabolicSolution ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicallyKappaNoncollapsedBelowScale_parabolicSolution

theorem parabolicNoLocalCollapsing_parabolicSolution
    (S : SolutionOn (I := I) (M := M) D)
    (tau R : Real) (hR : 0 < R) (htau : tau ∈ D.carrier)
    (rho : Real) (hS : ParabolicNoLocalCollapsing S rho) :
    ParabolicNoLocalCollapsing (parabolicSolution (I := I) S tau R hR htau)
      (Real.sqrt R * rho) := by
  rcases hS with ⟨kappa, hkappa, hbelow⟩
  exact ⟨kappa, hkappa,
    parabolicallyKappaNoncollapsedBelowScale_parabolicSolution
      (I := I) S tau R hR htau kappa rho hbelow⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicNoLocalCollapsing_parabolicSolution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicNoLocalCollapsing_parabolicSolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicNoLocalCollapsing_parabolicSolution ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicNoLocalCollapsing_parabolicSolution

end Scaling

end DifferentialGeometry.PDE.RicciFlow.Perelman

end

noncomputable section

open _root_.Set _root_.Bundle _root_.Submission.Bundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D} {time : D.FlowTime}

theorem isParabolicallyRmControlled_of_radius_le
    {B B' : FlowMetricBall S time} (hcenter : B'.center = B.center)
    (hradius : B'.radius ≤ B.radius) (hB : B.IsParabolicallyRmControlled) :
    B'.IsParabolicallyRmControlled := by
  have hsquare : B'.radius ^ 2 ≤ B.radius ^ 2 :=
    pow_le_pow_left₀ B'.radius_pos.le hradius 2
  have hinterval : _root_.Set.Icc ((time : ℝ) - B'.radius ^ 2) time ⊆
      Icc ((time : ℝ) - B.radius ^ 2) time := by
    intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩
  refine ⟨hinterval.trans hB.1, ?_⟩
  intro t ht x hx
  have hx' : x ∈ B.set := by
    change riemannianEDistOf (S.base.metric time) B.center x < ENNReal.ofReal B.radius
    change riemannianEDistOf (S.base.metric time) B'.center x < ENNReal.ofReal B'.radius at hx
    rw [hcenter] at hx
    exact hx.trans_le (ENNReal.ofReal_le_ofReal hradius)
  have hnorm : 0 ≤ rmNormSq S t x := normSq0S_nonneg _ _ _ _
  exact (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ B'.radius_pos.le hradius 4) hnorm).trans (hB.2 t (hinterval ht) x hx')

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.isParabolicallyRmControlled_of_radius_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.isParabolicallyRmControlled_of_radius_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.isParabolicallyRmControlled_of_radius_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.isParabolicallyRmControlled_of_radius_le

theorem exists_larger_isParabolicallyRmControlled_of_strict_curvature_bound
    (hS : IsSolutionOn S) (B : FlowMetricBall S time) {R : ℝ}
    (hBR : B.radius < R)
    (hcompact : IsCompact (riemannianClosedBallOf (S.base.metric time) B.center R))
    (hwindow : _root_.Set.Icc ((time : ℝ) - R ^ 2) time ⊆ D.carrier)
    (hstrict : ∀ t ∈ _root_.Set.Icc ((time : ℝ) - B.radius ^ 2) time,
      ∀ x ∈ riemannianClosedBallOf (S.base.metric time) B.center B.radius,
        B.radius ^ 4 * rmNormSq S t x < 1) :
    ∃ B' : FlowMetricBall S time, B'.center = B.center ∧
      B.radius < B'.radius ∧ B'.radius < R ∧ B'.IsParabolicallyRmControlled := by
  let K := riemannianClosedBallOf (S.base.metric time) B.center B.radius
  have hR : 0 < R := B.radius_pos.trans hBR
  let clip : ℝ → ℝ := fun r => _root_.Max.max 0 (_root_.Min.min r R)
  have hclip : Continuous clip := continuous_const.max (continuous_id.min continuous_const)
  have hcpos (r : ℝ) : 0 ≤ clip r := le_max_left _ _
  have hcle (r : ℝ) : clip r ≤ R := max_le hR.le (min_le_right _ _)
  have hceq (r : ℝ) (hr : 0 ≤ r) (hrR : r ≤ R) : clip r = r := by
    exact (congrArg (_root_.Max.max 0) (min_eq_left hrR)).trans (max_eq_right hr)
  have hK : IsCompact K := hcompact.of_isClosed_subset
    (Geometry.Metric.isClosed_riemannianClosedBallOf _ _ _)
    (fun x hx => hx.trans (ENNReal.ofReal_le_ofReal hBR.le))
  have hmaps : _root_.Set.MapsTo (fun p : ℝ × (ℝ × M) =>
      ((time : ℝ) - p.1 * (clip p.2.1) ^ 2, p.2.2))
      (_root_.Set.Icc (0 : ℝ) 1 ×ˢ _root_.Set.univ) (D.carrier ×ˢ _root_.Set.univ) := by
    intro p hp
    refine ⟨hwindow ⟨?_, ?_⟩, _root_.Set.mem_univ _⟩
    · have hpow : (clip p.2.1) ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (hcpos _) (hcle _) 2
      have hu : p.1 * (clip p.2.1) ^ 2 ≤ (clip p.2.1) ^ 2 :=
        mul_le_of_le_one_left (sq_nonneg _) hp.1.2
      linarith
    · exact sub_le_self _ (mul_nonneg hp.1.1 (sq_nonneg _))
  have hm : Continuous (fun p : ℝ × (ℝ × M) =>
      ((time : ℝ) - p.1 * (clip p.2.1) ^ 2, p.2.2)) :=
    (continuous_const.sub (continuous_fst.mul ((hclip.comp continuous_snd.fst).pow 2))).prodMk
      continuous_snd.snd
  have hcurv : ContinuousOn (fun p : ℝ × M => rmNormSq S p.1 p.2)
      (D.carrier ×ˢ _root_.Set.univ) := hS.continuousOn_rmNormSq
  have hf : ContinuousOn (fun p : ℝ × (ℝ × M) =>
      (clip p.2.1) ^ 4 * rmNormSq S ((time : ℝ) - p.1 * (clip p.2.1) ^ 2) p.2.2)
      (_root_.Set.Icc (0 : ℝ) 1 ×ˢ _root_.Set.univ) := by
    have hc := ContinuousOn.comp'
      (f := fun p : ℝ × (ℝ × M) => ((time : ℝ) - p.1 * (clip p.2.1) ^ 2, p.2.2))
      hcurv hm.continuousOn hmaps
    exact ((hclip.comp continuous_snd.fst).pow 4).continuousOn.mul hc
  have hstrict' : ∀ u ∈ _root_.Set.Icc (0 : ℝ) 1, ∀ x ∈ K,
      (clip B.radius) ^ 4 * rmNormSq S ((time : ℝ) - u * (clip B.radius) ^ 2) x < 1 := by
    intro u hu x hx
    rw [hceq B.radius B.radius_pos.le hBR.le]
    apply hstrict _ ⟨?_, ?_⟩ x hx
    · have hh := mul_le_of_le_one_left (sq_nonneg B.radius) hu.2
      linarith
    · exact sub_le_self _ (mul_nonneg hu.1 (sq_nonneg _))
  obtain ⟨η, hη, V, hV, hKV, hb⟩ :=
    hf.exists_pos_radius_open_superset_forall_lt _root_.CompactIccSpace.isCompact_Icc hK hstrict'
  obtain ⟨r₁, hBr₁, hr₁R, hball⟩ :=
    hcompact.exists_lt_lt_ofReal_sublevel_subset
      (Geometry.Riemannian.continuous_riemannianEDist (S.base.metric time) B.center).continuousOn
      hV hKV hBR
  obtain ⟨r₂, hBr₂, hr₂⟩ := exists_between
    (lt_min hBr₁ (lt_add_of_pos_right B.radius hη))
  have hr₂pos : 0 < r₂ := B.radius_pos.trans hBr₂
  let B' : FlowMetricBall S time := ⟨B.center, r₂, hr₂pos⟩
  have hr₂R : r₂ < R := (hr₂.trans_le (min_le_left _ _)).trans hr₁R
  refine ⟨B', rfl, hBr₂, hr₂R, ?_, ?_⟩
  · intro t ht
    apply hwindow
    refine ⟨?_, ht.2⟩
    have hp : r₂ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hr₂pos.le hr₂R.le 2
    have htlo : (time : ℝ) - r₂ ^ 2 ≤ t := ht.1
    linarith
  · intro t ht x hx
    have hrange : r₂ ∈ _root_.Set.Ioo (B.radius - η) (B.radius + η) :=
      ⟨by linarith, hr₂.trans_le (min_le_right _ _)⟩
    have hxV : x ∈ V := by
      apply hball
      change riemannianEDistOf (S.base.metric time) B.center x < ENNReal.ofReal r₂ at hx
      exact hx.le.trans (ENNReal.ofReal_le_ofReal (hr₂.trans_le (min_le_left _ _)).le)
    have hpow : 0 < r₂ ^ 2 := sq_pos_of_pos hr₂pos
    have hu : ((time : ℝ) - t) / r₂ ^ 2 ∈ _root_.Set.Icc (0 : ℝ) 1 := by
      refine ⟨div_nonneg (sub_nonneg.mpr ht.2) hpow.le, ?_⟩
      apply (div_le_one hpow).mpr
      have htlo : (time : ℝ) - r₂ ^ 2 ≤ t := ht.1
      linarith
    have hh := hb _ hu r₂ hrange x hxV
    rw [hceq r₂ hr₂pos.le hr₂R.le, div_mul_cancel₀ _ hpow.ne', sub_sub_cancel] at hh
    exact hh.le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.exists_larger_isParabolicallyRmControlled_of_strict_curvature_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.exists_larger_isParabolicallyRmControlled_of_strict_curvature_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.exists_larger_isParabolicallyRmControlled_of_strict_curvature_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.exists_larger_isParabolicallyRmControlled_of_strict_curvature_bound

theorem exists_curvature_contact_of_not_exists_larger_isParabolicallyRmControlled
    (hS : IsSolutionOn S) (B : FlowMetricBall S time) {R : ℝ}
    (hBR : B.radius < R)
    (hcompact : IsCompact (riemannianClosedBallOf (S.base.metric time) B.center R))
    (hwindow : _root_.Set.Icc ((time : ℝ) - R ^ 2) time ⊆ D.carrier)
    (hbound : ∀ t ∈ _root_.Set.Icc ((time : ℝ) - B.radius ^ 2) time,
      ∀ x ∈ riemannianClosedBallOf (S.base.metric time) B.center B.radius,
        B.radius ^ 4 * rmNormSq S t x ≤ 1)
    (hmax : ¬ ∃ B' : FlowMetricBall S time, B'.center = B.center ∧
      B.radius < B'.radius ∧ B'.radius < R ∧ B'.IsParabolicallyRmControlled) :
    ∃ t ∈ _root_.Set.Icc ((time : ℝ) - B.radius ^ 2) time,
      ∃ x ∈ riemannianClosedBallOf (S.base.metric time) B.center B.radius,
        B.radius ^ 4 * rmNormSq S t x = 1 := by
  by_contra hnone
  apply hmax
  apply exists_larger_isParabolicallyRmControlled_of_strict_curvature_bound hS B hBR hcompact hwindow
  intro t ht x hx
  exact lt_of_le_of_ne (hbound t ht x hx) (fun he => hnone ⟨t, ht, x, hx, he⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.exists_curvature_contact_of_not_exists_larger_isParabolicallyRmControlled then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.exists_curvature_contact_of_not_exists_larger_isParabolicallyRmControlled"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.exists_curvature_contact_of_not_exists_larger_isParabolicallyRmControlled ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.exists_curvature_contact_of_not_exists_larger_isParabolicallyRmControlled


end DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall
