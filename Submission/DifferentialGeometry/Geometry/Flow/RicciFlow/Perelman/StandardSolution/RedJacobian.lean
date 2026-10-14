import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Jacobian.Monotonicity
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.MinNonconjugacy
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.RedLengthRay
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ExpDensity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.BranchTrace
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.BranchTraceBound

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.Submission.Topology _root_.Submission.DifferentialGeometry.Topology

namespace DifferentialGeometry.PDE.RicciFlow

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

private theorem regularized_costs_bdd_of_min_rm
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (K T : ℝ) (x : M)
    {Z : TangentSpace I x} {sigma : ℝ}
    (hmin : (Z, sigma) ∈ lMinDomain S T x)
    (hRm : ∀ t ∈ _root_.Set.Icc (T - sigma) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric t) z 4
        (S.base.rm04 t z) ≤ K) :
    BddBelow {r : ℝ | ∃ alpha : ℝ → M,
      ContMDiff 𝓘(ℝ, ℝ) I 1 alpha ∧
        alpha 0 = x ∧
        alpha (Real.sqrt sigma) = lExp S T x Z sigma ∧
        lRegularizedAction S T alpha 0 (Real.sqrt sigma) = r} := by
  have hsigma : 0 < sigma := lMinDomain_pos S T x Z sigma hmin
  have hdom : (Z, sigma) ∈ lExpPosDom S T x :=
    ((mem_lMinDomain S T x Z sigma).1 hmin).1
  have hreg : _root_.Set.Icc (T - sigma) T ⊆ D.regular := by
    intro t ht
    have hnonneg : 0 ≤ T - t := sub_nonneg.mpr ht.2
    have hback : T - t ≤ sigma := by linarith [ht.1]
    have hclock := lExpPosDom_regularity S T x Z hdom
      (show Real.sqrt (T - t) ∈ _root_.Set.Icc (0 : ℝ) (Real.sqrt sigma) from
        ⟨Real.sqrt_nonneg _, Real.sqrt_le_sqrt hback⟩)
    rwa [Real.sq_sqrt hnonneg, sub_sub_cancel] at hclock
  exact lRegularizedCosts_bdd_rm (I := I) S hS K T 0 (Real.sqrt sigma)
    le_rfl (Real.sqrt_nonneg sigma)
    (by simpa only [Real.sq_sqrt hsigma.le] using hreg)
    (by simpa only [Real.sq_sqrt hsigma.le] using hRm)
    x (lExp S T x Z sigma)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.regularized_costs_bdd_of_min_rm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.regularized_costs_bdd_of_min_rm target :: scope.openDecls } }

theorem lRedLog_hasDeriv_of_bdd
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (T : ℝ) (x : M)
    {Z : TangentSpace I x} {sigma tau : ℝ}
    (hmin : (Z, sigma) ∈ lMinDomain S T x)
    (htau : 0 < tau) (hlt : tau < sigma)
    (hbddSigma : BddBelow {r : ℝ | ∃ alpha : ℝ → M,
      ContMDiff 𝓘(ℝ, ℝ) I 1 alpha ∧
        alpha 0 = x ∧
        alpha (Real.sqrt sigma) = lExp S T x Z sigma ∧
        lRegularizedAction S T alpha 0 (Real.sqrt sigma) = r}) :
    HasDerivAt (lRedLog S T x Z)
      ((1 / 2 : ℝ) * Matrix.trace
          ((lExpGram S T x Z tau)⁻¹ * lExpGramDeriv S T x Z tau) +
        lK S T (lRegularizedCurve S T x Z) (Real.sqrt tau) /
          (2 * tau * Real.sqrt tau) -
        (Module.finrank ℝ E : ℝ) / (2 * tau)) tau := by
  have hdom : (Z, tau) ∈ lExpPosDom S T x :=
    lExpPosDom_down S T x Z
      (((mem_lMinDomain S T x Z sigma).1 hmin).1)
      htau hlt.le
  have hnconj : ¬ IsLConjugate S T x Z tau :=
    lMinVec_nconj_lt_of_bdd (I := I) S hS T x hmin hlt hbddSigma
  have hJ :=
    lExpJac_log_hasDeriv_of_nonconj
      (I := I) S hS T x Z tau hdom hnconj
  have hL :=
    redLength_ray_K_of_bdd (I := I) S hS T x hmin htau hlt hbddSigma
  let n2 : ℝ := (Module.finrank ℝ E : ℝ) / 2
  have htlog :
      HasDerivAt (fun r : ℝ ↦ n2 * Real.log r)
        (n2 * tau⁻¹) tau :=
    (Real.hasDerivAt_log htau.ne').const_mul n2
  have hout :=
    ((hJ.sub hL).sub htlog).sub_const
      (n2 * Real.log (4 * Real.pi))
  change HasDerivAt (lRedLog S T x Z) _ tau at hout
  apply hout.congr_deriv
  dsimp only [n2]
  field_simp [htau.ne', (Real.sqrt_pos.2 htau).ne']
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.lRedLog_hasDeriv_of_bdd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.lRedLog_hasDeriv_of_bdd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.lRedLog_hasDeriv_of_bdd ``Submission.DifferentialGeometry.PDE.RicciFlow.lRedLog_hasDeriv_of_bdd

theorem lRedJac_hasDeriv_of_bdd
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (T : ℝ) (x : M)
    {Z : TangentSpace I x} {sigma tau : ℝ}
    (hmin : (Z, sigma) ∈ lMinDomain S T x)
    (htau : 0 < tau) (hlt : tau < sigma)
    (hbddSigma : BddBelow {r : ℝ | ∃ alpha : ℝ → M,
      ContMDiff 𝓘(ℝ, ℝ) I 1 alpha ∧
        alpha 0 = x ∧
        alpha (Real.sqrt sigma) = lExp S T x Z sigma ∧
        lRegularizedAction S T alpha 0 (Real.sqrt sigma) = r}) :
    HasDerivAt (lReducedJacobian S T x Z)
      (lReducedJacobian S T x Z tau *
        ((1 / 2 : ℝ) * Matrix.trace
            ((lExpGram S T x Z tau)⁻¹ * lExpGramDeriv S T x Z tau) +
          lK S T (lRegularizedCurve S T x Z) (Real.sqrt tau) /
            (2 * tau * Real.sqrt tau) -
          (Module.finrank ℝ E : ℝ) / (2 * tau))) tau := by
  exact (lRedLog_hasDeriv_of_bdd
      (I := I) S hS T x hmin htau hlt hbddSigma).exp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.lRedJac_hasDeriv_of_bdd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.lRedJac_hasDeriv_of_bdd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.lRedJac_hasDeriv_of_bdd ``Submission.DifferentialGeometry.PDE.RicciFlow.lRedJac_hasDeriv_of_bdd

theorem lRedLog_hasDeriv_of_rm
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (K T : ℝ) (x : M)
    {Z : TangentSpace I x} {sigma tau : ℝ}
    (hmin : (Z, sigma) ∈ lMinDomain S T x)
    (htau : 0 < tau) (hlt : tau < sigma)
    (hRm : ∀ t ∈ _root_.Set.Icc (T - sigma) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric t) z 4
        (S.base.rm04 t z) ≤ K) :
    HasDerivAt (lRedLog S T x Z)
      ((1 / 2 : ℝ) * Matrix.trace
          ((lExpGram S T x Z tau)⁻¹ * lExpGramDeriv S T x Z tau) +
        lK S T (lRegularizedCurve S T x Z) (Real.sqrt tau) /
          (2 * tau * Real.sqrt tau) -
        (Module.finrank ℝ E : ℝ) / (2 * tau)) tau := by
  exact lRedLog_hasDeriv_of_bdd S hS T x hmin htau hlt
    (regularized_costs_bdd_of_min_rm S hS K T x hmin hRm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.lRedLog_hasDeriv_of_rm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.lRedLog_hasDeriv_of_rm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.lRedLog_hasDeriv_of_rm ``Submission.DifferentialGeometry.PDE.RicciFlow.lRedLog_hasDeriv_of_rm

theorem lRedJac_hasDeriv_of_rm
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (K T : ℝ) (x : M)
    {Z : TangentSpace I x} {sigma tau : ℝ}
    (hmin : (Z, sigma) ∈ lMinDomain S T x)
    (htau : 0 < tau) (hlt : tau < sigma)
    (hRm : ∀ t ∈ _root_.Set.Icc (T - sigma) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric t) z 4
        (S.base.rm04 t z) ≤ K) :
    HasDerivAt (lReducedJacobian S T x Z)
      (lReducedJacobian S T x Z tau *
        ((1 / 2 : ℝ) * Matrix.trace
            ((lExpGram S T x Z tau)⁻¹ * lExpGramDeriv S T x Z tau) +
          lK S T (lRegularizedCurve S T x Z) (Real.sqrt tau) /
            (2 * tau * Real.sqrt tau) -
          (Module.finrank ℝ E : ℝ) / (2 * tau))) tau := by
  exact lRedJac_hasDeriv_of_bdd S hS T x hmin htau hlt
    (regularized_costs_bdd_of_min_rm S hS K T x hmin hRm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.lRedJac_hasDeriv_of_rm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.lRedJac_hasDeriv_of_rm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.lRedJac_hasDeriv_of_rm ``Submission.DifferentialGeometry.PDE.RicciFlow.lRedJac_hasDeriv_of_rm

variable [NeZero (Module.finrank ℝ E)]

theorem lRedLog_deriv_nonpos_of_bdd
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (T : ℝ) (x : M)
    {Z : TangentSpace I x} {sigma tau : ℝ}
    (hmin : (Z, sigma) ∈ lMinDomain S T x)
    (htau : 0 < tau) (hlt : tau < sigma)
    (hbddSigma : BddBelow {r : ℝ | ∃ alpha : ℝ → M,
      ContMDiff 𝓘(ℝ, ℝ) I 1 alpha ∧
        alpha 0 = x ∧
        alpha (Real.sqrt sigma) = lExp S T x Z sigma ∧
        lRegularizedAction S T alpha 0 (Real.sqrt sigma) = r}) :
    deriv (lRedLog S T x Z) tau ≤ 0 := by
  rw [(lRedLog_hasDeriv_of_bdd
    (I := I) S hS T x hmin htau hlt hbddSigma).deriv]
  obtain ⟨hdom, hnconj, hbound⟩ :=
    lActBranch_trace_le_of_bdd (I := I) S hS T x hmin htau hlt
      hbddSigma
  have htrace :=
    lExpTrace_eq_branch (I := I) S hS T x Z tau hdom hnconj
  rw [htrace]
  let A : ℝ :=
    metricTracePair0SAt (I := I) (S.base.metric (T - tau))
      (hessTensorAt (I := I) (S.base.metric (T - tau))
        (lActBranch S hS T x Z tau hdom hnconj)
        (lExp S T x Z tau))
  change A / (2 * Real.sqrt tau) ≤
    (Module.finrank ℝ E : ℝ) / (2 * tau) -
      S.scalar (T - tau) (lExp S T x Z tau) -
      lK S T (lRegularizedCurve S T x Z) (Real.sqrt tau) /
        (2 * tau * Real.sqrt tau) at hbound
  change (1 / (2 * Real.sqrt tau)) * A +
      S.scalar (T - tau) (lExp S T x Z tau) +
      lK S T (lRegularizedCurve S T x Z) (Real.sqrt tau) /
        (2 * tau * Real.sqrt tau) -
      (Module.finrank ℝ E : ℝ) / (2 * tau) ≤ 0
  have hfrac :
      (1 / (2 * Real.sqrt tau)) * A =
        A / (2 * Real.sqrt tau) := by ring
  rw [hfrac]
  linarith only [hbound]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.lRedLog_deriv_nonpos_of_bdd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.lRedLog_deriv_nonpos_of_bdd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.lRedLog_deriv_nonpos_of_bdd ``Submission.DifferentialGeometry.PDE.RicciFlow.lRedLog_deriv_nonpos_of_bdd

theorem lRedJac_deriv_nonpos_of_bdd
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (T : ℝ) (x : M)
    {Z : TangentSpace I x} {sigma tau : ℝ}
    (hmin : (Z, sigma) ∈ lMinDomain S T x)
    (htau : 0 < tau) (hlt : tau < sigma)
    (hbddSigma : BddBelow {r : ℝ | ∃ alpha : ℝ → M,
      ContMDiff 𝓘(ℝ, ℝ) I 1 alpha ∧
        alpha 0 = x ∧
        alpha (Real.sqrt sigma) = lExp S T x Z sigma ∧
        lRegularizedAction S T alpha 0 (Real.sqrt sigma) = r}) :
    deriv (lReducedJacobian S T x Z) tau ≤ 0 := by
  have hlog :=
    lRedLog_deriv_nonpos_of_bdd
      (I := I) S hS T x hmin htau hlt hbddSigma
  rw [(lRedLog_hasDeriv_of_bdd
    (I := I) S hS T x hmin htau hlt hbddSigma).deriv] at hlog
  rw [(lRedJac_hasDeriv_of_bdd
    (I := I) S hS T x hmin htau hlt hbddSigma).deriv]
  have hpos : 0 ≤ lReducedJacobian S T x Z tau := by
    exact (Real.exp_pos _).le
  exact mul_nonpos_of_nonneg_of_nonpos hpos hlog

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.lRedJac_deriv_nonpos_of_bdd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.lRedJac_deriv_nonpos_of_bdd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.lRedJac_deriv_nonpos_of_bdd ``Submission.DifferentialGeometry.PDE.RicciFlow.lRedJac_deriv_nonpos_of_bdd

theorem lRedJac_antitoneOn_of_bdd
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (T : ℝ) (x : M)
    {Z : TangentSpace I x} {sigma : ℝ}
    (hmin : (Z, sigma) ∈ lMinDomain S T x)
    (hbddSigma : BddBelow {r : ℝ | ∃ alpha : ℝ → M,
      ContMDiff 𝓘(ℝ, ℝ) I 1 alpha ∧
        alpha 0 = x ∧
        alpha (Real.sqrt sigma) = lExp S T x Z sigma ∧
        lRegularizedAction S T alpha 0 (Real.sqrt sigma) = r}) :
    AntitoneOn (lReducedJacobian S T x Z) (_root_.Set.Ioo (0 : ℝ) sigma) := by
  have hdiff :
      DifferentiableOn ℝ (lReducedJacobian S T x Z) (_root_.Set.Ioo (0 : ℝ) sigma) := by
    intro tau htau
    exact (lRedJac_hasDeriv_of_bdd
      (I := I) S hS T x hmin htau.1 htau.2 hbddSigma).differentiableAt.differentiableWithinAt
  apply antitoneOn_of_deriv_nonpos
    (convex_Ioo (0 : ℝ) sigma) hdiff.continuousOn
  · exact hdiff.mono interior_subset
  · intro tau htau
    have htau' : tau ∈ _root_.Set.Ioo (0 : ℝ) sigma := interior_subset htau
    exact lRedJac_deriv_nonpos_of_bdd
      (I := I) S hS T x hmin htau'.1 htau'.2 hbddSigma

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.lRedJac_antitoneOn_of_bdd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.lRedJac_antitoneOn_of_bdd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.lRedJac_antitoneOn_of_bdd ``Submission.DifferentialGeometry.PDE.RicciFlow.lRedJac_antitoneOn_of_bdd

theorem lRedLog_deriv_nonpos_of_rm
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (K T : ℝ) (x : M)
    {Z : TangentSpace I x} {sigma tau : ℝ}
    (hmin : (Z, sigma) ∈ lMinDomain S T x)
    (htau : 0 < tau) (hlt : tau < sigma)
    (hRm : ∀ t ∈ _root_.Set.Icc (T - sigma) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric t) z 4
        (S.base.rm04 t z) ≤ K) :
    deriv (lRedLog S T x Z) tau ≤ 0 := by
  exact lRedLog_deriv_nonpos_of_bdd S hS T x hmin htau hlt
    (regularized_costs_bdd_of_min_rm S hS K T x hmin hRm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.lRedLog_deriv_nonpos_of_rm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.lRedLog_deriv_nonpos_of_rm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.lRedLog_deriv_nonpos_of_rm ``Submission.DifferentialGeometry.PDE.RicciFlow.lRedLog_deriv_nonpos_of_rm

theorem lRedJac_deriv_nonpos_of_rm
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (K T : ℝ) (x : M)
    {Z : TangentSpace I x} {sigma tau : ℝ}
    (hmin : (Z, sigma) ∈ lMinDomain S T x)
    (htau : 0 < tau) (hlt : tau < sigma)
    (hRm : ∀ t ∈ _root_.Set.Icc (T - sigma) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric t) z 4
        (S.base.rm04 t z) ≤ K) :
    deriv (lReducedJacobian S T x Z) tau ≤ 0 := by
  exact lRedJac_deriv_nonpos_of_bdd S hS T x hmin htau hlt
    (regularized_costs_bdd_of_min_rm S hS K T x hmin hRm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.lRedJac_deriv_nonpos_of_rm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.lRedJac_deriv_nonpos_of_rm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.lRedJac_deriv_nonpos_of_rm ``Submission.DifferentialGeometry.PDE.RicciFlow.lRedJac_deriv_nonpos_of_rm

theorem lRedJac_antitoneOn_of_rm
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (K T : ℝ) (x : M)
    {Z : TangentSpace I x} {sigma : ℝ}
    (hmin : (Z, sigma) ∈ lMinDomain S T x)
    (hRm : ∀ t ∈ _root_.Set.Icc (T - sigma) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric t) z 4
        (S.base.rm04 t z) ≤ K) :
    AntitoneOn (lReducedJacobian S T x Z) (_root_.Set.Ioo (0 : ℝ) sigma) := by
  exact lRedJac_antitoneOn_of_bdd S hS T x hmin
    (regularized_costs_bdd_of_min_rm S hS K T x hmin hRm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.lRedJac_antitoneOn_of_rm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.lRedJac_antitoneOn_of_rm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.lRedJac_antitoneOn_of_rm ``Submission.DifferentialGeometry.PDE.RicciFlow.lRedJac_antitoneOn_of_rm

end DifferentialGeometry.PDE.RicciFlow
