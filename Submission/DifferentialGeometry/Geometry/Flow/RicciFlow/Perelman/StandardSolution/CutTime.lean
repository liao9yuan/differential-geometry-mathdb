import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.CutLocus.Defs
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.MinVector
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.MinPrefix

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
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.Submission.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

private theorem lInjDomain_eq_iUnion_rat_of_down
    (S : SolutionOn (I := I) (M := M) D)
    (T : ℝ) (x : M) (tau : ℝ)
    (hdown : ∀ {Z : E} {sigma rho : ℝ},
      (Z, sigma) ∈ lMinDomain S T x →
      0 < rho → rho ≤ sigma →
      (Z, rho) ∈ lMinDomain S T x) :
    lInjDomain S T x tau =
      ⋃ q : {q : ℚ // _root_.Max.max tau 0 < (q : ℝ)},
        {Z : E | (Z, (q.1 : ℝ)) ∈ lMinDomain S T x} := by
  ext Z
  change (∃ sigma > tau, (Z, sigma) ∈ lMinDomain S T x) ↔ _
  constructor
  · rintro ⟨sigma, hsigma, hmin⟩
    have hsigmaPos : 0 < sigma :=
      lMinDomain_pos S T x Z sigma hmin
    obtain ⟨q, hqlo, hqhi⟩ :=
      exists_rat_btwn (max_lt hsigma hsigmaPos)
    refine mem_iUnion.mpr ⟨⟨q, hqlo⟩, ?_⟩
    exact hdown hmin ((le_max_right tau 0).trans_lt hqlo) hqhi.le
  · intro hZ
    rcases mem_iUnion.mp hZ with ⟨q, hq⟩
    exact ⟨(q.1 : ℝ), (le_max_left tau 0).trans_lt q.2, hq⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.lInjDomain_eq_iUnion_rat_of_down
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.lInjDomain_eq_iUnion_rat_of_down target :: scope.openDecls } }

private theorem lCutDomain_eq_diff
    (S : SolutionOn (I := I) (M := M) D)
    (T : ℝ) (x : M) (tau : ℝ) :
    lCutDomain S T x tau =
      {Z : E | (Z, tau) ∈ lMinDomain S T x} \
        lInjDomain S T x tau := by
  ext Z
  exact mem_lCutDomain S T x tau Z

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.lCutDomain_eq_diff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.lCutDomain_eq_diff target :: scope.openDecls } }

noncomputable def lCutTime
    (S : SolutionOn (I := I) (M := M) D)
    (T : ℝ) (x : M) (Z : E) : ℝ≥0∞ :=
  ⨆ sigma : {sigma : ℝ // (Z, sigma) ∈ lMinDomain S T x},
    ENNReal.ofReal sigma.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.lCutTime then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.lCutTime"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.lCutTime ``Submission.DifferentialGeometry.PDE.RicciFlow.lCutTime

theorem ofReal_lt_lCutTime_iff
    (S : SolutionOn (I := I) (M := M) D)
    (T : ℝ) (x : M) (tau : ℝ) (Z : E) :
    ENNReal.ofReal tau < lCutTime S T x Z ↔
      Z ∈ lInjDomain S T x tau := by
  unfold lCutTime
  rw [lt_iSup_iff]
  constructor
  · rintro ⟨sigma, hsigma⟩
    refine ⟨sigma.1, ?_, sigma.2⟩
    exact (ENNReal.ofReal_lt_ofReal_iff
      (lMinDomain_pos S T x Z sigma.1 sigma.2)).1 hsigma
  · rintro ⟨sigma, hsigma, hmin⟩
    refine ⟨⟨sigma, hmin⟩, ?_⟩
    exact (ENNReal.ofReal_lt_ofReal_iff
      (lMinDomain_pos S T x Z sigma hmin)).2 hsigma

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ofReal_lt_lCutTime_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ofReal_lt_lCutTime_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ofReal_lt_lCutTime_iff ``Submission.DifferentialGeometry.PDE.RicciFlow.ofReal_lt_lCutTime_iff

theorem mem_lCutDomain_iff_lCutTime_eq
    (S : SolutionOn (I := I) (M := M) D)
    (T : ℝ) (x : M) (tau : ℝ) (Z : E) :
    Z ∈ lCutDomain S T x tau ↔
      (Z, tau) ∈ lMinDomain S T x ∧ lCutTime S T x Z = ENNReal.ofReal tau := by
  rw [mem_lCutDomain S T x tau Z]
  constructor
  · rintro ⟨hmin, hnot⟩
    refine ⟨hmin, le_antisymm ?_ ?_⟩
    · exact le_of_not_gt (fun h => hnot ((ofReal_lt_lCutTime_iff S T x tau Z).mp h))
    · exact le_iSup_of_le (⟨tau, hmin⟩ : {sigma : ℝ // (Z, sigma) ∈ lMinDomain S T x}) le_rfl
  · rintro ⟨hmin, heq⟩
    refine ⟨hmin, ?_⟩
    intro hinj
    have hlt := (ofReal_lt_lCutTime_iff S T x tau Z).mpr hinj
    rw [heq] at hlt
    exact (lt_irrefl _) hlt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.mem_lCutDomain_iff_lCutTime_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.mem_lCutDomain_iff_lCutTime_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.mem_lCutDomain_iff_lCutTime_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.mem_lCutDomain_iff_lCutTime_eq

section Measurable

variable [MeasurableSpace E]

private theorem lInjDomain_meas_of_down
    (S : SolutionOn (I := I) (M := M) D)
    (T : ℝ) (x : M) (tau : ℝ)
    (hdown : ∀ {Z : E} {sigma rho : ℝ},
      (Z, sigma) ∈ lMinDomain S T x →
      0 < rho → rho ≤ sigma →
      (Z, rho) ∈ lMinDomain S T x)
    (hslice : ∀ rho : ℝ, 0 < rho →
      MeasurableSet {Z : E | (Z, rho) ∈ lMinDomain S T x}) :
    MeasurableSet (lInjDomain S T x tau) := by
  rw [lInjDomain_eq_iUnion_rat_of_down S T x tau hdown]
  apply MeasurableSet.iUnion
  intro q
  exact hslice (q.1 : ℝ) ((le_max_right tau 0).trans_lt q.2)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.lInjDomain_meas_of_down
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.lInjDomain_meas_of_down target :: scope.openDecls } }

private theorem lCutTime_measurable_of_inj
    (S : SolutionOn (I := I) (M := M) D)
    (T : ℝ) (x : M)
    (hinj : ∀ tau : ℝ,
      MeasurableSet (lInjDomain S T x tau)) :
    Measurable (lCutTime S T x) := by
  apply measurable_of_Ioi (f := lCutTime S T x)
  intro a
  by_cases ha : a = (∞ : ℝ≥0∞)
  · subst a
    simpa only [_root_.Set.Ioi_top, _root_.Set.preimage_empty] using
      (MeasurableSet.empty : MeasurableSet (∅ : Set E))
  · have heq :
        (lCutTime S T x) ⁻¹' _root_.Set.Ioi a =
          lInjDomain S T x a.toReal := by
      ext Z
      change a < lCutTime S T x Z ↔ _
      simpa only [ENNReal.ofReal_toReal ha] using
        (ofReal_lt_lCutTime_iff S T x a.toReal Z)
    rw [heq]
    exact hinj a.toReal

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.lCutTime_measurable_of_inj
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.lCutTime_measurable_of_inj target :: scope.openDecls } }

end Measurable

private theorem downward_minimality_of_regular_slab_bounds
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → _root_.Set.Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ _root_.Set.Icc (T - sigma) T, ∀ z : M,
        normSq0S (I := I) (S.base.metric t) z 4 (S.base.rm04 t z) ≤ K) :
    ∀ {Z : E} {sigma rho : ℝ}, (Z, sigma) ∈ lMinDomain S T x →
      0 < rho → rho ≤ sigma → (Z, rho) ∈ lMinDomain S T x := by
  intro Z sigma rho hmin hrho hle
  have hdom := ((mem_lMinDomain S T x Z sigma).mp hmin).1
  have hsigma := lMinDomain_pos S T x Z sigma hmin
  have hreg : _root_.Set.Icc (T - sigma) T ⊆ D.regular := by
    intro t ht
    have ht0 : 0 ≤ T - t := sub_nonneg.mpr ht.2
    have htS : T - t ≤ sigma := by linarith only [ht.1]
    have hsqrt : Real.sqrt (T - t) ∈ _root_.Set.Icc (0 : ℝ) (Real.sqrt sigma) :=
      ⟨Real.sqrt_nonneg _, Real.sqrt_le_sqrt htS⟩
    have h := lExpPosDom_regularity S T x Z hdom hsqrt
    have heq : T - (Real.sqrt (T - t)) ^ 2 = t := by rw [Real.sq_sqrt ht0]; ring
    simpa only [heq] using h
  obtain ⟨K, hK⟩ := hRm sigma hsigma hreg
  exact lMinDomain_down_of_rm S hS K T x Z hmin hrho hle hK

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.downward_minimality_of_regular_slab_bounds
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.downward_minimality_of_regular_slab_bounds target :: scope.openDecls } }

theorem measurableSet_lInjDomain_of_rm
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → _root_.Set.Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ _root_.Set.Icc (T - sigma) T, ∀ z : M,
        normSq0S (I := I) (S.base.metric t) z 4 (S.base.rm04 t z) ≤ K)
    (tau : ℝ) : @MeasurableSet E (borel E) (lInjDomain S T x tau) := by
  let : MeasurableSpace E := borel E
  exact lInjDomain_meas_of_down S T x tau
    (downward_minimality_of_regular_slab_bounds S hS T x hRm)
    (fun rho _hrho => measurableSet_lMinDomain_slice_of_rm S hS T x hRm rho)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.measurableSet_lInjDomain_of_rm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.measurableSet_lInjDomain_of_rm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.measurableSet_lInjDomain_of_rm ``Submission.DifferentialGeometry.PDE.RicciFlow.measurableSet_lInjDomain_of_rm

theorem measurableSet_lCutDomain_of_rm
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → _root_.Set.Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ _root_.Set.Icc (T - sigma) T, ∀ z : M,
        normSq0S (I := I) (S.base.metric t) z 4 (S.base.rm04 t z) ≤ K)
    (tau : ℝ) : @MeasurableSet E (borel E) (lCutDomain S T x tau) := by
  let : MeasurableSpace E := borel E
  rw [lCutDomain_eq_diff S T x tau]
  exact (measurableSet_lMinDomain_slice_of_rm S hS T x hRm tau).diff
    (measurableSet_lInjDomain_of_rm S hS T x hRm tau)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.measurableSet_lCutDomain_of_rm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.measurableSet_lCutDomain_of_rm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.measurableSet_lCutDomain_of_rm ``Submission.DifferentialGeometry.PDE.RicciFlow.measurableSet_lCutDomain_of_rm

theorem measurable_lCutTime_of_rm
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → _root_.Set.Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ _root_.Set.Icc (T - sigma) T, ∀ z : M,
        normSq0S (I := I) (S.base.metric t) z 4 (S.base.rm04 t z) ≤ K) :
    @Measurable E ℝ≥0∞ (borel E) (borel ℝ≥0∞) (lCutTime S T x) := by
  let : MeasurableSpace E := borel E
  exact lCutTime_measurable_of_inj S T x
    (measurableSet_lInjDomain_of_rm S hS T x hRm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.measurable_lCutTime_of_rm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.measurable_lCutTime_of_rm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.measurable_lCutTime_of_rm ``Submission.DifferentialGeometry.PDE.RicciFlow.measurable_lCutTime_of_rm
end DifferentialGeometry.PDE.RicciFlow
