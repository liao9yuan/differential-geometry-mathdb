import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.CutLocus.Injectivity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open _root_.Bornology _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Function _root_.Set
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.Submission.Topology

open _root_.Submission.DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.instBorelSpace_differentialGeometry target :: scope.openDecls } }

def lCutDomain
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x : M)
    (tau : Real) : Set E :=
  {Z | IsGreatest {sigma : Real | (Z, sigma) ∈ lMinDomain S T x} tau}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lCutDomain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lCutDomain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lCutDomain ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lCutDomain

def lCutImage
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x : M)
    (tau : Real) : Set M :=
  (fun Z : E ↦ lExp S T x Z tau) '' lCutDomain S T x tau

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lCutImage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lCutImage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lCutImage ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lCutImage

def lCutConj
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x : M)
    (tau : Real) : Set M :=
  {y | ∃ Z : E, Z ∈ lCutDomain S T x tau ∧
    IsLConjugate S T x Z tau ∧ lExp S T x Z tau = y}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lCutConj then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lCutConj"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lCutConj ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lCutConj

def lCutMulti
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x : M)
    (tau : Real) : Set M :=
  {y | ∃ Z : E, Z ∈ lCutDomain S T x tau ∧
    ∃ W : TangentSpace I x, W ≠ Z ∧
      ((W : E), tau) ∈ lMinDomain S T x ∧
        lExp S T x W tau = lExp S T x Z tau ∧ lExp S T x Z tau = y}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lCutMulti then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lCutMulti"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lCutMulti ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lCutMulti

omit [NeZero (Module.finrank Real E)] [CompactSpace M] in
theorem mem_lCutDomain
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x : M)
    (tau : Real) (Z : E) :
    Z ∈ lCutDomain S T x tau ↔
      (Z, tau) ∈ lMinDomain S T x ∧ Z ∉ lInjDomain S T x tau := by
  constructor
  · intro hcut
    refine ⟨hcut.1, ?_⟩
    rintro ⟨sigma, hsigma, hmin⟩
    exact (not_lt_of_ge (hcut.2 hmin)) hsigma
  · rintro ⟨hmin, hnot⟩
    refine ⟨hmin, ?_⟩
    intro sigma hminSigma
    apply le_of_not_gt
    intro hlt
    exact hnot ⟨sigma, hlt, hminSigma⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.mem_lCutDomain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.mem_lCutDomain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.mem_lCutDomain ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.mem_lCutDomain

omit [NeZero (Module.finrank ℝ E)] in
theorem lMinSlice_closed
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (tau : Real) (htau : 0 < tau) :
    IsClosed {Z : E | (Z, tau) ∈ lMinDomain S T x} := by
  rw [← isSeqClosed_iff_isClosed]
  intro Z Z₀ hmin hZ
  have hdom0 : (Z 0, tau) ∈ lExpPosDom S T x :=
    ((mem_lMinDomain S T x (Z 0) tau).1 (hmin 0)).1
  let b : Real := Real.sqrt tau
  have hb : 0 ≤ b := by
    exact Real.sqrt_nonneg _
  have hb2 : b ^ 2 = tau := by
    simpa only [b] using Real.sq_sqrt htau.le
  have hslab : _root_.Set.Icc (T - b ^ 2) T ⊆ D.regular := by
    intro r hr
    have hnonneg : 0 ≤ T - r := by
      linarith [hr.2]
    have hle : T - r ≤ tau := by
      rw [hb2] at hr
      linarith [hr.1]
    have hsqrt : Real.sqrt (T - r) ∈ _root_.Set.Icc (0 : Real) (Real.sqrt tau) :=
      ⟨Real.sqrt_nonneg _, Real.sqrt_le_sqrt hle⟩
    have hreg := lExpPosDom_regularity S T x (Z 0) hdom0 hsqrt
    have heq : T - (Real.sqrt (T - r)) ^ 2 = r := by
      rw [Real.sq_sqrt hnonneg]
      ring
    simpa only [heq] using hreg
  have hreg : b ∈ lRegularizedDomain S T x Z₀ :=
    mem_lRegularizedDomain_of_time_slab S hS T x Z₀ b hb hslab
  have hdom : (Z₀, tau) ∈ lExpPosDom S T x :=
    (mem_lExpPosDom S T x Z₀ tau).2 ⟨htau, htau.le, by
      simpa only [b] using hreg⟩
  exact lMinimizingVector_lim S hS T x hmin hZ hdom

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lMinSlice_closed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lMinSlice_closed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lMinSlice_closed ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lMinSlice_closed

theorem lCutDom_closed
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (tau : Real) (htau : 0 < tau) :
    IsClosed (lCutDomain S T x tau) := by
  have hslice := lMinSlice_closed S hS T x tau htau
  have hinj := (lInj_isOpen S hS T x tau).isClosed_compl
  rw [show lCutDomain S T x tau =
      {Z : E | (Z, tau) ∈ lMinDomain S T x} ∩ (lInjDomain S T x tau)ᶜ by
    ext Z
    simpa only [_root_.Set.mem_ofPred_eq, _root_.Set.mem_inter_iff, _root_.Set.mem_compl_iff] using
      (mem_lCutDomain S T x tau Z)]
  exact hslice.inter hinj

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lCutDom_closed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lCutDom_closed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lCutDom_closed ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lCutDom_closed

theorem lCutDom_meas
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (tau : Real) (htau : 0 < tau) :
    MeasurableSet (lCutDomain S T x tau) :=
  (lCutDom_closed S hS T x tau htau).measurableSet

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lCutDom_meas then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lCutDom_meas"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lCutDom_meas ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lCutDom_meas

theorem lCut_split
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (tau : Real) :
    lCutImage S T x tau = lCutConj S T x tau ∪ lCutMulti S T x tau := by
  ext y
  constructor
  · rintro ⟨Z, hcut, rfl⟩
    rcases isLConjugate_or_exists_distinct_minimizer_same_endpoint S hS T x Z tau hcut with hconj | ⟨W, hWne, hWmin, hend⟩
    · exact Or.inl ⟨Z, hcut, hconj, rfl⟩
    · exact Or.inr ⟨Z, hcut, W, hWne, hWmin, hend, rfl⟩
  · rintro (⟨Z, hcut, hconj, rfl⟩ | ⟨Z, hcut, W, hWne, hWmin, hend, rfl⟩)
    · exact ⟨Z, hcut, rfl⟩
    · exact ⟨Z, hcut, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lCut_split then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lCut_split"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lCut_split ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lCut_split

end DifferentialGeometry.PDE.RicciFlow.Perelman
