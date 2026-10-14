import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.AreaEvolution
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Topology.Order.Compact

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

private def factor (rho : ℝ → ℝ) (s t : ℝ) : ℝ :=
  Real.exp (∫ w in s..t, rho w)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.factor
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.factor target :: scope.openDecls } }

private def affine (rho : ℝ → ℝ) (s t z : ℝ) : ℝ :=
  (factor rho s t)⁻¹ * (z - 2 * Real.pi * ∫ v in s..t, factor rho s v)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.affine
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.affine target :: scope.openDecls } }

private theorem rho_int {rho : ℝ → ℝ} {a b s t : ℝ}
    (hc : ContinuousOn rho (_root_.Set.Icc a b)) (hs : s ∈ _root_.Set.Icc a b) (ht : t ∈ _root_.Set.Icc a b) :
    IntervalIntegrable rho _root_.MeasureTheory.MeasureSpace.volume s t :=
  (hc.mono (_root_.Set.uIcc_subset_Icc hs ht)).intervalIntegrable

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.rho_int
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.rho_int target :: scope.openDecls } }

private theorem primitive_deriv {rho : ℝ → ℝ} {a b s t : ℝ}
    (hc : ContinuousOn rho (_root_.Set.Icc a b)) (hs : s ∈ _root_.Set.Icc a b) (ht : t ∈ _root_.Set.Icc a b) :
    HasDerivWithinAt (fun v => ∫ w in s..v, rho w) (rho t) (_root_.Set.Icc a b) t := by
  let : Fact (t ∈ _root_.Set.Icc a b) := ⟨ht⟩
  have hm : StronglyMeasurableAtFilter rho (𝓝[_root_.Set.Icc a b] t) volume :=
    ⟨Icc a b, self_mem_nhdsWithin, hc.aestronglyMeasurable measurableSet_Icc⟩
  exact intervalIntegral.integral_hasDerivWithinAt_right (rho_int hc hs ht) hm (hc t ht)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.primitive_deriv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.primitive_deriv target :: scope.openDecls } }

private theorem factor_cont {rho : ℝ → ℝ} {a b s : ℝ}
    (hc : ContinuousOn rho (_root_.Set.Icc a b)) (hs : s ∈ _root_.Set.Icc a b) :
    ContinuousOn (factor rho s) (_root_.Set.Icc a b) := by
  intro t ht
  change ContinuousWithinAt (fun v => Real.exp (∫ w in s..v, rho w)) (_root_.Set.Icc a b) t
  exact Real.continuous_exp.continuousAt.comp_continuousWithinAt
    (primitive_deriv hc hs ht).continuousWithinAt

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.factor_cont
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.factor_cont target :: scope.openDecls } }

private theorem factor_deriv {rho : ℝ → ℝ} {a b s t : ℝ}
    (hc : ContinuousOn rho (_root_.Set.Icc a b)) (hs : s ∈ _root_.Set.Icc a b) (ht : t ∈ _root_.Set.Icc a b) :
    HasDerivWithinAt (factor rho s) (rho t * factor rho s t) (_root_.Set.Icc a b) t := by
  change HasDerivWithinAt (fun v => Real.exp (∫ w in s..v, rho w))
    (rho t * Real.exp (∫ w in s..t, rho w)) (_root_.Set.Icc a b) t
  simpa only [mul_comm] using (primitive_deriv hc hs ht).exp

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.factor_deriv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.factor_deriv target :: scope.openDecls } }

private theorem factor_pos (rho : ℝ → ℝ) (s t : ℝ) : 0 < factor rho s t :=
  Real.exp_pos _

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.factor_pos
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.factor_pos target :: scope.openDecls } }

private theorem factor_cocycle {rho : ℝ → ℝ} {a b s u t : ℝ}
    (hc : ContinuousOn rho (_root_.Set.Icc a b)) (hs : s ∈ _root_.Set.Icc a b)
    (hu : u ∈ _root_.Set.Icc a b) (ht : t ∈ _root_.Set.Icc a b) :
    factor rho s t = factor rho s u * factor rho u t := by
  unfold factor
  rw [← intervalIntegral.integral_add_adjacent_intervals (rho_int hc hs hu) (rho_int hc hu ht),
    Real.exp_add]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.factor_cocycle
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.factor_cocycle target :: scope.openDecls } }

private theorem factor_primitive_cocycle {rho : ℝ → ℝ} {a b s u t : ℝ}
    (hc : ContinuousOn rho (_root_.Set.Icc a b)) (hs : s ∈ _root_.Set.Icc a b)
    (hu : u ∈ _root_.Set.Icc a b) (ht : t ∈ _root_.Set.Icc a b) :
    (∫ v in s..t, factor rho s v) = (∫ v in s..u, factor rho s v) +
      factor rho s u * ∫ v in u..t, factor rho u v := by
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (rho_int (factor_cont hc hs) hs hu) (rho_int (factor_cont hc hs) hu ht)]
  congr 1
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro v hv
  exact factor_cocycle hc hs hu (_root_.Set.uIcc_subset_Icc hu ht hv)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.factor_primitive_cocycle
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.factor_primitive_cocycle target :: scope.openDecls } }

private theorem affine_cocycle {rho : ℝ → ℝ} {a b s u t : ℝ}
    (hc : ContinuousOn rho (_root_.Set.Icc a b)) (hs : s ∈ _root_.Set.Icc a b)
    (hu : u ∈ _root_.Set.Icc a b) (ht : t ∈ _root_.Set.Icc a b) (z : ℝ) :
    affine rho u t (affine rho s u z) = affine rho s t z := by
  unfold affine
  rw [factor_cocycle hc hs hu ht, factor_primitive_cocycle hc hs hu ht]
  field_simp [(factor_pos rho s u).ne', (factor_pos rho u t).ne']
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.affine_cocycle
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.affine_cocycle target :: scope.openDecls } }

private theorem affine_deriv {rho : ℝ → ℝ} {a b s t : ℝ}
    (hc : ContinuousOn rho (_root_.Set.Icc a b)) (hs : s ∈ _root_.Set.Icc a b) (ht : t ∈ _root_.Set.Icc a b) (z : ℝ) :
    HasDerivWithinAt (fun v => affine rho s v z)
      (-2 * Real.pi - rho t * affine rho s t z) (_root_.Set.Icc a b) t := by
  have hF := ((factor_deriv hc hs ht).inv (factor_pos rho s t).ne').mul
    ((hasDerivWithinAt_const t (_root_.Set.Icc a b) z).sub
      ((primitive_deriv (factor_cont hc hs) hs ht).const_mul (2 * Real.pi)))
  convert! hF using 1
  simp only [affine, Pi.inv_apply, Pi.sub_apply]
  field_simp [(factor_pos rho s t).ne']
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.affine_deriv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.affine_deriv target :: scope.openDecls } }

private theorem integral_abs_bound {rho : ℝ → ℝ} {a b s t M : ℝ}
    (hs : s ∈ _root_.Set.Icc a b) (ht : t ∈ _root_.Set.Icc a b) (hst : s ≤ t)
    (hbound : ∀ v ∈ _root_.Set.Icc a b, |rho v| ≤ M) :
    |∫ w in s..t, rho w| ≤ M * (t - s) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := s) (b := t)
    (f := rho) (C := M) (fun v hv => by
      rw [Real.norm_eq_abs]
      exact hbound v (_root_.Set.uIcc_subset_Icc hs ht (_root_.Set.uIoc_subset_uIcc hv)))
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hst)] using h

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.integral_abs_bound
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.integral_abs_bound target :: scope.openDecls } }

private theorem factor_bounds {rho : ℝ → ℝ} {a b s t M : ℝ}
    (hs : s ∈ _root_.Set.Icc a b) (ht : t ∈ _root_.Set.Icc a b) (hst : s ≤ t)
    (hbound : ∀ v ∈ _root_.Set.Icc a b, |rho v| ≤ M) :
    Real.exp (-M * (t - s)) ≤ factor rho s t ∧
      factor rho s t ≤ Real.exp (M * (t - s)) := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp (integral_abs_bound hs ht hst hbound)
  exact ⟨Real.exp_le_exp.mpr (by linarith), Real.exp_le_exp.mpr hhi⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.factor_bounds
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.factor_bounds target :: scope.openDecls } }

private theorem affine_lipschitz {rho : ℝ → ℝ} {a b s t M : ℝ}
    (hs : s ∈ _root_.Set.Icc a b) (ht : t ∈ _root_.Set.Icc a b) (hst : s ≤ t)
    (hM : 0 ≤ M) (hbound : ∀ v ∈ _root_.Set.Icc a b, |rho v| ≤ M) (z z' : ℝ) :
    |affine rho s t z' - affine rho s t z| ≤ Real.exp (M * (b - a)) * |z' - z| := by
  have hsub : affine rho s t z' - affine rho s t z = (factor rho s t)⁻¹ * (z' - z) := by
    unfold affine
    ring
  have hi : (factor rho s t)⁻¹ ≤ Real.exp (M * (b - a)) := by
    rw [factor, ← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    have hlo := (abs_le.mp (integral_abs_bound hs ht hst hbound)).1
    have hlen : M * (t - s) ≤ M * (b - a) := mul_le_mul_of_nonneg_left (by linarith [hs.1, ht.2]) hM
    linarith
  rw [hsub, abs_mul, abs_of_pos (inv_pos.mpr (factor_pos rho s t))]
  exact mul_le_mul_of_nonneg_right hi (abs_nonneg _)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.affine_lipschitz
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.affine_lipschitz target :: scope.openDecls } }

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
    [SigmaCompactSpace Q] [hT2 : T2Space Q] [hCompact : CompactSpace Q]
    [hNonempty : Nonempty Q] [hBoundary : I.Boundaryless]


def halfScalarMinimum (G : SolutionFamily (I := I) (M := Q)) (t : ℝ) : ℝ :=
  scalarMinimum G t / 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.halfScalarMinimum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Families.halfScalarMinimum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.halfScalarMinimum ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.halfScalarMinimum


def scalarComparisonBound (G : SolutionFamily (I := I) (M := Q)) (a b : ℝ) : ℝ :=
  _root_.SupSet.sSup ((fun t => |halfScalarMinimum G t|) '' _root_.Set.Icc a b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.scalarComparisonBound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Families.scalarComparisonBound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.scalarComparisonBound ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.scalarComparisonBound


def affineComparison (G : SolutionFamily (I := I) (M := Q)) (s t z : ℝ) : ℝ :=
  (areaIntegratingFactor G s t)⁻¹ *
    (z - 2 * Real.pi * ∫ v in s..t, areaIntegratingFactor G s v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.affineComparison then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Families.affineComparison"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.affineComparison ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.affineComparison

omit [SigmaCompactSpace Q] hT2 hCompact hNonempty hBoundary in
theorem areaIntegratingFactor_pos (G : SolutionFamily (I := I) (M := Q)) (s t : ℝ) :
    0 < areaIntegratingFactor G s t := Real.exp_pos _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.areaIntegratingFactor_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Families.areaIntegratingFactor_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.areaIntegratingFactor_pos ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.areaIntegratingFactor_pos

omit [SigmaCompactSpace Q] hT2 hCompact hNonempty hBoundary in
@[simp] theorem affineComparison_self (G : SolutionFamily (I := I) (M := Q)) (s z : ℝ) :
    affineComparison G s s z = z := by
  simp [affineComparison, areaIntegratingFactor]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.affineComparison_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Families.affineComparison_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.affineComparison_self ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.affineComparison_self

omit [SigmaCompactSpace Q] hT2 hCompact hNonempty hBoundary in
theorem affineComparison_sub (G : SolutionFamily (I := I) (M := Q)) (s t z z' : ℝ) :
    affineComparison G s t z' - affineComparison G s t z =
      (areaIntegratingFactor G s t)⁻¹ * (z' - z) := by
  unfold affineComparison
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.affineComparison_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Families.affineComparison_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.affineComparison_sub ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.affineComparison_sub

omit [SigmaCompactSpace Q] hT2 hCompact hNonempty hBoundary in
theorem affineComparison_strictMono (G : SolutionFamily (I := I) (M := Q)) (s t : ℝ) :
    StrictMono (affineComparison G s t) := by
  intro z z' h
  unfold affineComparison
  exact mul_lt_mul_of_pos_left (sub_lt_sub_right h _)
    (inv_pos.mpr (areaIntegratingFactor_pos G s t))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.affineComparison_strictMono then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Families.affineComparison_strictMono"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.affineComparison_strictMono ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.affineComparison_strictMono

omit [SigmaCompactSpace Q] hT2 hCompact hNonempty hBoundary in
private theorem areaIntegratingFactor_eq_factor (G : SolutionFamily (I := I) (M := Q)) (s t : ℝ) :
    areaIntegratingFactor G s t = factor (halfScalarMinimum G) s t := by
  unfold areaIntegratingFactor factor halfScalarMinimum
  rw [intervalIntegral.integral_div]
  congr 1
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.areaIntegratingFactor_eq_factor
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.areaIntegratingFactor_eq_factor target :: scope.openDecls } }

omit [SigmaCompactSpace Q] hT2 hCompact hNonempty hBoundary in
private theorem affineComparison_eq_affine (G : SolutionFamily (I := I) (M := Q)) (s t z : ℝ) :
    affineComparison G s t z = affine (halfScalarMinimum G) s t z := by
  unfold affineComparison affine
  simp only [← areaIntegratingFactor_eq_factor]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.affineComparison_eq_affine
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.affineComparison_eq_affine target :: scope.openDecls } }

variable [hConnected : ConnectedSpace Q] {D : RealTimeInterval} {a b : ℝ}
include hT2 hCompact hNonempty hBoundary hConnected

omit [SigmaCompactSpace Q] hCompact hNonempty hBoundary hConnected in
private theorem scalar_window_cont (B : RicciBackground (I := I) (M := Q) D a b) :
    Continuous (fun p : _root_.Set.Icc a b × Q => B.family.scalar p.1 p.2) := by
  have hraw : ContinuousOn (fun p : ℝ × Q => B.family.scalar p.1 p.2)
      (D.carrier ×ˢ (_root_.Set.univ : Set Q)) := by
    simpa only [SolutionOn.scalar] using B.equation.scalarCont
  have hmap : Continuous (fun p : _root_.Set.Icc a b × Q => ((p.1 : ℝ), p.2)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have hmem : ∀ p : _root_.Set.Icc a b × Q, ((p.1 : ℝ), p.2) ∈ D.carrier ×ˢ (_root_.Set.univ : Set Q) :=
    fun p => ⟨D.regular_subset (B.regular p.1.property), _root_.Set.mem_univ p.2⟩
  exact hraw.comp_continuous (f := fun p : _root_.Set.Icc a b × Q => ((p.1 : ℝ), p.2)) hmap hmem

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.scalar_window_cont
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.scalar_window_cont target :: scope.openDecls } }

omit [SigmaCompactSpace Q] hBoundary hConnected in
theorem rfs_width_flow_background
    (B : RicciBackground (I := I) (M := Q) D a b) :
    ContinuousOn (halfScalarMinimum B.family) (_root_.Set.Icc a b) ∧
      (∀ t ∈ _root_.Set.Icc a b, ∃ q : Q,
        B.family.scalar t q / 2 = halfScalarMinimum B.family t) ∧
      0 ≤ scalarComparisonBound B.family a b ∧
      (∀ t ∈ _root_.Set.Icc a b,
        |halfScalarMinimum B.family t| ≤ scalarComparisonBound B.family a b) ∧
      ∃ t ∈ _root_.Set.Icc a b,
        |halfScalarMinimum B.family t| = scalarComparisonBound B.family a b := by
  have hscalar := scalar_window_cont B
  have hmin : Continuous (fun t : _root_.Set.Icc a b => halfScalarMinimum B.family t) := by
    have hc : Continuous (fun t : _root_.Set.Icc a b =>
        sInf ((fun q : Q => B.family.scalar t q) '' (_root_.Set.univ : Set Q))) :=
      (isCompact_univ : IsCompact (_root_.Set.univ : Set Q)).continuous_sInf
        (f := fun (t : _root_.Set.Icc a b) (q : Q) => B.family.scalar t q) hscalar
    simpa only [_root_.Set.image_univ, halfScalarMinimum, scalarMinimum] using hc.div_const (2 : ℝ)
  have hcontinuous : ContinuousOn (halfScalarMinimum B.family) (_root_.Set.Icc a b) :=
    continuousOn_iff_continuous_domRestrict.mpr hmin
  have hattain : ∀ t ∈ _root_.Set.Icc a b, ∃ q : Q, B.family.scalar t q / 2 = halfScalarMinimum B.family t := by
    intro t ht
    have htcont : Continuous (B.family.scalar t) :=
      hscalar.comp (g := fun p : _root_.Set.Icc a b × Q => B.family.scalar p.1 p.2)
        (f := fun q : Q => ((⟨t, ht⟩ : _root_.Set.Icc a b), q))
        (continuous_const.prodMk continuous_id :
        Continuous (fun q : Q => ((⟨t, ht⟩ : _root_.Set.Icc a b), q)))
    obtain ⟨q, _, hq⟩ := (isCompact_univ : IsCompact (_root_.Set.univ : Set Q)).exists_sInf_image_eq
      Set.univ_nonempty htcont.continuousOn
    refine ⟨q, ?_⟩
    simpa only [_root_.Set.image_univ, halfScalarMinimum, scalarMinimum] using congrArg (fun x : ℝ => x / 2) hq.symm
  obtain ⟨t, ht, hM, hmax⟩ := isCompact_Icc.exists_sSup_image_eq_and_ge
    (nonempty_Icc.mpr B.lt.le) hcontinuous.abs
  have hbound : ∀ v ∈ _root_.Set.Icc a b, |halfScalarMinimum B.family v| ≤ scalarComparisonBound B.family a b := by
    intro v hv
    exact (hmax v hv).trans_eq hM.symm
  exact ⟨hcontinuous, hattain, (abs_nonneg _).trans (hbound t ht), hbound, t, ht, hM.symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.rfs_width_flow_background then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Families.rfs_width_flow_background"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.rfs_width_flow_background ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.rfs_width_flow_background


omit [SigmaCompactSpace Q] hBoundary hConnected in
theorem areaIntegratingFactor_continuousOn
    (B : RicciBackground (I := I) (M := Q) D a b) {s : ℝ} (hs : s ∈ _root_.Set.Icc a b) :
    ContinuousOn (areaIntegratingFactor B.family s) (_root_.Set.Icc a b) := by
  have hfun : areaIntegratingFactor B.family s = factor (halfScalarMinimum B.family) s :=
    funext (areaIntegratingFactor_eq_factor B.family s)
  rw [hfun]
  exact factor_cont (rfs_width_flow_background B).1 hs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.areaIntegratingFactor_continuousOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Families.areaIntegratingFactor_continuousOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.areaIntegratingFactor_continuousOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.areaIntegratingFactor_continuousOn

omit [SigmaCompactSpace Q] hBoundary hConnected in
theorem rfs_width_affine_comparison
    (B : RicciBackground (I := I) (M := Q) D a b) :
    (∀ s ∈ _root_.Set.Icc a b, ∀ z t, t ∈ _root_.Set.Icc a b →
      HasDerivWithinAt (fun v => affineComparison B.family s v z)
        (-2 * Real.pi - halfScalarMinimum B.family t * affineComparison B.family s t z)
        (_root_.Set.Icc a b) t) ∧
    (∀ s ∈ _root_.Set.Icc a b, ∀ u ∈ _root_.Set.Icc s b, ∀ t ∈ _root_.Set.Icc u b, ∀ z,
      affineComparison B.family u t (affineComparison B.family s u z) =
        affineComparison B.family s t z) ∧
    (∀ s ∈ _root_.Set.Icc a b, ∀ t ∈ _root_.Set.Icc s b,
      Real.exp (-scalarComparisonBound B.family a b * (t - s)) ≤
          areaIntegratingFactor B.family s t ∧
        areaIntegratingFactor B.family s t ≤
          Real.exp (scalarComparisonBound B.family a b * (t - s))) ∧
    (∀ s ∈ _root_.Set.Icc a b, ∀ t ∈ _root_.Set.Icc s b, ∀ z z' : ℝ,
      |affineComparison B.family s t z' - affineComparison B.family s t z| ≤
        Real.exp (scalarComparisonBound B.family a b * (b - a)) * |z' - z|) := by
  obtain ⟨hc, _, hM, hbound, _⟩ := rfs_width_flow_background B
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hs z t ht
    simpa only [affineComparison_eq_affine] using affine_deriv hc hs ht z
  · intro s hs u hu t ht z
    have hu' : u ∈ _root_.Set.Icc a b := ⟨hs.1.trans hu.1, hu.2⟩
    have ht' : t ∈ _root_.Set.Icc a b := ⟨hu'.1.trans ht.1, ht.2⟩
    simpa only [affineComparison_eq_affine] using affine_cocycle hc hs hu' ht' z
  · intro s hs t ht
    have ht' : t ∈ _root_.Set.Icc a b := ⟨hs.1.trans ht.1, ht.2⟩
    simpa only [areaIntegratingFactor_eq_factor] using factor_bounds hs ht' ht.1 hbound
  · intro s hs t ht z z'
    have ht' : t ∈ _root_.Set.Icc a b := ⟨hs.1.trans ht.1, ht.2⟩
    simpa only [affineComparison_eq_affine] using affine_lipschitz hs ht' ht.1 hM hbound z z'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.rfs_width_affine_comparison then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Families.rfs_width_affine_comparison"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.rfs_width_affine_comparison ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.rfs_width_affine_comparison

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families
