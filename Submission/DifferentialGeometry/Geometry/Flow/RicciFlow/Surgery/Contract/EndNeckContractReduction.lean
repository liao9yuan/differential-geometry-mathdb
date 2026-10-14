import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.EndNeckFields
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CoOrientedNeckChainReflection

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Submission.Set _root_.Function _root_.Submission.Function
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

def cylinderAxialReflectionShift (c : ℝ) : PartialDiffeomorph IC IC Cylinder Cylinder ∞ :=
  cylinderAxialReflection.trans (cylinderAxialShift c)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderAxialReflectionShift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderAxialReflectionShift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderAxialReflectionShift ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderAxialReflectionShift

theorem cylinderAxialReflectionShift_source (c : ℝ) :
    (cylinderAxialReflectionShift c).source = Set.univ := by
  rw [cylinderAxialReflectionShift, PartialDiffeomorph.trans_source]
  simp [cylinderAxialReflection, cylinderAxialShift]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderAxialReflectionShift_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderAxialReflectionShift_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderAxialReflectionShift_source ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderAxialReflectionShift_source

@[simp]
theorem cylinderAxialReflectionShift_apply (c : ℝ) (y : Cylinder) :
    cylinderAxialReflectionShift c y = (y.1, c - y.2) := by
  rw [cylinderAxialReflectionShift, PartialDiffeomorph.trans_apply,
    cylinderAxialReflection_apply]
  simp only [cylinderAxialShift, sub_eq_add_neg, add_comm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderAxialReflectionShift_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderAxialReflectionShift_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderAxialReflectionShift_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderAxialReflectionShift_apply

theorem cylinderAxialReflectionShift_symm_apply (c : ℝ) (y : Cylinder) :
    (cylinderAxialReflectionShift c).symm y = (y.1, c - y.2) := by
  have hy : (y.1, y.2 - c) ∈ (cylinderAxialShift c).source := trivial
  have h := PartialDiffeomorph.trans_symm_apply cylinderAxialReflection
    (cylinderAxialShift c) hy
  have hshift : (cylinderAxialShift c) (y.1, y.2 - c) = y := by
    apply Prod.ext
    · rfl
    · simp only [cylinderAxialShift]
      ring
  have hrefl : cylinderAxialReflection.symm (y.1, y.2 - c) = (y.1, c - y.2) := by
    rw [cylinderAxialReflection_symm_apply]
    apply Prod.ext
    · rfl
    · ring
  rw [hshift, hrefl] at h
  simpa [cylinderAxialReflectionShift] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderAxialReflectionShift_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderAxialReflectionShift_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderAxialReflectionShift_symm_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderAxialReflectionShift_symm_apply

theorem cylinderAxialReflectionShift_fiberPreserving (c : ℝ) :
    CylinderFiberPreserving (cylinderAxialReflectionShift c) := by
  intro y a
  rw [cylinderAxialReflectionShift_apply, cylinderAxialReflectionShift_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderAxialReflectionShift_fiberPreserving then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderAxialReflectionShift_fiberPreserving"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderAxialReflectionShift_fiberPreserving ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderAxialReflectionShift_fiberPreserving

theorem cylinderAxialReflectionShift_symm_fiberPreserving (c : ℝ) :
    CylinderFiberPreserving (cylinderAxialReflectionShift c).symm := by
  intro y a
  rw [cylinderAxialReflectionShift_symm_apply, cylinderAxialReflectionShift_symm_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderAxialReflectionShift_symm_fiberPreserving then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderAxialReflectionShift_symm_fiberPreserving"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderAxialReflectionShift_symm_fiberPreserving ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderAxialReflectionShift_symm_fiberPreserving

theorem cylinderAxialReflectionShift_axial_fderiv (c : ℝ) (y : Cylinder) :
    fderiv ℝ (fun a : ℝ => (cylinderAxialReflectionShift c (y.1, a)).2) y.2 1 = -1 := by
  have h : (fun a : ℝ => (cylinderAxialReflectionShift c (y.1, a)).2) = fun a : ℝ => c - a := by
    funext a
    rw [cylinderAxialReflectionShift_apply]
  rw [h]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderAxialReflectionShift_axial_fderiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderAxialReflectionShift_axial_fderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderAxialReflectionShift_axial_fderiv ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderAxialReflectionShift_axial_fderiv

theorem not_cylinderAxiallyIncreasing_cylinderAxialReflectionShift (c : ℝ) :
    ¬ CylinderAxiallyIncreasing (cylinderAxialReflectionShift c) := by
  intro h
  have hpos := h (DifferentialGeometry.Topology.sphereTwoNorth, (0 : ℝ))
    (by rw [cylinderAxialReflectionShift_source]; exact Set.mem_univ _)
  rw [cylinderAxialReflectionShift_axial_fderiv] at hpos
  norm_num at hpos

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.not_cylinderAxiallyIncreasing_cylinderAxialReflectionShift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.not_cylinderAxiallyIncreasing_cylinderAxialReflectionShift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.not_cylinderAxiallyIncreasing_cylinderAxialReflectionShift ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.not_cylinderAxiallyIncreasing_cylinderAxialReflectionShift

theorem not_cylinderCoOriented_cylinderAxialReflectionShift (c : ℝ) :
    ¬ CylinderCoOriented (cylinderAxialReflectionShift c) :=
  fun h => not_cylinderAxiallyIncreasing_cylinderAxialReflectionShift c h.2.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.not_cylinderCoOriented_cylinderAxialReflectionShift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.not_cylinderCoOriented_cylinderAxialReflectionShift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.not_cylinderCoOriented_cylinderAxialReflectionShift ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.not_cylinderCoOriented_cylinderAxialReflectionShift

theorem cylinderAxialReflectionShift_trans_reflection_apply (c : ℝ) (y : Cylinder) :
    (cylinderAxialReflectionShift c).trans cylinderAxialReflection y =
      cylinderAxialShift (-c) y := by
  rw [PartialDiffeomorph.trans_apply, cylinderAxialReflectionShift_apply,
    cylinderAxialReflection_apply]
  apply Prod.ext
  · rfl
  · simp only [cylinderAxialShift]
    ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderAxialReflectionShift_trans_reflection_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderAxialReflectionShift_trans_reflection_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderAxialReflectionShift_trans_reflection_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderAxialReflectionShift_trans_reflection_apply

theorem cylinderAxialReflectionShift_zero (y : Cylinder) :
    cylinderAxialReflectionShift 0 y = cylinderAxialReflection y := by
  rw [cylinderAxialReflectionShift_apply, cylinderAxialReflection_apply]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderAxialReflectionShift_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderAxialReflectionShift_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderAxialReflectionShift_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderAxialReflectionShift_zero


end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open _root_.Submission.DifferentialGeometry.Topology
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u

variable {D : OneStepIncoming.{u}}

private theorem not_isCompact_Ici_zero : ¬ IsCompact (Set.Ici (0 : ℝ)) := by
  intro h
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp (Metric.isCompact_iff_isClosed_bounded.mp h).2
  have h1 : |C| + 1 ≤ C := by
    have h2 := hC (Set.mem_Ici.mpr le_rfl)
      (Set.mem_Ici.mpr (by positivity : (0 : ℝ) ≤ |C| + 1))
    have h3 : _root_.Dist.dist (0 : ℝ) (|C| + 1) = |C| + 1 := by
      rw [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg (by positivity)]
    rwa [h3] at h2
  have hCnonneg : 0 ≤ C := by linarith [abs_nonneg C]
  rw [abs_of_nonneg hCnonneg] at h1
  linarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_isCompact_Ici_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_isCompact_Ici_zero target :: scope.openDecls } }

theorem not_isCompact_univ_halfNeckCylinder : ¬ IsCompact (Set.univ : Set HalfNeckCylinder) := by
  intro h
  have himage : IsCompact (Set.range fun p : HalfNeckCylinder => p.1.2) := by
    simpa [Set.image_univ] using h.image continuous_subtype_val.snd
  have hrange : Set.range (fun p : HalfNeckCylinder => p.1.2) = Set.Ici (0 : ℝ) := by
    ext t
    constructor
    · rintro ⟨p, rfl⟩
      exact p.2
    · intro ht
      exact ⟨⟨(DifferentialGeometry.Topology.sphereTwoNorth, t), ht⟩, rfl⟩
  rw [hrange] at himage
  exact not_isCompact_Ici_zero himage

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_isCompact_univ_halfNeckCylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_isCompact_univ_halfNeckCylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_isCompact_univ_halfNeckCylinder ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_isCompact_univ_halfNeckCylinder

theorem TerminalCorePresentation.horn_range_not_isCompact {ε Λ : ℝ}
    (P : TerminalCorePresentation D ε Λ)
    (c : ConnectedComponents ↥D.slab.terminalRegularOpen) (e : P.hornIndex c) :
    ¬ IsCompact (Set.range fun p : HalfNeckCylinder => P.horn c e p.1) := by
  intro hcomp
  have hpre := (P.horn_proper c e).isCompact_preimage hcomp
  rw [Set.preimage_range] at hpre
  exact not_isCompact_univ_halfNeckCylinder hpre

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.horn_range_not_isCompact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.horn_range_not_isCompact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.horn_range_not_isCompact ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.horn_range_not_isCompact

theorem AdaptedHistoricalNeck.chart_apply_reflectionShift
    {horn : NeckCylinder → ↥D.slab.terminalRegularOpen} {d h : ℝ} {k : ℕ}
    (A : AdaptedHistoricalNeck D horn d h k) (p : neckBuffer d) :
    A.chart (cylinderAxialReflectionShift A.shift p.1) = A.neck.chart p := by
  rw [cylinderAxialReflectionShift_apply]
  exact A.chart_eq_neck p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.AdaptedHistoricalNeck.chart_apply_reflectionShift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.AdaptedHistoricalNeck.chart_apply_reflectionShift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.AdaptedHistoricalNeck.chart_apply_reflectionShift ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.AdaptedHistoricalNeck.chart_apply_reflectionShift

theorem TerminalCorePresentation.component_eq_empty_of_forall_not_low {ε Λ : ℝ}
    (P : TerminalCorePresentation D ε Λ)
    (h : ∀ x : ↥D.slab.terminalRegularOpen,
      ¬ metricScalarAt D.terminal.metric x ≤ (P.coreRadius ^ 2)⁻¹) :
    P.component = ∅ := by
  ext c
  constructor
  · intro hc
    obtain ⟨x, -, hx⟩ := (P.component_iff_meets_low c).mp hc
    exact absurd hx (h x)
  · intro hc
    exact hc.elim

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.component_eq_empty_of_forall_not_low then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.component_eq_empty_of_forall_not_low"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.component_eq_empty_of_forall_not_low ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.component_eq_empty_of_forall_not_low

theorem TerminalCorePresentation.core_eq_componentSet_of_isEmpty_hornIndex {ε Λ : ℝ}
    (P : TerminalCorePresentation D ε Λ)
    {c : ConnectedComponents ↥D.slab.terminalRegularOpen} (hc : c ∈ P.component)
    (h : IsEmpty (P.hornIndex c)) :
    P.core c = {x : ↥D.slab.terminalRegularOpen | ConnectedComponents.mk x = c} := by
  rw [P.horn_covers_component c hc, Set.iUnion_of_empty, Set.union_empty]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.core_eq_componentSet_of_isEmpty_hornIndex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.core_eq_componentSet_of_isEmpty_hornIndex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.core_eq_componentSet_of_isEmpty_hornIndex ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.core_eq_componentSet_of_isEmpty_hornIndex

theorem TerminalCorePresentation.core_eq_componentSet_or_hornIndex_nonempty {ε Λ : ℝ}
    (P : TerminalCorePresentation D ε Λ)
    {c : ConnectedComponents ↥D.slab.terminalRegularOpen} (hc : c ∈ P.component) :
    P.core c = {x : ↥D.slab.terminalRegularOpen | ConnectedComponents.mk x = c} ∨
      Nonempty (P.hornIndex c) := by
  by_cases h : Nonempty (P.hornIndex c)
  · exact Or.inr h
  · exact Or.inl (P.core_eq_componentSet_of_isEmpty_hornIndex hc ⟨fun a => h ⟨a⟩⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.core_eq_componentSet_or_hornIndex_nonempty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.core_eq_componentSet_or_hornIndex_nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.core_eq_componentSet_or_hornIndex_nonempty ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.core_eq_componentSet_or_hornIndex_nonempty

theorem TerminalCorePresentation.coreRadius_inv_sq_lt_scalar_of_not_mem_core {ε Λ : ℝ}
    (P : TerminalCorePresentation D ε Λ)
    {c : ConnectedComponents ↥D.slab.terminalRegularOpen} (hc : c ∈ P.component)
    {x : ↥D.slab.terminalRegularOpen} (hxc : ConnectedComponents.mk x = c)
    (hx : x ∉ P.core c) :
    (P.coreRadius ^ 2)⁻¹ < metricScalarAt D.terminal.metric x := by
  apply lt_of_not_ge
  intro h
  exact hx (interior_subset (P.low_mem_interior_core c hc x hxc h))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.coreRadius_inv_sq_lt_scalar_of_not_mem_core then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.coreRadius_inv_sq_lt_scalar_of_not_mem_core"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.coreRadius_inv_sq_lt_scalar_of_not_mem_core ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.coreRadius_inv_sq_lt_scalar_of_not_mem_core

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
