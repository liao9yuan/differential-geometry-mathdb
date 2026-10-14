import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.DifferentialGeometry.Topology.FundamentalGroup.Sphere
import Submission.DifferentialGeometry.Topology.SphereSeparation.ComponentCount
import Submission.DifferentialGeometry.Topology.SphereSeparation.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

namespace DifferentialGeometry.Topology.SphereSeparation

open _root_.Set
open _root_.Metric

abbrev EuclideanThree := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.EuclideanThree then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.EuclideanThree"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.EuclideanThree ``Submission.DifferentialGeometry.Topology.SphereSeparation.EuclideanThree

private theorem unitSphere_connected :
    IsConnected (_root_.Metric.sphere (0 : EuclideanThree) 1) := by
  apply isConnected_sphere
  · rw [← Module.finrank_eq_rank']
    norm_num [EuclideanThree, Module.finrank_fin_fun]
  · positivity

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphereSeparation.unitSphere_connected
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphereSeparation.unitSphere_connected target :: scope.openDecls } }

theorem isConnected_sphereTwo : IsConnected (Set.univ : Set SphereTwo) := by
  let _ : ConnectedSpace SphereTwo := Subtype.connectedSpace unitSphere_connected
  exact isConnected_univ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.isConnected_sphereTwo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.isConnected_sphereTwo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.isConnected_sphereTwo ``Submission.DifferentialGeometry.Topology.SphereSeparation.isConnected_sphereTwo

private theorem exterior_connected :
    IsConnected ((_root_.Metric.closedBall (0 : EuclideanThree) 1)ᶜ) := by
  let f : EuclideanThree × ℝ → EuclideanThree := fun p => p.2 • p.1
  have hsource :
      IsConnected (_root_.Metric.sphere (0 : EuclideanThree) 1 ×ˢ _root_.Set.Ioi (1 : ℝ)) :=
    unitSphere_connected.prod isConnected_Ioi
  have himage :
      f '' (_root_.Metric.sphere (0 : EuclideanThree) 1 ×ˢ _root_.Set.Ioi (1 : ℝ)) =
        (_root_.Metric.closedBall (0 : EuclideanThree) 1)ᶜ := by
    ext x
    constructor
    · rintro ⟨⟨u, r⟩, ⟨hu, hr⟩, rfl⟩
      rw [_root_.Set.mem_compl_iff, mem_closedBall_zero_iff, not_le]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (lt_trans zero_lt_one hr)]
      rw [mem_sphere_zero_iff_norm] at hu
      rw [hu, mul_one]
      exact hr
    · intro hx
      have hxnorm : 1 < ‖x‖ := by
        simpa only [_root_.Set.mem_compl_iff, mem_closedBall_zero_iff, not_le] using hx
      have hxne : ‖x‖ ≠ 0 := ne_of_gt (lt_trans zero_lt_one hxnorm)
      refine ⟨(‖x‖⁻¹ • x, ‖x‖), ?_, ?_⟩
      · constructor
        · rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x))]
          exact inv_mul_cancel₀ hxne
        · exact hxnorm
      · dsimp [f]
        rw [smul_smul, mul_inv_cancel₀ hxne, one_smul]
  rw [← himage]
  exact hsource.image f (by fun_prop)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphereSeparation.exterior_connected
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphereSeparation.exterior_connected target :: scope.openDecls } }

private theorem exterior_noncompact :
    ¬ IsCompact (closure ((_root_.Metric.closedBall (0 : EuclideanThree) 1)ᶜ)) := by
  intro hcompact
  have hbounded := hcompact.isBounded
  rw [Metric.isBounded_iff_subset_closedBall 0] at hbounded
  obtain ⟨r, hr⟩ := hbounded
  let e : EuclideanThree := EuclideanSpace.single 0 (_root_.Max.max 2 (r + 1))
  have heNorm : ‖e‖ = _root_.Max.max 2 (r + 1) := by
    simp [e, Real.norm_eq_abs, abs_of_nonneg (le_trans (by positivity) (le_max_left _ _))]
  have heExterior : e ∈ (_root_.Metric.closedBall (0 : EuclideanThree) 1)ᶜ := by
    rw [_root_.Set.mem_compl_iff, mem_closedBall_zero_iff, not_le, heNorm]
    exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have heClosure : e ∈ closure ((_root_.Metric.closedBall (0 : EuclideanThree) 1)ᶜ) :=
    subset_closure heExterior
  have heBounded : e ∈ _root_.Metric.closedBall (0 : EuclideanThree) r := hr heClosure
  rw [mem_closedBall_zero_iff, heNorm] at heBounded
  have : r < _root_.Max.max 2 (r + 1) := lt_of_lt_of_le (lt_add_one r) (le_max_right _ _)
  exact (not_lt_of_ge heBounded) this

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphereSeparation.exterior_noncompact
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphereSeparation.exterior_noncompact target :: scope.openDecls } }

noncomputable def standardUnitSphereSides :
    SphereSides (_root_.Metric.sphere (0 : EuclideanThree) 1) where
  compactSide := _root_.Metric.ball 0 1
  endSide := (_root_.Metric.closedBall 0 1)ᶜ
  isOpen_compactSide := _root_.Metric.isOpen_ball
  isOpen_endSide := isClosed_closedBall.isOpen_compl
  isConnected_compactSide := _root_.Metric.isConnected_ball (by positivity)
  isConnected_endSide := exterior_connected
  disjoint := by
    rw [Set.disjoint_left]
    intro x hxBall hxExterior
    exact hxExterior (_root_.Metric.ball_subset_closedBall hxBall)
  union_eq_compl := by
    ext x
    simp only [_root_.Set.mem_union, mem_ball_zero_iff, _root_.Set.mem_compl_iff,
      mem_closedBall_zero_iff, mem_sphere_zero_iff_norm]
    rw [not_le]
    constructor
    · rintro (h | h)
      · exact ne_of_lt h
      · exact ne_of_gt h
    · exact lt_or_gt_of_ne
  isCompact_closure_compactSide := by
    rw [closure_ball 0 one_ne_zero]
    exact _root_.ProperSpace.isCompact_closedBall 0 1
  not_isCompact_closure_endSide := exterior_noncompact
  frontier_compactSide := frontier_ball 0 one_ne_zero
  frontier_endSide := by
    rw [frontier_compl, frontier_closedBall 0 one_ne_zero]
  closure_compactSide := by
    rw [closure_ball 0 one_ne_zero]
    ext x
    simp only [mem_closedBall_zero_iff, _root_.Set.mem_union, mem_ball_zero_iff,
      mem_sphere_zero_iff_norm]
    exact le_iff_lt_or_eq
  closure_endSide := by
    rw [closure_compl, interior_closedBall 0 one_ne_zero]
    ext x
    simp only [_root_.Set.mem_compl_iff, mem_ball_zero_iff, mem_closedBall_zero_iff,
      _root_.Set.mem_union, mem_sphere_zero_iff_norm]
    rw [not_lt, not_le]
    constructor
    · intro h
      rcases lt_or_eq_of_le h with h | h
      · exact Or.inl h
      · exact Or.inr h.symm
    · rintro (h | h)
      · exact h.le
      · exact h.symm.le
  interior_closure_compactSide := by
    rw [closure_ball 0 one_ne_zero, interior_closedBall 0 one_ne_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.standardUnitSphereSides then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.standardUnitSphereSides"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.standardUnitSphereSides ``Submission.DifferentialGeometry.Topology.SphereSeparation.standardUnitSphereSides

noncomputable def standardUnitSphereComplementComponents :
    ConnectedComponents
      ((Metric.sphere (0 : EuclideanThree) 1)ᶜ : Set EuclideanThree) ≃ Fin 2 :=
  connectedComponentsComplEquivFinTwo standardUnitSphereSides

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.standardUnitSphereComplementComponents then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.standardUnitSphereComplementComponents"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.standardUnitSphereComplementComponents ``Submission.DifferentialGeometry.Topology.SphereSeparation.standardUnitSphereComplementComponents

end DifferentialGeometry.Topology.SphereSeparation
