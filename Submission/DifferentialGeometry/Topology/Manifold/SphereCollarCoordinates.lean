import Submission.DifferentialGeometry.Topology.Manifold.SmoothTwoSidedCollar
import Submission.DifferentialGeometry.Topology.Manifold.SpherePolarCoordinates

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Manifold
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology.SmoothTwoSidedCollar

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]
  {F H M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
  [TopologicalSpace M] [ChartedSpace H M]
  {e : Metric.sphere (0 : E) 1 → M}
  (d : SmoothTwoSidedCollar (𝓡 n) I e)

private def reverseRadius : ℝ ≃ₘ[ℝ] ℝ where
  toFun r := 1 - r
  invFun r := 1 - r
  left_inv r := by dsimp; ring
  right_inv r := by dsimp; ring
  contMDiff_toFun := contMDiff_const.sub contMDiff_id
  contMDiff_invFun := contMDiff_const.sub contMDiff_id

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SmoothTwoSidedCollar.reverseRadius
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SmoothTwoSidedCollar.reverseRadius target :: scope.openDecls } }

private def reverseRadiusProd :
    (Metric.sphere (0 : E) 1 × ℝ) ≃ₘ⟮(𝓡 n).prod 𝓘(ℝ, ℝ), (𝓡 n).prod 𝓘(ℝ, ℝ)⟯
      (Metric.sphere (0 : E) 1 × ℝ) :=
  (Diffeomorph.refl (𝓡 n) _ ∞).prodCongr reverseRadius

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SmoothTwoSidedCollar.reverseRadiusProd
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SmoothTwoSidedCollar.reverseRadiusProd target :: scope.openDecls } }

def radialPartialDiffeomorph (v : Metric.sphere (0 : E) 1) :
    _root_.PartialDiffeomorph 𝓘(ℝ, E) I E M ∞ := by
  let _ : Nonempty (Metric.sphere (0 : E) 1) := ⟨v⟩
  exact ((Manifold.spherePolarChart (n := n) v).symm.trans
    (reverseRadiusProd (E := E) (n := n)).toPartialDiffeomorph).trans d.toPartialDiffeomorph

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothTwoSidedCollar.radialPartialDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothTwoSidedCollar.radialPartialDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothTwoSidedCollar.radialPartialDiffeomorph ``Submission.DifferentialGeometry.Topology.SmoothTwoSidedCollar.radialPartialDiffeomorph

theorem radialPartialDiffeomorph_apply (v z : Metric.sphere (0 : E) 1) (r : ℝ)
    (hr : 0 < r) (ht : 1 - r ∈ _root_.Set.Ioo (-d.radius) d.radius) :
    d.radialPartialDiffeomorph v (r • (z : E)) =
      d.toFun (z, ⟨1 - r, ht⟩) := by
  let _ : Nonempty (Metric.sphere (0 : E) 1) := ⟨v⟩
  change d.toPartialDiffeomorph ((reverseRadiusProd (E := E) (n := n))
    ((Manifold.spherePolarChart (n := n) v).symm (r • (z : E)))) = _
  rw [Manifold.spherePolarChart_symm_apply, Manifold.sphereDirection_pos_smul v z hr]
  have hn : ‖r • (z : E)‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, norm_eq_of_mem_sphere, mul_one]
  rw [hn]
  exact d.toPartialDiffeomorph_apply (z, ⟨1 - r, ht⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothTwoSidedCollar.radialPartialDiffeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothTwoSidedCollar.radialPartialDiffeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothTwoSidedCollar.radialPartialDiffeomorph_apply ``Submission.DifferentialGeometry.Topology.SmoothTwoSidedCollar.radialPartialDiffeomorph_apply

theorem mem_radialPartialDiffeomorph_source (v z : Metric.sphere (0 : E) 1) (r : ℝ)
    (hr : 0 < r) (ht : 1 - r ∈ _root_.Set.Ioo (-d.radius) d.radius) :
    r • (z : E) ∈ (d.radialPartialDiffeomorph v).source := by
  let _ : Nonempty (Metric.sphere (0 : E) 1) := ⟨v⟩
  refine ⟨⟨?_, trivial⟩, ?_⟩
  · exact smul_ne_zero (ne_of_gt hr) (ne_zero_of_mem_unit_sphere z)
  · change (reverseRadiusProd (E := E) (n := n))
      ((Manifold.spherePolarChart (n := n) v).symm (r • (z : E))) ∈ d.toPartialDiffeomorph.source
    rw [d.toPartialDiffeomorph_source, Manifold.spherePolarChart_symm_apply,
      Manifold.sphereDirection_pos_smul v z hr]
    have hn : ‖r • (z : E)‖ = r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, norm_eq_of_mem_sphere, mul_one]
    rw [hn]
    exact ⟨trivial, ht⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothTwoSidedCollar.mem_radialPartialDiffeomorph_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothTwoSidedCollar.mem_radialPartialDiffeomorph_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothTwoSidedCollar.mem_radialPartialDiffeomorph_source ``Submission.DifferentialGeometry.Topology.SmoothTwoSidedCollar.mem_radialPartialDiffeomorph_source

@[simp] theorem radialPartialDiffeomorph_sphere (v z : Metric.sphere (0 : E) 1) :
    d.radialPartialDiffeomorph v (z : E) = e z := by
  have h := d.radialPartialDiffeomorph_apply v z 1 zero_lt_one
    (by simp only [sub_self]; exact ⟨neg_lt_zero.mpr d.radius_pos, d.radius_pos⟩)
  simpa only [one_smul, sub_self, d.toFun_zero] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothTwoSidedCollar.radialPartialDiffeomorph_sphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothTwoSidedCollar.radialPartialDiffeomorph_sphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothTwoSidedCollar.radialPartialDiffeomorph_sphere ``Submission.DifferentialGeometry.Topology.SmoothTwoSidedCollar.radialPartialDiffeomorph_sphere

theorem sphere_subset_radialPartialDiffeomorph_source (v : Metric.sphere (0 : E) 1) :
    Metric.sphere (0 : E) 1 ⊆ (d.radialPartialDiffeomorph v).source := by
  intro x hx
  have h := d.mem_radialPartialDiffeomorph_source v ⟨x, hx⟩ 1 zero_lt_one
    (by simp only [sub_self]; exact ⟨neg_lt_zero.mpr d.radius_pos, d.radius_pos⟩)
  simpa only [one_smul] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothTwoSidedCollar.sphere_subset_radialPartialDiffeomorph_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothTwoSidedCollar.sphere_subset_radialPartialDiffeomorph_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothTwoSidedCollar.sphere_subset_radialPartialDiffeomorph_source ``Submission.DifferentialGeometry.Topology.SmoothTwoSidedCollar.sphere_subset_radialPartialDiffeomorph_source

theorem radialPartialDiffeomorph_symm_apply (v : Metric.sphere (0 : E) 1) (p : d.neighborhood) :
    (d.radialPartialDiffeomorph v).symm p.val =
      (1 - (d.toDiffeomorph.symm p).2.val) • ((d.toDiffeomorph.symm p).1 : E) := by
  let _ : Nonempty (Metric.sphere (0 : E) 1) := ⟨v⟩
  change Manifold.spherePolarChart (n := n) v
    ((reverseRadiusProd (E := E) (n := n)).symm (d.toPartialDiffeomorph.symm p.val)) = _
  rw [d.toPartialDiffeomorph_symm_apply p]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothTwoSidedCollar.radialPartialDiffeomorph_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothTwoSidedCollar.radialPartialDiffeomorph_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothTwoSidedCollar.radialPartialDiffeomorph_symm_apply ``Submission.DifferentialGeometry.Topology.SmoothTwoSidedCollar.radialPartialDiffeomorph_symm_apply

theorem mem_radialPartialDiffeomorph_target (v : Metric.sphere (0 : E) 1)
    (hwidth : d.radius ≤ 1) (p : d.neighborhood) :
    p.val ∈ (d.radialPartialDiffeomorph v).target := by
  let _ : Nonempty (Metric.sphere (0 : E) 1) := ⟨v⟩
  refine ⟨?_, trivial, ?_⟩
  · change p.val ∈ d.toPartialDiffeomorph.target
    rw [d.toPartialDiffeomorph_target]
    exact p.property
  · change 0 < ((reverseRadiusProd (E := E) (n := n)).symm
      (d.toPartialDiffeomorph.symm p.val)).2
    rw [d.toPartialDiffeomorph_symm_apply p]
    change 0 < 1 - (d.toDiffeomorph.symm p).2.val
    linarith [(d.toDiffeomorph.symm p).2.property.2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothTwoSidedCollar.mem_radialPartialDiffeomorph_target then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothTwoSidedCollar.mem_radialPartialDiffeomorph_target"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothTwoSidedCollar.mem_radialPartialDiffeomorph_target ``Submission.DifferentialGeometry.Topology.SmoothTwoSidedCollar.mem_radialPartialDiffeomorph_target

theorem norm_radialPartialDiffeomorph_symm (v : Metric.sphere (0 : E) 1)
    (hwidth : d.radius ≤ 1) (p : d.neighborhood) :
    ‖(d.radialPartialDiffeomorph v).symm p.val‖ = 1 - (d.toDiffeomorph.symm p).2.val := by
  rw [d.radialPartialDiffeomorph_symm_apply v p, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by linarith [(d.toDiffeomorph.symm p).2.property.2] :
      0 < 1 - (d.toDiffeomorph.symm p).2.val), norm_eq_of_mem_sphere, mul_one]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothTwoSidedCollar.norm_radialPartialDiffeomorph_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothTwoSidedCollar.norm_radialPartialDiffeomorph_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothTwoSidedCollar.norm_radialPartialDiffeomorph_symm ``Submission.DifferentialGeometry.Topology.SmoothTwoSidedCollar.norm_radialPartialDiffeomorph_symm

theorem mem_radialPartialDiffeomorph_source_iff (v : Metric.sphere (0 : E) 1) (x : E) :
    x ∈ (d.radialPartialDiffeomorph v).source ↔
      x ≠ 0 ∧ 1 - ‖x‖ ∈ _root_.Set.Ioo (-d.radius) d.radius := by
  let _ : Nonempty (Metric.sphere (0 : E) 1) := ⟨v⟩
  change ((x ∈ ((Manifold.spherePolarChart (n := n) v).symm.trans
    (reverseRadiusProd (E := E) (n := n)).toPartialDiffeomorph).source) ∧
    (reverseRadiusProd (E := E) (n := n))
      ((Manifold.spherePolarChart (n := n) v).symm x) ∈ d.toPartialDiffeomorph.source) ↔ _
  rw [d.toPartialDiffeomorph_source]
  change ((x ≠ 0 ∧ True) ∧ (True ∧ 1 - ‖x‖ ∈ _root_.Set.Ioo (-d.radius) d.radius)) ↔ _
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothTwoSidedCollar.mem_radialPartialDiffeomorph_source_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothTwoSidedCollar.mem_radialPartialDiffeomorph_source_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothTwoSidedCollar.mem_radialPartialDiffeomorph_source_iff ``Submission.DifferentialGeometry.Topology.SmoothTwoSidedCollar.mem_radialPartialDiffeomorph_source_iff

end DifferentialGeometry.Topology.SmoothTwoSidedCollar
