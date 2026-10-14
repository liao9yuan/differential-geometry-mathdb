import Submission.DifferentialGeometry.Topology.Manifold.SpherePolarCoordinates
import Submission.DifferentialGeometry.Topology.Diffeomorph.FiberwiseAffine
import Mathlib.Tactic.Linarith

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Metric _root_.Manifold
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology.Manifold

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]
  {E' E'' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [NormedAddCommGroup E''] [NormedSpace ℝ E'']
  {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E' H} {J : ModelWithCorners ℝ E'' H'}
  {Z P : Type*} [TopologicalSpace Z] [ChartedSpace H Z]
  [TopologicalSpace P] [ChartedSpace H' P]

def ballComplementRadialCollar
    (b : PartialDiffeomorph 𝓘(ℝ, E) I E Z ∞)
    (F : PartialDiffeomorph I J Z P ∞)
    (v : _root_.Metric.sphere (0 : E) 1) (R : ℝ) (hR : R ≠ 1) :
    PartialDiffeomorph ((𝓡 n).prod 𝓘(ℝ, ℝ)) J
      (_root_.Metric.sphere (0 : E) 1 × ℝ) P ∞ :=
  (((Diffeomorph.fiberwiseAffine (I := 𝓡 n)
      (fun _ : _root_.Metric.sphere (0 : E) 1 => R) (fun _ => 1 - R)
      contMDiff_const contMDiff_const
      (fun _ => sub_ne_zero.mpr hR.symm)).toPartialDiffeomorph.trans
      (spherePolarChart (n := n) v)).trans b).trans F

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.ballComplementRadialCollar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.ballComplementRadialCollar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.ballComplementRadialCollar ``Submission.DifferentialGeometry.Topology.Manifold.ballComplementRadialCollar

@[simp] theorem ballComplementRadialCollar_apply
    (b : PartialDiffeomorph 𝓘(ℝ, E) I E Z ∞)
    (F : PartialDiffeomorph I J Z P ∞)
    (v : _root_.Metric.sphere (0 : E) 1) (R : ℝ) (hR : R ≠ 1)
    (q : _root_.Metric.sphere (0 : E) 1 × ℝ) :
    ballComplementRadialCollar (n := n) b F v R hR q =
      F (b ((R + (1 - R) * q.2) • (q.1 : E))) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.ballComplementRadialCollar_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.ballComplementRadialCollar_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.ballComplementRadialCollar_apply ``Submission.DifferentialGeometry.Topology.Manifold.ballComplementRadialCollar_apply

theorem ballComplementRadialCollar_apply_one
    (b : PartialDiffeomorph 𝓘(ℝ, E) I E Z ∞)
    (F : PartialDiffeomorph I J Z P ∞)
    (v z : _root_.Metric.sphere (0 : E) 1) (R : ℝ) (hR : R ≠ 1) :
    ballComplementRadialCollar (n := n) b F v R hR (z, 1) = F (b z) := by
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.ballComplementRadialCollar_apply_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.ballComplementRadialCollar_apply_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.ballComplementRadialCollar_apply_one ``Submission.DifferentialGeometry.Topology.Manifold.ballComplementRadialCollar_apply_one

private theorem radial_slab_bounds {R t : ℝ} (hR : 1 < R) (ht : t ∈ _root_.Set.Icc (0 : ℝ) 1) :
    R + (1 - R) * t ∈ _root_.Set.Icc (1 : ℝ) R := by
  constructor <;> nlinarith [ht.1, ht.2]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.radial_slab_bounds
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.radial_slab_bounds target :: scope.openDecls } }

private theorem radial_slab_mem_complement
    (b : PartialDiffeomorph 𝓘(ℝ, E) I E Z ∞) {R : ℝ} (hR : 1 < R)
    (hb : _root_.Metric.closedBall (0 : E) R ⊆ b.source)
    (q : _root_.Metric.sphere (0 : E) 1 × ℝ) (hq : q.2 ∈ _root_.Set.Icc (0 : ℝ) 1) :
    b ((R + (1 - R) * q.2) • (q.1 : E)) ∈ (b '' _root_.Metric.ball (0 : E) 1)ᶜ := by
  have hr := radial_slab_bounds hR hq
  have hn : ‖(R + (1 - R) * q.2) • (q.1 : E)‖ = R + (1 - R) * q.2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith [hr.1]),
      norm_eq_of_mem_sphere, mul_one]
  rintro ⟨w, hw, heq⟩
  have hws : w ∈ b.source := hb ((_root_.Metric.closedBall_subset_closedBall hR.le) (_root_.Metric.ball_subset_closedBall hw))
  have hqs : (R + (1 - R) * q.2) • (q.1 : E) ∈ b.source := by
    apply hb
    rw [mem_closedBall_zero_iff, hn]
    exact hr.2
  have hwq := b.injOn hws hqs heq
  have hnlt := mem_ball_zero_iff.mp hw
  rw [hwq, hn] at hnlt
  exact not_lt_of_ge hr.1 hnlt

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.radial_slab_mem_complement
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.radial_slab_mem_complement target :: scope.openDecls } }

theorem unit_slab_subset_ballComplementRadialCollar_source
    (b : PartialDiffeomorph 𝓘(ℝ, E) I E Z ∞)
    (F : PartialDiffeomorph I J Z P ∞)
    (v : _root_.Metric.sphere (0 : E) 1) {R : ℝ} (hR : 1 < R)
    (hb : _root_.Metric.closedBall (0 : E) R ⊆ b.source)
    (hF : (b '' _root_.Metric.ball (0 : E) 1)ᶜ ⊆ F.source) :
    _root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1 ⊆
      (ballComplementRadialCollar (n := n) b F v R hR.ne').source := by
  intro q hq
  have hr := radial_slab_bounds hR hq.2
  refine ⟨⟨⟨mem_univ _, ?_⟩, ?_⟩, ?_⟩
  · change 0 < R + (1 - R) * q.2
    linarith [hr.1]
  · apply hb
    change (R + (1 - R) * q.2) • (q.1 : E) ∈ _root_.Metric.closedBall (0 : E) R
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith [hr.1]),
      norm_eq_of_mem_sphere, mul_one]
    exact hr.2
  · exact hF (radial_slab_mem_complement b hR hb q hq.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.unit_slab_subset_ballComplementRadialCollar_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.unit_slab_subset_ballComplementRadialCollar_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.unit_slab_subset_ballComplementRadialCollar_source ``Submission.DifferentialGeometry.Topology.Manifold.unit_slab_subset_ballComplementRadialCollar_source

theorem ballComplementRadialCollar_image_unit_slab_subset
    (b : PartialDiffeomorph 𝓘(ℝ, E) I E Z ∞)
    (F : PartialDiffeomorph I J Z P ∞)
    (v : _root_.Metric.sphere (0 : E) 1) {R : ℝ} (hR : 1 < R)
    (hb : _root_.Metric.closedBall (0 : E) R ⊆ b.source) :
    ballComplementRadialCollar (n := n) b F v R hR.ne' '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) ⊆
      F '' (b '' _root_.Metric.ball (0 : E) 1)ᶜ := by
  rintro y ⟨q, hq, rfl⟩
  exact ⟨_, radial_slab_mem_complement b hR hb q hq.2, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.ballComplementRadialCollar_image_unit_slab_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.ballComplementRadialCollar_image_unit_slab_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.ballComplementRadialCollar_image_unit_slab_subset ``Submission.DifferentialGeometry.Topology.Manifold.ballComplementRadialCollar_image_unit_slab_subset

end DifferentialGeometry.Topology.Manifold
