import Submission.DifferentialGeometry.Geometry.Curvature.Riemann.Tensor

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {x : M}


omit [FiniteDimensional ℝ E] in
private theorem tensor02_vec2_smul
    (Q : Tensor02At (I := I) (M := M) x) (c : Real) (v : TangentSpace I x) :
    Q (vec2 (I := I) (c • v) (c • v)) = c ^ 2 * Q (vec2 (I := I) v v) := by
  have hfun :
      vec2 (I := I) (c • v) (c • v) = fun a : Fin 2 => c • vec2 (I := I) v v a := by
    funext a; fin_cases a <;> simp [vec2]
  rw [hfun]
  have hmap := Q.map_smul_univ (fun _ : Fin 2 => c) (vec2 (I := I) v v)
  simpa [Fin.prod_univ_two, pow_two, smul_eq_mul] using hmap

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.tensor02_vec2_smul
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.tensor02_vec2_smul target :: scope.openDecls } }


omit [FiniteDimensional ℝ E] in
private theorem metric_inner_smul_self
    (g : SmoothRiemannianMetric I M) (c : Real) (v : TangentSpace I x) :
    g.inner x (c • v) (c • v) = c ^ 2 * g.inner x v v := by
  have h1 : ∀ w : TangentSpace I x, g.inner x (c • v) w = c * g.inner x v w := by
    intro w
    rw [(g.inner x).map_smul c v, smul_apply, smul_eq_mul]
  rw [h1 (c • v), g.symm x v (c • v), h1 v]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.metric_inner_smul_self
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.metric_inner_smul_self target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
theorem tensor02_quadForm_le_of_unit_bound
    (g : SmoothRiemannianMetric I M) (Q : Tensor02At (I := I) (M := M) x) {Λ : Real}
    (hunit : ∀ u : TangentSpace I x, g.inner x u u = 1 → Q (vec2 (I := I) u u) ≤ Λ)
    (v : TangentSpace I x) :
    Q (vec2 (I := I) v v) ≤ Λ * g.inner x v v := by
  classical
  by_cases hv : v = 0
  · subst hv
    have hQ0 : Q (vec2 (I := I) (0 : TangentSpace I x) 0) = 0 :=
      Q.map_coord_zero (i := 0) (by simp [vec2])
    have hg0 : g.inner x (0 : TangentSpace I x) 0 = 0 := by
      rw [(g.inner x).map_zero, zero_apply]
    rw [hQ0, hg0, _root_.MulZeroClass.mul_zero]
  · have hpos : 0 < g.inner x v v := g.pos x v hv
    set c := (Real.sqrt (g.inner x v v))⁻¹ with hcdef
    have hr2 : Real.sqrt (g.inner x v v) ^ 2 = g.inner x v v := Real.sq_sqrt hpos.le
    have hc2 : c ^ 2 = (g.inner x v v)⁻¹ := by rw [hcdef, inv_pow, hr2]
    have hc2r : c ^ 2 * g.inner x v v = 1 := by
      rw [hc2]; exact inv_mul_cancel₀ (ne_of_gt hpos)
    have hgunit : g.inner x (c • v) (c • v) = 1 := by
      rw [metric_inner_smul_self g c v, hc2r]
    have hQunit : Q (vec2 (I := I) (c • v) (c • v)) ≤ Λ := hunit (c • v) hgunit
    have hQsmul : Q (vec2 (I := I) (c • v) (c • v)) = c ^ 2 * Q (vec2 (I := I) v v) :=
      tensor02_vec2_smul Q c v
    have hQv :
        Q (vec2 (I := I) v v) = g.inner x v v * Q (vec2 (I := I) (c • v) (c • v)) := by
      rw [hQsmul, ← mul_assoc, mul_comm (g.inner x v v) (c ^ 2), hc2r, one_mul]
    rw [hQv, mul_comm Λ (g.inner x v v)]
    exact mul_le_mul_of_nonneg_left hQunit hpos.le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.tensor02_quadForm_le_of_unit_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.tensor02_quadForm_le_of_unit_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.tensor02_quadForm_le_of_unit_bound ``Submission.DifferentialGeometry.Geometry.Curvature.tensor02_quadForm_le_of_unit_bound

omit [FiniteDimensional ℝ E] in
theorem tensor02_quadForm_abs_le_of_unit_bound
    (g : SmoothRiemannianMetric I M) (Q : Tensor02At (I := I) (M := M) x) {Λ : Real}
    (hunit : ∀ u : TangentSpace I x, g.inner x u u = 1 → |Q (vec2 (I := I) u u)| ≤ Λ)
    (v : TangentSpace I x) :
    |Q (vec2 (I := I) v v)| ≤ Λ * g.inner x v v := by
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · have h := tensor02_quadForm_le_of_unit_bound g (-Q) (Λ := Λ) ?_ v
    · change -(Q (vec2 (I := I) v v)) ≤ Λ * g.inner x v v at h
      linarith
    · intro u hu
      change -(Q (vec2 (I := I) u u)) ≤ Λ
      exact le_trans (neg_le_abs _) (hunit u hu)
  · refine tensor02_quadForm_le_of_unit_bound g Q (Λ := Λ) ?_ v
    intro u hu
    exact le_trans (le_abs_self _) (hunit u hu)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.tensor02_quadForm_abs_le_of_unit_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.tensor02_quadForm_abs_le_of_unit_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.tensor02_quadForm_abs_le_of_unit_bound ``Submission.DifferentialGeometry.Geometry.Curvature.tensor02_quadForm_abs_le_of_unit_bound

end DifferentialGeometry.Geometry.Curvature
