import Submission.DifferentialGeometry.External.Schoenflies.JordanSchoenflies
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Homeomorph.Lemmas

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PlanarJordan

private theorem isJordanCurve_range_circle
    {e : Circle → Schoenflies.Plane} (he : Continuous e)
    (hi : Function.Injective e) : Schoenflies.IsJordanCurve (_root_.Set.range e) := by
  have hp : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  let f : ℝ → Schoenflies.Plane :=
    fun t ↦ e (Circle.exp (2 * Real.pi * t - Real.pi))
  refine ⟨f, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact (he.comp (Circle.exp.continuous.comp
      ((continuous_const.mul continuous_id).sub continuous_const))).continuousOn
  · change e (Circle.exp _) = e (Circle.exp _)
    apply congrArg e
    apply Circle.exp_eq_exp.mpr
    refine ⟨-1, ?_⟩
    norm_num
    ring
  · intro x hx y hy h
    have hx' : 2 * Real.pi * x - Real.pi ∈ _root_.Set.Ico (-Real.pi) Real.pi := by
      constructor
      · linarith [mul_nonneg hp.le hx.1]
      · linarith [mul_lt_mul_of_pos_left hx.2 hp]
    have hy' : 2 * Real.pi * y - Real.pi ∈ _root_.Set.Ico (-Real.pi) Real.pi := by
      constructor
      · linarith [mul_nonneg hp.le hy.1]
      · linarith [mul_lt_mul_of_pos_left hy.2 hp]
    have hxy := Circle.exp_injOn_Ico (a := -Real.pi) (b := Real.pi)
      (by linarith) hx' hy' (hi h)
    have hmul : 2 * Real.pi * x = 2 * Real.pi * y := by linarith [hxy]
    exact mul_left_cancel₀ hp.ne' hmul
  · apply Subset.antisymm
    · rintro _ ⟨t, _, rfl⟩
      exact _root_.Set.mem_range_self _
    · rintro _ ⟨z, rfl⟩
      let t := (Complex.arg (z : ℂ) + Real.pi) / (2 * Real.pi)
      have ht : t ∈ _root_.Set.Icc (0 : ℝ) 1 := by
        constructor
        · exact div_nonneg (by linarith [Complex.neg_pi_lt_arg (z : ℂ)]) hp.le
        · apply (div_le_iff₀ hp).mpr
          linarith [Complex.arg_le_pi (z : ℂ)]
      refine ⟨t, ht, ?_⟩
      have hangle : 2 * Real.pi * t - Real.pi = Complex.arg (z : ℂ) := by
        dsimp [t]
        field_simp
        ring
      dsimp [f]
      rw [hangle, Circle.exp_arg]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PlanarJordan.isJordanCurve_range_circle
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PlanarJordan.isJordanCurve_range_circle target :: scope.openDecls } }

theorem isJordanCurve_range_of_isEmbedding_circle
    {e : Metric.sphere (0 : Schoenflies.Plane) 1 → Schoenflies.Plane}
    (he : Topology.IsEmbedding e) : Schoenflies.IsJordanCurve (_root_.Set.range e) := by
  let r := Complex.orthonormalBasisOneI.repr
  let q : Circle ≃ₜ Metric.sphere (0 : Schoenflies.Plane) 1 :=
    r.toHomeomorph.subtype (fun z ↦ by
      change z ∈ Metric.sphere (0 : ℂ) 1 ↔ r z ∈ Metric.sphere 0 1
      rw [mem_sphere_zero_iff_norm, mem_sphere_zero_iff_norm, r.norm_map])
  have h := isJordanCurve_range_circle (he.continuous.comp q.continuous)
    (he.injective.comp q.injective)
  rwa [_root_.Set.range_comp, q.surjective.range_eq, _root_.Set.image_univ] at h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PlanarJordan.isJordanCurve_range_of_isEmbedding_circle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PlanarJordan.isJordanCurve_range_of_isEmbedding_circle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PlanarJordan.isJordanCurve_range_of_isEmbedding_circle ``Submission.DifferentialGeometry.Topology.PlanarJordan.isJordanCurve_range_of_isEmbedding_circle

theorem isJordanCurve_range_of_isEmbedding_addCircle {T : ℝ} (hT : T ≠ 0)
    {e : AddCircle T → Schoenflies.Plane} (he : Topology.IsEmbedding e) :
    Schoenflies.IsJordanCurve (_root_.Set.range e) := by
  let G := AddCircle.homeomorphCircle hT
  have h := isJordanCurve_range_circle (he.continuous.comp G.symm.continuous)
    (he.injective.comp G.symm.injective)
  rwa [_root_.Set.range_comp, G.symm.surjective.range_eq, _root_.Set.image_univ] at h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PlanarJordan.isJordanCurve_range_of_isEmbedding_addCircle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PlanarJordan.isJordanCurve_range_of_isEmbedding_addCircle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PlanarJordan.isJordanCurve_range_of_isEmbedding_addCircle ``Submission.DifferentialGeometry.Topology.PlanarJordan.isJordanCurve_range_of_isEmbedding_addCircle

theorem exists_homeomorph_extending_circle_embedding
    {e : Metric.sphere (0 : Schoenflies.Plane) 1 → Schoenflies.Plane}
    (he : Topology.IsEmbedding e) :
    ∃ F : Schoenflies.Plane ≃ₜ Schoenflies.Plane,
      ∀ z : Metric.sphere (0 : Schoenflies.Plane) 1, F z = e z := by
  have hs : Schoenflies.IsJordanCurve (Metric.sphere (0 : Schoenflies.Plane) 1) := by
    have hi : Topology.IsEmbedding
        (Subtype.val : Metric.sphere (0 : Schoenflies.Plane) 1 → Schoenflies.Plane) :=
      .subtypeVal
    simpa only [Subtype.range_coe] using isJordanCurve_range_of_isEmbedding_circle hi
  obtain ⟨F, hF⟩ := Schoenflies.jordan_schoenflies_of_homeomorph
    hs (isJordanCurve_range_of_isEmbedding_circle he) he.toHomeomorph
  exact ⟨F, fun z ↦ by
    simpa only [Topology.IsEmbedding.toHomeomorph_apply_coe] using hF z⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PlanarJordan.exists_homeomorph_extending_circle_embedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PlanarJordan.exists_homeomorph_extending_circle_embedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PlanarJordan.exists_homeomorph_extending_circle_embedding ``Submission.DifferentialGeometry.Topology.PlanarJordan.exists_homeomorph_extending_circle_embedding

end DifferentialGeometry.Topology.PlanarJordan
