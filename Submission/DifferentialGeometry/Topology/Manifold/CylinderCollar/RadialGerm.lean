import Submission.DifferentialGeometry.Topology.Manifold.CylinderCollar.Coordinates
import Submission.DifferentialGeometry.Topology.Diffeomorph.SphereGerm

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Function _root_.Manifold _root_.Metric
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology.Manifold

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.E3 target :: scope.openDecls } }
private abbrev S2 := Metric.sphere (0 : E3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.S2 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.Manifold.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }

def cylinderRadialGerm (v : S2)
    (A : PartialDiffeomorph SphereCylinderModel SphereCylinderModel SphereCylinder SphereCylinder ∞) :
    PartialDiffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞ :=
  ((cylinderExponentialChart v).symm.trans A).trans (cylinderExponentialChart v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.cylinderRadialGerm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.cylinderRadialGerm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.cylinderRadialGerm ``Submission.DifferentialGeometry.Topology.Manifold.cylinderRadialGerm

theorem cylinderRadialGerm_source (v : S2)
    (A : PartialDiffeomorph SphereCylinderModel SphereCylinderModel SphereCylinder SphereCylinder ∞)
    (x : E3) :
    x ∈ (cylinderRadialGerm v A).source ↔ x ≠ 0 ∧ (cylinderExponentialChart v).symm x ∈ A.source := by
  change ((x ∈ (cylinderExponentialChart v).target ∧ _ ∈ A.source) ∧ _ ∈ (cylinderExponentialChart v).source) ↔ _
  rw [cylinderExponentialChart_target, cylinderExponentialChart_source]
  simp only [_root_.Set.mem_compl_iff, _root_.Set.mem_singleton_iff, OpenPartialHomeomorph.symm_symm, _root_.Set.mem_univ, and_true, ne_eq,
    PartialDiffeomorph.symm_toPartialEquiv, and_congr_right_iff]
  intro _
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.cylinderRadialGerm_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.cylinderRadialGerm_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.cylinderRadialGerm_source ``Submission.DifferentialGeometry.Topology.Manifold.cylinderRadialGerm_source

theorem cylinderRadialGerm_sphere_source (v : S2)
    (A : PartialDiffeomorph SphereCylinderModel SphereCylinderModel SphereCylinder SphereCylinder ∞)
    (hsource : ∀ p : S2, (p, 0) ∈ A.source) :
    sphere (0 : E3) 1 ⊆ (cylinderRadialGerm v A).source := by
  intro x hx
  rw [cylinderRadialGerm_source]
  refine ⟨ne_zero_of_mem_unit_sphere ⟨x, hx⟩, ?_⟩
  rw [cylinderExponentialChart_symm_sphere v ⟨x, hx⟩]
  exact hsource _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.cylinderRadialGerm_sphere_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.cylinderRadialGerm_sphere_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.cylinderRadialGerm_sphere_source ``Submission.DifferentialGeometry.Topology.Manifold.cylinderRadialGerm_sphere_source

theorem cylinderRadialGerm_sphere_fixed (v : S2)
    (A : PartialDiffeomorph SphereCylinderModel SphereCylinderModel SphereCylinder SphereCylinder ∞)
    (hfixed : ∀ p : S2, A (p, 0) = (p, 0)) :
    EqOn (cylinderRadialGerm v A) id (_root_.Metric.sphere (0 : E3) 1) := by
  intro x hx
  change cylinderExponentialChart v (A ((cylinderExponentialChart v).symm x)) = x
  rw [cylinderExponentialChart_symm_sphere v ⟨x, hx⟩, hfixed, cylinderExponentialChart_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.cylinderRadialGerm_sphere_fixed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.cylinderRadialGerm_sphere_fixed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.cylinderRadialGerm_sphere_fixed ``Submission.DifferentialGeometry.Topology.Manifold.cylinderRadialGerm_sphere_fixed

theorem cylinderRadialGerm_mapsTo_closedBall (v : S2)
    (A : PartialDiffeomorph SphereCylinderModel SphereCylinderModel SphereCylinder SphereCylinder ∞)
    (hside : ∀ q ∈ A.source, q.2 ≤ 0 → (A q).2 ≤ 0) :
    _root_.Set.MapsTo (cylinderRadialGerm v A)
      (_root_.Metric.closedBall (0 : E3) 1 ∩ (cylinderRadialGerm v A).source) (_root_.Metric.closedBall (0 : E3) 1) := by
  intro x hx
  obtain ⟨hx0, hxA⟩ := (cylinderRadialGerm_source v A x).mp hx.2
  have hq : ((cylinderExponentialChart v).symm x).2 ≤ 0 := by
    rw [cylinderExponentialChart_symm_apply v x hx0]
    exact Real.log_nonpos (norm_nonneg x) (mem_closedBall_zero_iff.mp hx.1)
  change ‖cylinderExponentialChart v (A ((cylinderExponentialChart v).symm x)) - 0‖ ≤ 1
  rw [sub_zero, norm_cylinderExponentialChart]
  exact Real.exp_le_one_iff.mpr (hside _ hxA hq)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.cylinderRadialGerm_mapsTo_closedBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.cylinderRadialGerm_mapsTo_closedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.cylinderRadialGerm_mapsTo_closedBall ``Submission.DifferentialGeometry.Topology.Manifold.cylinderRadialGerm_mapsTo_closedBall

theorem exists_supported_radial_diffeomorph_eq_cylinder_germ
    (v : S2)
    (A : PartialDiffeomorph SphereCylinderModel SphereCylinderModel SphereCylinder SphereCylinder ∞)
    (hsource : ∀ p : S2, (p, 0) ∈ A.source)
    (hfixed : ∀ p : S2, A (p, 0) = (p, 0))
    (hside : ∀ q ∈ A.source, q.2 ≤ 0 → (A q).2 ≤ 0)
    (l u : ℝ) (hl : l < 0) (hu : 0 < u) :
    ∃ F : E3 ≃ₘ[ℝ] E3,
      ∃ V : Set E3, IsOpen V ∧ _root_.Metric.sphere (0 : E3) 1 ⊆ V ∧ V ⊆ (cylinderRadialGerm v A).source ∧
        _root_.Set.EqOn F (cylinderRadialGerm v A) V ∧ F 0 = 0 ∧
        ∃ K : Set E3, IsCompact K ∧ K ⊆ {x : E3 | Real.exp l < ‖x‖ ∧ ‖x‖ < Real.exp u} ∧
          EqOn F id Kᶜ ∧ _root_.Set.EqOn F.symm id Kᶜ := by
  let O : Set E3 := {x | Real.exp l < ‖x‖ ∧ ‖x‖ < Real.exp u}
  have hO : IsOpen O := (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)
  have hSO : _root_.Metric.sphere (0 : E3) 1 ⊆ O := by
    intro x hx
    change Real.exp l < ‖x‖ ∧ ‖x‖ < Real.exp u
    rw [mem_sphere_zero_iff_norm.mp hx]
    exact ⟨Real.exp_lt_one_iff.mpr hl, Real.one_lt_exp_iff.mpr hu⟩
  obtain ⟨V, hV, hSV, hVA, Φ, _, _, _, hΦ, _, _, K, hK, hKO, hfix⟩ :=
    (cylinderRadialGerm v A).exists_contDiff_compact_isotopy_eqOn_sphere_neighborhood zero_lt_one
      (cylinderRadialGerm_sphere_source v A hsource) (cylinderRadialGerm_sphere_fixed v A hfixed)
      (cylinderRadialGerm_mapsTo_closedBall v A hside) hO hSO
  refine ⟨Φ 1, V, hV, hSV, hVA, hΦ, ?_, K, hK, hKO, (hfix 1).1, (hfix 1).2⟩
  apply (hfix 1).1
  intro hz
  have hbad := (hKO hz).1
  rw [norm_zero] at hbad
  exact (not_lt_of_ge (Real.exp_pos l).le) hbad

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_supported_radial_diffeomorph_eq_cylinder_germ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_supported_radial_diffeomorph_eq_cylinder_germ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_supported_radial_diffeomorph_eq_cylinder_germ ``Submission.DifferentialGeometry.Topology.Manifold.exists_supported_radial_diffeomorph_eq_cylinder_germ

end DifferentialGeometry.Topology.Manifold
