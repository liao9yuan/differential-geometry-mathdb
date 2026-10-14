import Submission.DifferentialGeometry.Topology.Manifold.SphereDiffeomorphDegree
import Submission.DifferentialGeometry.Topology.Manifold.StereographicAntipodal

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Function _root_.Manifold _root_.Submission.Manifold _root_.Module _root_.Submission.Module
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

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

private theorem radialExtension_post_antipodal
    (η : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2) :
    sphereRadialExtension (η.trans (sphereAntipodalDiffeomorph (n := 2))) =
      -sphereRadialExtension η := by
  funext x
  by_cases hx : x = 0
  · subst x
    simp [sphereRadialExtension]
  · rw [sphereRadialExtension_of_ne_zero _ hx, Pi.neg_apply, sphereRadialExtension_of_ne_zero _ hx]
    change ‖x‖ • (-(η _ : E3)) = -(‖x‖ • (η _ : E3))
    exact smul_neg _ _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.radialExtension_post_antipodal
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.radialExtension_post_antipodal target :: scope.openDecls } }

theorem sphereDiffeomorphDegree_eq_one_or_neg_one
    (η : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2) :
    sphereDiffeomorphDegree η = 1 ∨ sphereDiffeomorphDegree η = -1 := by
  let v : S2 := ⟨EuclideanSpace.single 0 1, by simp⟩
  rw [sphereDiffeomorphDegree_eq_sign η v]
  split_ifs <;> simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.sphereDiffeomorphDegree_eq_one_or_neg_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.sphereDiffeomorphDegree_eq_one_or_neg_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.sphereDiffeomorphDegree_eq_one_or_neg_one ``Submission.DifferentialGeometry.Topology.Manifold.sphereDiffeomorphDegree_eq_one_or_neg_one

theorem sphereDiffeomorphDegree_post_antipodal_eq_one
    (η : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2) (hη : sphereDiffeomorphDegree η = -1) :
    sphereDiffeomorphDegree (η.trans (sphereAntipodalDiffeomorph (n := 2))) = 1 := by
  let v : S2 := ⟨EuclideanSpace.single 0 1, by simp⟩
  apply (sphereDiffeomorphDegree_eq_one_iff _ v).mpr
  have hne := det_fderiv_sphereRadialExtension_ne_zero η (ne_zero_of_mem_unit_sphere v)
  have hnot : ¬ 0 < (fderiv ℝ (sphereRadialExtension η) (v : E3)).toLinearMap.det := by
    intro hp
    have hh := (sphereDiffeomorphDegree_eq_one_iff η v).mpr hp
    rw [hη] at hh
    norm_num at hh
  have hneg : (fderiv ℝ (sphereRadialExtension η) (v : E3)).toLinearMap.det < 0 :=
    lt_of_le_of_ne (le_of_not_gt hnot) hne
  rw [radialExtension_post_antipodal, fderiv_neg]
  change LinearMap.det (-(fderiv ℝ (sphereRadialExtension η) (v : E3)).toLinearMap) > 0
  rw [← neg_one_smul ℝ ((fderiv ℝ (sphereRadialExtension η) (v : E3)).toLinearMap), LinearMap.det_smul]
  norm_num
  exact hneg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.sphereDiffeomorphDegree_post_antipodal_eq_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.sphereDiffeomorphDegree_post_antipodal_eq_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.sphereDiffeomorphDegree_post_antipodal_eq_one ``Submission.DifferentialGeometry.Topology.Manifold.sphereDiffeomorphDegree_post_antipodal_eq_one

theorem exists_sphere_degree_one_reflection
    (η : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2) :
    ∃ ηpos : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2,
      sphereDiffeomorphDegree ηpos = 1 ∧
      ((sphereDiffeomorphDegree η = 1 ∧ ηpos = η) ∨
        (sphereDiffeomorphDegree η = -1 ∧ ηpos = η.trans (sphereAntipodalDiffeomorph (n := 2)))) := by
  rcases sphereDiffeomorphDegree_eq_one_or_neg_one η with h | h
  · exact ⟨η, h, Or.inl ⟨h, rfl⟩⟩
  · exact ⟨η.trans (sphereAntipodalDiffeomorph (n := 2)),
      sphereDiffeomorphDegree_post_antipodal_eq_one η h, Or.inr ⟨h, rfl⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_sphere_degree_one_reflection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_sphere_degree_one_reflection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_sphere_degree_one_reflection ``Submission.DifferentialGeometry.Topology.Manifold.exists_sphere_degree_one_reflection


theorem sphereDiffeomorphDegree_symm_eq_one_iff
    (η : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2) :
    sphereDiffeomorphDegree η.symm = 1 ↔ sphereDiffeomorphDegree η = 1 := by
  have himp (f : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2) (hf : sphereDiffeomorphDegree f = 1) :
      sphereDiffeomorphDegree f.symm = 1 := by
    obtain ⟨J, hJ, hJi, hJ0, hJ1⟩ := (sphereDiffeomorphDegree_eq_one_iff_isotopy f).mp hf
    apply (sphereDiffeomorphDegree_eq_one_iff_isotopy f.symm).mpr
    exact ⟨fun t => (J t).symm, hJi, hJ, by change (J 0).symm = _; rw [hJ0], by change (J 1).symm = _; rw [hJ1, Diffeomorph.symm_refl]⟩
  constructor
  · intro h
    have hh := himp η.symm h
    have heq : η.symm.symm = η := by ext p; rfl
    rw [heq] at hh
    exact hh
  · exact himp η

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.sphereDiffeomorphDegree_symm_eq_one_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.sphereDiffeomorphDegree_symm_eq_one_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.sphereDiffeomorphDegree_symm_eq_one_iff ``Submission.DifferentialGeometry.Topology.Manifold.sphereDiffeomorphDegree_symm_eq_one_iff

theorem sphereDiffeomorphDegree_pre_antipodal_eq_one
    (η : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2) (hη : sphereDiffeomorphDegree η = -1) :
    sphereDiffeomorphDegree ((sphereAntipodalDiffeomorph (n := 2)).trans η) = 1 := by
  have hn : sphereDiffeomorphDegree η.symm = -1 := by
    rcases sphereDiffeomorphDegree_eq_one_or_neg_one η.symm with h | h
    · have hh := (sphereDiffeomorphDegree_symm_eq_one_iff η).mp h
      rw [hη] at hh
      norm_num at hh
    · exact h
  have hp := sphereDiffeomorphDegree_post_antipodal_eq_one η.symm hn
  have hi := (sphereDiffeomorphDegree_symm_eq_one_iff
    (η.symm.trans (sphereAntipodalDiffeomorph (n := 2)))).mpr hp
  have heq : (η.symm.trans (sphereAntipodalDiffeomorph (n := 2))).symm =
      (sphereAntipodalDiffeomorph (n := 2)).trans η := by ext q; rfl
  rw [heq] at hi
  exact hi

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.sphereDiffeomorphDegree_pre_antipodal_eq_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.sphereDiffeomorphDegree_pre_antipodal_eq_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.sphereDiffeomorphDegree_pre_antipodal_eq_one ``Submission.DifferentialGeometry.Topology.Manifold.sphereDiffeomorphDegree_pre_antipodal_eq_one

end DifferentialGeometry.Topology.Manifold
