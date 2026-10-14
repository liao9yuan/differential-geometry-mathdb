import Submission.DifferentialGeometry.Topology.Morse.RegularLevel.LevelSet
import Submission.DifferentialGeometry.Topology.Manifold.ModelHomeomorph
import Mathlib.Geometry.Manifold.Instances.Real

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.Manifold

namespace DifferentialGeometry.Topology.Morse

noncomputable def morseModelEuclideanEquiv (m : ℕ) :
    MorseModel (m + 1) ≃L[ℝ] EuclideanSpace ℝ (Fin (m + 1)) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (m + 1) => ℝ)).symm.trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
      (Equiv.swap (0 : Fin (m + 1)) (Fin.last m))).toContinuousLinearEquiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Morse.morseModelEuclideanEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Morse.morseModelEuclideanEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Morse.morseModelEuclideanEquiv ``Submission.DifferentialGeometry.Topology.Morse.morseModelEuclideanEquiv

@[simp]
theorem morseModelEuclideanEquiv_apply_zero (m : ℕ) (x : MorseModel (m + 1)) :
    morseModelEuclideanEquiv m x 0 = x (Fin.last m) := by
  simp [morseModelEuclideanEquiv, LinearIsometryEquiv.piLpCongrLeft_apply,
    Equiv.piCongrLeft']

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Morse.morseModelEuclideanEquiv_apply_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Morse.morseModelEuclideanEquiv_apply_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Morse.morseModelEuclideanEquiv_apply_zero ``Submission.DifferentialGeometry.Topology.Morse.morseModelEuclideanEquiv_apply_zero

@[simp]
theorem morseModelEuclideanEquiv_symm_apply_last (m : ℕ)
    (x : EuclideanSpace ℝ (Fin (m + 1))) :
    (morseModelEuclideanEquiv m).symm x (Fin.last m) = x 0 := by
  have h := morseModelEuclideanEquiv_apply_zero m ((morseModelEuclideanEquiv m).symm x)
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using h.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Morse.morseModelEuclideanEquiv_symm_apply_last then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Morse.morseModelEuclideanEquiv_symm_apply_last"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Morse.morseModelEuclideanEquiv_symm_apply_last ``Submission.DifferentialGeometry.Topology.Morse.morseModelEuclideanEquiv_symm_apply_last

noncomputable def morseHalfSpaceEuclideanHomeomorph (m : ℕ) :
    MorseHalfSpace m ≃ₜ EuclideanHalfSpace (m + 1) where
  toFun x := ⟨morseModelEuclideanEquiv m x.1, by simpa using x.2⟩
  invFun x := ⟨(morseModelEuclideanEquiv m).symm x.1, by simpa using x.2⟩
  left_inv x := Subtype.ext ((morseModelEuclideanEquiv m).symm_apply_apply x.1)
  right_inv x := Subtype.ext ((morseModelEuclideanEquiv m).apply_symm_apply x.1)
  continuous_toFun := ((morseModelEuclideanEquiv m).continuous.comp
    continuous_subtype_val).subtype_mk _
  continuous_invFun := ((morseModelEuclideanEquiv m).symm.continuous.comp
    continuous_subtype_val).subtype_mk _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Morse.morseHalfSpaceEuclideanHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Morse.morseHalfSpaceEuclideanHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Morse.morseHalfSpaceEuclideanHomeomorph ``Submission.DifferentialGeometry.Topology.Morse.morseHalfSpaceEuclideanHomeomorph

@[simp]
theorem morseHalfSpaceEuclideanHomeomorph_apply_val (m : ℕ) (x : MorseHalfSpace m) :
    (morseHalfSpaceEuclideanHomeomorph m x).1 = morseModelEuclideanEquiv m x.1 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Morse.morseHalfSpaceEuclideanHomeomorph_apply_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Morse.morseHalfSpaceEuclideanHomeomorph_apply_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Morse.morseHalfSpaceEuclideanHomeomorph_apply_val ``Submission.DifferentialGeometry.Topology.Morse.morseHalfSpaceEuclideanHomeomorph_apply_val

@[simp]
theorem morseHalfSpaceEuclideanHomeomorph_symm_apply_val (m : ℕ)
    (x : EuclideanHalfSpace (m + 1)) :
    ((morseHalfSpaceEuclideanHomeomorph m).symm x).1 =
      (morseModelEuclideanEquiv m).symm x.1 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Morse.morseHalfSpaceEuclideanHomeomorph_symm_apply_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Morse.morseHalfSpaceEuclideanHomeomorph_symm_apply_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Morse.morseHalfSpaceEuclideanHomeomorph_symm_apply_val ``Submission.DifferentialGeometry.Topology.Morse.morseHalfSpaceEuclideanHomeomorph_symm_apply_val

@[simp]
theorem modelWithCornersEuclideanHalfSpace_morseHalfSpaceEuclideanHomeomorph
    (m : ℕ) (x : MorseHalfSpace m) :
    modelWithCornersEuclideanHalfSpace (m + 1) (morseHalfSpaceEuclideanHomeomorph m x) =
      morseModelEuclideanEquiv m (morseModelWithCornersHalfSpace m x) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Morse.modelWithCornersEuclideanHalfSpace_morseHalfSpaceEuclideanHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Morse.modelWithCornersEuclideanHalfSpace_morseHalfSpaceEuclideanHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Morse.modelWithCornersEuclideanHalfSpace_morseHalfSpaceEuclideanHomeomorph ``Submission.DifferentialGeometry.Topology.Morse.modelWithCornersEuclideanHalfSpace_morseHalfSpaceEuclideanHomeomorph

end DifferentialGeometry.Topology.Morse

namespace DifferentialGeometry.Topology.Morse

theorem morseHalfSpaceEuclideanHomeomorph_isManifold {m : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (MorseHalfSpace m) M] {n : WithTop ℕ∞}
    [IsManifold (morseModelWithCornersHalfSpace m) n M] :
    letI := ChartedSpace.transHomeomorph (M := M) (morseHalfSpaceEuclideanHomeomorph m)
    IsManifold (modelWithCornersEuclideanHalfSpace (m + 1)) n M := by
  apply ChartedSpace.isManifold_transHomeomorph
    (I := (morseModelWithCornersHalfSpace m).transContinuousLinearEquiv
      (morseModelEuclideanEquiv m))
  exact fun _ => rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Morse.morseHalfSpaceEuclideanHomeomorph_isManifold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Morse.morseHalfSpaceEuclideanHomeomorph_isManifold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Morse.morseHalfSpaceEuclideanHomeomorph_isManifold ``Submission.DifferentialGeometry.Topology.Morse.morseHalfSpaceEuclideanHomeomorph_isManifold

end DifferentialGeometry.Topology.Morse
