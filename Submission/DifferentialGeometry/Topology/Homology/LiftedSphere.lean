import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SphereTopHomology

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.ContinuousMap _root_.Metric _root_.Module
open scoped _root_.InnerProductSpace

universe u

namespace DifferentialGeometry.Topology


abbrev liftedSphereSpace (n : ℕ) := ULift.{u} (EuclideanSpace ℝ (Fin (n + 2)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedSphereSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedSphereSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedSphereSpace ``Submission.DifferentialGeometry.Topology.liftedSphereSpace



instance liftedSphereSpaceInnerProductSpace (n : ℕ) :
    InnerProductSpace ℝ (liftedSphereSpace.{u} n) where
  inner x y := _root_.Inner.inner ℝ x.down y.down
  norm_sq_eq_re_inner x := _root_.InnerProductSpace.norm_sq_eq_re_inner x.down
  conj_inner_symm x y := inner_conj_symm x.down y.down
  add_left x y z := inner_add_left x.down y.down z.down
  smul_left x y r := inner_smul_left x.down y.down r

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedSphereSpaceInnerProductSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedSphereSpaceInnerProductSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedSphereSpaceInnerProductSpace ``Submission.DifferentialGeometry.Topology.liftedSphereSpaceInnerProductSpace


theorem liftedSphereSpace_finrank (n : ℕ) : _root_.Module.finrank ℝ (liftedSphereSpace.{u} n) = n + 2 :=
  (ULift.moduleEquiv : liftedSphereSpace.{u} n ≃ₗ[ℝ]
    EuclideanSpace ℝ (Fin (n + 2))).finrank_eq.trans (by simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedSphereSpace_finrank then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedSphereSpace_finrank"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedSphereSpace_finrank ``Submission.DifferentialGeometry.Topology.liftedSphereSpace_finrank

instance liftedSphereSpace_finiteDimensional (n : ℕ) :
    FiniteDimensional ℝ (liftedSphereSpace.{u} n) :=
  FiniteDimensional.of_finrank_pos (by rw [liftedSphereSpace_finrank]; omega)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedSphereSpace_finiteDimensional then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedSphereSpace_finiteDimensional"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedSphereSpace_finiteDimensional ``Submission.DifferentialGeometry.Topology.liftedSphereSpace_finiteDimensional


abbrev liftedHomotopySphere (n : ℕ) :=
  ULift.{u} (_root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedHomotopySphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedHomotopySphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedHomotopySphere ``Submission.DifferentialGeometry.Topology.liftedHomotopySphere



def liftedSphereHomeomorph (n : ℕ) :
    liftedHomotopySphere.{u} n ≃ₜ _root_.Metric.sphere (0 : liftedSphereSpace.{u} n) 1 where
  toFun x := ⟨ULift.up x.down.val, x.down.property⟩
  invFun x := ULift.up ⟨x.val.down, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := ((Homeomorph.ulift.symm.continuous).comp
    (continuous_subtype_val.comp Homeomorph.ulift.continuous)).subtype_mk _
  continuous_invFun := Homeomorph.ulift.symm.continuous.comp
    ((Homeomorph.ulift.continuous.comp continuous_subtype_val).subtype_mk _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedSphereHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedSphereHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedSphereHomeomorph ``Submission.DifferentialGeometry.Topology.liftedSphereHomeomorph




def integralLiftedSphereTopEquiv (n : ℕ) :
    integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n) ≃ₗ[ℤ] ℤ :=
  (integralSingularHomologyHomotopyEquiv (n + 1)
    (liftedSphereHomeomorph n).toHomotopyEquiv).trans
      (integralSphereTopHomologyEquiv n (liftedSphereSpace n) (liftedSphereSpace_finrank n))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralLiftedSphereTopEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralLiftedSphereTopEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralLiftedSphereTopEquiv ``Submission.DifferentialGeometry.Topology.integralLiftedSphereTopEquiv




def integralLiftedSphereGenerator (n : ℕ) :
    integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n) :=
  (integralLiftedSphereTopEquiv n).symm 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralLiftedSphereGenerator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralLiftedSphereGenerator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralLiftedSphereGenerator ``Submission.DifferentialGeometry.Topology.integralLiftedSphereGenerator


theorem integralLiftedSphereGenerator_coordinate (n : ℕ) :
    integralLiftedSphereTopEquiv n (integralLiftedSphereGenerator.{u} n) = 1 :=
  (integralLiftedSphereTopEquiv n).apply_symm_apply 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralLiftedSphereGenerator_coordinate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralLiftedSphereGenerator_coordinate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralLiftedSphereGenerator_coordinate ``Submission.DifferentialGeometry.Topology.integralLiftedSphereGenerator_coordinate

end DifferentialGeometry.Topology
