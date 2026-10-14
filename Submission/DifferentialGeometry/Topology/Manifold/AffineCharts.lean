import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Calculus.ContDiff.Operations

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Manifold
open scoped _root_.ContDiff _root_.Manifold _root_.Topology

namespace DifferentialGeometry.Topology

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [TopologicalSpace M]



def affineChart (c : OpenPartialHomeomorph E M) (a : E) (L : V ≃L[ℝ] E) :
    OpenPartialHomeomorph V M :=
  (L.toHomeomorph.trans (Homeomorph.addLeft a)).toOpenPartialHomeomorph.trans c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.affineChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.affineChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.affineChart ``Submission.DifferentialGeometry.Topology.affineChart

@[simp] theorem affineChart_apply (c : OpenPartialHomeomorph E M) (a : E)
    (L : V ≃L[ℝ] E) (x : V) : affineChart c a L x = c (a + L x) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.affineChart_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.affineChart_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.affineChart_apply ``Submission.DifferentialGeometry.Topology.affineChart_apply

@[simp] theorem affineChart_source (c : OpenPartialHomeomorph E M) (a : E)
    (L : V ≃L[ℝ] E) : (affineChart c a L).source = (fun x => a + L x) ⁻¹' c.source := by
  simp [affineChart, Function.comp_def]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.affineChart_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.affineChart_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.affineChart_source ``Submission.DifferentialGeometry.Topology.affineChart_source

@[simp] theorem affineChart_target (c : OpenPartialHomeomorph E M) (a : E)
    (L : V ≃L[ℝ] E) : (affineChart c a L).target = c.target := by
  simp [affineChart]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.affineChart_target then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.affineChart_target"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.affineChart_target ``Submission.DifferentialGeometry.Topology.affineChart_target

@[simp] theorem affineChart_symm_apply (c : OpenPartialHomeomorph E M) (a : E)
    (L : V ≃L[ℝ] E) (x : M) : (affineChart c a L).symm x = L.symm (-a + c.symm x) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.affineChart_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.affineChart_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.affineChart_symm_apply ``Submission.DifferentialGeometry.Topology.affineChart_symm_apply

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [ChartedSpace F M]


theorem contMDiffOn_affineChart {c : OpenPartialHomeomorph E M}
    (hc : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ c c.source)
    (hi : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ c.symm c.target)
    (a : E) (L : V ≃L[ℝ] E) :
    ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, F) ∞ (affineChart c a L) (affineChart c a L).source ∧
    ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, V) ∞ (affineChart c a L).symm (affineChart c a L).target := by
  constructor
  · rw [affineChart_source]
    exact hc.comp (contDiff_const.add L.contDiff).contMDiff.contMDiffOn (fun _ hx => hx)
  · rw [affineChart_target]
    exact (L.symm.contDiff.comp (contDiff_const.add contDiff_id)).contMDiff.comp_contMDiffOn hi

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.contMDiffOn_affineChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.contMDiffOn_affineChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.contMDiffOn_affineChart ``Submission.DifferentialGeometry.Topology.contMDiffOn_affineChart



theorem affineChart_mfderiv {c : OpenPartialHomeomorph E M} (a : E) (L : V ≃L[ℝ] E)
    {x : V} (hc : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, F) c (a + L x)) (v : V) :
    mfderiv 𝓘(ℝ, V) 𝓘(ℝ, F) (affineChart c a L) x v =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) c (a + L x) (L v) := by
  have hA : HasFDerivAt (fun y : V => a + L y) (L : V →L[ℝ] E) x :=
    L.hasFDerivAt.const_add a
  have hd := mfderiv_comp x hc hA.differentiableAt.mdifferentiableAt
  rw [mfderiv_eq_fderiv, hA.fderiv] at hd
  exact congrArg (fun A => A v) hd

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.affineChart_mfderiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.affineChart_mfderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.affineChart_mfderiv ``Submission.DifferentialGeometry.Topology.affineChart_mfderiv

end DifferentialGeometry.Topology
