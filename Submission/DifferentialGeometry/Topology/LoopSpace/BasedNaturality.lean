import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.LoopSpace.BasedCircle

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Function _root_.ContinuousMap
open scoped _root_.Topology

namespace DifferentialGeometry.Topology

variable {P Q : Type*} [TopologicalSpace P] [TopologicalSpace Q]


def basedCirclePostcompose (f : C(P, Q)) (p : P) : C(basedCircleLoop p, basedCircleLoop (f p)) :=
  ⟨fun γ => ⟨f.comp γ.val, congrArg f γ.property⟩,
    ((_root_.ContinuousMap.continuous_postcomp f).comp continuous_subtype_val).subtype_mk _⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.basedCirclePostcompose then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.basedCirclePostcompose"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.basedCirclePostcompose ``Submission.DifferentialGeometry.Topology.basedCirclePostcompose


theorem pathToCircle_natural (f : C(P, Q)) (p : P) (γ : Path p p) :
    pathToCircle (γ.map f.continuous) = f.comp (pathToCircle γ) := by
  ext θ
  obtain ⟨t, rfl⟩ := unitInterval_to_loopCircle_surjective θ
  simp only [ContinuousMap.comp_apply, pathToCircle_coe]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.pathToCircle_natural then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.pathToCircle_natural"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.pathToCircle_natural ``Submission.DifferentialGeometry.Topology.pathToCircle_natural


theorem basedPathCircleHomeomorph_natural (f : C(P, Q)) (p : P) (γ : Path p p) :
    basedPathCircleHomeomorph (f p) (γ.map f.continuous) =
      basedCirclePostcompose f p (basedPathCircleHomeomorph p γ) := by
  apply Subtype.ext
  exact pathToCircle_natural f p γ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.basedPathCircleHomeomorph_natural then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.basedPathCircleHomeomorph_natural"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.basedPathCircleHomeomorph_natural ``Submission.DifferentialGeometry.Topology.basedPathCircleHomeomorph_natural


theorem basedPathCircleHomeomorph_refl (p : P) :
    (basedPathCircleHomeomorph p (Path.refl p)).val = FreeLoop.constants p := by
  ext θ
  obtain ⟨t, rfl⟩ := unitInterval_to_loopCircle_surjective θ
  exact pathToCircle_coe (Path.refl p) t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.basedPathCircleHomeomorph_refl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.basedPathCircleHomeomorph_refl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.basedPathCircleHomeomorph_refl ``Submission.DifferentialGeometry.Topology.basedPathCircleHomeomorph_refl

end DifferentialGeometry.Topology
