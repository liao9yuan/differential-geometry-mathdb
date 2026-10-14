import Submission.DifferentialGeometry.Topology.ThreeManifold.StandardFactors
import Submission.DifferentialGeometry.Topology.ThreeManifold.StandardSphere
import Mathlib.Geometry.Manifold.LocalDiffeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Manifold _root_.Metric
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology

universe u

theorem exists_orientedDiffeomorph_standardThreeSphere_of_subsingleton_group
    (G : SphericalSpaceFormGroup) (h : Subsingleton G.group) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      G.manifold.toClosedOrientedManifold
      standardThreeSphereLift.{u}.toClosedOrientedManifold) := by
  classical
  have hbij : Function.Bijective G.projection := by
    refine ⟨fun x y hxy => ?_, G.projection_surjective⟩
    obtain ⟨γ, hγ⟩ := (G.projection_eq_iff x y).mp hxy
    have hsmul : (γ : G.group) • x = y := hγ
    have hγ1 : γ = 1 := h.elim γ 1
    rw [hγ1] at hsmul
    simpa using hsmul
  let d : Diffeomorph (𝓡 3) (𝓡 3)
      (_root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) G.Orbit ∞ :=
    G.projection_isLocalDiffeomorph.diffeomorphOfBijective hbij
  have hd : d.preservesOrientation (sphereOrientation 3 (by decide)) G.manifold.orientation :=
    fun x => G.projection_positive x
  refine ⟨?_, ?_⟩
  · exact d.symm.trans standardThreeSphereLiftDiffeomorph.{u}
  · exact Diffeomorph.preservesOrientation_trans (Diffeomorph.preservesOrientation_symm hd)
      standardThreeSphereLiftDiffeomorph_preservesOrientation

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_orientedDiffeomorph_standardThreeSphere_of_subsingleton_group then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_orientedDiffeomorph_standardThreeSphere_of_subsingleton_group"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_orientedDiffeomorph_standardThreeSphere_of_subsingleton_group ``Submission.DifferentialGeometry.Topology.exists_orientedDiffeomorph_standardThreeSphere_of_subsingleton_group

end DifferentialGeometry.Topology
