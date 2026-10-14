import Submission.DifferentialGeometry.Topology.Manifold.SphereRadialExtension
import Submission.DifferentialGeometry.Analysis.Calculus.Derivative.Coordinates.JacobianSign
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Analysis.Normed.Module.Connected

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Metric _root_.Manifold _root_.Module
open scoped _root_.ContDiff

namespace DifferentialGeometry.Topology.Manifold

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n : ℕ} [Fact (finrank ℝ E = n + 1)]

def sphereRadialDiffeomorph
    (f : Diffeomorph (𝓡 n) (𝓡 n) (_root_.Metric.sphere (0 : E) 1) (_root_.Metric.sphere (0 : E) 1) ∞) :
    PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞ where
  toFun := sphereRadialExtension f
  invFun := sphereRadialExtension f.symm
  source := {0}ᶜ
  target := {0}ᶜ
  map_source' := by
    intro x hx
    change sphereRadialExtension f x ≠ 0
    intro h
    have hn := norm_sphereRadialExtension f x
    rw [h, norm_zero] at hn
    exact hx (norm_eq_zero.mp hn.symm)
  map_target' := by
    intro x hx
    change sphereRadialExtension f.symm x ≠ 0
    intro h
    have hn := norm_sphereRadialExtension f.symm x
    rw [h, norm_zero] at hn
    exact hx (norm_eq_zero.mp hn.symm)
  left_inv' := by
    intro x _
    have heq : f.symm ∘ f = id := funext f.symm_apply_apply
    have h := sphereRadialExtension_comp (f : _ → _) (f.symm : _ → _)
    rw [heq, sphereRadialExtension_id] at h
    exact (congrFun h x).symm
  right_inv' := by
    intro x _
    have heq : f ∘ f.symm = id := funext f.apply_symm_apply
    have h := sphereRadialExtension_comp (f.symm : _ → _) (f : _ → _)
    rw [heq, sphereRadialExtension_id] at h
    exact (congrFun h x).symm
  open_source := isOpen_compl_singleton
  open_target := isOpen_compl_singleton
  contMDiffOn_toFun := (contDiffOn_sphereRadialExtension f f.contMDiff).contMDiffOn
  contMDiffOn_invFun := (contDiffOn_sphereRadialExtension f.symm f.symm.contMDiff).contMDiffOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.sphereRadialDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.sphereRadialDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.sphereRadialDiffeomorph ``Submission.DifferentialGeometry.Topology.Manifold.sphereRadialDiffeomorph

theorem det_fderiv_sphereRadialExtension_ne_zero
    (f : Diffeomorph (𝓡 n) (𝓡 n) (_root_.Metric.sphere (0 : E) 1) (_root_.Metric.sphere (0 : E) 1) ∞)
    {x : E} (hx : x ≠ 0) :
    (fderiv ℝ (sphereRadialExtension f) x).toLinearMap.det ≠ 0 :=
  DifferentialGeometry.Analysis.det_fderiv_ne_zero_of_partialDiffeomorph (sphereRadialDiffeomorph f) hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.det_fderiv_sphereRadialExtension_ne_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.det_fderiv_sphereRadialExtension_ne_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.det_fderiv_sphereRadialExtension_ne_zero ``Submission.DifferentialGeometry.Topology.Manifold.det_fderiv_sphereRadialExtension_ne_zero

theorem det_fderiv_sphereRadialExtension_pos_iff
    (hrank : 1 < Module.rank ℝ E)
    (f : Diffeomorph (𝓡 n) (𝓡 n) (_root_.Metric.sphere (0 : E) 1) (_root_.Metric.sphere (0 : E) 1) ∞)
    {x y : E} (hx : x ≠ 0) (hy : y ≠ 0) :
    0 < (fderiv ℝ (sphereRadialExtension f) x).toLinearMap.det ↔
      0 < (fderiv ℝ (sphereRadialExtension f) y).toLinearMap.det :=
  DifferentialGeometry.Analysis.det_fderiv_pos_iff_of_preconnected (sphereRadialDiffeomorph f)
    (isConnected_compl_singleton_of_one_lt_rank hrank 0).isPreconnected hx hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.det_fderiv_sphereRadialExtension_pos_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.det_fderiv_sphereRadialExtension_pos_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.det_fderiv_sphereRadialExtension_pos_iff ``Submission.DifferentialGeometry.Topology.Manifold.det_fderiv_sphereRadialExtension_pos_iff

end DifferentialGeometry.Topology.Manifold
