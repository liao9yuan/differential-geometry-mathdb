import Submission.DifferentialGeometry.Topology.Manifold.SpherePlanarChart
import Submission.DifferentialGeometry.Topology.Manifold.ChartSupportedIsotopy

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Metric _root_.Filter _root_.Topology _root_.Manifold
open scoped _root_.ContDiff

namespace DifferentialGeometry.Topology.Manifold

theorem exists_sphere_isotopy_of_identity_near_point
    (f : Diffeomorph (𝓡 2) (𝓡 2)
      (_root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
      (_root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞)
    (v : _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (hfix : (f : _ → _) =ᶠ[𝓝 v] id) :
    ∃ J : ℝ → Diffeomorph (𝓡 2) (𝓡 2)
      (_root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
      (_root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞,
      ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞
        (fun q : ℝ × _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ J q.1 q.2) ∧
      ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞
        (fun q : ℝ × _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ (J q.1).symm q.2) ∧
      J 0 = f ∧ J 1 = Diffeomorph.refl (𝓡 2) _ ∞ ∧
      ∃ U : Set (_root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1),
        IsOpen U ∧ v ∈ U ∧ ∀ p x, x ∈ U → J p x = x ∧ (J p).symm x = x := by
  obtain ⟨N, hNfix, hN, hvN⟩ := _root_.mem_nhds_iff.mp hfix
  obtain ⟨e, hes, het, he, hei⟩ := exists_smooth_planar_chart_sphere v
  have hK : IsCompact Nᶜ := hN.isClosed_compl.isCompact
  have hKs : Nᶜ ⊆ e.source := by
    intro x hx
    rw [hes]
    intro h
    exact hx (mem_singleton_iff.mp h ▸ hvN)
  obtain ⟨J, hJ, hJi, hJ0, hJ1, C, hC, hCs, hJfix⟩ :=
    exists_isotopy_of_support_in_planar_chart e het he hei f hK hKs
      (fun x hx ↦ hNfix (not_not.mp hx))
  refine ⟨J, hJ, hJi, hJ0, hJ1, Cᶜ, hC.isClosed.isOpen_compl, ?_, hJfix⟩
  intro hvC
  have hvs := hCs hvC
  rw [hes] at hvs
  exact hvs (_root_.Set.mem_singleton v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_sphere_isotopy_of_identity_near_point then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_sphere_isotopy_of_identity_near_point"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_sphere_isotopy_of_identity_near_point ``Submission.DifferentialGeometry.Topology.Manifold.exists_sphere_isotopy_of_identity_near_point

end DifferentialGeometry.Topology.Manifold
