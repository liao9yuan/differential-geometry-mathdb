import Submission.DifferentialGeometry.Topology.Manifold.SphereRadialChartSign
import Submission.DifferentialGeometry.Topology.Manifold.SphereRadialIsotopy
import Submission.DifferentialGeometry.Topology.Manifold.SphereChartIsotopy
import Submission.DifferentialGeometry.Topology.Manifold.SpherePointIsotopy
import Submission.DifferentialGeometry.Topology.Manifold.ChartCentering

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Metric _root_.Manifold _root_.Module
open scoped _root_.ContDiff

namespace DifferentialGeometry.Topology.Manifold

theorem sphere_isotopy_iff_positive_radial_derivative
    (f : Diffeomorph (𝓡 2) (𝓡 2)
      (_root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
      (_root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞)
    (v : _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    (∃ J : ℝ → Diffeomorph (𝓡 2) (𝓡 2)
        (_root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
        (_root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞,
      ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞
        (fun q : ℝ × _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ J q.1 q.2) ∧
      ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞
        (fun q : ℝ × _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ (J q.1).symm q.2) ∧
      J 0 = f ∧ J 1 = Diffeomorph.refl (𝓡 2) _ ∞) ↔
    0 < (fderiv ℝ (sphereRadialExtension f) (v : EuclideanSpace ℝ (Fin 3))).toLinearMap.det := by
  let : Fact (_root_.Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  constructor
  · rintro ⟨J, hJ, _, hJ0, hJ1⟩
    let D (p : ℝ) := J (1 - p)
    have ht : ContMDiff (𝓘(ℝ).prod (𝓡 2)) 𝓘(ℝ) ∞
        (fun q : ℝ × _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ 1 - q.1) :=
      contMDiff_const.sub contMDiff_fst
    have hD : ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞
        (fun q : ℝ × _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ D q.1 q.2) :=
      hJ.comp (ht.prodMk contMDiff_snd)
    have hD0 : D 0 = Diffeomorph.refl (𝓡 2) _ ∞ := by simpa [D] using hJ1
    have hp := det_fderiv_sphereRadialExtension_pos_of_isotopy D hD hD0 1
      (ne_zero_of_mem_unit_sphere v)
    simpa only [D, sub_self, hJ0] using hp
  · intro hp
    obtain ⟨e₀, hv₀, hfv₀, het₀, he₀, hei₀⟩ := exists_smooth_planar_chart_containing_pair v (f v)
    obtain ⟨e, hes, het, hev, _, he, hei⟩ :=
      exists_smooth_chart_centered e₀ het₀ he₀ hei₀ v hv₀
    have hv : v ∈ e.source := hes ▸ hv₀
    have hfv : f v ∈ e.source := hes ▸ hfv₀
    have hc := (det_radial_pos_iff_det_chart_pos e het he hei f v hv hfv).mp hp
    rw [hev] at hc
    exact exists_sphere_isotopy_of_positive_chart_derivative e het he hei f v hv hev hfv hc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.sphere_isotopy_iff_positive_radial_derivative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.sphere_isotopy_iff_positive_radial_derivative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.sphere_isotopy_iff_positive_radial_derivative ``Submission.DifferentialGeometry.Topology.Manifold.sphere_isotopy_iff_positive_radial_derivative

end DifferentialGeometry.Topology.Manifold
