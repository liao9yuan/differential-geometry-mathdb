import Submission.DifferentialGeometry.Topology.LevelSet.QuadraticGraph
import Submission.DifferentialGeometry.Topology.PlanarJordan.InnermostDisk
import Submission.DifferentialGeometry.Topology.FiberwiseHomeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Submission.Set _root_.Metric

namespace DifferentialGeometry.Topology.PlanarJordan


theorem image_closedBall_eq_of_image_quadratic_level_eq
    {M : Type*} (f : M → Schoenflies.Plane × ℝ)
    (A₀ A₁ : (Schoenflies.Plane × ℝ) ≃ₜ (Schoenflies.Plane × ℝ))
    (hA₀ : ∀ z, (A₀ z).2 = z.2) (hA₁ : ∀ z, (A₁ z).2 = z.2)
    (D : Schoenflies.Plane ≃ₜ Schoenflies.Plane)
    {c₀ c₁ α₀ α₁ r₀ r₁ : ℝ} (hα₀ : α₀ ≠ 0) (hα₁ : α₁ ≠ 0)
    (hr₀ : 0 < r₀) (hr₁ : 0 < r₁) {K₀ K₁ : Set M}
    (hK₀ : {x | (f x).2 = c₀ + α₀ / 2 * r₀ ^ 2} ⊆ K₀)
    (hK₁ : {x | (f x).2 = c₁ + α₁ / 2 * r₁ ^ 2} ⊆ K₁)
    (hcap₀ : f '' K₀ = (fun y => A₀ (y, c₀ + α₀ / 2 * ‖y‖ ^ 2)) '' _root_.Metric.closedBall 0 r₀)
    (hcap₁ : f '' K₁ = (fun y => A₁ (y, c₁ + α₁ / 2 * ‖y‖ ^ 2)) '' _root_.Metric.closedBall 0 r₁)
    (hD : D '' ((fun x => (f x).1) '' {x | (f x).2 = c₀ + α₀ / 2 * r₀ ^ 2}) =
      (fun x => (f x).1) '' {x | (f x).2 = c₁ + α₁ / 2 * r₁ ^ 2}) :
    D '' ((fun y => (A₀ (y, c₀ + α₀ / 2 * r₀ ^ 2)).1) '' _root_.Metric.closedBall 0 r₀) =
      (fun y => (A₁ (y, c₁ + α₁ / 2 * r₁ ^ 2)).1) '' _root_.Metric.closedBall 0 r₁ := by
  rw [Function.image_level_eq_image_sphere_of_image_quadratic_graph_eq f A₀
      hA₀ hα₀ hr₀.le hK₀ hcap₀,
    Function.image_level_eq_image_sphere_of_image_quadratic_graph_eq f A₁
      hA₁ hα₁ hr₁.le hK₁ hcap₁] at hD
  rw [_root_.Set.image_image] at hD ⊢
  exact image_closedBall_eq_of_image_sphere_eq
    ((A₀.restrictFiber hA₀ (c₀ + α₀ / 2 * r₀ ^ 2)).trans D)
    (A₁.restrictFiber hA₁ (c₁ + α₁ / 2 * r₁ ^ 2)) 0 0 hr₀ hr₁ hD

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PlanarJordan.image_closedBall_eq_of_image_quadratic_level_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PlanarJordan.image_closedBall_eq_of_image_quadratic_level_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PlanarJordan.image_closedBall_eq_of_image_quadratic_level_eq ``Submission.DifferentialGeometry.Topology.PlanarJordan.image_closedBall_eq_of_image_quadratic_level_eq

end DifferentialGeometry.Topology.PlanarJordan
