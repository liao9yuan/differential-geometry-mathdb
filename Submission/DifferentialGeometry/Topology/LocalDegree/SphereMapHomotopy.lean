import Submission.DifferentialGeometry.Topology.LocalDegree.SphereMap

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
open _root_.Metric _root_.Set
open scoped _root_.unitInterval
noncomputable section
namespace DifferentialGeometry.LocalDegree
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]


def sphereMapHomotopyOfFamily {f g : E → F} {x : E} {R : ℝ}
    (hf : ContinuousOn f (_root_.Metric.closedBall x R)) (hg : ContinuousOn g (_root_.Metric.closedBall x R))
    (hfzero : ∀ y ∈ _root_.Metric.closedBall x R, y ≠ x → f y ≠ 0)
    (hgzero : ∀ y ∈ _root_.Metric.closedBall x R, y ≠ x → g y ≠ 0) (r : _root_.Set.Ioc (0 : ℝ) R)
    (H : I × _root_.Metric.sphere (0 : E) 1 → F) (hH : Continuous H) (hn : ∀ p, H p ≠ 0)
    (h₀ : ∀ v, H (0, v) = f (x + (r : ℝ) • (v : E)))
    (h₁ : ∀ v, H (1, v) = g (x + (r : ℝ) • (v : E))) :
    (sphereMap f x R hf hfzero r).Homotopy (sphereMap g x R hg hgzero r) where
  toFun p := (homeomorphUnitSphereProd F ⟨H p, hn p⟩).1
  continuous_toFun := (homeomorphUnitSphereProd F).continuous.fst.comp (hH.subtype_mk hn)
  map_zero_left v := by
    apply Subtype.ext
    simp only [homeomorphUnitSphereProd_apply_fst_coe, h₀, sphereMap_apply]
  map_one_left v := by
    apply Subtype.ext
    simp only [homeomorphUnitSphereProd_apply_fst_coe, h₁, sphereMap_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.sphereMapHomotopyOfFamily then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.sphereMapHomotopyOfFamily"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.sphereMapHomotopyOfFamily ``Submission.DifferentialGeometry.LocalDegree.sphereMapHomotopyOfFamily


@[simp]
theorem sphereMapHomotopyOfFamily_apply {f g : E → F} {x : E} {R : ℝ}
    (hf : ContinuousOn f (_root_.Metric.closedBall x R)) (hg : ContinuousOn g (_root_.Metric.closedBall x R))
    (hfzero : ∀ y ∈ _root_.Metric.closedBall x R, y ≠ x → f y ≠ 0)
    (hgzero : ∀ y ∈ _root_.Metric.closedBall x R, y ≠ x → g y ≠ 0) (r : _root_.Set.Ioc (0 : ℝ) R)
    (H : I × _root_.Metric.sphere (0 : E) 1 → F) (hH : Continuous H) (hn : ∀ p, H p ≠ 0)
    (h₀ : ∀ v, H (0, v) = f (x + (r : ℝ) • (v : E)))
    (h₁ : ∀ v, H (1, v) = g (x + (r : ℝ) • (v : E)))
    (t : I) (v : _root_.Metric.sphere (0 : E) 1) :
    (sphereMapHomotopyOfFamily hf hg hfzero hgzero r H hH hn h₀ h₁ (t, v) : F) =
      ‖H (t, v)‖⁻¹ • H (t, v) :=
  homeomorphUnitSphereProd_apply_fst_coe F _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.sphereMapHomotopyOfFamily_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.sphereMapHomotopyOfFamily_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.sphereMapHomotopyOfFamily_apply ``Submission.DifferentialGeometry.LocalDegree.sphereMapHomotopyOfFamily_apply

end DifferentialGeometry.LocalDegree
