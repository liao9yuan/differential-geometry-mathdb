import Submission.DifferentialGeometry.Topology.LocalDegree.SphereMapHomotopy
import Submission.DifferentialGeometry.Topology.LocalDegree.Euclidean

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

private theorem boundaryPoint_mem {x : E} {R : ℝ} (hR : 0 < R)
    (v : _root_.Metric.sphere (0 : E) 1) : x + R • (v : E) ∈ _root_.Metric.sphere x R := by
  rw [_root_.Metric.mem_sphere, dist_eq_norm, add_sub_cancel_left, norm_smul,
    Real.norm_of_nonneg hR.le, norm_eq_of_mem_sphere v, mul_one]

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.boundaryPoint_mem
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.boundaryPoint_mem target :: scope.openDecls } }

def sphereMapHomotopyOfBoundary {f g : E → F} {x : E} {R : ℝ}
    (hf : IsolatingRadius f x R) (hg : IsolatingRadius g x R)
    (H : I × E → F) (hH : ContinuousOn H (_root_.Set.univ ×ˢ _root_.Metric.sphere x R))
    (hn : ∀ t y, y ∈ _root_.Metric.sphere x R → H (t, y) ≠ 0)
    (h₀ : ∀ y ∈ _root_.Metric.sphere x R, H (0, y) = f y)
    (h₁ : ∀ y ∈ _root_.Metric.sphere x R, H (1, y) = g y) :
    (sphereMap f x R hf.continuousOn hf.nonzero ⟨R, hf.pos, le_rfl⟩).Homotopy
      (sphereMap g x R hg.continuousOn hg.nonzero ⟨R, hg.pos, le_rfl⟩) :=
  sphereMapHomotopyOfFamily hf.continuousOn hg.continuousOn hf.nonzero hg.nonzero
    ⟨R, hf.pos, le_rfl⟩ (fun p => H (p.1, x + R • (p.2 : E)))
    (hH.comp_continuous
      (continuous_fst.prodMk
        (continuous_const.add (continuous_const.smul (continuous_subtype_val.comp continuous_snd))))
      (fun p => ⟨mem_univ _, boundaryPoint_mem hf.pos p.2⟩))
    (fun p => hn p.1 _ (boundaryPoint_mem hf.pos p.2))
    (fun v => h₀ _ (boundaryPoint_mem hf.pos v))
    (fun v => h₁ _ (boundaryPoint_mem hf.pos v))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.sphereMapHomotopyOfBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.sphereMapHomotopyOfBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.sphereMapHomotopyOfBoundary ``Submission.DifferentialGeometry.LocalDegree.sphereMapHomotopyOfBoundary


@[simp]
theorem sphereMapHomotopyOfBoundary_apply {f g : E → F} {x : E} {R : ℝ}
    (hf : IsolatingRadius f x R) (hg : IsolatingRadius g x R)
    (H : I × E → F) (hH : ContinuousOn H (_root_.Set.univ ×ˢ _root_.Metric.sphere x R))
    (hn : ∀ t y, y ∈ _root_.Metric.sphere x R → H (t, y) ≠ 0)
    (h₀ : ∀ y ∈ _root_.Metric.sphere x R, H (0, y) = f y)
    (h₁ : ∀ y ∈ _root_.Metric.sphere x R, H (1, y) = g y) (t : I) (v : _root_.Metric.sphere (0 : E) 1) :
    (sphereMapHomotopyOfBoundary hf hg H hH hn h₀ h₁ (t, v) : F) =
      ‖H (t, x + R • (v : E))‖⁻¹ • H (t, x + R • (v : E)) :=
  sphereMapHomotopyOfFamily_apply _ _ _ _ _ _ _ _ _ _ _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.sphereMapHomotopyOfBoundary_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.sphereMapHomotopyOfBoundary_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.sphereMapHomotopyOfBoundary_apply ``Submission.DifferentialGeometry.LocalDegree.sphereMapHomotopyOfBoundary_apply

theorem euclideanLocalDegree_eq_of_boundaryHomotopy {d : ℕ}
    {f g : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    {x : EuclideanSpace ℝ (Fin (d + 1))} {R : ℝ}
    (hf : IsolatingRadius f x R) (hg : IsolatingRadius g x R)
    (H : I × EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1)))
    (hH : ContinuousOn H (_root_.Set.univ ×ˢ _root_.Metric.sphere x R))
    (hn : ∀ t y, y ∈ _root_.Metric.sphere x R → H (t, y) ≠ 0)
    (h₀ : ∀ y ∈ _root_.Metric.sphere x R, H (0, y) = f y)
    (h₁ : ∀ y ∈ _root_.Metric.sphere x R, H (1, y) = g y) :
    euclideanLocalDegree f x ⟨R, hf⟩ = euclideanLocalDegree g x ⟨R, hg⟩ := by
  erw [euclideanLocalDegree_eq_sphereDegree _ hf ⟨R, hf.pos, le_rfl⟩,
    euclideanLocalDegree_eq_sphereDegree _ hg ⟨R, hg.pos, le_rfl⟩]
  exact euclideanSphereDegree_eq_of_homotopy (sphereMapHomotopyOfBoundary hf hg H hH hn h₀ h₁)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanLocalDegree_eq_of_boundaryHomotopy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanLocalDegree_eq_of_boundaryHomotopy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanLocalDegree_eq_of_boundaryHomotopy ``Submission.DifferentialGeometry.LocalDegree.euclideanLocalDegree_eq_of_boundaryHomotopy

end DifferentialGeometry.LocalDegree
