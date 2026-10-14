import Submission.DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Orientation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology.Manifold

variable {n : ℕ} {A B C : Type*}
  [TopologicalSpace A] [ChartedSpace (EuclideanSpace ℝ (Fin n)) A]
  [TopologicalSpace B] [ChartedSpace (EuclideanSpace ℝ (Fin n)) B]
  [TopologicalSpace C] [ChartedSpace (EuclideanSpace ℝ (Fin n)) C]
  [IsManifold (𝓡 n) ∞ A] [IsManifold (𝓡 n) ∞ B] [IsManifold (𝓡 n) ∞ C]

theorem local_orientation_of_comp_eq_at
    (f : A → B) (g : B → C) (h : A → C)
    (hf : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ f)
    (hg : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ g)
    (hh : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ h)
    (heq : g ∘ f = h)
    (oA : ManifoldOrientation (𝓡 n) A n) (oB : ManifoldOrientation (𝓡 n) B n)
    (oC : ManifoldOrientation (𝓡 n) C n) (x : A)
    (hfo : Orientation.map (Fin n) (hf.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
      (oA.orientation x) = oB.orientation (f x))
    (hho : Orientation.map (Fin n) (hh.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
      (oA.orientation x) = oC.orientation (h x)) :
    Orientation.map (Fin n) (hg.mfderivToContinuousLinearEquiv (by simp) (f x)).toLinearEquiv
      (oB.orientation (f x)) = oC.orientation (g (f x)) := by
  have hlin : (hf.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv.trans
      (hg.mfderivToContinuousLinearEquiv (by simp) (f x)).toLinearEquiv =
      (hh.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv := by
    apply LinearEquiv.ext
    intro v
    change mfderiv (𝓡 n) (𝓡 n) g (f x) (mfderiv (𝓡 n) (𝓡 n) f x v) = mfderiv (𝓡 n) (𝓡 n) h x v
    rw [← mfderiv_comp_apply x (hg.mdifferentiable (by simp) _) (hf.mdifferentiable (by simp) _) v]
    exact congrArg (fun k : A → C => mfderiv (𝓡 n) (𝓡 n) k x v) heq
  rw [← hfo]
  erw [DifferentialGeometry.VectorBundle.map_orientation_trans_between, hlin]
  have hp : g (f x) = h x := congrFun heq x
  rw [hp]
  exact hho

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.local_orientation_of_comp_eq_at then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.local_orientation_of_comp_eq_at"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.local_orientation_of_comp_eq_at ``Submission.DifferentialGeometry.Topology.Manifold.local_orientation_of_comp_eq_at

theorem local_orientation_of_comp
    (f : A → B) (g : B → C) (h : A → C)
    (hf : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ f)
    (hg : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ g)
    (hh : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ h)
    (heq : g ∘ f = h)
    (oA : ManifoldOrientation (𝓡 n) A n) (oB : ManifoldOrientation (𝓡 n) B n)
    (oC : ManifoldOrientation (𝓡 n) C n)
    (hgo : ∀ y, Orientation.map (Fin n) (hg.mfderivToContinuousLinearEquiv (by simp) y).toLinearEquiv
      (oB.orientation y) = oC.orientation (g y))
    (hho : ∀ x, Orientation.map (Fin n) (hh.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
      (oA.orientation x) = oC.orientation (h x)) :
    ∀ x, Orientation.map (Fin n) (hf.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
      (oA.orientation x) = oB.orientation (f x) := by
  intro x
  let L := (hg.mfderivToContinuousLinearEquiv (by simp) (f x)).toLinearEquiv
  apply (Orientation.map (Fin n) L).injective
  have hlin : (hf.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv.trans L =
      (hh.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv := by
    apply LinearEquiv.ext
    intro v
    change mfderiv (𝓡 n) (𝓡 n) g (f x) (mfderiv (𝓡 n) (𝓡 n) f x v) = mfderiv (𝓡 n) (𝓡 n) h x v
    rw [← mfderiv_comp_apply x (hg.mdifferentiable (by simp) _) (hf.mdifferentiable (by simp) _) v]
    exact congrArg (fun k : A → C => mfderiv (𝓡 n) (𝓡 n) k x v) heq
  erw [DifferentialGeometry.VectorBundle.map_orientation_trans_between, hlin, hho, hgo]
  congr 1
  exact (congrFun heq x).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.local_orientation_of_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.local_orientation_of_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.local_orientation_of_comp ``Submission.DifferentialGeometry.Topology.Manifold.local_orientation_of_comp

variable [ConnectedSpace A]

theorem localDiffeomorph_orientation_of_eq_at
    (f : A → B) (hf : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ f) (hi : _root_.Function.Injective f)
    (oA : ManifoldOrientation (𝓡 n) A n) (oB : ManifoldOrientation (𝓡 n) B n) (x₀ : A)
    (h0 : Orientation.map (Fin n) (hf.mfderivToContinuousLinearEquiv (by simp) x₀).toLinearEquiv
      (oA.orientation x₀) = oB.orientation (f x₀)) :
    ∀ x, Orientation.map (Fin n) (hf.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
      (oA.orientation x) = oB.orientation (f x) := by
  rcases localDiffeomorph_orientation_dichotomy f hf hi oA oB with hp | hn
  · exact hp
  · have heq := h0.symm.trans (hn x₀)
    exact False.elim (Module.Ray.ne_neg_self _ heq)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.localDiffeomorph_orientation_of_eq_at then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.localDiffeomorph_orientation_of_eq_at"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.localDiffeomorph_orientation_of_eq_at ``Submission.DifferentialGeometry.Topology.Manifold.localDiffeomorph_orientation_of_eq_at

end DifferentialGeometry.Topology.Manifold
