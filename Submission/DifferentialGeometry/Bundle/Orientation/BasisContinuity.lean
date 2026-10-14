import Submission.DifferentialGeometry.Bundle.Orientation.Transport

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open scoped _root_.Topology

namespace DifferentialGeometry.VectorBundle

variable {n : ℕ} {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace X]
attribute [local instance] orientationTopology
local instance basisContinuityDiscreteTopology : DiscreteTopology (Orientation ℝ E (Fin n)) := ⟨rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.VectorBundle.basisContinuityDiscreteTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.VectorBundle.basisContinuityDiscreteTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.VectorBundle.basisContinuityDiscreteTopology ``Submission.DifferentialGeometry.VectorBundle.basisContinuityDiscreteTopology

theorem continuous_basis_orientation (hdim : Module.finrank ℝ E = n)
    (b : X → Module.Basis (Fin n) ℝ E) (hb : ∀ i, Continuous (fun x => b x i)) :
    Continuous (fun x => (b x).orientation) := by
  let b₀ := (Module.finBasis ℝ E).reindex (finCongr hdim)
  let A : X → E ≃L[ℝ] E := fun x => (b₀.equiv (b x) (Equiv.refl _)).toContinuousLinearEquiv
  have hA : Continuous (fun x => (A x : E →L[ℝ] E)) := by
    rw [continuous_clm_apply]
    intro v
    have heq (x : X) : A x v = ∑ i, b₀.repr v i • b x i := by
      calc
        A x v = A x (∑ i, b₀.repr v i • b₀ i) := congrArg (A x) (b₀.sum_repr v).symm
        _ = _ := by
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [map_smul]
          congr 1
          change b₀.equiv (b x) (Equiv.refl _) (b₀ i) = b x i
          simp only [Module.Basis.equiv_apply, Equiv.refl_apply]
    change Continuous (fun x => A x v)
    simp_rw [heq]
    exact continuous_finsetSum _ (fun i _ => (hb i).const_smul _)
  have hh := (continuous_orientation_transport hdim A hA).comp
    (continuous_id.prodMk continuous_const : Continuous (fun x : X => (x, b₀.orientation)))
  convert hh using 1
  ext x
  change (b x).orientation = Orientation.map (Fin n) (b₀.equiv (b x) (Equiv.refl _)) b₀.orientation
  rw [← Module.Basis.orientation_map, Module.Basis.map_equiv]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.VectorBundle.continuous_basis_orientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.VectorBundle.continuous_basis_orientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.VectorBundle.continuous_basis_orientation ``Submission.DifferentialGeometry.VectorBundle.continuous_basis_orientation

end DifferentialGeometry.VectorBundle
