import Submission.DifferentialGeometry.Topology.Homology.Spheres.SphereTopology

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

universe u

namespace DifferentialGeometry.Topology.SingularPair

open _root_.Metric
open scoped _root_.ContinuousMap _root_.unitInterval

theorem discreteTopology_of_chartedSpace_zero {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 0)) M] : DiscreteTopology M := by
  rw [discreteTopology_iff_isOpen_singleton]
  intro x
  have hsub : ({x} : Set M) = (chartAt (EuclideanSpace ℝ (Fin 0)) x).source := by
    ext y
    constructor
    · rintro rfl
      exact mem_chart_source _ _
    · intro hy
      exact (chartAt (EuclideanSpace ℝ (Fin 0)) x).injOn hy (mem_chart_source _ x)
        (Subsingleton.elim _ _)
  rw [hsub]
  exact (chartAt _ x).open_source

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.discreteTopology_of_chartedSpace_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.discreteTopology_of_chartedSpace_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.discreteTopology_of_chartedSpace_zero ``Submission.DifferentialGeometry.Topology.SingularPair.discreteTopology_of_chartedSpace_zero

theorem homotopy_apply_eq_of_discrete {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [DiscreteTopology Y] {f g : C(X, Y)} (H : f.Homotopy g) (x : X) : f x = g x := by
  have hc : Continuous fun t : I => H (t, x) :=
    H.continuous.comp (continuous_id.prodMk continuous_const)
  have := PreconnectedSpace.constant inferInstance hc (x := 0) (y := 1)
  simpa using this

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.homotopy_apply_eq_of_discrete then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.homotopy_apply_eq_of_discrete"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.homotopy_apply_eq_of_discrete ``Submission.DifferentialGeometry.Topology.SingularPair.homotopy_apply_eq_of_discrete

theorem injective_homotopyEquiv_of_discrete {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [DiscreteTopology X] (e : X ≃ₕ Y) : Function.Injective e.toFun := by
  obtain ⟨H⟩ := e.left_inv
  intro a b hab
  have ha := homotopy_apply_eq_of_discrete H a
  have hb := homotopy_apply_eq_of_discrete H b
  simp only [ContinuousMap.comp_apply, ContinuousMap.id_apply] at ha hb
  rw [← ha, ← hb, hab]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.injective_homotopyEquiv_of_discrete then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.injective_homotopyEquiv_of_discrete"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.injective_homotopyEquiv_of_discrete ``Submission.DifferentialGeometry.Topology.SingularPair.injective_homotopyEquiv_of_discrete

theorem compactSpace_of_homotopyEquiv_sphere_zero {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 0)) M]
    (e : M ≃ₕ _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) : CompactSpace M := by
  have : DiscreteTopology M := discreteTopology_of_chartedSpace_zero
  have : Finite M := Finite.of_injective _ (injective_homotopyEquiv_of_discrete e)
  infer_instance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.compactSpace_of_homotopyEquiv_sphere_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.compactSpace_of_homotopyEquiv_sphere_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.compactSpace_of_homotopyEquiv_sphere_zero ``Submission.DifferentialGeometry.Topology.SingularPair.compactSpace_of_homotopyEquiv_sphere_zero

end DifferentialGeometry.Topology.SingularPair
