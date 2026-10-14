import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SphereHomologyVanishing
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.LocalCharts
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ContractibleCoverOne
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeEmpty
import Mathlib.Analysis.Normed.Module.FiniteDimension

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

/-! # Actual top local homology of Euclidean spaces and their manifolds -/

noncomputable section

open _root_.CategoryTheory _root_.ContinuousMap _root_.Metric _root_.Module _root_.Set

universe u

namespace DifferentialGeometry.Topology

variable (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The actual point-complement pair at zero has top homology Z in each
real dimension at least two. The original relative connecting map and the
same radial normalization identify it with the computed sphere group. -/
def integralEuclideanLocalTopZeroEquiv (n : ℕ) (hd : _root_.Module.finrank ℝ E = n + 2) :
    integralLocalHomology (n + 2) (0 : E) ≃ₗ[ℤ] ℤ :=
  ((integralRelativeConnectingEquivOfContractible (n + 1) (by omega)
    ({0}ᶜ : Set E)).trans (integralPuncturedSpaceSphereHomologyEquiv E (n + 1))).trans
      (integralSphereTopHomologyEquiv n E hd)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralEuclideanLocalTopZeroEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralEuclideanLocalTopZeroEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralEuclideanLocalTopZeroEquiv ``Submission.DifferentialGeometry.Topology.integralEuclideanLocalTopZeroEquiv

/-- Translation of the same actual point-complement pair gives top local
homology at every original point, with no local orientation assumed. -/
def integralEuclideanLocalTopEquiv (n : ℕ) (hd : _root_.Module.finrank ℝ E = n + 2) (x : E) :
    integralLocalHomology (n + 2) x ≃ₗ[ℤ] ℤ := by
  let e : E ≃ₜ E := Homeomorph.addRight (-x)
  have hx : e x = 0 := add_neg_cancel x
  have h := (integralLocalHomologyHomeomorphIso (n + 2) e x).toLinearEquiv
  rw [hx] at h
  exact h.trans (integralEuclideanLocalTopZeroEquiv E n hd)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralEuclideanLocalTopEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralEuclideanLocalTopEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralEuclideanLocalTopEquiv ``Submission.DifferentialGeometry.Topology.integralEuclideanLocalTopEquiv

/-- The original chart and original relative group yield actual top local
homology of a manifold. This computes the group; a coherent choice of local
orientations and its global fundamental class remain separate obligations. -/
def integralManifoldLocalTopEquiv (n : ℕ) (hd : _root_.Module.finrank ℝ E = n + 2)
    (M : Type u) [TopologicalSpace M] [T1Space M] [ChartedSpace E M] (x : M) :
    integralLocalHomology (n + 2) x ≃ₗ[ℤ] ℤ :=
  (integralLocalHomologyChartIso (Y := E) (n + 2) x).toLinearEquiv.trans
    (integralEuclideanLocalTopEquiv E n hd (chartAt E x x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralManifoldLocalTopEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralManifoldLocalTopEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralManifoldLocalTopEquiv ``Submission.DifferentialGeometry.Topology.integralManifoldLocalTopEquiv

end DifferentialGeometry.Topology

end

end

section

noncomputable section

open _root_.CategoryTheory _root_.Metric _root_.Module _root_.Set

universe u

namespace DifferentialGeometry.Topology

private def innerProductLocalTopEquiv
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    integralLocalHomology (_root_.Module.finrank ℝ E) (0 : E) ≃ₗ[ℤ] ℤ := by
  by_cases hlarge : 2 ≤ _root_.Module.finrank ℝ E
  · have hd : _root_.Module.finrank ℝ E = (_root_.Module.finrank ℝ E - 2) + 2 := by omega
    rw [hd]
    exact integralEuclideanLocalTopZeroEquiv E (_root_.Module.finrank ℝ E - 2) hd
  by_cases hzero : _root_.Module.finrank ℝ E = 0
  · have hempty : ({0}ᶜ : Set E) = ∅ := by
      ext x
      constructor
      · intro hx
        exact (hx (finrank_zero_iff_forall_zero.mp hzero x)).elim
      · intro hx
        exact hx.elim
    change integralRelativeHomology (_root_.Module.finrank ℝ E) ({0}ᶜ : Set E) ≃ₗ[ℤ] ℤ
    rw [hzero, hempty]
    exact (integralAbsoluteToRelativeEmptyEquiv 0 E).symm.trans
      (integralSingularHomologyZeroEquiv (X := E))
  have hone : _root_.Module.finrank ℝ E = 1 := by omega
  change integralRelativeHomology (_root_.Module.finrank ℝ E) ({0}ᶜ : Set E) ≃ₗ[ℤ] ℤ
  rw [hone]
  exact (((integralRelativeConnectingZeroKernelEquiv ({0}ᶜ : Set E)).trans
    (integralZeroMapKernelReducedEquiv (singularSubspaceInclusion ({0}ᶜ : Set E)))).trans
      (integralReducedZeroHomotopyEquiv (puncturedSpaceSphereHomotopyEquiv E))).trans
        (integralZeroSphereReducedEquiv hone)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.innerProductLocalTopEquiv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.innerProductLocalTopEquiv target :: scope.openDecls } }

theorem exists_integralLocalHomology_generator
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (p : E) :
    ∃ c : integralLocalHomology (_root_.Module.finrank ℝ E) p,
      Function.Bijective (fun k : ℤ => k • c) := by
  let ι := Module.Free.ChooseBasisIndex ℝ E
  let b : _root_.Module.Basis ι ℝ E := Module.Free.chooseBasis ℝ E
  let e : E ≃L[ℝ] EuclideanSpace ℝ ι :=
    b.equivFunL.trans (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm
  let h := e.toHomeomorph.trans (Homeomorph.subRight (e p))
  have hp : h p = 0 := sub_self (e p)
  have he := (integralLocalHomologyHomeomorphIso (_root_.Module.finrank ℝ E) h p).toLinearEquiv
  rw [hp] at he
  have hzero : integralLocalHomology (_root_.Module.finrank ℝ E) (0 : EuclideanSpace ℝ ι) ≃ₗ[ℤ] ℤ := by
    rw [e.toLinearEquiv.finrank_eq]
    exact innerProductLocalTopEquiv (EuclideanSpace ℝ ι)
  let f := he.trans hzero
  let c := f.symm 1
  have hmap (k : ℤ) : f (k • c) = k := by
    rw [map_zsmul]
    change k • f (f.symm 1) = k
    rw [f.apply_symm_apply]
    exact mul_one k
  refine ⟨c, ?_, ?_⟩
  · intro k l hkl
    exact (hmap k).symm.trans ((congrArg f hkl).trans (hmap l))
  · intro a
    exact ⟨f a, f.injective (hmap (f a))⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_integralLocalHomology_generator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_integralLocalHomology_generator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_integralLocalHomology_generator ``Submission.DifferentialGeometry.Topology.exists_integralLocalHomology_generator

end DifferentialGeometry.Topology

end

end
