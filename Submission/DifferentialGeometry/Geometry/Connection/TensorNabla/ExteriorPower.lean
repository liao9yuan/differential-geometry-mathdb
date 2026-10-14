import Submission.DifferentialGeometry.Geometry.Metric.ExteriorPowerDualityBundle
import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.Alternating
import Submission.DifferentialGeometry.Geometry.Connection.Trivial

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.ContDiff

namespace CovariantDerivative
open _root_.CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]

open _root_.CovariantDerivative in
private instance alternatingFiniteDimensional (k : ℕ) :
    FiniteDimensional ℝ (F [⋀^Fin k]→L[ℝ] ℝ) :=
  (ContinuousAlternatingMap.elementaryCovectorBasis (k := k)
    (Module.finBasis ℝ F)).finiteDimensional_of_finite

run_cmd do
  let target := ``Submission.CovariantDerivative.alternatingFiniteDimensional
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `CovariantDerivative.alternatingFiniteDimensional target :: scope.openDecls } }

open _root_.CovariantDerivative in
def exteriorPower (cov : CovariantDerivative I F V) (k : ℕ) :
    letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    letI := Bundle.ExteriorPower.totalSpaceTopology F V k
    letI := Bundle.ExteriorPower.fiberBundle F V k
    letI := Bundle.ExteriorPower.vector_bundle F V k
    CovariantDerivative I (⋀[ℝ]^k F) (fun x => ⋀[ℝ]^k (V x)) := by
  let : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  let := Bundle.ExteriorPower.totalSpaceTopology F V k
  let := Bundle.ExteriorPower.fiberBundle F V k
  let := Bundle.ExteriorPower.vector_bundle F V k
  exact pullbackFiberwiseLinearEquiv
    (fun x => (_root_.Submission.exteriorPower.alternatingDualEquiv (E := V x) k).toLinearEquiv)
    (Bundle.ExteriorPower.contMDiff_alternatingDualEquiv_map (IB := I) F V k 1)
    (DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen I M
      (F [⋀^Fin k]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial M ℝ))
      ℝ (Bundle.Trivial M ℝ) (alternating cov k) (trivial I M ℝ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.exteriorPower then
    throwError "Refusing to shadow existing declaration CovariantDerivative.exteriorPower"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.exteriorPower ``Submission.CovariantDerivative.exteriorPower

open _root_.CovariantDerivative in
theorem exteriorPower_apply (cov : CovariantDerivative I F V) (k : ℕ)
    (u : ∀ x, ⋀[ℝ]^k (V x)) (x : M) (X : TangentSpace I x) :
    letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    letI := Bundle.ExteriorPower.totalSpaceTopology F V k
    letI := Bundle.ExteriorPower.fiberBundle F V k
    letI := Bundle.ExteriorPower.vector_bundle F V k
    exteriorPower cov k u x X =
      (_root_.Submission.exteriorPower.alternatingDualEquiv k).symm
        (DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen I M
          (F [⋀^Fin k]→L[ℝ] ℝ)
          (Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial M ℝ))
          ℝ (Bundle.Trivial M ℝ) (alternating cov k) (trivial I M ℝ)
          (fun y => _root_.Submission.exteriorPower.alternatingDualEquiv k (u y)) x X) := by
  let : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  let := Bundle.ExteriorPower.totalSpaceTopology F V k
  let := Bundle.ExteriorPower.fiberBundle F V k
  let := Bundle.ExteriorPower.vector_bundle F V k
  exact pullbackFiberwiseLinearEquiv_apply _
    (Bundle.ExteriorPower.contMDiff_alternatingDualEquiv_map (IB := I) F V k 1) _ u x X

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.exteriorPower_apply then
    throwError "Refusing to shadow existing declaration CovariantDerivative.exteriorPower_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.exteriorPower_apply ``Submission.CovariantDerivative.exteriorPower_apply

open _root_.CovariantDerivative in
theorem exteriorPower_contMDiff (cov : CovariantDerivative I F V)
    [_root_.CovariantDerivative.ContMDiffCovariantDerivative cov ∞] (k : ℕ) :
    letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    letI := Bundle.ExteriorPower.totalSpaceTopology F V k
    letI := Bundle.ExteriorPower.fiberBundle F V k
    letI := Bundle.ExteriorPower.vector_bundle F V k
    ContMDiffCovariantDerivative (exteriorPower cov k) ∞ := by
  let : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  let := Bundle.ExteriorPower.totalSpaceTopology F V k
  let := Bundle.ExteriorPower.fiberBundle F V k
  let := Bundle.ExteriorPower.vector_bundle F V k
  exact ContMDiffCovariantDerivative.pullbackFiberwiseLinearEquiv _
    (Bundle.ExteriorPower.contMDiff_alternatingDualEquiv_map (IB := I) F V k ∞)
    (Bundle.ExteriorPower.contMDiff_alternatingDualEquiv_symm_map (IB := I) F V k ∞) _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.exteriorPower_contMDiff then
    throwError "Refusing to shadow existing declaration CovariantDerivative.exteriorPower_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.exteriorPower_contMDiff ``Submission.CovariantDerivative.exteriorPower_contMDiff

open _root_.CovariantDerivative in
theorem exteriorPower_ιMulti (cov : CovariantDerivative I F V) (k : ℕ)
    (Y : Fin k → ∀ x, V x) {x : M}
    (hY : ∀ i, MDifferentiableAt I (I.prod 𝓘(ℝ, F))
      (fun y => (⟨y, Y i y⟩ : _root_.Bundle.TotalSpace F V)) x) (X : TangentSpace I x) :
    letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    letI := Bundle.ExteriorPower.totalSpaceTopology F V k
    letI := Bundle.ExteriorPower.fiberBundle F V k
    letI := Bundle.ExteriorPower.vector_bundle F V k
    exteriorPower cov k (fun y => _root_.exteriorPower.ιMulti ℝ k (fun i => Y i y)) x X =
      ∑ i, _root_.exteriorPower.ιMulti ℝ k
        (Function.update (fun j => Y j x) i (cov (Y i) x X)) := by
  let : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  let := Bundle.ExteriorPower.totalSpaceTopology F V k
  let := Bundle.ExteriorPower.fiberBundle F V k
  let := Bundle.ExteriorPower.vector_bundle F V k
  classical
  apply (_root_.Submission.exteriorPower.alternatingDualEquiv k).injective
  rw [exteriorPower_apply, ContinuousLinearEquiv.apply_symm_apply, map_sum]
  apply ContinuousLinearMap.ext
  intro a
  obtain ⟨A, hA⟩ := ContMDiffSection.exists_eq_at (I := I)
    (F := F [⋀^Fin k]→L[ℝ] ℝ)
    (V := Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial M ℝ))
    (n := (⊤ : ℕ∞)) x a
  obtain ⟨Z, hZ⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := TangentSpace I) (n := (⊤ : ℕ∞)) x X
  rw [← hA, ← hZ]
  have hu := Bundle.ExteriorPower.mdifferentiableAt_ιMulti (IB := I) F V k Y hY
  have hmap := Bundle.ExteriorPower.contMDiff_alternatingDualEquiv_map (IB := I) F V k 1
  have hd := (hmap.mdifferentiableAt one_ne_zero).comp x hu
  rw [DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen_apply_of_mdifferentiableAt
    I M (F [⋀^Fin k]→L[ℝ] ℝ)
    (Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial M ℝ))
    ℝ (Bundle.Trivial M ℝ) (alternating cov k) (trivial I M ℝ)
    _ hd Z.mdifferentiableAt A.mdifferentiableAt]
  simp only [_root_.Submission.exteriorPower.alternatingDualEquiv_ιMulti_apply, sum_apply]
  rw [alternating_apply_of_mdifferentiableAt cov k Y A.mdifferentiableAt hY]
  change mvfderiv (I := I) (fun y => A y (fun i => Y i y)) x (Z x) -
      (mvfderiv (I := I) (fun y => A y (fun i => Y i y)) x (Z x) -
        ∑ i, A x (Function.update (fun j => Y j x) i (cov (Y i) x (Z x)))) = _
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.exteriorPower_ιMulti then
    throwError "Refusing to shadow existing declaration CovariantDerivative.exteriorPower_ιMulti"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.exteriorPower_ιMulti ``Submission.CovariantDerivative.exteriorPower_ιMulti

open _root_.CovariantDerivative in
theorem exteriorPower_alternatingDualEquiv_apply
    (cov : CovariantDerivative I F V) (k : ℕ)
    (u : ∀ x, ⋀[ℝ]^k (V x)) (a : ∀ x, V x [⋀^Fin k]→L[ℝ] ℝ)
    (x : M) (X : TangentSpace I x)
    (ha : MDifferentiableAt I (I.prod 𝓘(ℝ, F [⋀^Fin k]→L[ℝ] ℝ))
      (fun y => (⟨y, a y⟩ : _root_.Bundle.TotalSpace (F [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial M ℝ)))) x) :
    letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    letI := Bundle.ExteriorPower.totalSpaceTopology F V k
    letI := Bundle.ExteriorPower.fiberBundle F V k
    letI := Bundle.ExteriorPower.vector_bundle F V k
    MDifferentiableAt I (I.prod 𝓘(ℝ, ⋀[ℝ]^k F))
      (fun y => (⟨y, u y⟩ : _root_.Bundle.TotalSpace (⋀[ℝ]^k F) (fun z => ⋀[ℝ]^k (V z)))) x →
      _root_.Submission.exteriorPower.alternatingDualEquiv k (cov.exteriorPower k u x X) (a x) =
        mvfderiv (I := I)
          (fun y => _root_.Submission.exteriorPower.alternatingDualEquiv k (u y) (a y)) x X -
            _root_.Submission.exteriorPower.alternatingDualEquiv k (u x)
              (CovariantDerivative.alternating cov k a x X) := by
  let : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  let := Bundle.ExteriorPower.totalSpaceTopology F V k
  let := Bundle.ExteriorPower.fiberBundle F V k
  let := Bundle.ExteriorPower.vector_bundle F V k
  intro hu
  have heval := Bundle.ExteriorPower.contMDiff_alternatingDualEquiv_map (IB := I) F V k 1
  have heu := (heval.mdifferentiableAt one_ne_zero).comp x hu
  obtain ⟨Z, hZ⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := TangentSpace I) (n := (⊤ : ℕ∞)) x X
  rw [← hZ, exteriorPower_apply, ContinuousLinearEquiv.apply_symm_apply]
  exact DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen_apply_of_mdifferentiableAt
    I M (F [⋀^Fin k]→L[ℝ] ℝ)
    (Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial M ℝ))
    ℝ (Bundle.Trivial M ℝ) (CovariantDerivative.alternating cov k) (trivial I M ℝ)
    _ heu Z.mdifferentiableAt ha

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.exteriorPower_alternatingDualEquiv_apply then
    throwError "Refusing to shadow existing declaration CovariantDerivative.exteriorPower_alternatingDualEquiv_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.exteriorPower_alternatingDualEquiv_apply ``Submission.CovariantDerivative.exteriorPower_alternatingDualEquiv_apply

end CovariantDerivative
