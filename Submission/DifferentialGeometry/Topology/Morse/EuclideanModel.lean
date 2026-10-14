import Submission.DifferentialGeometry.Topology.Manifold.SmoothModelTransport
import Submission.DifferentialGeometry.Topology.Morse.NormalForm.Local
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Geometry.Manifold.Instances.Real

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology.Morse

noncomputable def morseModelEuclideanModelEquiv (n : ℕ) :
    MorseModel n ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Morse.morseModelEuclideanModelEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Morse.morseModelEuclideanModelEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Morse.morseModelEuclideanModelEquiv ``Submission.DifferentialGeometry.Topology.Morse.morseModelEuclideanModelEquiv

theorem morseModelEuclideanModelCompat (n : ℕ) (y : MorseModel n) :
    (𝓡 n) (morseModelEuclideanModelEquiv n y) =
      morseModelEuclideanModelEquiv n ((𝓘(ℝ, MorseModel n)) y) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Morse.morseModelEuclideanModelCompat then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Morse.morseModelEuclideanModelCompat"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Morse.morseModelEuclideanModelCompat ``Submission.DifferentialGeometry.Topology.Morse.morseModelEuclideanModelCompat

@[instance_reducible]
noncomputable def morseModelEuclideanModelChartedSpace (n : ℕ) (M : Type*)
    [TopologicalSpace M] [ChartedSpace (MorseModel n) M] :
    ChartedSpace (EuclideanSpace ℝ (Fin n)) M :=
  DifferentialGeometry.Manifold.chartedSpaceTransHomeomorph (M := M)
    (morseModelEuclideanModelEquiv n).toHomeomorph

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Morse.morseModelEuclideanModelChartedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Morse.morseModelEuclideanModelChartedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Morse.morseModelEuclideanModelChartedSpace ``Submission.DifferentialGeometry.Topology.Morse.morseModelEuclideanModelChartedSpace

theorem isManifold_morseModelEuclideanModel {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (MorseModel n) M] [IsManifold (𝓘(ℝ, MorseModel n)) ∞ M] :
    letI := morseModelEuclideanModelChartedSpace n M
    IsManifold (𝓡 n) ∞ M :=
  DifferentialGeometry.Manifold.isManifold_transHomeomorph (M := M)
    (𝓘(ℝ, MorseModel n)) (𝓡 n) (morseModelEuclideanModelEquiv n).toHomeomorph
    (morseModelEuclideanModelEquiv n) (morseModelEuclideanModelCompat n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Morse.isManifold_morseModelEuclideanModel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Morse.isManifold_morseModelEuclideanModel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Morse.isManifold_morseModelEuclideanModel ``Submission.DifferentialGeometry.Topology.Morse.isManifold_morseModelEuclideanModel

noncomputable def diffeomorph_morseModelEuclideanModel {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (MorseModel n) M] [IsManifold (𝓘(ℝ, MorseModel n)) ∞ M] :
    letI := morseModelEuclideanModelChartedSpace n M
    M ≃ₘ⟮𝓡 n, 𝓘(ℝ, MorseModel n)⟯ M := by
  letI := morseModelEuclideanModelChartedSpace n M
  letI := isManifold_morseModelEuclideanModel (n := n) (M := M)
  refine ⟨Equiv.refl M, ?_, ?_⟩
  · change ContMDiff (𝓡 n) (𝓘(ℝ, MorseModel n)) ∞ (id : M → M)
    exact (DifferentialGeometry.Manifold.contMDiff_chartedSpaceTransHomeomorph_iff
      (𝓘(ℝ, MorseModel n)) (𝓡 n) (morseModelEuclideanModelEquiv n).toHomeomorph
      (morseModelEuclideanModelEquiv n) (morseModelEuclideanModelCompat n)
      (I₀ := 𝓡 n) (f := id)).mp contMDiff_id
  · change ContMDiff (𝓘(ℝ, MorseModel n)) (𝓡 n) ∞ (id : M → M)
    exact (DifferentialGeometry.Manifold.contMDiff_chartedSpaceTransHomeomorph_iff
      (𝓘(ℝ, MorseModel n)) (𝓡 n) (morseModelEuclideanModelEquiv n).toHomeomorph
      (morseModelEuclideanModelEquiv n) (morseModelEuclideanModelCompat n)
      (I₀ := 𝓘(ℝ, MorseModel n)) (f := id)).mpr contMDiff_id

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Morse.diffeomorph_morseModelEuclideanModel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Morse.diffeomorph_morseModelEuclideanModel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Morse.diffeomorph_morseModelEuclideanModel ``Submission.DifferentialGeometry.Topology.Morse.diffeomorph_morseModelEuclideanModel

theorem diffeomorph_morseModelEuclideanModel_apply {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (MorseModel n) M] [IsManifold (𝓘(ℝ, MorseModel n)) ∞ M] (x : M) :
    letI := morseModelEuclideanModelChartedSpace n M
    (diffeomorph_morseModelEuclideanModel (n := n) (M := M) : M → M) x = x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Morse.diffeomorph_morseModelEuclideanModel_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Morse.diffeomorph_morseModelEuclideanModel_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Morse.diffeomorph_morseModelEuclideanModel_apply ``Submission.DifferentialGeometry.Topology.Morse.diffeomorph_morseModelEuclideanModel_apply

theorem nonempty_diffeomorph_morseModelEuclideanModel_self (n : ℕ) :
    letI := morseModelEuclideanModelChartedSpace n (MorseModel n)
    ∃ f : MorseModel n ≃ₘ⟮𝓡 n, 𝓘(ℝ, MorseModel n)⟯ MorseModel n, f 0 = 0 :=
  ⟨diffeomorph_morseModelEuclideanModel, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Morse.nonempty_diffeomorph_morseModelEuclideanModel_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Morse.nonempty_diffeomorph_morseModelEuclideanModel_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Morse.nonempty_diffeomorph_morseModelEuclideanModel_self ``Submission.DifferentialGeometry.Topology.Morse.nonempty_diffeomorph_morseModelEuclideanModel_self

end DifferentialGeometry.Topology.Morse
