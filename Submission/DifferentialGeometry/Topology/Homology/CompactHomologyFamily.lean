import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ManifoldCompactHomology
import Submission.DifferentialGeometry.Topology.Homology.LocalOrientation
import Submission.DifferentialGeometry.Topology.Homology.EuclideanLocalTop
import Mathlib.Topology.Sets.Compacts

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Set _root_.TopologicalSpace _root_.Module
open scoped _root_.Manifold

universe u

namespace DifferentialGeometry.Topology

theorem exists_unique_compact_homology_family_of_locally_realized_family
    {E X : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace X] [T2Space X] [ChartedSpace E X]
    (n : ℕ) (hn : _root_.Module.finrank ℝ E ≤ n) (μ : ∀ x : X, integralLocalHomology n x)
    (hlocal : ∀ x : X, ∃ L : Set X, IsCompact L ∧ x ∈ interior L ∧
      ∃ a : integralRelativeHomology n Lᶜ, ∀ y (hy : y ∈ L),
        integralRelativeHomologyMap n (ContinuousMap.id X)
          (show Lᶜ ⊆ ({y}ᶜ : Set X) from
            compl_subset_compl.mpr (singleton_subset_iff.mpr hy)) a = μ y) :
    ∃! c : ∀ K : _root_.TopologicalSpace.Compacts X, integralRelativeHomology n (K : Set X)ᶜ,
      (∀ (K L : _root_.TopologicalSpace.Compacts X) (h : K ≤ L),
        integralRelativeHomologyMap n (ContinuousMap.id X)
          (show (L : Set X)ᶜ ⊆ (K : Set X)ᶜ from compl_subset_compl.mpr h) (c L) = c K) ∧
      ∀ (K : _root_.TopologicalSpace.Compacts X) (x : X) (hx : x ∈ K),
        integralRelativeHomologyMap n (ContinuousMap.id X)
          (show (K : Set X)ᶜ ⊆ ({x}ᶜ : Set X) from
            compl_subset_compl.mpr (singleton_subset_iff.mpr hx)) (c K) = μ x := by
  have hex (K : _root_.TopologicalSpace.Compacts X) := exists_unique_compact_class_of_locally_realized_family
    (E := E) n hn (K : Set X) K.isCompact μ (fun x _ => by
      obtain ⟨L, hL, hx, a, ha⟩ := hlocal x
      exact ⟨L, hL, hx, a, fun y hy => ha y hy.2⟩)
  choose c hc huniq using hex
  refine ⟨c, ⟨?_, hc⟩, ?_⟩
  · intro K L hKL
    apply huniq K
    intro x hx
    have hcomp := LinearMap.congr_fun (integralRelativeHomologyMap_comp n
      (ContinuousMap.id X) (ContinuousMap.id X)
      (show (L : Set X)ᶜ ⊆ (K : Set X)ᶜ from compl_subset_compl.mpr hKL)
      (show (K : Set X)ᶜ ⊆ ({x}ᶜ : Set X) from
        compl_subset_compl.mpr (singleton_subset_iff.mpr hx))) (c L)
    exact hcomp.symm.trans (hc L x (hKL hx))
  · intro d hd
    funext K
    exact huniq K (d K) (hd.2 K)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_unique_compact_homology_family_of_locally_realized_family then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_unique_compact_homology_family_of_locally_realized_family"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_unique_compact_homology_family_of_locally_realized_family ``Submission.DifferentialGeometry.Topology.exists_unique_compact_homology_family_of_locally_realized_family

theorem exists_compact_homology_family_of_simplyConnected
    {E M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
    [SimplyConnectedSpace M] :
    ∃ c : ∀ K : _root_.TopologicalSpace.Compacts M, integralRelativeHomology (Module.finrank ℝ E) (K : Set M)ᶜ,
      (∀ (K L : _root_.TopologicalSpace.Compacts M) (h : K ≤ L),
        integralRelativeHomologyMap (Module.finrank ℝ E) (ContinuousMap.id M)
          (show (L : Set M)ᶜ ⊆ (K : Set M)ᶜ from compl_subset_compl.mpr h) (c L) = c K) ∧
      ∀ p : M, Function.Bijective (fun z : ℤ => z • c {p}) := by
  let p := Classical.arbitrary M
  let ω := (Module.finBasis ℝ E).orientation
  let ωp := Orientation.map (Fin (Module.finrank ℝ E))
    ((_root_.FiberBundle.trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).continuousLinearEquivAt ℝ p
      (by simpa only [TangentBundle.trivializationAt_baseSet] using
        mem_chart_source E p)).symm.toLinearEquiv ω
  obtain ⟨o, _, hlocal⟩ := exists_tangent_orientation_locality_of_simplyConnected p ωp
  obtain ⟨a, ha⟩ := exists_integralLocalHomology_generator (0 : E)
  obtain ⟨μ, ⟨hmaps, hreal⟩, _⟩ :=
    exists_locally_realized_family_of_tangent_orientation_locality o ω a hlocal
  obtain ⟨c, ⟨hc, hpoints⟩, _⟩ :=
    exists_unique_compact_homology_family_of_locally_realized_family
      (E := E) (Module.finrank ℝ E) le_rfl μ hreal
  refine ⟨c, hc, ?_⟩
  intro x
  have hpoint := hpoints {x} x (by simp)
  rw [integralRelativeHomologyMap_id] at hpoint
  simp only [LinearMap.id_apply] at hpoint
  rw [hpoint]
  exact integralLocalHomology_generator_of_orientation_coordinates
    x x (mem_chart_source E x) (o x) ω a ha (μ x) (hmaps x x (mem_chart_source E x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_compact_homology_family_of_simplyConnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_compact_homology_family_of_simplyConnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_compact_homology_family_of_simplyConnected ``Submission.DifferentialGeometry.Topology.exists_compact_homology_family_of_simplyConnected

end DifferentialGeometry.Topology
