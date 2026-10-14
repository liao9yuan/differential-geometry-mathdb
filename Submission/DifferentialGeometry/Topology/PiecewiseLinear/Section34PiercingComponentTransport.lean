import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34Frame

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem Homeomorph.exists_component_containing_outside_image {M : Type*}
    [TopologicalSpace M] (φ : M ≃ₜ M) {S T : Set M}
    (hcomponent : ∃ y₀ ∈ S, ∀ z ∈ S, z ∉ T → z ∈ connectedComponentIn S y₀)
    (houtside : ∀ z ∈ S, φ z ∉ T → z ∉ T) :
    ∃ y₀ ∈ φ '' S, ∀ z ∈ φ '' S, z ∉ T → z ∈ connectedComponentIn (φ '' S) y₀ := by
  obtain ⟨y₀, hy₀, hcomponent⟩ := hcomponent
  refine ⟨φ y₀, _root_.Set.mem_image_of_mem φ hy₀, ?_⟩
  rintro _ ⟨z, hz, rfl⟩ hnot
  rw [← φ.image_connectedComponentIn hy₀]
  exact _root_.Set.mem_image_of_mem φ (hcomponent z hz (houtside z hz hnot))

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Topology.PiecewiseLinear.Homeomorph
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.Homeomorph.exists_component_containing_outside_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.Homeomorph.exists_component_containing_outside_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.Homeomorph.exists_component_containing_outside_image ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.Homeomorph.exists_component_containing_outside_image

theorem Homeomorph.exists_piercing_components_of_preserving_cell {M : Type*}
    [TopologicalSpace M] (φ : M ≃ₜ M) {A B T : Set M} (hA : φ '' A = A)
    (houtside : ∀ z ∈ B, φ z ∉ T → z ∉ T)
    (hin : ∃ y₀ ∈ B ∩ A, ∀ z ∈ B ∩ A, z ∉ T → z ∈ connectedComponentIn (B ∩ A) y₀)
    (hout : ∃ y₀ ∈ B \ A, ∀ z ∈ B \ A, z ∉ T → z ∈ connectedComponentIn (B \ A) y₀) :
    (∃ y₀ ∈ φ '' B ∩ A, ∀ z ∈ φ '' B ∩ A, z ∉ T →
      z ∈ connectedComponentIn (φ '' B ∩ A) y₀) ∧
    ∃ y₀ ∈ φ '' B \ A, ∀ z ∈ φ '' B \ A, z ∉ T →
      z ∈ connectedComponentIn (φ '' B \ A) y₀ := by
  have hinside := Homeomorph.exists_component_containing_outside_image φ hin
    (fun z hz => houtside z hz.1)
  have hexterior := Homeomorph.exists_component_containing_outside_image φ hout
    (fun z hz => houtside z hz.1)
  rw [_root_.Set.image_inter φ.injective, hA] at hinside
  rw [_root_.Set.image_sdiff φ.injective, hA] at hexterior
  exact ⟨hinside, hexterior⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.Homeomorph.exists_piercing_components_of_preserving_cell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.Homeomorph.exists_piercing_components_of_preserving_cell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.Homeomorph.exists_piercing_components_of_preserving_cell ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.Homeomorph.exists_piercing_components_of_preserving_cell

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] {U : Set M₁} {h : M₁ → M₂}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {Q : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {Cp CpBd Cc : Section34VertexIndex 𝒦 𝒦' → Set M₁}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}
  {Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ : Section34EdgeIndex 𝒦 𝒦' → Set M₁}
  {Sp Tp : Section34EdgeIndex 𝒦 𝒦' → Set M₂} {cnt : Section34EdgeIndex 𝒦 𝒦' → ℕ}
  {Pg : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂}
  {G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂}

theorem section34_piercing_components_of_preserving_first_cell
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') (φ : M₂ ≃ₜ M₂)
    (hcell : φ '' (G (ends e).1 '' Cp (ends e).1) = G (ends e).1 '' Cp (ends e).1)
    (houtside : ∀ z ∈ G (ends e).2 '' Bb e, φ z ∉ Tp e → z ∉ Tp e) :
    (∃ y₀ ∈ (φ ∘ G (ends e).2) '' Bb e ∩ G (ends e).1 '' Cp (ends e).1,
      ∀ z ∈ (φ ∘ G (ends e).2) '' Bb e ∩ G (ends e).1 '' Cp (ends e).1, z ∉ Tp e →
        z ∈ connectedComponentIn
          ((φ ∘ G (ends e).2) '' Bb e ∩ G (ends e).1 '' Cp (ends e).1) y₀) ∧
    ∃ y₀ ∈ (φ ∘ G (ends e).2) '' Bb e \ G (ends e).1 '' Cp (ends e).1,
      ∀ z ∈ (φ ∘ G (ends e).2) '' Bb e \ G (ends e).1 '' Cp (ends e).1, z ∉ Tp e →
        z ∈ connectedComponentIn
          ((φ ∘ G (ends e).2) '' Bb e \ G (ends e).1 '' Cp (ends e).1) y₀ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hin, hout, -⟩ := hpack
  simpa only [_root_.Set.image_comp] using
    Homeomorph.exists_piercing_components_of_preserving_cell φ hcell houtside (hin e) (hout e)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34_piercing_components_of_preserving_first_cell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34_piercing_components_of_preserving_first_cell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34_piercing_components_of_preserving_first_cell ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34_piercing_components_of_preserving_first_cell

end DifferentialGeometry.Topology.PiecewiseLinear
