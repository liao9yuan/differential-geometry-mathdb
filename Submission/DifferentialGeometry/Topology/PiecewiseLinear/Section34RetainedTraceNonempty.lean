import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34SurvivingTrace

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] {U : Set M₁} {h : M₁ → M₂}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {Q : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {Cp CpBd Cc CcBd Kcore : Section34VertexIndex 𝒦 𝒦' → Set M₁}
  {ε : Section34VertexIndex 𝒦 𝒦' → ℝ}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}
  {Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ : Section34EdgeIndex 𝒦 𝒦' → Set M₁}
  {Sp Tp : Section34EdgeIndex 𝒦 𝒦' → Set M₂} {cnt : Section34EdgeIndex 𝒦 𝒦' → ℕ}
  {Pg : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂}
  {G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂}

theorem section34_modified_second_boundary_trace_nonempty
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') (Ψ : M₂ ≃ₜ M₂)
    (hfix : _root_.Set.EqOn Ψ id (G (ends e).1 '' (Ab₀ e ∪ Ab₁ e))) :
    (G (ends e).1 '' CpBd (ends e).1 ∩ Ψ '' (G (ends e).2 '' CpBd (ends e).2)).Nonempty := by
  have hinv : _root_.Set.EqOn Ψ.symm id (G (ends e).1 '' (Ab₀ e ∪ Ab₁ e)) := by
    intro x hx
    have heq := congrArg Ψ.symm (hfix hx)
    simpa only [Homeomorph.symm_apply_apply, id_eq] using heq.symm
  obtain ⟨x, ⟨y, hy, hyx⟩, hxB⟩ :=
    section34_modified_first_boundary_trace_nonempty hprep hpack e Ψ.symm hinv
  refine ⟨Ψ x, ?_, _root_.Set.mem_image_of_mem Ψ hxB⟩
  rw [← hyx, Ψ.apply_symm_apply]
  exact hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34_modified_second_boundary_trace_nonempty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34_modified_second_boundary_trace_nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34_modified_second_boundary_trace_nonempty ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34_modified_second_boundary_trace_nonempty

theorem section34_retained_trace_nonempty
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') (Ψ : M₂ ≃ₜ M₂)
    (hfix : _root_.Set.EqOn Ψ id (G (ends e).1 '' (Ab₀ e ∪ Ab₁ e)))
    {ι : Type*} {Γ : ι → Set M₂} (I : Set ι)
    (htrace : G (ends e).1 '' CpBd (ends e).1 ∩
      Ψ '' (G (ends e).2 '' CpBd (ends e).2) = ⋃ k : I, Γ k.1) :
    I.Nonempty := by
  obtain ⟨x, hx⟩ := section34_modified_second_boundary_trace_nonempty hprep hpack e Ψ hfix
  obtain ⟨k, -⟩ := mem_iUnion.mp (htrace.subset hx)
  exact ⟨k.1, k.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34_retained_trace_nonempty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34_retained_trace_nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34_retained_trace_nonempty ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34_retained_trace_nonempty

end DifferentialGeometry.Topology.PiecewiseLinear
