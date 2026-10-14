import Submission.DifferentialGeometry.Analysis.ODE.Flow.LinearODE.Solution
import Submission.DifferentialGeometry.Bundle.ContinuousLinearMapSection.Spacetime
import Submission.DifferentialGeometry.Bundle.SmoothSubbundle.KernelAPI

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Set
open scoped _root_.InnerProductSpace _root_.Manifold _root_.ContDiff _root_.Topology

open _root_.ContinuousLinearMap in
theorem ContinuousLinearMap.ker_and_range_eq_on_Ioo_of_contDiffOn_spacetime_kernel_frame_deriv_annihilation
    {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {V : M → Type*} [TopologicalSpace (_root_.Bundle.TotalSpace F V)]
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V]
    [ContMDiffVectorBundle 1 F V I]
    {ι : Type*} [Finite ι]
    {A : ℝ → (x : M) → V x →L[ℝ] V x}
    {w : ι → (p : ℝ × M) → V p.2}
    {U : Set (ℝ × M)} (hU : IsOpen U)
    (hw : ∀ i, ContMDiffOn (𝓘(ℝ, ℝ).prod I)
      ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, F)) 1
      (fun p => TotalSpace.mk' F p (w i p) : ℝ × M →
        _root_.Bundle.TotalSpace F ((ContMDiffMap.snd :
          C^1⟮𝓘(ℝ, ℝ).prod I, ℝ × M; I, M⟯) *ᵖ V)) U)
    {x : M} {a b : ℝ} (hslice : ∀ t ∈ _root_.Set.Ioo a b, (t, x) ∈ U)
    (hA : ContDiffOn ℝ 1 (fun t => A t x) (_root_.Set.Ioo a b))
    (hli : ∀ t ∈ _root_.Set.Ioo a b, LinearIndependent ℝ (fun i => w i (t, x)))
    (hker : ∀ t ∈ _root_.Set.Ioo a b,
      Submodule.span ℝ (Set.range fun i => w i (t, x)) = (A t x).ker)
    (hann : ∀ t ∈ _root_.Set.Ioo a b, ∀ v, v ∈ (A t x).ker →
      deriv (fun q => A q x) t v = 0)
    (hsymm : ∀ t ∈ _root_.Set.Ioo a b, (A t x).toLinearMap.IsSymmetric)
    {s t : ℝ} (hs : s ∈ _root_.Set.Ioo a b) (ht : t ∈ _root_.Set.Ioo a b) :
    (A s x).ker = (A t x).ker ∧ (A s x).range = (A t x).range := by
  let _ := VectorBundle.finiteDimensional ℝ F V x
  apply ContinuousLinearMap.ker_and_range_eq_on_Ioo_of_contDiffOn_kernel_frame_deriv_annihilation
    (A := fun q => A q x) (w := fun i q => w i (q, x))
  · exact hA
  · intro i
    exact contDiffOn_fixed_spatial_of_contMDiffOn_pullback_section
      (I := I) (F := F) (V := V) (w := w i) hU (hw i) hslice
  · exact hli
  · exact hker
  · exact hann
  · exact hsymm
  · exact hs
  · exact ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousLinearMap.ker_and_range_eq_on_Ioo_of_contDiffOn_spacetime_kernel_frame_deriv_annihilation then
    throwError "Refusing to shadow existing declaration ContinuousLinearMap.ker_and_range_eq_on_Ioo_of_contDiffOn_spacetime_kernel_frame_deriv_annihilation"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousLinearMap.ker_and_range_eq_on_Ioo_of_contDiffOn_spacetime_kernel_frame_deriv_annihilation ``Submission.ContinuousLinearMap.ker_and_range_eq_on_Ioo_of_contDiffOn_spacetime_kernel_frame_deriv_annihilation

open _root_.ContinuousLinearMap in
theorem ContinuousLinearMap.ker_and_range_eq_on_Ioo_of_contMDiffOn_constant_finrank_deriv_annihilation
    {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {V : M → Type*} [TopologicalSpace (_root_.Bundle.TotalSpace F V)]
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V]
    [ContMDiffVectorBundle 1 F V I]
    {A : ℝ → (x : M) → V x →L[ℝ] V x} {a b : ℝ}
    (hA_space : ContMDiffOnSpacetimeEndomorphism
      (I := I) (F := F) (V := V) (n := 1) A
      (_root_.Set.Ioo a b ×ˢ (Set.univ : Set M)))
    (hA_time : ∀ x, ContDiffOn ℝ 1 (fun t => A t x) (_root_.Set.Ioo a b))
    (k : ℕ) (hker_rank : ∀ t ∈ _root_.Set.Ioo a b, ∀ x,
      Module.finrank ℝ (A t x).ker = k)
    (hann : ∀ t ∈ _root_.Set.Ioo a b, ∀ x v, v ∈ (A t x).ker →
      deriv (fun q => A q x) t v = 0)
    (hsymm : ∀ t ∈ _root_.Set.Ioo a b, ∀ x,
      (A t x).toLinearMap.IsSymmetric)
    {x : M} {s t : ℝ} (hs : s ∈ _root_.Set.Ioo a b) (ht : t ∈ _root_.Set.Ioo a b) :
    (A s x).ker = (A t x).ker ∧ (A s x).range = (A t x).range := by
  let c : C^1⟮𝓘(ℝ, ℝ).prod I, ℝ × M; I, M⟯ := ContMDiffMap.snd
  let _ : TopologicalSpace (_root_.Bundle.TotalSpace F (fun p : ℝ × M => V p.2)) := by
    change TopologicalSpace (_root_.Bundle.TotalSpace F (c *ᵖ V)); infer_instance
  let _ : FiberBundle F (fun p : ℝ × M => V p.2) := by
    change FiberBundle F (c *ᵖ V); infer_instance
  let _ : VectorBundle ℝ F (fun p : ℝ × M => V p.2) := by
    change VectorBundle ℝ F (c *ᵖ V); infer_instance
  let _ : ContMDiffVectorBundle 1 F (fun p : ℝ × M => V p.2)
      (𝓘(ℝ, ℝ).prod I) := by
    change ContMDiffVectorBundle 1 F (c *ᵖ V) (𝓘(ℝ, ℝ).prod I); infer_instance
  have hA_space' : ContMDiffOn (𝓘(ℝ, ℝ).prod I)
      ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, F →L[ℝ] F)) 1
      (fun p => TotalSpace.mk' (F →L[ℝ] F) p (A p.1 p.2) :
        ℝ × M → _root_.Bundle.TotalSpace (F →L[ℝ] F)
          (fun p => V p.2 →L[ℝ] V p.2))
      (_root_.Set.Ioo a b ×ˢ (Set.univ : Set M)) := by
    simpa only [ContMDiffOnSpacetimeEndomorphism] using hA_space
  have hlocal : IsLocallyConstant (fun u : _root_.Set.Ioo a b =>
      ((A u x).ker, (A u x).range)) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro u
    obtain ⟨U, w, hU, huU, hUW, hw⟩ :=
      ContMDiffVectorSubbundle.exists_kernel_frameOn
        (I := 𝓘(ℝ, ℝ).prod I) (F₁ := F) (F₂ := F)
        (V₁ := fun p : ℝ × M => V p.2)
        (V₂ := fun p : ℝ × M => V p.2)
        (fun p : ℝ × M => A p.1 p.2)
        (_root_.Set.Ioo a b ×ˢ (Set.univ : Set M))
        (isOpen_Ioo.prod isOpen_univ) hA_space' k
        (fun p hp => hker_rank p.1 hp.1 p.2)
        ((u : ℝ), x) ⟨u.property, Set.mem_univ x⟩
    have hpreimage_open : IsOpen ((fun q : ℝ => (q, x)) ⁻¹' U) :=
      hU.preimage (continuous_id.prodMk continuous_const)
    have hu_preimage : (u : ℝ) ∈ (fun q : ℝ => (q, x)) ⁻¹' U := huU
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
      (hpreimage_open.mem_nhds hu_preimage)
    have hinterval : _root_.Set.Ioo ((u : ℝ) - ε) ((u : ℝ) + ε) ⊆
        (fun q : ℝ => (q, x)) ⁻¹' U := by
      simpa only [← Real.ball_eq_Ioo] using hball
    have hinterval_global : _root_.Set.Ioo ((u : ℝ) - ε) ((u : ℝ) + ε) ⊆ _root_.Set.Ioo a b := by
      intro q hq
      exact (hUW (hinterval hq)).1
    have hu_local : (u : ℝ) ∈ _root_.Set.Ioo ((u : ℝ) - ε) ((u : ℝ) + ε) := by
      constructor <;> linarith
    have hbridge {q : ℝ}
        (hq : q ∈ _root_.Set.Ioo ((u : ℝ) - ε) ((u : ℝ) + ε)) :
        (A q x).ker = (A u x).ker ∧ (A q x).range = (A u x).range := by
      apply ContinuousLinearMap.ker_and_range_eq_on_Ioo_of_contDiffOn_spacetime_kernel_frame_deriv_annihilation
        (I := I) (F := F) (V := V) (A := A) (w := w) hU
      · exact hw.contMDiffOn
      · exact hinterval
      · exact (hA_time x).mono hinterval_global
      · intro τ hτ
        exact hw.linearIndependent (hinterval hτ)
      · intro τ hτ
        exact hw.spans (hinterval hτ)
      · intro τ hτ v hv
        exact hann τ (hinterval_global hτ) x v hv
      · intro τ hτ
        exact hsymm τ (hinterval_global hτ) x
      · exact hq
      · exact hu_local
    have hlocal_nhds : Subtype.val ⁻¹'
        Ioo ((u : ℝ) - ε) ((u : ℝ) + ε) ∈ 𝓝 u :=
      continuous_subtype_val.continuousAt.preimage_mem_nhds
        (isOpen_Ioo.mem_nhds hu_local)
    filter_upwards [hlocal_nhds] with v hv
    exact Prod.ext (hbridge hv).1 (hbridge hv).2
  let hpre : PreconnectedSpace (_root_.Set.Ioo a b) :=
    Subtype.preconnectedSpace isPreconnected_Ioo
  have hpair := hlocal.apply_eq_of_isPreconnected
    (@_root_.PreconnectedSpace.isPreconnected_univ _ _ hpre)
    (x := ⟨s, hs⟩) (y := ⟨t, ht⟩) trivial trivial
  exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousLinearMap.ker_and_range_eq_on_Ioo_of_contMDiffOn_constant_finrank_deriv_annihilation then
    throwError "Refusing to shadow existing declaration ContinuousLinearMap.ker_and_range_eq_on_Ioo_of_contMDiffOn_constant_finrank_deriv_annihilation"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousLinearMap.ker_and_range_eq_on_Ioo_of_contMDiffOn_constant_finrank_deriv_annihilation ``Submission.ContinuousLinearMap.ker_and_range_eq_on_Ioo_of_contMDiffOn_constant_finrank_deriv_annihilation
