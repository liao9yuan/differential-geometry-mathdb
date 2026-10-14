import Submission.DifferentialGeometry.Topology.LoopSpace.GenericApproximation
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.LoopFamilyExtension
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ContractibleLoopPerturbation
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.LeastAreaConvergence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.AreaError.Convergence
import Mathlib.Analysis.SpecificLimits.Basic
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.AreaEvolution.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] in
private theorem isEmbedding_of_continuous_injective_of_compact {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X] [T2Space Y] {f : X → Y}
    (hf : Continuous f) (hinj : Function.Injective f) : Topology.IsEmbedding f :=
  (Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap hf hinj
    fun _ hs => (hs.isCompact.image hf).isClosed).toIsEmbedding

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.isEmbedding_of_continuous_injective_of_compact
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.isEmbedding_of_continuous_injective_of_compact target :: scope.openDecls } }

def LoopFamilyEmbeddedOffFinset (γ : ℝ → ContinuousFreeLoop M) (J : Set ℝ) : Prop :=
  ∃ exceptional : Finset ℝ, ∀ t ∈ J, t ∉ exceptional → Topology.IsEmbedding (γ t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.LoopFamilyEmbeddedOffFinset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.LoopFamilyEmbeddedOffFinset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.LoopFamilyEmbeddedOffFinset ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.LoopFamilyEmbeddedOffFinset

namespace LoopFamilyEmbeddedOffFinset

variable {γ : ℝ → ContinuousFreeLoop M} {J J' : Set ℝ}

theorem mono (h : J' ⊆ J) (hγ : LoopFamilyEmbeddedOffFinset γ J) :
    LoopFamilyEmbeddedOffFinset γ J' :=
  let ⟨exceptional, hexc⟩ := hγ
  ⟨exceptional, fun t ht hne => hexc t (h ht) hne⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.LoopFamilyEmbeddedOffFinset.mono then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.LoopFamilyEmbeddedOffFinset.mono"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.LoopFamilyEmbeddedOffFinset.mono ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.LoopFamilyEmbeddedOffFinset.mono

theorem of_slicewiseEmbedding (h : ∀ t ∈ J, Topology.IsEmbedding (γ t)) :
    LoopFamilyEmbeddedOffFinset γ J :=
  ⟨∅, fun t ht _ => h t ht⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.LoopFamilyEmbeddedOffFinset.of_slicewiseEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.LoopFamilyEmbeddedOffFinset.of_slicewiseEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.LoopFamilyEmbeddedOffFinset.of_slicewiseEmbedding ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.LoopFamilyEmbeddedOffFinset.of_slicewiseEmbedding

end LoopFamilyEmbeddedOffFinset

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] in
theorem loopFamilyEmbeddedOffFinset_iff_injective [T2Space M]
    (γ : ℝ → ContinuousFreeLoop M) (J : Set ℝ) :
    LoopFamilyEmbeddedOffFinset γ J ↔ ∃ exceptional : Finset ℝ,
      ∀ t ∈ J, t ∉ exceptional → Function.Injective (γ t) := by
  constructor
  · rintro ⟨exceptional, hexc⟩
    exact ⟨exceptional, fun t ht hne => (hexc t ht hne).injective⟩
  · rintro ⟨exceptional, hinj⟩
    exact ⟨exceptional, fun t ht hne =>
      isEmbedding_of_continuous_injective_of_compact (γ t).continuous (hinj t ht hne)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.loopFamilyEmbeddedOffFinset_iff_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.loopFamilyEmbeddedOffFinset_iff_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.loopFamilyEmbeddedOffFinset_iff_injective ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.loopFamilyEmbeddedOffFinset_iff_injective

theorem loopFamily_spacetimeMap_injOn_of_embeddedOffFinset (γ : ℝ → ContinuousFreeLoop M)
    {J : Set ℝ} (hemb : LoopFamilyEmbeddedOffFinset γ J) :
    ∃ exceptional : Finset ℝ,
      Set.InjOn (fun p : ℝ × Surgery.Topology.Circle => (p.1, γ p.1 p.2))
        ((J \ ↑exceptional) ×ˢ _root_.Set.univ) :=
  let ⟨exceptional, hexc⟩ := hemb
  ⟨exceptional, loopFamily_spacetimeMap_injective γ (J := J \ ↑exceptional)
    (fun t ht => hexc t ht.1 ht.2)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.loopFamily_spacetimeMap_injOn_of_embeddedOffFinset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.loopFamily_spacetimeMap_injOn_of_embeddedOffFinset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.loopFamily_spacetimeMap_injOn_of_embeddedOffFinset ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.loopFamily_spacetimeMap_injOn_of_embeddedOffFinset

variable [hBoundary : I.Boundaryless] [hT2 : T2Space M]
    [hCompact : CompactSpace M] [hNonempty : Nonempty M]
variable [SigmaCompactSpace M]
variable {D : RealTimeInterval} {a b : ℝ}

include hBoundary hT2 hCompact hNonempty

omit hBoundary hCompact hNonempty [SigmaCompactSpace M] in
theorem rfs_csf_generic_curves_of_slicewiseEmbedding
    (B : RicciBackground (I := I) (M := M) D a b) {N : ℕ}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (γ : ℝ → ContinuousFreeLoop M)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (_root_.Set.Icc a b))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := I) (_root_.Set.Icc a b))
    (hemb : ∀ t ∈ _root_.Set.Icc a b, Topology.IsEmbedding (γ t)) :
    ∃ approximants : ℕ → ℝ → ContinuousFreeLoop M,
      (∀ j, (curveOfLoopFamily (approximants j)).SmoothOn (I := I) (_root_.Set.Icc a b) ∧
        (curveOfLoopFamily (approximants j)).ImmersedOn (I := I) (_root_.Set.Icc a b) ∧
        ∃ exceptional : Finset ℝ, ∀ t ∈ _root_.Set.Icc a b,
          t ∉ exceptional → Topology.IsEmbedding (approximants j t)) ∧
      (∀ ε > 0, ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ m : ℕ, m ≤ 2 →
        ∀ p ∈ _root_.Set.Icc (0 : ℝ) 1 ×ˢ _root_.Set.Icc a b,
          ‖iteratedFDerivWithin ℝ m
              (fun q : ℝ × ℝ => e.map (approximants j q.2 (q.1 : Surgery.Topology.Circle)))
              (_root_.Set.univ ×ˢ _root_.Set.Icc a b) p -
            iteratedFDerivWithin ℝ m
              (fun q : ℝ × ℝ => e.map (γ q.2 (q.1 : Surgery.Topology.Circle)))
              (_root_.Set.univ ×ˢ _root_.Set.Icc a b) p‖ < ε) ∧
      (∀ ε > 0, ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ t ∈ _root_.Set.Icc a b,
        |(curveOfLoopFamily (approximants j)).areaError B.family.metric (_root_.Set.Icc a b) t -
          (curveOfLoopFamily γ).areaError B.family.metric (_root_.Set.Icc a b) t| < ε) ∧
      ((∀ t ∈ _root_.Set.Icc a b, IsContractibleLoop (γ t)) →
        (∀ j t, t ∈ _root_.Set.Icc a b → IsContractibleLoop (approximants j t)) ∧
        ∀ ε > 0, ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ t ∈ _root_.Set.Icc a b,
          |loopFamilyLeastArea B.family.metric (approximants j) t -
            loopFamilyLeastArea B.family.metric γ t| < ε) := by
  refine ⟨fun _ => γ, ?_, ?_, ?_, ?_⟩
  · intro j
    exact ⟨hγ, hi, ⟨∅, fun t ht _ => hemb t ht⟩⟩
  · intro ε hε
    refine ⟨0, ?_⟩
    intro j _ m _ p _
    rw [sub_self, norm_zero]
    exact hε
  · intro ε hε
    refine ⟨0, ?_⟩
    intro j _ t _
    rw [sub_self, abs_zero]
    exact hε
  · intro hctr
    refine ⟨fun j t ht => hctr t ht, ?_⟩
    intro ε hε
    refine ⟨0, ?_⟩
    intro j _ t _
    rw [sub_self, abs_zero]
    exact hε

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.rfs_csf_generic_curves_of_slicewiseEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.rfs_csf_generic_curves_of_slicewiseEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.rfs_csf_generic_curves_of_slicewiseEmbedding ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.rfs_csf_generic_curves_of_slicewiseEmbedding

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end

noncomputable section

open _root_.Set _root_.Filter _root_.Metric _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Topology _root_.Submission.Topology _root_.ContDiff _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem exists_generic_loopFamily_approximation_of_smoothOn_univ
    (hdim : Module.finrank ℝ E = 3) {N : ℕ}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (γ : ℝ → ContinuousFreeLoop M) {a b : ℝ} (hab : a < b)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) _root_.Set.univ)
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := I) (_root_.Set.Icc a b))
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ Γ : ℝ → ContinuousFreeLoop M,
      (curveOfLoopFamily Γ).SmoothOn (I := I) _root_.Set.univ ∧
      (curveOfLoopFamily Γ).ImmersedOn (I := I) (_root_.Set.Icc a b) ∧
      (∃ exceptional : Finset ℝ, ∀ t ∈ _root_.Set.Icc a b, t ∉ exceptional → Topology.IsEmbedding (Γ t)) ∧
      ∀ m : ℕ, m ≤ n → ∀ p ∈ _root_.Set.Icc (0 : ℝ) 1 ×ˢ _root_.Set.Icc a b,
        ‖iteratedFDerivWithin ℝ m
            (fun q : ℝ × ℝ => e.map (Γ q.2 (q.1 : Surgery.Topology.Circle)))
            (_root_.Set.univ ×ˢ _root_.Set.Icc a b) p -
          iteratedFDerivWithin ℝ m
            (fun q : ℝ × ℝ => e.map (γ q.2 (q.1 : Surgery.Topology.Circle)))
            (_root_.Set.univ ×ˢ _root_.Set.Icc a b) p‖ < ε := by
  obtain ⟨β, hβ, hβi, hβemb, hβjets⟩ :=
    DifferentialGeometry.Topology.exists_generic_loop_family_approximation_of_contMDiff
      hdim e.map e.smooth e.isClosedEmbedding.isEmbedding e.injective_mfderiv
      (fun p => γ p.1 p.2) hab (contMDiff_uncurry_of_smoothOn_univ γ hγ) hi n hε
  let Γ : ℝ → ContinuousFreeLoop M := fun t =>
    ⟨fun z => β (t, z), hβ.continuous.comp (continuous_const.prodMk continuous_id)⟩
  exact ⟨Γ, smoothOn_curveOfLoopFamily_of_contMDiff Γ hβ _root_.Set.univ, hβi, hβemb, hβjets⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.exists_generic_loopFamily_approximation_of_smoothOn_univ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.exists_generic_loopFamily_approximation_of_smoothOn_univ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.exists_generic_loopFamily_approximation_of_smoothOn_univ ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.exists_generic_loopFamily_approximation_of_smoothOn_univ

theorem exists_generic_loopFamily_approximation
    (hdim : Module.finrank ℝ E = 3) {N : ℕ}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (R : Width.SmoothTubularRetraction e)
    (γ : ℝ → ContinuousFreeLoop M) {a b : ℝ} (hab : a < b)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (_root_.Set.Icc a b))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := I) (_root_.Set.Icc a b))
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ Γ : ℝ → ContinuousFreeLoop M,
      (curveOfLoopFamily Γ).SmoothOn (I := I) _root_.Set.univ ∧
      (curveOfLoopFamily Γ).ImmersedOn (I := I) (_root_.Set.Icc a b) ∧
      (∃ exceptional : Finset ℝ, ∀ t ∈ _root_.Set.Icc a b, t ∉ exceptional → Topology.IsEmbedding (Γ t)) ∧
      ∀ m : ℕ, m ≤ n → ∀ p ∈ _root_.Set.Icc (0 : ℝ) 1 ×ˢ _root_.Set.Icc a b,
        ‖iteratedFDerivWithin ℝ m
            (fun q : ℝ × ℝ => e.map (Γ q.2 (q.1 : Surgery.Topology.Circle)))
            (_root_.Set.univ ×ˢ _root_.Set.Icc a b) p -
          iteratedFDerivWithin ℝ m
            (fun q : ℝ × ℝ => e.map (γ q.2 (q.1 : Surgery.Topology.Circle)))
            (_root_.Set.univ ×ˢ _root_.Set.Icc a b) p‖ < ε := by
  obtain ⟨γext, lo, hi', hlo, hhi, hext, hiext, heq⟩ :=
    exists_smooth_immersed_loopFamily_extension hab.le e R γ hγ hi
  have hiexact : (curveOfLoopFamily γext).ImmersedOn (I := I) (_root_.Set.Icc a b) :=
    fun x t ht => hiext x t ⟨hlo.le.trans ht.1, ht.2.trans hhi.le⟩
  obtain ⟨Γ, hΓ, hΓi, hΓemb, hΓjets⟩ :=
    exists_generic_loopFamily_approximation_of_smoothOn_univ hdim e γext hab hext hiexact n hε
  refine ⟨Γ, hΓ, hΓi, hΓemb, ?_⟩
  have hagree : _root_.Set.EqOn
      (fun q : ℝ × ℝ => e.map (γext q.2 (q.1 : Surgery.Topology.Circle)))
      (fun q : ℝ × ℝ => e.map (γ q.2 (q.1 : Surgery.Topology.Circle))) (_root_.Set.univ ×ˢ _root_.Set.Icc a b) := by
    intro q hq
    change e.map (γext q.2 (q.1 : Surgery.Topology.Circle)) =
      e.map (γ q.2 (q.1 : Surgery.Topology.Circle))
    rw [heq q.2 hq.2]
  intro m hm p hp
  have h := hΓjets m hm p hp
  rw [iteratedFDerivWithin_congr hagree ⟨mem_univ _, hp.2⟩ m] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.exists_generic_loopFamily_approximation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.exists_generic_loopFamily_approximation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.exists_generic_loopFamily_approximation ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.exists_generic_loopFamily_approximation

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end

noncomputable section

open _root_.Set _root_.Filter _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Topology _root_.Submission.Topology _root_.ContDiff _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M]

theorem exists_generic_loopFamily_approximation_sequence
    (hdim : Module.finrank ℝ E = 3) {N : ℕ}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    {D : RealTimeInterval} (g : ℝ → SmoothRiemannianMetric I M)
    (hg : MetricFamilySmoothOn D g) {a b : ℝ} (hab : a < b) (hreg : _root_.Set.Icc a b ⊆ D.regular)
    (γ : ℝ → ContinuousFreeLoop M)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (_root_.Set.Icc a b))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := I) (_root_.Set.Icc a b)) :
    ∃ approximants : ℕ → ℝ → ContinuousFreeLoop M,
      (∀ j, (curveOfLoopFamily (approximants j)).SmoothOn (I := I) (_root_.Set.Icc a b) ∧
        (curveOfLoopFamily (approximants j)).ImmersedOn (I := I) (_root_.Set.Icc a b) ∧
        ∃ exceptional : Finset ℝ, ∀ t ∈ _root_.Set.Icc a b,
          t ∉ exceptional → Topology.IsEmbedding (approximants j t)) ∧
      (∀ ε > 0, ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ m : ℕ, m ≤ 2 →
        ∀ p ∈ _root_.Set.Icc (0 : ℝ) 1 ×ˢ _root_.Set.Icc a b,
          ‖iteratedFDerivWithin ℝ m
              (fun q : ℝ × ℝ => e.map (approximants j q.2 (q.1 : Surgery.Topology.Circle)))
              (_root_.Set.univ ×ˢ _root_.Set.Icc a b) p -
            iteratedFDerivWithin ℝ m
              (fun q : ℝ × ℝ => e.map (γ q.2 (q.1 : Surgery.Topology.Circle)))
              (_root_.Set.univ ×ˢ _root_.Set.Icc a b) p‖ < ε) ∧
      (∀ ε > 0, ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ t ∈ _root_.Set.Icc a b,
        |(curveOfLoopFamily (approximants j)).areaError g (_root_.Set.Icc a b) t -
          (curveOfLoopFamily γ).areaError g (_root_.Set.Icc a b) t| < ε) ∧
      ((∀ t ∈ _root_.Set.Icc a b, IsContractibleLoop (γ t)) →
        (∀ j t, t ∈ _root_.Set.Icc a b → IsContractibleLoop (approximants j t)) ∧
        ∀ ε > 0, ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ t ∈ _root_.Set.Icc a b,
          |loopFamilyLeastArea g (approximants j) t - loopFamilyLeastArea g γ t| < ε) := by
  let _ : Nonempty M := ⟨γ a 0⟩
  let _ : NeZero (Module.finrank ℝ E) := ⟨by rw [hdim]; norm_num⟩
  obtain ⟨r, U, hU, heU, hr, hleft⟩ :=
    DifferentialGeometry.Geometry.exists_smooth_neighborhood_retraction
      e.smooth e.isClosedEmbedding.isEmbedding e.injective_mfderiv
  let R : Width.SmoothTubularRetraction e := ⟨U, hU, heU, r, hr, hleft⟩
  obtain ⟨δ, hδ, hctr⟩ :=
    exists_pos_forall_loopFamily_isContractibleLoop_of_iteratedFDerivWithin_zero
      (g a) e.map e.isClosedEmbedding.isEmbedding
  have hsize (j : ℕ) : 0 < _root_.Min.min δ (1 / ((j : ℝ) + 1)) :=
    lt_min hδ (by positivity)
  choose app hsmooth himm hemb hbound using fun j : ℕ =>
    exists_generic_loopFamily_approximation hdim e R γ hab hγ hi 2 (hsize j)
  have hs (j : ℕ) : (curveOfLoopFamily (app j)).SmoothOn (I := I) (_root_.Set.Icc a b) :=
    (hsmooth j).mono (_root_.Set.prod_mono subset_rfl (_root_.Set.subset_univ _))
  have hconv : ∀ ε > 0, ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ m : ℕ, m ≤ 2 →
      ∀ p ∈ _root_.Set.Icc (0 : ℝ) 1 ×ˢ _root_.Set.Icc a b,
        ‖iteratedFDerivWithin ℝ m
            (fun q : ℝ × ℝ => e.map (app j q.2 (q.1 : Surgery.Topology.Circle)))
            (_root_.Set.univ ×ˢ _root_.Set.Icc a b) p -
          iteratedFDerivWithin ℝ m
            (fun q : ℝ × ℝ => e.map (γ q.2 (q.1 : Surgery.Topology.Circle)))
            (_root_.Set.univ ×ˢ _root_.Set.Icc a b) p‖ < ε := by
    intro ε hε
    have hsmall : ∀ᶠ j : ℕ in _root_.Filter.atTop, 1 / ((j : ℝ) + 1) < ε :=
      tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds hε)
    obtain ⟨j₀, hj₀⟩ := eventually_atTop.mp hsmall
    exact ⟨j₀, fun j hj m hm p hp =>
      (hbound j m hm p hp).trans ((min_le_right _ _).trans_lt (hj₀ j hj))⟩
  have hjet : ∀ m ≤ 2, TendstoUniformlyOn
      (fun j p => iteratedFDerivWithin ℝ m
        (fun q : ℝ × ℝ => e.map ((curveOfLoopFamily (app j)).lift q.1 q.2))
        (_root_.Set.univ ×ˢ _root_.Set.Icc a b) p)
      (fun p => iteratedFDerivWithin ℝ m
        (fun q : ℝ × ℝ => e.map ((curveOfLoopFamily γ).lift q.1 q.2))
        (_root_.Set.univ ×ˢ _root_.Set.Icc a b) p) _root_.Filter.atTop (_root_.Set.Icc (0 : ℝ) 1 ×ˢ _root_.Set.Icc a b) := by
    intro m hm
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨j₀, hj₀⟩ := hconv ε hε
    filter_upwards [_root_.Filter.eventually_ge_atTop j₀] with j hj p hp
    rw [dist_eq_norm, norm_sub_rev]
    exact hj₀ j hj m hm p hp
  have harea := CurveMap.tendstoUniformlyOn_areaError_of_embedding_iteratedFDerivWithin
    hg hab hreg e.smooth e.isClosedEmbedding.isEmbedding e.injective_mfderiv
    (fun j => curveOfLoopFamily (app j)) (curveOfLoopFamily γ) hs himm hγ hi hjet
  refine ⟨app, fun j => ⟨hs j, himm j, hemb j⟩, hconv, ?_, ?_⟩
  · intro ε hε
    have h := Metric.tendstoUniformlyOn_iff.mp harea ε hε
    obtain ⟨j₀, hj₀⟩ := eventually_atTop.mp h
    refine ⟨j₀, fun j hj t ht => ?_⟩
    simpa only [Real.dist_eq, abs_sub_comm] using hj₀ j hj t ht
  · intro hγctr
    have happctr : ∀ j t, t ∈ _root_.Set.Icc a b → IsContractibleLoop (app j t) := fun j =>
      hctr γ (app j) (_root_.Set.Icc a b) hγctr (fun p hp =>
        (hbound j 0 (by norm_num) p hp).trans_le (min_le_left _ _))
    refine ⟨happctr, ?_⟩
    exact uniform_loopFamilyLeastArea_of_uniform_c1 D g hg hab (hreg.trans D.regular_subset)
      e γ app hγ hs hγctr happctr (fun ε hε => by
        obtain ⟨j₀, hj₀⟩ := hconv ε hε
        exact ⟨j₀, fun j hj m hm p hp => hj₀ j hj m (hm.trans (by norm_num)) p hp⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.exists_generic_loopFamily_approximation_sequence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.exists_generic_loopFamily_approximation_sequence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.exists_generic_loopFamily_approximation_sequence ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.exists_generic_loopFamily_approximation_sequence

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end
