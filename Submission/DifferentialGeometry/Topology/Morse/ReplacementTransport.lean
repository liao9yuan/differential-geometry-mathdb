import Submission.DifferentialGeometry.Topology.Morse.EmbeddingNaturality
import Submission.DifferentialGeometry.Topology.Morse.Naturality
import Submission.DifferentialGeometry.Topology.Morse.ConstantGerm

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Filter
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Topology

namespace DifferentialGeometry.Topology.Morse

variable {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H H' : Type} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
  {M N : Type} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace H' N]
  {e f : M → N} {h : N → ℝ} {D : Set M}

theorem criticalPoints_comp_diffeomorph_replacement_eq
    [IsManifold J ∞ N]
    (he : Manifold.IsSmoothEmbedding I J ∞ e) (Φ : Diffeomorph J J N N ∞)
    (hD : IsClosed D) (hfix : _root_.Set.EqOn f e Dᶜ)
    (himage : Φ '' _root_.Set.range e = _root_.Set.range e)
    (hΦfix : ∀ x, IsCriticalPointAt I (h ∘ e) x → Φ (e x) = e x)
    (hshift : ∀ x ∈ D, ∃ a : ℝ,
      (h ∘ Φ ∘ f) =ᶠ[𝓝 x] (fun y => h (f y) + a)) :
    criticalPoints I (h ∘ Φ ∘ f) = criticalPoints I (h ∘ f) := by
  have hcrit := criticalPoints_comp_diffeomorph_comp_eq_of_fixed he Φ (by simp) h
    himage hΦfix
  ext x
  change IsCriticalPointAt I (h ∘ Φ ∘ f) x ↔ IsCriticalPointAt I (h ∘ f) x
  by_cases hx : x ∈ D
  · obtain ⟨a, ha⟩ := hshift x hx
    exact (isCriticalPointAt_congr_of_eventuallyEq ha).trans
      (isCriticalPointAt_add_const_iff (h ∘ f) a x)
  · have heq : f =ᶠ[𝓝 x] e :=
      Filter.eventuallyEq_of_mem (hD.isOpen_compl.mem_nhds hx) hfix
    have hcritx : IsCriticalPointAt I (h ∘ Φ ∘ e) x ↔
        IsCriticalPointAt I (h ∘ e) x := Set.ext_iff.mp hcrit x
    exact (isCriticalPointAt_congr_of_eventuallyEq (heq.fun_comp (h ∘ Φ))).trans
      (hcritx.trans (isCriticalPointAt_congr_of_eventuallyEq (heq.fun_comp h)).symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Morse.criticalPoints_comp_diffeomorph_replacement_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Morse.criticalPoints_comp_diffeomorph_replacement_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Morse.criticalPoints_comp_diffeomorph_replacement_eq ``Submission.DifferentialGeometry.Topology.Morse.criticalPoints_comp_diffeomorph_replacement_eq

theorem exists_eventuallyEq_add_const_comp_diffeomorph_replacement
    (Φ : Diffeomorph J J N N ∞) (hD : IsClosed D) (hfix : _root_.Set.EqOn f e Dᶜ)
    (hΦnear : ∀ x, IsCriticalPointAt I (h ∘ e) x → (Φ ∘ e) =ᶠ[𝓝 x] e)
    (hshift : ∀ x ∈ D, ∃ a : ℝ,
      (h ∘ Φ ∘ f) =ᶠ[𝓝 x] (fun y => h (f y) + a))
    {x : M} (hx : IsCriticalPointAt I (h ∘ f) x) :
    ∃ a : ℝ, (h ∘ Φ ∘ f) =ᶠ[𝓝 x] (fun y => h (f y) + a) := by
  by_cases hxD : x ∈ D
  · exact hshift x hxD
  · have heq : f =ᶠ[𝓝 x] e :=
      Filter.eventuallyEq_of_mem (hD.isOpen_compl.mem_nhds hxD) hfix
    have hc := (isCriticalPointAt_congr_of_eventuallyEq (heq.fun_comp h)).mp hx
    refine ⟨0, ?_⟩
    have hh := (heq.fun_comp (h ∘ Φ)).trans
      (((hΦnear x hc).fun_comp h).trans (heq.fun_comp h).symm)
    simpa only [add_zero, Function.comp_def] using hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Morse.exists_eventuallyEq_add_const_comp_diffeomorph_replacement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Morse.exists_eventuallyEq_add_const_comp_diffeomorph_replacement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Morse.exists_eventuallyEq_add_const_comp_diffeomorph_replacement ``Submission.DifferentialGeometry.Topology.Morse.exists_eventuallyEq_add_const_comp_diffeomorph_replacement

theorem chartHessianAt_comp_diffeomorph_replacement_eq
    [I.Boundaryless] [IsManifold I ∞ M]
    (Φ : Diffeomorph J J N N ∞) (hD : IsClosed D) (hfix : _root_.Set.EqOn f e Dᶜ)
    (hΦnear : ∀ x, IsCriticalPointAt I (h ∘ e) x → (Φ ∘ e) =ᶠ[𝓝 x] e)
    (hshift : ∀ x ∈ D, ∃ a : ℝ,
      (h ∘ Φ ∘ f) =ᶠ[𝓝 x] (fun y => h (f y) + a))
    {x : M} (hx : IsCriticalPointAt I (h ∘ f) x) :
    chartHessianAt (fun y => h (Φ (f ((extChartAt I x).symm y)))) (extChartAt I x x) =
      chartHessianAt (fun y => h (f ((extChartAt I x).symm y))) (extChartAt I x x) := by
  obtain ⟨a, ha⟩ := exists_eventuallyEq_add_const_comp_diffeomorph_replacement
    Φ hD hfix hΦnear hshift hx
  exact DifferentialGeometry.Morse.chartHessianAt_eq_of_eventuallyEq_add_const
    (I := I) BoundarylessManifold.isInteriorPoint ha

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Morse.chartHessianAt_comp_diffeomorph_replacement_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Morse.chartHessianAt_comp_diffeomorph_replacement_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Morse.chartHessianAt_comp_diffeomorph_replacement_eq ``Submission.DifferentialGeometry.Topology.Morse.chartHessianAt_comp_diffeomorph_replacement_eq

end DifferentialGeometry.Topology.Morse
