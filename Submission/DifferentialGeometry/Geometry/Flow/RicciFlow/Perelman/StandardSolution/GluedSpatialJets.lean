import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extension.Limit.Smooth
import Submission.DifferentialGeometry.Geometry.Operator.Hessian.Basic
import Mathlib.Topology.ContinuousOn

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem gluedFamily_spatial_gram_jets
    (G H : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) E)
    (T τ : ℝ) (hT : 0 < T) (hτ : 0 < τ)
    (hzero : H 0 = G T)
    (hG : ∀ (r : ℕ) (x₀ : E) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun p : ℝ × E =>
          iteratedFDeriv ℝ r (chartGramOnE (G p.1) x₀ i j) p.2)
        (_root_.Set.Icc 0 T ×ˢ interior (extChartAt 𝓘(ℝ, E) x₀).target))
    (hH : ∀ (r : ℕ) (x₀ : E) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun p : ℝ × E =>
          iteratedFDeriv ℝ r (chartGramOnE (H p.1) x₀ i j) p.2)
        (_root_.Set.Icc 0 τ ×ˢ interior (extChartAt 𝓘(ℝ, E) x₀).target)) :
    ∀ (r : ℕ) (x₀ : E) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun p : ℝ × E =>
          iteratedFDeriv ℝ r
            (chartGramOnE (gluedFamily G H T p.1) x₀ i j) p.2)
        (_root_.Set.Icc 0 (T + τ) ×ˢ
          interior (extChartAt 𝓘(ℝ, E) x₀).target) := by
  intro r x₀ i j
  have htarget :
      interior (extChartAt 𝓘(ℝ, E) x₀).target = (_root_.Set.univ : Set E) := by
    simp only [extChartAt_model_space_eq_id,
      PartialEquiv.refl_target, interior_univ]
  rw [htarget]
  have hGc := hG r x₀ i j
  have hHc := hH r x₀ i j
  rw [htarget] at hGc hHc
  let f : ℝ × E → E [×r]→L[ℝ] ℝ := fun p =>
    iteratedFDeriv ℝ r
      (chartGramOnE (gluedFamily G H T p.1) x₀ i j) p.2
  change ContinuousOn f (_root_.Set.Icc 0 (T + τ) ×ˢ (_root_.Set.univ : Set E))
  have hleftSlice (t : ℝ) (ht : t ∈ _root_.Set.Icc 0 T) :
      gluedFamily G H T t = G t := by
    rcases lt_or_eq_of_le ht.2 with hlt | heq
    · exact gluedFamily_of_lt G H T hlt
    · rw [heq, gluedFamily_at_endpoint, hzero]
  have hleft : ContinuousOn f (_root_.Set.Icc 0 T ×ˢ (_root_.Set.univ : Set E)) := by
    apply hGc.congr
    intro p hp
    dsimp only [f]
    rw [hleftSlice p.1 hp.1]
  have hshift : Continuous (fun p : ℝ × E => (p.1 - T, p.2)) :=
    (continuous_fst.sub continuous_const).prodMk continuous_snd
  have hmaps :
      _root_.Set.MapsTo (fun p : ℝ × E => (p.1 - T, p.2))
        (_root_.Set.Icc T (T + τ) ×ˢ (_root_.Set.univ : Set E))
        (_root_.Set.Icc 0 τ ×ˢ (_root_.Set.univ : Set E)) := by
    intro p hp
    refine ⟨⟨sub_nonneg.mpr hp.1.1, ?_⟩, _root_.Set.mem_univ _⟩
    linarith [hp.1.2]
  have hrightTranslated := hHc.comp hshift.continuousOn hmaps
  have hright :
      ContinuousOn f (_root_.Set.Icc T (T + τ) ×ˢ (_root_.Set.univ : Set E)) := by
    apply hrightTranslated.congr
    intro p hp
    change
      iteratedFDeriv ℝ r
          (chartGramOnE (gluedFamily G H T p.1) x₀ i j) p.2 =
        iteratedFDeriv ℝ r
          (chartGramOnE (H (p.1 - T)) x₀ i j) p.2
    rw [gluedFamily_of_ge G H T hp.1.1]
  have hunion := hleft.union_of_isClosed hright
    (isClosed_Icc.prod isClosed_univ)
    (isClosed_Icc.prod isClosed_univ)
  rw [← _root_.Set.union_prod,
    _root_.Set.Icc_union_Icc_eq_Icc hT.le
      (le_add_of_nonneg_right hτ.le)] at hunion
  exact hunion

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.gluedFamily_spatial_gram_jets then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.gluedFamily_spatial_gram_jets"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.gluedFamily_spatial_gram_jets ``Submission.DifferentialGeometry.PDE.RicciFlow.gluedFamily_spatial_gram_jets

end DifferentialGeometry.PDE.RicciFlow
