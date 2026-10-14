import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ClosedGluing
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardInitialExistence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.E3 target :: scope.openDecls } }

theorem PartialStandardSolution.exists_strict_extension_of_closed_restart
    (S : PartialStandardSolution)
    (T τ : ℝ) (hT : 0 < T) (hτ : 0 < τ)
    (hlifetime : S.lifetime = ENNReal.ofReal T)
    (G H : ℝ → SmoothRiemannianMetric (𝓡 3) E3)
    (hagree : ∀ t ∈ _root_.Set.Ico 0 T, G t = S.metric t)
    (hGinitial : G 0 = DifferentialGeometry.PDE.RicciFlow.StandardCap.metric)
    (hGcomplete : ∀ t ∈ _root_.Set.Icc 0 T, RiemannianMetricComplete (G t))
    (hGjets :
      ∀ (r : ℕ) (x₀ : E3) (i j : Fin (Module.finrank ℝ E3)),
        ContinuousOn
          (fun p : ℝ × E3 =>
            iteratedFDeriv ℝ r (chartGramOnE (G p.1) x₀ i j) p.2)
          (_root_.Set.Icc 0 T ×ˢ interior (extChartAt (𝓡 3) x₀).target))
    (hGright :
      ∀ t ∈ _root_.Set.Ico 0 T, ∀ (x : E3) (v w : TangentSpace (𝓡 3) x),
        HasDerivWithinAt (fun s => (G s).inner x v w)
          (-2 * ricciTensor (G t) x v w) (_root_.Set.Ici 0) t)
    (hGend :
      ∀ (x : E3) (v w : TangentSpace (𝓡 3) x),
        HasDerivWithinAt (fun s => (G s).inner x v w)
          (-2 * ricciTensor (G T) x v w) (_root_.Set.Icc 0 T) T)
    (hHzero : H 0 = G T)
    (hHcomplete : ∀ t ∈ _root_.Set.Icc 0 τ, RiemannianMetricComplete (H t))
    (hHjets :
      ∀ (r : ℕ) (x₀ : E3) (i j : Fin (Module.finrank ℝ E3)),
        ContinuousOn
          (fun p : ℝ × E3 =>
            iteratedFDeriv ℝ r (chartGramOnE (H p.1) x₀ i j) p.2)
          (_root_.Set.Icc 0 τ ×ˢ interior (extChartAt (𝓡 3) x₀).target))
    (hHinterior :
      ∀ t ∈ _root_.Set.Ioo 0 τ, ∀ (x : E3) (v w : TangentSpace (𝓡 3) x),
        HasDerivAt (fun s => (H s).inner x v w)
          (-2 * ricciTensor (H t) x v w) t)
    (KG KH : ℝ)
    (hKG :
      ∀ t ∈ _root_.Set.Ico 0 T, ∀ x : E3,
        Real.sqrt (normSq0S (S.metric t) x 4
          (metricRm04 (S.metric t) x)) ≤ KG)
    (hKH :
      ∀ t ∈ _root_.Set.Icc 0 τ, ∀ x : E3,
        Real.sqrt (normSq0S (H t) x 4
          (metricRm04 (H t) x)) ≤ KH) :
    ∃ Q : PartialStandardSolution,
      Q.lifetime = ENNReal.ofReal (T + τ) ∧
      Q.metric = gluedFamily G H T ∧
      S.IsExtendedBy Q ∧
      S.lifetime < Q.lifetime ∧
      (∀ t ∈ _root_.Set.Icc 0 (T + τ),
        RiemannianMetricComplete (Q.metric t)) ∧
      ∀ t ∈ _root_.Set.Icc 0 (T + τ), ∀ x : E3,
        Real.sqrt (normSq0S (Q.metric t) x 4
          (metricRm04 (Q.metric t) x)) ≤ _root_.Max.max 0 (_root_.Max.max KG KH) := by
  let F := gluedFamily G H T
  have hsum : 0 < T + τ := add_pos hT hτ
  have hregular := gluedFamily_closed_regularity
    G H T τ hT hτ hHzero hGjets hHjets hGright hGend hHinterior
  have hCartesian := cartesian_contDiffOn_of_chartGram
    F (_root_.Set.Icc 0 (T + τ)) hregular.2.1
  have hleftSlice (t : ℝ) (ht : t < T) : F t = G t :=
    gluedFamily_of_lt G H T ht
  have hrightSlice (t : ℝ) (ht : T ≤ t) : F t = H (t - T) :=
    gluedFamily_of_ge G H T ht
  have hFzero : F 0 = DifferentialGeometry.PDE.RicciFlow.StandardCap.metric :=
    (hleftSlice 0 hT).trans hGinitial
  have hFcomplete :
      ∀ t ∈ _root_.Set.Icc 0 (T + τ), RiemannianMetricComplete (F t) := by
    intro t ht
    by_cases hlt : t < T
    · rw [hleftSlice t hlt]
      exact hGcomplete t ⟨ht.1, hlt.le⟩
    · have hge : T ≤ t := le_of_not_gt hlt
      rw [hrightSlice t hge]
      exact hHcomplete (t - T)
        ⟨sub_nonneg.mpr hge, by linarith [ht.2]⟩
  let K : ℝ := _root_.Max.max 0 (_root_.Max.max KG KH)
  have hK : 0 ≤ K := le_max_left _ _
  have hKGK : KG ≤ K :=
    (le_max_left KG KH).trans (le_max_right 0 (_root_.Max.max KG KH))
  have hKHK : KH ≤ K :=
    (le_max_right KG KH).trans (le_max_right 0 (_root_.Max.max KG KH))
  have hFcurvature :
      ∀ t ∈ _root_.Set.Icc 0 (T + τ), ∀ x : E3,
        Real.sqrt (normSq0S (F t) x 4
          (metricRm04 (F t) x)) ≤ K := by
    intro t ht x
    by_cases hlt : t < T
    · rw [hleftSlice t hlt, hagree t ⟨ht.1, hlt⟩]
      exact (hKG t ⟨ht.1, hlt⟩ x).trans hKGK
    · have hge : T ≤ t := le_of_not_gt hlt
      rw [hrightSlice t hge]
      exact (hKH (t - T)
        ⟨sub_nonneg.mpr hge, by linarith [ht.2]⟩ x).trans hKHK
  have hdomain :
      (lifetimeInterval (ENNReal.ofReal (T + τ))
        (ENNReal.ofReal_pos.mpr hsum)).carrier = _root_.Set.Ico 0 (T + τ) := by
    rw [lifetimeInterval_ofReal (T + τ) hsum]
    rfl
  let Q : PartialStandardSolution :=
    { lifetime := ENNReal.ofReal (T + τ)
      lifetime_pos := ENNReal.ofReal_pos.mpr hsum
      metric := F
      smooth := by
        rw [hdomain]
        exact hCartesian.mono (_root_.Set.prod_mono _root_.Set.Ico_subset_Icc_self subset_rfl)
      equation := by
        rw [hdomain]
        exact hregular.2.2.2
      initial := hFzero
      complete := by
        rw [hdomain]
        exact fun t ht => hFcomplete t (_root_.Set.Ico_subset_Icc_self ht)
      curvature_bound := by
        intro θ _ hθlifetime
        have hθ : θ < T + τ :=
          (ENNReal.ofReal_lt_ofReal_iff hsum).mp hθlifetime
        exact ⟨K, hK, fun t ht x =>
          hFcurvature t ⟨ht.1, ht.2.trans hθ.le⟩ x⟩ }
  have hstrict : S.lifetime < Q.lifetime := by
    change S.lifetime < ENNReal.ofReal (T + τ)
    rw [hlifetime]
    exact (ENNReal.ofReal_lt_ofReal_iff hsum).mpr (by linarith)
  have hextends : S.IsExtendedBy Q := by
    refine ⟨hstrict.le, ?_⟩
    intro t ht
    have htdomain :=
      (mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos t).mp ht
    rw [hlifetime] at htdomain
    have htT : t < T :=
      (ENNReal.ofReal_lt_ofReal_iff hT).mp htdomain.2
    change F t = S.metric t
    exact (hleftSlice t htT).trans (hagree t ⟨htdomain.1, htT⟩)
  exact ⟨Q, rfl, rfl, hextends, hstrict, hFcomplete, hFcurvature⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.exists_strict_extension_of_closed_restart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.exists_strict_extension_of_closed_restart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.exists_strict_extension_of_closed_restart ``Submission.DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.exists_strict_extension_of_closed_restart

end DifferentialGeometry.PDE.RicciFlow
