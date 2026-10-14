import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.LoopFamilyContinuity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.ClassWidth
import Mathlib.Topology.Sequences

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [IsManifold I ∞ M] in
private theorem deriv_embeddedLoopFamily_eq_fderivWithin {N : ℕ}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (γ : ℝ → ContinuousFreeLoop M) {J : Set ℝ}
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) J)
    (x t : ℝ) (ht : t ∈ J) :
    deriv (fun s : ℝ => e.map (γ t (s : Surgery.Topology.Circle))) x =
      fderivWithin ℝ (fun p : ℝ × ℝ => e.map (γ p.2 (p.1 : Surgery.Topology.Circle)))
        (_root_.Set.univ ×ˢ J) (x, t) (1, 0) := by
  have hG : ContDiffOn ℝ ∞
      (fun p : ℝ × ℝ => e.map (γ p.2 (p.1 : Surgery.Topology.Circle))) (_root_.Set.univ ×ˢ J) :=
    contMDiffOn_iff_contDiffOn.mp
      ((e.smooth.contMDiffOn (s := _root_.Set.univ)).comp hγ fun p _ => _root_.Set.mem_univ _)
  have hd := ((hG.contDiffWithinAt (x := (x, t)) ⟨mem_univ x, ht⟩).differentiableWithinAt
    (by simp)).hasFDerivWithinAt
  have hι : HasDerivWithinAt (fun s : ℝ => (s, t)) (1, 0) _root_.Set.univ x :=
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) x t).hasDerivAt.hasDerivWithinAt
  exact (hd.comp_hasDerivWithinAt (t := (_root_.Set.univ : Set ℝ) ×ˢ J) x hι
    (fun s (_ : s ∈ (_root_.Set.univ : Set ℝ)) => ⟨mem_univ _, ht⟩)).hasDerivAt _root_.Filter.univ_mem |>.deriv

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.deriv_embeddedLoopFamily_eq_fderivWithin
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.deriv_embeddedLoopFamily_eq_fderivWithin target :: scope.openDecls } }

variable [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M]
  [CompactSpace M]

theorem uniform_loopFamilyLeastArea_of_uniform_c1
    (D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval)
    (g : ℝ → SmoothRiemannianMetric I M)
    (hg : DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn D g)
    {a b : ℝ} (hab : a < b) (hreg : _root_.Set.Icc a b ⊆ D.carrier) {N : ℕ}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (γ : ℝ → ContinuousFreeLoop M) (γseq : ℕ → ℝ → ContinuousFreeLoop M)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (_root_.Set.Icc a b))
    (hγseq : ∀ j, (curveOfLoopFamily (γseq j)).SmoothOn (I := I) (_root_.Set.Icc a b))
    (hctr : ∀ t ∈ _root_.Set.Icc a b, IsContractibleLoop (γ t))
    (hctrseq : ∀ j t, t ∈ _root_.Set.Icc a b → IsContractibleLoop (γseq j t))
    (hconv : ∀ ε > 0, ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ m : ℕ, m ≤ 1 →
      ∀ p ∈ _root_.Set.Icc (0 : ℝ) 1 ×ˢ _root_.Set.Icc a b,
        ‖iteratedFDerivWithin ℝ m
            (fun q : ℝ × ℝ => e.map (γseq j q.2 (q.1 : Surgery.Topology.Circle)))
            (_root_.Set.univ ×ˢ _root_.Set.Icc a b) p -
          iteratedFDerivWithin ℝ m
            (fun q : ℝ × ℝ => e.map (γ q.2 (q.1 : Surgery.Topology.Circle)))
            (_root_.Set.univ ×ˢ _root_.Set.Icc a b) p‖ < ε) :
    ∀ ε > 0, ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ t ∈ _root_.Set.Icc a b,
      |loopFamilyLeastArea g (γseq j) t - loopFamilyLeastArea g γ t| < ε := by
  classical
  let _ : Nonempty M := ⟨γ a 0⟩
  obtain ⟨Γ, hΓ, hΓeq⟩ := exists_continuousOn_contractibleRegularLoop_family γ hγ hctr
  choose Γseq hΓseq hΓseqeq using fun j =>
    exists_continuousOn_contractibleRegularLoop_family (γseq j) (hγseq j) (hctrseq j)
  have hjets : ∀ ε > 0, ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ t ∈ _root_.Set.Icc a b,
      _root_.Dist.dist (Width.embeddingFirstJet e (Γseq j t).1)
        (Width.embeddingFirstJet e (Γ t).1) < ε := by
    intro ε hε
    obtain ⟨j₀, hj₀⟩ := hconv ε hε
    refine ⟨j₀, fun j hj t ht => (ContinuousMap.dist_lt_iff hε).mpr ?_⟩
    intro x
    change _root_.Dist.dist
      (e.map ((Γseq j t).1.toContinuousLoop (x.1 : Surgery.Topology.Circle)),
        deriv (e.map ∘ Width.loopLift (Γseq j t).1.toContinuousLoop) x.1)
      (e.map ((Γ t).1.toContinuousLoop (x.1 : Surgery.Topology.Circle)),
        deriv (e.map ∘ Width.loopLift (Γ t).1.toContinuousLoop) x.1) < ε
    rw [hΓseqeq j t ht, hΓeq t ht, Prod.dist_eq, max_lt_iff]
    constructor
    · have hv := hj₀ j hj 0 (by omega) (x.1, t) ⟨x.2, ht⟩
      simpa only [← dist_eq_norm, dist_iteratedFDerivWithin_zero] using hv
    · change _root_.Dist.dist (deriv (fun s : ℝ => e.map (γseq j t (s : Surgery.Topology.Circle))) x.1)
        (deriv (fun s : ℝ => e.map (γ t (s : Surgery.Topology.Circle))) x.1) < ε
      rw [deriv_embeddedLoopFamily_eq_fderivWithin e (γseq j) (hγseq j) x.1 t ht,
        deriv_embeddedLoopFamily_eq_fderivWithin e γ hγ x.1 t ht]
      have hu : UniqueDiffWithinAt ℝ ((_root_.Set.univ : Set ℝ) ×ˢ _root_.Set.Icc a b) (x.1, t) :=
        (uniqueDiffOn_univ.prod (uniqueDiffOn_Icc hab)) (x.1, t) ⟨mem_univ _, ht⟩
      have hd := hj₀ j hj 1 le_rfl (x.1, t) ⟨x.2, ht⟩
      rw [← dist_eq_norm, dist_iteratedFDerivWithin_one _ _ hu hu, dist_eq_norm] at hd
      refine lt_of_le_of_lt ?_ hd
      rw [dist_eq_norm, ← sub_apply]
      simpa using (ContinuousLinearMap.le_opNorm
        (fderivWithin ℝ
          (fun q : ℝ × ℝ => e.map (γseq j q.2 (q.1 : Surgery.Topology.Circle)))
          (_root_.Set.univ ×ˢ _root_.Set.Icc a b) (x.1, t) -
        fderivWithin ℝ
          (fun q : ℝ × ℝ => e.map (γ q.2 (q.1 : Surgery.Topology.Circle)))
          (_root_.Set.univ ×ˢ _root_.Set.Icc a b) (x.1, t)) (1, 0))
  obtain harea := Width.uniform_regularLeastArea_of_uniform_embeddingFirstJet
    D g hg hreg e Γ Γseq hΓ hjets
  intro ε hε
  obtain ⟨j₀, hj₀⟩ := harea ε hε
  refine ⟨j₀, fun j hj t ht => ?_⟩
  simpa only [Width.regularLeastArea, Width.leastArea, hΓseqeq j t ht, hΓeq t ht,
    loopFamilyLeastArea] using hj₀ j hj t ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.uniform_loopFamilyLeastArea_of_uniform_c1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.uniform_loopFamilyLeastArea_of_uniform_c1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.uniform_loopFamilyLeastArea_of_uniform_c1 ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.uniform_loopFamilyLeastArea_of_uniform_c1

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end
