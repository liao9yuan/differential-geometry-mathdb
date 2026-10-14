import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Seam

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Submission.DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private theorem exists_finite_gluing_metric (n : ℕ)
    (time : Fin (n + 2) → ℝ) (htime : StrictMono time)
    (g : Fin (n + 1) → ℝ → SmoothRiemannianMetric I M)
    (hsmooth : ∀ i, ContMDiffOn (𝓘(ℝ, ℝ).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q : ℝ × M => (⟨q.2, (g i q.1).inner q.2⟩ :
        _root_.Bundle.TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (_root_.Set.Icc (time i.castSucc) (time i.succ) ×ˢ (_root_.Set.univ : Set M)))
    (hpde : ∀ i, ∀ t ∈ _root_.Set.Ioo (time i.castSucc) (time i.succ),
      ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivAt (fun s => (g i s).inner x v w)
        (-2 * ricciTensor (I := I) (g i t) x v w) t)
    (hmatch : ∀ i : Fin n, g i.castSucc (time i.succ.castSucc) =
      g i.succ (time i.succ.castSucc)) :
    ∃ G : ℝ → SmoothRiemannianMetric I M,
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (fun q : ℝ × M => (⟨q.2, (G q.1).inner q.2⟩ :
          _root_.Bundle.TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
            (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
        (_root_.Set.Icc (time 0) (time (Fin.last (n + 1))) ×ˢ (_root_.Set.univ : Set M)) ∧
      (∀ t ∈ _root_.Set.Ioo (time 0) (time (Fin.last (n + 1))),
        ∀ x : M, ∀ v w : TangentSpace I x,
        HasDerivAt (fun s => (G s).inner x v w)
          (-2 * ricciTensor (I := I) (G t) x v w) t) ∧
      ∀ i, ∀ t ∈ _root_.Set.Icc (time i.castSucc) (time i.succ), G t = g i t := by
  induction n with
  | zero =>
    refine ⟨g 0, ?_, ?_, ?_⟩
    · simpa using hsmooth 0
    · simpa using hpde 0
    · intro i t ht
      have hi : i = 0 := by apply Fin.ext; simp
      rw [hi]
  | succ n ih =>
    let time' : Fin (n + 2) → ℝ := fun i => time i.castSucc
    let g' : Fin (n + 1) → ℝ → SmoothRiemannianMetric I M := fun i => g i.castSucc
    have htime' : StrictMono time' := htime.comp Fin.strictMono_castSucc
    have hsmooth' : ∀ i, ContMDiffOn (𝓘(ℝ, ℝ).prod I)
        (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (fun q : ℝ × M => (⟨q.2, (g' i q.1).inner q.2⟩ :
          _root_.Bundle.TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
            (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
        (_root_.Set.Icc (time' i.castSucc) (time' i.succ) ×ˢ (_root_.Set.univ : Set M)) := by
      intro i
      exact hsmooth i.castSucc
    have hpde' : ∀ i, ∀ t ∈ _root_.Set.Ioo (time' i.castSucc) (time' i.succ),
        ∀ x : M, ∀ v w : TangentSpace I x,
        HasDerivAt (fun s => (g' i s).inner x v w)
          (-2 * ricciTensor (I := I) (g' i t) x v w) t := by
      intro i
      exact hpde i.castSucc
    have hmatch' : ∀ i : Fin n, g' i.castSucc (time' i.succ.castSucc) =
        g' i.succ (time' i.succ.castSucc) := by
      intro i
      exact hmatch i.castSucc
    obtain ⟨G, hG, hGpde, hGeq⟩ := ih time' htime' g' hsmooth' hpde' hmatch'
    let c := time (Fin.last (n + 1)).castSucc
    let R := g (Fin.last (n + 1))
    have ha : time 0 < c := htime (by change (0 : ℕ) < n + 1; omega)
    have hb : c < time (Fin.last (n + 2)) := htime (Fin.castSucc_lt_last _)
    have hGc : G c = R c := by
      have heq := hGeq (Fin.last n) c
        ⟨htime'.monotone (by apply Fin.le_iff_val_le_val.mpr; simp), le_rfl⟩
      exact heq.trans (hmatch (Fin.last n))
    refine ⟨fun t => if t ≤ c then G t else R t, ?_, ?_, ?_⟩
    · exact metricCLMSection_jointContMDiffOn_ite_of_ricciFlow G R ha hb
        hG (hsmooth (Fin.last (n + 1))) hGpde (hpde (Fin.last (n + 1))) hGc
    · intro t ht
      exact metric_inner_hasDerivAt_ite_of_ricciFlow G R ha hb
        hG (hsmooth (Fin.last (n + 1))) hGpde (hpde (Fin.last (n + 1))) hGc ht
    · intro i t
      refine Fin.lastCases ?_ (fun j => ?_) i
      · intro ht
        dsimp only
        by_cases htc : t ≤ c
        · have htc' : t = c := le_antisymm htc ht.1
          subst t
          rw [if_pos le_rfl]
          exact hGc
        · rw [if_neg htc]
      · intro ht
        dsimp only
        have htc : t ≤ c := ht.2.trans (htime.monotone (by change j.val + 1 ≤ n + 1; omega))
        rw [if_pos htc]
        exact hGeq j t ht

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.exists_finite_gluing_metric
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.exists_finite_gluing_metric target :: scope.openDecls } }

theorem exists_isSolutionOn_finite_gluing (n : ℕ)
    (time : Fin (n + 2) → ℝ) (htime : StrictMono time)
    (g : Fin (n + 1) → ℝ → SmoothRiemannianMetric I M)
    (hsmooth : ∀ i, ContMDiffOn (𝓘(ℝ, ℝ).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q : ℝ × M => (⟨q.2, (g i q.1).inner q.2⟩ :
        _root_.Bundle.TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (_root_.Set.Icc (time i.castSucc) (time i.succ) ×ˢ (_root_.Set.univ : Set M)))
    (hpde : ∀ i, ∀ t ∈ _root_.Set.Ioo (time i.castSucc) (time i.succ),
      ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivAt (fun s => (g i s).inner x v w)
        (-2 * ricciTensor (I := I) (g i t) x v w) t)
    (hmatch : ∀ i : Fin n, g i.castSucc (time i.succ.castSucc) =
      g i.succ (time i.succ.castSucc)) :
    ∃ G : ℝ → SmoothRiemannianMetric I M,
      (∀ i, ∀ t ∈ _root_.Set.Icc (time i.castSucc) (time i.succ), G t = g i t) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (fun q : ℝ × M => (⟨q.2, (G q.1).inner q.2⟩ :
          _root_.Bundle.TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
            (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
        (_root_.Set.Icc (time 0) (time (Fin.last (n + 1))) ×ˢ (_root_.Set.univ : Set M)) ∧
      IsSolutionOn ({ base := { metric := G } } :
        SolutionOn (I := I) (M := M)
          (RealTimeInterval.closed (time 0) (time (Fin.last (n + 1)))
            (htime.monotone (by simp)))) := by
  obtain ⟨G, hG, hGpde, hGeq⟩ :=
    exists_finite_gluing_metric n time htime g hsmooth hpde hmatch
  refine ⟨G, hGeq, hG, ?_⟩
  have hab : time 0 < time (Fin.last (n + 1)) :=
    htime (by change (0 : ℕ) < n + 1; omega)
  apply isSolutionOn_of_joint_metric _ (uniqueDiffOn_Icc hab) G hG
  intro t ht x v w
  exact (hGpde t ht x v w).hasDerivWithinAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.exists_isSolutionOn_finite_gluing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.exists_isSolutionOn_finite_gluing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.exists_isSolutionOn_finite_gluing ``Submission.DifferentialGeometry.PDE.RicciFlow.exists_isSolutionOn_finite_gluing

end DifferentialGeometry.PDE.RicciFlow
