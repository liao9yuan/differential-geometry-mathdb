import Submission.DifferentialGeometry.Analysis.Schauder.Holder.CompactRegularity
import Mathlib.Analysis.Calculus.ContDiff.Comp

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Filter
open scoped _root_.ContDiff _root_.Topology _root_.NNReal

namespace DifferentialGeometry.Analysis.Schauder

private theorem holder_difference_isBigO
    {X Y : Type*} [PseudoMetricSpace X] [NormedAddCommGroup Y]
    {s : Set X} {f : X → Y} {K α : ℝ≥0} (hf : HolderOnWith K α f s) :
    (fun a : s × s => f a.1 - f a.2) =O[⊤]
      (fun a : s × s => _root_.Dist.dist (a.1 : X) (a.2 : X) ^ (α : ℝ)) := by
  apply Asymptotics.IsBigO.of_bound (K : ℝ)
  apply Filter.Eventually.of_forall
  intro a
  simpa only [dist_eq_norm, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (dist_nonneg) _)] using hf.dist_le a.1.property a.2.property

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Schauder.holder_difference_isBigO
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Schauder.holder_difference_isBigO target :: scope.openDecls } }

private theorem exists_holderOnWith_taylorComp
    {X E F G : Type*} [PseudoMetricSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {s : Set X} (hs : IsCompact s) {n : ℕ} {α : ℝ≥0} (hα : 0 < α)
    {p : X → FormalMultilinearSeries ℝ E F} {q : X → FormalMultilinearSeries ℝ F G}
    (hp : ∀ k ≤ n, ∃ K : ℝ≥0, HolderOnWith K α (fun x => p x k) s)
    (hq : ∀ k ≤ n, ∃ K : ℝ≥0, HolderOnWith K α (fun x => q x k) s) :
    ∃ K : ℝ≥0, HolderOnWith K α (fun x => (q x).taylorComp (p x) n) s := by
  have hqp : (fun a : s × s =>
      (q a.1).taylorComp (p a.1) n - (q a.2).taylorComp (p a.2) n) =O[⊤]
      (fun a : s × s => _root_.Dist.dist (a.1 : X) (a.2 : X) ^ (α : ℝ)) := by
    apply FormalMultilinearSeries.taylorComp_sub_taylorComp_isBigO
    · intro k hk
      obtain ⟨K, hK⟩ := hq k hk
      obtain ⟨M, hM⟩ := hs.exists_bound_of_continuousOn (hK.continuousOn hα)
      exact Filter.isBoundedUnder_of_eventually_le
        (Filter.Eventually.of_forall fun a : s × s => hM a.1 a.1.property)
    · intro k hk
      obtain ⟨K, hK⟩ := hq k hk
      exact holder_difference_isBigO hK
    · intro k hk
      obtain ⟨K, hK⟩ := hp k hk
      obtain ⟨M, hM⟩ := hs.exists_bound_of_continuousOn (hK.continuousOn hα)
      exact Filter.isBoundedUnder_of_eventually_le
        (Filter.Eventually.of_forall fun a : s × s => hM a.1 a.1.property)
    · intro k hk
      obtain ⟨K, hK⟩ := hp k hk
      obtain ⟨M, hM⟩ := hs.exists_bound_of_continuousOn (hK.continuousOn hα)
      exact Filter.isBoundedUnder_of_eventually_le
        (Filter.Eventually.of_forall fun a : s × s => hM a.2 a.2.property)
    · intro k hk
      obtain ⟨K, hK⟩ := hp k hk
      exact holder_difference_isBigO hK
  obtain ⟨K, hKpos, hK⟩ := Asymptotics.isBigO_iff'.mp hqp
  let C : ℝ≥0 := ⟨K, hKpos.le⟩
  refine ⟨C, ?_⟩
  intro x hx y hy
  have hb := Filter.eventually_top.mp hK (⟨x, hx⟩, ⟨y, hy⟩)
  have hb' : _root_.Dist.dist ((q x).taylorComp (p x) n) ((q y).taylorComp (p y) n) ≤
      K * _root_.Dist.dist x y ^ (α : ℝ) := by
    simpa only [dist_eq_norm, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (dist_nonneg) _)] using hb
  calc
    _ ≤ ENNReal.ofReal (K * _root_.Dist.dist x y ^ (α : ℝ)) := by
      rw [edist_dist]
      exact ENNReal.ofReal_le_ofReal hb'
    _ = _ := by
      rw [ENNReal.ofReal_mul hKpos.le, edist_dist,
        ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg]
      congr 1
      change ENNReal.ofReal (C : ℝ) = (C : ENNReal)
      exact ENNReal.ofReal_coe_nnreal

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Schauder.exists_holderOnWith_taylorComp
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Schauder.exists_holderOnWith_taylorComp target :: scope.openDecls } }

theorem exists_holderOnWith_iteratedFDerivWithin_comp
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {s : Set E} (hs : IsCompact s) (hsD : UniqueDiffOn ℝ s)
    {u : E → F} {n : ℕ} (hu : ContDiffOn ℝ n u s) {α : ℝ≥0} (hα : 0 < α)
    (hjets : ∀ k ≤ n, ∃ K : ℝ≥0, HolderOnWith K α (iteratedFDerivWithin ℝ k u s) s)
    {U : Set F} (hU : IsOpen U) (huU : _root_.Set.MapsTo u s U)
    {f : F → G} (hf : ContDiffOn ℝ (n + 1) f U) :
    ∃ K : ℝ≥0, HolderOnWith K α (iteratedFDerivWithin ℝ n (f ∘ u) s) s := by
  obtain ⟨K, hK⟩ := hjets 0 (Nat.zero_le n)
  have huH : HolderOnWith K α u s := by
    intro x hx y hy
    simpa only [edist_dist, dist_iteratedFDerivWithin_zero] using hK x hx y hy
  have houter : ∀ k ≤ n, ∃ C : ℝ≥0,
      HolderOnWith C α (fun x => iteratedFDerivWithin ℝ k f U (u x)) s := by
    intro k hk
    have hfJ : ContDiffOn ℝ 1 (iteratedFDerivWithin ℝ k f U) U := by
      intro y hy
      apply (hf y hy).iteratedFDerivWithin_right hU.uniqueDiffOn _ hy
      norm_cast
      omega
    exact exists_holderOnWith_comp_of_contDiffOn_isCompact hs hU huH hα huU hfJ
  obtain ⟨C, hC⟩ := exists_holderOnWith_taylorComp hs hα
    (p := ftaylorSeriesWithin ℝ u s)
    (q := fun x => ftaylorSeriesWithin ℝ f U (u x)) hjets houter
  have heq : _root_.Set.EqOn (iteratedFDerivWithin ℝ n (f ∘ u) s)
      (fun x => (ftaylorSeriesWithin ℝ f U (u x)).taylorComp
        (ftaylorSeriesWithin ℝ u s x) n) s := by
    intro x hx
    exact iteratedFDerivWithin_comp ((hf (u x) (huU hx)).of_le (by simp))
      (hu x hx) hU.uniqueDiffOn hsD hx huU le_rfl
  refine ⟨C, ?_⟩
  intro x hx y hy
  rw [heq hx, heq hy]
  exact hC x hx y hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.exists_holderOnWith_iteratedFDerivWithin_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.exists_holderOnWith_iteratedFDerivWithin_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.exists_holderOnWith_iteratedFDerivWithin_comp ``Submission.DifferentialGeometry.Analysis.Schauder.exists_holderOnWith_iteratedFDerivWithin_comp

theorem exists_holderOnWith_iteratedFDerivWithin_comp_of_convex
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {s : Set E} (hs : IsCompact s) (hsconv : Convex ℝ s) (hsD : UniqueDiffOn ℝ s)
    {u : E → F} {n : ℕ} (hu : ContDiffOn ℝ n u s) {K α : ℝ≥0}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hjet : HolderOnWith K α (iteratedFDerivWithin ℝ n u s) s)
    {U : Set F} (hU : IsOpen U) (huU : _root_.Set.MapsTo u s U)
    {f : F → G} (hf : ContDiffOn ℝ (n + 1) f U) :
    ∃ C : ℝ≥0, HolderOnWith C α (iteratedFDerivWithin ℝ n (f ∘ u) s) s := by
  apply exists_holderOnWith_iteratedFDerivWithin_comp hs hsD hu hα _ hU huU hf
  intro k hk
  by_cases hkn : k = n
  · subst k
    exact ⟨K, hjet⟩
  · have hJ : ContDiffOn ℝ 1 (iteratedFDerivWithin ℝ k u s) s := by
      intro x hx
      apply (hu x hx).iteratedFDerivWithin_right hsD _ hx
      norm_cast
      omega
    obtain ⟨C, hC⟩ := exists_holderWith_restrict_of_contDiffOn_isCompact hs hsconv hJ hα1
    exact ⟨C, HolderWith.restrict_iff.mp hC⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.exists_holderOnWith_iteratedFDerivWithin_comp_of_convex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.exists_holderOnWith_iteratedFDerivWithin_comp_of_convex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.exists_holderOnWith_iteratedFDerivWithin_comp_of_convex ``Submission.DifferentialGeometry.Analysis.Schauder.exists_holderOnWith_iteratedFDerivWithin_comp_of_convex

theorem holderOnWith_iteratedFDerivWithin_succ_iff
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {s : Set E} (hs : UniqueDiffOn 𝕜 s) {u : E → F} {n : ℕ} {K α : ℝ≥0} :
    HolderOnWith K α (iteratedFDerivWithin 𝕜 (n + 1) u s) s ↔
      HolderOnWith K α (iteratedFDerivWithin 𝕜 n (fderivWithin 𝕜 u s) s) s := by
  have heq (x : E) (hx : x ∈ s) (y : E) (hy : y ∈ s) :
      _root_.EDist.edist (iteratedFDerivWithin 𝕜 (n + 1) u s x)
        (iteratedFDerivWithin 𝕜 (n + 1) u s y) =
      _root_.EDist.edist (iteratedFDerivWithin 𝕜 n (fderivWithin 𝕜 u s) s x)
        (iteratedFDerivWithin 𝕜 n (fderivWithin 𝕜 u s) s y) := by
    rw [iteratedFDerivWithin_succ_eq_comp_right hs hx,
      iteratedFDerivWithin_succ_eq_comp_right hs hy]
    exact (continuousMultilinearCurryRightEquiv' 𝕜 n E F).symm.edist_map _ _
  constructor <;> intro h x hx y hy
  · rw [← heq x hx y hy]
    exact h x hx y hy
  · rw [heq x hx y hy]
    exact h x hx y hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.holderOnWith_iteratedFDerivWithin_succ_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.holderOnWith_iteratedFDerivWithin_succ_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.holderOnWith_iteratedFDerivWithin_succ_iff ``Submission.DifferentialGeometry.Analysis.Schauder.holderOnWith_iteratedFDerivWithin_succ_iff

private theorem holderOnWith_iteratedFDerivWithin_prodMk
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {s : Set E} (hs : UniqueDiffOn ℝ s) {n : ℕ} {u : E → F} {v : E → G}
    (hu : ContDiffOn ℝ n u s) (hv : ContDiffOn ℝ n v s) {K L α : ℝ≥0}
    (huj : HolderOnWith K α (iteratedFDerivWithin ℝ n u s) s)
    (hvj : HolderOnWith L α (iteratedFDerivWithin ℝ n v s) s) :
    HolderOnWith (_root_.Max.max K L) α (iteratedFDerivWithin ℝ n (fun x => (u x, v x)) s) s := by
  intro x hx y hy
  rw [iteratedFDerivWithin_prodMk (hu x hx) (hv x hx) hs hx le_rfl,
    iteratedFDerivWithin_prodMk (hu y hy) (hv y hy) hs hy le_rfl]
  change _root_.EDist.edist (ContinuousMultilinearMap.prodL ℝ (fun _ : Fin n => E) F G (_, _))
    (ContinuousMultilinearMap.prodL ℝ (fun _ : Fin n => E) F G (_, _)) ≤ _
  rw [LinearIsometryEquiv.edist_map]
  exact holderOnWith_prodMk huj hvj x hx y hy

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Schauder.holderOnWith_iteratedFDerivWithin_prodMk
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Schauder.holderOnWith_iteratedFDerivWithin_prodMk target :: scope.openDecls } }

private theorem exists_holderOnWith_iteratedFDerivWithin_of_contDiffOn
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} (hs : IsCompact s) (hc : Convex ℝ s) (hsD : UniqueDiffOn ℝ s)
    {u : E → F} {n : ℕ} (hu : ContDiffOn ℝ (n + 1) u s)
    {α : ℝ≥0} (hα : α ≤ 1) :
    ∃ C : ℝ≥0, HolderOnWith C α (iteratedFDerivWithin ℝ n u s) s := by
  have hJ : ContDiffOn ℝ 1 (iteratedFDerivWithin ℝ n u s) s := by
    intro x hx
    exact (hu x hx).iteratedFDerivWithin_right hsD (by simp [add_comm]) hx
  obtain ⟨C, hC⟩ := exists_holderWith_restrict_of_contDiffOn_isCompact hs hc hJ hα
  exact ⟨C, HolderWith.restrict_iff.mp hC⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Schauder.exists_holderOnWith_iteratedFDerivWithin_of_contDiffOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Schauder.exists_holderOnWith_iteratedFDerivWithin_of_contDiffOn target :: scope.openDecls } }

theorem exists_holderOnWith_iteratedFDerivWithin_firstJet
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} (hs : IsCompact s) (hc : Convex ℝ s) (hsD : UniqueDiffOn ℝ s)
    {u : E → F} {n : ℕ} (hu : ContDiffOn ℝ (n + 1) u s) {K α : ℝ≥0}
    (hα : α ≤ 1) (hjet : HolderOnWith K α (iteratedFDerivWithin ℝ (n + 1) u s) s) :
    ∃ C : ℝ≥0,
      ContDiffOn ℝ n (fun x => (x, u x, fderivWithin ℝ u s x)) s ∧
      HolderOnWith C α
        (iteratedFDerivWithin ℝ n (fun x => (x, u x, fderivWithin ℝ u s x)) s) s := by
  obtain ⟨A, hA⟩ := exists_holderOnWith_iteratedFDerivWithin_of_contDiffOn hs hc hsD
    (contDiffOn_id : ContDiffOn ℝ (n + 1) (fun x : E => x) s) hα
  obtain ⟨B, hB⟩ := exists_holderOnWith_iteratedFDerivWithin_of_contDiffOn hs hc hsD hu hα
  have hD := (holderOnWith_iteratedFDerivWithin_succ_iff hsD).mp hjet
  refine ⟨max A (_root_.Max.max B K),
    contDiffOn_id.prodMk ((hu.of_le (by simp)).prodMk (hu.fderivWithin hsD le_rfl)), ?_⟩
  exact holderOnWith_iteratedFDerivWithin_prodMk hsD
    contDiffOn_id ((hu.of_le (by simp)).prodMk (hu.fderivWithin hsD le_rfl)) hA
    (holderOnWith_iteratedFDerivWithin_prodMk hsD (hu.of_le (by simp))
      (hu.fderivWithin hsD le_rfl) hB hD)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.exists_holderOnWith_iteratedFDerivWithin_firstJet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.exists_holderOnWith_iteratedFDerivWithin_firstJet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.exists_holderOnWith_iteratedFDerivWithin_firstJet ``Submission.DifferentialGeometry.Analysis.Schauder.exists_holderOnWith_iteratedFDerivWithin_firstJet

theorem exists_holderOnWith_iteratedFDerivWithin_firstJet_comp
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {s : Set E} (hs : IsCompact s) (hc : Convex ℝ s) (hsD : UniqueDiffOn ℝ s)
    {u : E → F} {n : ℕ} (hu : ContDiffOn ℝ (n + 1) u s) {K α : ℝ≥0}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hjet : HolderOnWith K α (iteratedFDerivWithin ℝ (n + 1) u s) s)
    {U : Set (E × F × (E →L[ℝ] F))} (hU : IsOpen U)
    (huU : _root_.Set.MapsTo (fun x => (x, u x, fderivWithin ℝ u s x)) s U)
    {f : (E × F × (E →L[ℝ] F)) → G} (hf : ContDiffOn ℝ (n + 1) f U) :
    ∃ C : ℝ≥0, HolderOnWith C α
      (iteratedFDerivWithin ℝ n (fun x => f (x, u x, fderivWithin ℝ u s x)) s) s := by
  obtain ⟨A, hJ, hA⟩ := exists_holderOnWith_iteratedFDerivWithin_firstJet hs hc hsD hu hα1 hjet
  exact exists_holderOnWith_iteratedFDerivWithin_comp_of_convex hs hc hsD
    hJ hα hα1 hA hU huU hf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.exists_holderOnWith_iteratedFDerivWithin_firstJet_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.exists_holderOnWith_iteratedFDerivWithin_firstJet_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.exists_holderOnWith_iteratedFDerivWithin_firstJet_comp ``Submission.DifferentialGeometry.Analysis.Schauder.exists_holderOnWith_iteratedFDerivWithin_firstJet_comp

end DifferentialGeometry.Analysis.Schauder
