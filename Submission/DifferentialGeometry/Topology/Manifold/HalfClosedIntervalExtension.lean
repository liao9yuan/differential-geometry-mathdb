import Submission.DifferentialGeometry.Topology.Manifold.HalfClosedInterval
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Topology.Order.ProjIcc

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology.Manifold

private def clampToIco {a b r : ℝ} (har : a ≤ r) (hrb : r < b) (t : ℝ) : _root_.Set.Ico a b :=
  ⟨(_root_.Set.projIcc a r har t).val, (_root_.Set.projIcc a r har t).property.1,
    (_root_.Set.projIcc a r har t).property.2.trans_lt hrb⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.clampToIco
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.clampToIco target :: scope.openDecls } }

private theorem continuous_clampToIco {a b r : ℝ} (har : a ≤ r) (hrb : r < b) :
    Continuous (clampToIco har hrb) := by
  exact (continuous_subtype_val.comp continuous_projIcc).subtype_mk _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.continuous_clampToIco
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.continuous_clampToIco target :: scope.openDecls } }

private theorem clampToIco_val_of_mem {a b r t : ℝ} (har : a ≤ r) (hrb : r < b)
    (ht : t ∈ _root_.Set.Icc a r) : (clampToIco har hrb t).val = t :=
  congrArg Subtype.val (_root_.Set.projIcc_of_mem (h := har) ht)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.clampToIco_val_of_mem
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.clampToIco_val_of_mem target :: scope.openDecls } }

private theorem contMDiffOn_clampToIco {a b r : ℝ} (har : a ≤ r) (hrb : r < b)
    (n : ℕ∞ω) :
    letI := halfClosedIntervalChartedSpace (har.trans_lt hrb)
    ContMDiffOn 𝓘(ℝ) (𝓡∂ 1) n (clampToIco har hrb) (_root_.Set.Icc a r) := by
  let := halfClosedIntervalChartedSpace (har.trans_lt hrb)
  intro t ht
  rw [contMDiffWithinAt_iff_target]
  refine ⟨(continuous_clampToIco har hrb).continuousWithinAt, ?_⟩
  let L : ℝ ≃L[ℝ] EuclideanSpace ℝ (Fin 1) :=
    (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)).symm
  have hL : ContMDiff 𝓘(ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) n
      (fun z : ℝ => L (z - a)) :=
    L.toContinuousLinearMap.contMDiff.comp (contMDiff_id.sub contMDiff_const)
  apply hL.contMDiffAt.contMDiffWithinAt.congr_of_mem ?_ ht
  intro z hz
  ext j
  fin_cases j
  change (extChartAt (𝓡∂ 1) (clampToIco har hrb t) (clampToIco har hrb z)) 0 = _
  rw [halfClosedInterval_extChartAt_apply, clampToIco_val_of_mem har hrb hz]
  simp [L]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.contMDiffOn_clampToIco
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.contMDiffOn_clampToIco target :: scope.openDecls } }

variable {F HS S E HM M : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace HS] {J : ModelWithCorners ℝ F HS}
  [TopologicalSpace S] [ChartedSpace HS S]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace HM] {I : ModelWithCorners ℝ E HM}
  [TopologicalSpace M] [ChartedSpace HM M] {n : ℕ∞ω}

theorem exists_contMDiffOn_extension_prod_Icc {a b r : ℝ} (har : a ≤ r) (hrb : r < b)
    (c : S × _root_.Set.Ico a b → M)
    (hc : letI := halfClosedIntervalChartedSpace (har.trans_lt hrb)
      ContMDiff (J.prod (𝓡∂ 1)) I n c) :
    ∃ g : C(S × ℝ, M), ContMDiffOn (J.prod 𝓘(ℝ)) I n g (_root_.Set.univ ×ˢ _root_.Set.Icc a r) ∧
      ∀ (s : S) (t : ℝ) (ht : t ∈ _root_.Set.Icc a r),
        g (s, t) = c (s, ⟨t, ht.1, ht.2.trans_lt hrb⟩) := by
  let := halfClosedIntervalChartedSpace (har.trans_lt hrb)
  let κ := clampToIco har hrb
  let g : C(S × ℝ, M) := ⟨fun p => c (p.1, κ p.2),
    hc.continuous.comp (continuous_fst.prodMk
      ((continuous_clampToIco har hrb).comp continuous_snd))⟩
  have hκ : ContMDiffOn (J.prod 𝓘(ℝ)) (𝓡∂ 1) n
      (fun p : S × ℝ => κ p.2) (_root_.Set.univ ×ˢ _root_.Set.Icc a r) :=
    (contMDiffOn_clampToIco har hrb n).comp contMDiffOn_snd (fun _ hp => hp.2)
  refine ⟨g, hc.comp_contMDiffOn (contMDiffOn_fst.prodMk hκ), ?_⟩
  intro s t ht
  change c (s, clampToIco har hrb t) = c (s, ⟨t, ht.1, ht.2.trans_lt hrb⟩)
  exact congrArg (fun q : _root_.Set.Ico a b => c (s, q))
    (Subtype.ext (clampToIco_val_of_mem har hrb ht))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_contMDiffOn_extension_prod_Icc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_contMDiffOn_extension_prod_Icc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_contMDiffOn_extension_prod_Icc ``Submission.DifferentialGeometry.Topology.Manifold.exists_contMDiffOn_extension_prod_Icc

end DifferentialGeometry.Topology.Manifold
