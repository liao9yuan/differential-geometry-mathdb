import Submission.DifferentialGeometry.Analysis.Calculus.Cutoff.Clamp.Smooth
import Submission.DifferentialGeometry.Analysis.Calculus.SmoothExtension.Quadrant
import Submission.DifferentialGeometry.Analysis.Calculus.Cutoff.Compact
import Mathlib.Geometry.Manifold.Instances.Real
import Submission.DifferentialGeometry.Analysis.Calculus.SmoothExtension.BorelHalfLine.Parametric
import Mathlib.Geometry.Manifold.PartitionOfUnity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.ContDiff _root_.Manifold _root_.Topology

namespace DifferentialGeometry.Analysis

open _root_.Set _root_.Filter

private theorem exists_contDiff_extension_strip_local_of_lt
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {a b c : ℝ} {f : ℝ × (ℝ × E) → F} {U : Set (ℝ × (ℝ × E))}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f ((_root_.Set.Icc a b ×ˢ (_root_.Set.Ici c ×ˢ _root_.Set.univ)) ∩ U))
    {x : ℝ × (ℝ × E)} (hx : x ∈ U) (hxb : x.1 < b) :
    ∃ G : ℝ × (ℝ × E) → F, ContDiff ℝ ∞ G ∧
      G =ᶠ[𝓝[_root_.Set.Icc a b ×ˢ (_root_.Set.Ici c ×ˢ _root_.Set.univ)] x] f := by
  let W : Set (ℝ × (ℝ × E)) := U ∩ {q | q.1 < b}
  have hW : IsOpen W := hU.inter (isOpen_lt continuous_fst continuous_const)
  have hread : ContDiffOn ℝ ∞ f ((_root_.Set.Ici a ×ˢ (_root_.Set.Ici c ×ˢ _root_.Set.univ)) ∩ W) :=
    hf.mono (fun _ hq => ⟨⟨⟨hq.1.1, hq.2.2.le⟩, hq.1.2⟩, hq.2.1⟩)
  obtain ⟨g, hg, -, hgeq⟩ := exists_contDiffOn_cutoff_extension hW hread
    (show x ∈ W from ⟨hx, hxb⟩)
  obtain ⟨G, hG, hGg⟩ := hg.exists_contDiff_extension_quadrant
  refine ⟨G, hG, ?_⟩
  filter_upwards [self_mem_nhdsWithin, hgeq.filter_mono nhdsWithin_le_nhds] with q hq heq
  exact (hGg ⟨hq.1.1, hq.2⟩).trans heq

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.exists_contDiff_extension_strip_local_of_lt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.exists_contDiff_extension_strip_local_of_lt target :: scope.openDecls } }

private theorem exists_contDiff_extension_strip_local
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {a b c : ℝ} (hab : a < b) {f : ℝ × (ℝ × E) → F} {U : Set (ℝ × (ℝ × E))}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f ((_root_.Set.Icc a b ×ˢ (_root_.Set.Ici c ×ˢ _root_.Set.univ)) ∩ U))
    {x : ℝ × (ℝ × E)} (hx : x ∈ U) :
    ∃ G : ℝ × (ℝ × E) → F, ContDiff ℝ ∞ G ∧
      G =ᶠ[𝓝[_root_.Set.Icc a b ×ˢ (_root_.Set.Ici c ×ˢ _root_.Set.univ)] x] f := by
  by_cases hxb : x.1 < b
  · exact exists_contDiff_extension_strip_local_of_lt hU hf hx hxb
  · let σ : ℝ × (ℝ × E) → ℝ × (ℝ × E) := fun q => (-q.1, q.2)
    have hσ : ContDiff ℝ ∞ σ := contDiff_fst.neg.prodMk contDiff_snd
    have hread : ContDiffOn ℝ ∞ (f ∘ σ)
        ((_root_.Set.Icc (-b) (-a) ×ˢ (_root_.Set.Ici c ×ˢ _root_.Set.univ)) ∩ (σ ⁻¹' U)) := by
      apply hf.comp hσ.contDiffOn
      intro q hq
      exact ⟨⟨⟨by dsimp [σ]; linarith [hq.1.1.2],
        by dsimp [σ]; linarith [hq.1.1.1]⟩, hq.1.2⟩, hq.2⟩
    obtain ⟨G, hG, hGeq⟩ := exists_contDiff_extension_strip_local_of_lt
      (hU.preimage hσ.continuous) hread
      (show σ x ∈ σ ⁻¹' U by simpa only [σ, _root_.Set.mem_preimage, neg_neg] using hx)
      (show (σ x).1 < -a by dsimp [σ]; linarith)
    refine ⟨G ∘ σ, hG.comp hσ, ?_⟩
    have ht : _root_.Filter.Tendsto σ (𝓝[_root_.Set.Icc a b ×ˢ (_root_.Set.Ici c ×ˢ _root_.Set.univ)] x)
        (𝓝[_root_.Set.Icc (-b) (-a) ×ˢ (_root_.Set.Ici c ×ˢ _root_.Set.univ)] σ x) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨hσ.continuous.continuousAt.mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with q hq
      exact ⟨⟨by dsimp [σ]; linarith [hq.1.2],
        by dsimp [σ]; linarith [hq.1.1]⟩, hq.2⟩
    filter_upwards [hGeq.comp_tendsto ht] with q hq
    simpa only [Function.comp_apply, σ, neg_neg] using hq

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.exists_contDiff_extension_strip_local
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.exists_contDiff_extension_strip_local target :: scope.openDecls } }

private theorem exists_contDiff_extension_Icc_halfspace_local
    {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {a b : ℝ} (hab : a < b)
    {f : ℝ × EuclideanSpace ℝ (Fin (d + 1)) → F}
    {U : Set (ℝ × EuclideanSpace ℝ (Fin (d + 1)))} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f ((_root_.Set.Icc a b ×ˢ _root_.Set.range (𝓡∂ (d + 1))) ∩ U))
    {x : ℝ × EuclideanSpace ℝ (Fin (d + 1))} (hx : x ∈ U) :
    ∃ G : ℝ × EuclideanSpace ℝ (Fin (d + 1)) → F, ContDiff ℝ ∞ G ∧
      G =ᶠ[𝓝[_root_.Set.Icc a b ×ˢ _root_.Set.range (𝓡∂ (d + 1))] x] f := by
  let κ : (ℝ × (Fin d → ℝ)) ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1)) :=
    (Fin.consEquivL ℝ (fun _ : Fin (d + 1) => ℝ)).trans
      (EuclideanSpace.equiv (Fin (d + 1)) ℝ).symm
  have hκzero (z : ℝ × (Fin d → ℝ)) : κ z 0 = z.1 := by simp [κ]
  let k : ℝ × (ℝ × (Fin d → ℝ)) → ℝ × EuclideanSpace ℝ (Fin (d + 1)) :=
    fun q => (q.1, κ q.2)
  let j : ℝ × EuclideanSpace ℝ (Fin (d + 1)) → ℝ × (ℝ × (Fin d → ℝ)) :=
    fun q => (q.1, κ.symm q.2)
  have hk : ContDiff ℝ ∞ k := contDiff_fst.prodMk (κ.contDiff.comp contDiff_snd)
  have hj : ContDiff ℝ ∞ j := contDiff_fst.prodMk (κ.symm.contDiff.comp contDiff_snd)
  have hkj (q : ℝ × EuclideanSpace ℝ (Fin (d + 1))) : k (j q) = q := by
    change (q.1, κ (κ.symm q.2)) = q
    rw [κ.apply_symm_apply]
  have hread : ContDiffOn ℝ ∞ (f ∘ k)
      ((_root_.Set.Icc a b ×ˢ (_root_.Set.Ici 0 ×ˢ _root_.Set.univ)) ∩ (k ⁻¹' U)) := by
    apply hf.comp hk.contDiffOn
    intro q hq
    refine ⟨⟨hq.1.1, ?_⟩, hq.2⟩
    rw [range_modelWithCornersEuclideanHalfSpace]
    change 0 ≤ κ q.2 0
    rw [hκzero]
    exact mem_Ici.mp hq.1.2.1
  obtain ⟨G, hG, hGeq⟩ := exists_contDiff_extension_strip_local hab
    (hU.preimage hk.continuous) hread (show j x ∈ k ⁻¹' U by rwa [_root_.Set.mem_preimage, hkj])
  refine ⟨G ∘ j, hG.comp hj, ?_⟩
  have ht : _root_.Filter.Tendsto j (𝓝[_root_.Set.Icc a b ×ˢ _root_.Set.range (𝓡∂ (d + 1))] x)
      (𝓝[_root_.Set.Icc a b ×ˢ (_root_.Set.Ici (0 : ℝ) ×ˢ _root_.Set.univ)] j x) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hj.continuous.continuousAt.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with q hq
    refine ⟨hq.1, mem_Ici.mpr ?_, _root_.Set.mem_univ _⟩
    change 0 ≤ (κ.symm q.2).1
    rw [← hκzero _, κ.apply_symm_apply]
    simpa only [range_modelWithCornersEuclideanHalfSpace, _root_.Set.mem_ofPred_eq] using hq.2
  filter_upwards [hGeq.comp_tendsto ht] with q hq
  simpa only [Function.comp_apply, hkj] using hq

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.exists_contDiff_extension_Icc_halfspace_local
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.exists_contDiff_extension_Icc_halfspace_local target :: scope.openDecls } }

end DifferentialGeometry.Analysis

namespace Manifold

open _root_.Set

private theorem exists_contMDiff_extension_Icc_of_local
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × M → F} {a b : ℝ}
    (hlocal : ∀ q₀ : ℝ × M, ∃ U ∈ 𝓝 q₀, ∃ G : ℝ × M → F,
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F) ∞ G U ∧
        ∀ q ∈ U, q.1 ∈ _root_.Set.Icc a b → G q = f q) :
    ∃ G : ℝ × M → F, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F) ∞ G ∧
      EqOn G f (_root_.Set.Icc a b ×ˢ _root_.Set.univ) := by
  let C : ℝ × M → Set F := fun q => {v | q.1 ∈ _root_.Set.Icc a b → v = f q}
  have hC (q : ℝ × M) : Convex ℝ (C q) := by
    rw [convex_iff_add_mem]
    intro u hu v hv s t _ _ hsum hq
    rw [hu hq, hv hq, ← add_smul, hsum, one_smul]
  obtain ⟨G, hG⟩ := exists_contMDiffMap_forall_mem_convex_of_local
    (I := 𝓘(ℝ, ℝ).prod I) (n := (⊤ : ℕ∞)) hC hlocal
  exact ⟨G, G.contMDiff, fun q hq => hG q hq.1⟩

run_cmd do
  let target := ``Submission.Manifold.exists_contMDiff_extension_Icc_of_local
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Manifold.exists_contMDiff_extension_Icc_of_local target :: scope.openDecls } }

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

private theorem exists_contMDiff_extension_Icc_zero
    {f : ℝ × M → F} {T : ℝ} (hT : 0 < T)
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F) ∞ f (_root_.Set.Icc 0 T ×ˢ _root_.Set.univ)) :
    ∃ G : ℝ × M → F, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F) ∞ G ∧
      EqOn G f (_root_.Set.Icc 0 T ×ˢ _root_.Set.univ) := by
  apply exists_contMDiff_extension_Icc_of_local
  intro q₀
  let x := q₀.2
  let g : ℝ → E → F := fun t z => f (t, (extChartAt I x).symm z)
  have hread : ContDiffOn ℝ ∞ (Function.uncurry g)
      (_root_.Set.Icc 0 T ×ˢ (extChartAt I x).target) := by
    have hΨ : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) (𝓘(ℝ, ℝ).prod I) ∞
        (fun q : ℝ × E => (q.1, (extChartAt I x).symm q.2))
        (_root_.Set.Icc 0 T ×ˢ (extChartAt I x).target) :=
      contMDiffOn_fst.prodMk
        ((contMDiffOn_extChartAt_symm (I := I) (n := ∞) x).comp
          contMDiffOn_snd (fun _ hq => hq.2))
    have hcomp := hf.comp hΨ (fun _ hq => ⟨hq.1, _root_.Set.mem_univ _⟩)
    rw [← contMDiffOn_iff_contDiffOn, ← chartedSpaceSelf_prod, modelWithCornersSelf_prod]
    exact hcomp
  have hxint : extChartAt I x x ∈ interior (extChartAt I x).target := by
    rw [(isOpen_extChartAt_target (I := I) x).interior_eq]
    exact mem_extChartAt_target x
  obtain ⟨gext, V, hV, hgext, hgeq⟩ :=
    DifferentialGeometry.Analysis.borel_interval_extend_param
      g T hT (extChartAt I x).target (extChartAt I x x) hxint hread
  obtain ⟨W, hWV, hWopen, hxW⟩ := mem_nhds_iff.mp hV
  let U : Set M := (chartAt H x).source ∩ (extChartAt I x) ⁻¹' W
  have hUopen : IsOpen U := by
    have hc : ContinuousOn (extChartAt I x) (chartAt H x).source := by
      rw [← extChartAt_source (I := I) x]
      exact continuousOn_extChartAt x
    exact hc.isOpen_inter_preimage (chartAt H x).open_source hWopen
  have hxU : x ∈ U := ⟨mem_chart_source H x, hxW⟩
  let G : ℝ × M → F := fun q => gext q.1 (extChartAt I x q.2)
  have hgextM : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, F) ∞
      (Function.uncurry gext) (_root_.Set.univ ×ˢ V) := by
    rw [← contMDiffOn_iff_contDiffOn, ← chartedSpaceSelf_prod,
      modelWithCornersSelf_prod] at hgext
    exact hgext
  have hΦ : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (q.1, extChartAt I x q.2)) (_root_.Set.univ ×ˢ U) :=
    contMDiffOn_fst.prodMk
      ((contMDiffOn_extChartAt (I := I) (n := ∞) (x := x)).comp
        contMDiffOn_snd (fun _ hq => hq.2.1))
  refine ⟨univ ×ˢ U, (isOpen_univ.prod hUopen).mem_nhds ⟨mem_univ _, hxU⟩,
    G, hgextM.comp hΦ (fun _ hq => ⟨mem_univ _, hWV hq.2.2⟩), ?_⟩
  intro q hq ht
  change gext q.1 (extChartAt I x q.2) = f q
  rw [hgeq q.1 ht (extChartAt I x q.2) (hWV hq.2.2)]
  change f (q.1, (extChartAt I x).symm (extChartAt I x q.2)) = f q
  rw [(extChartAt I x).left_inv (by rw [extChartAt_source]; exact hq.2.1)]

run_cmd do
  let target := ``Submission.Manifold.exists_contMDiff_extension_Icc_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Manifold.exists_contMDiff_extension_Icc_zero target :: scope.openDecls } }

theorem exists_contMDiff_extension_Icc
    {f : ℝ × M → F} {a b : ℝ}
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F) ∞ f (_root_.Set.Icc a b ×ˢ _root_.Set.univ)) :
    ∃ G : ℝ × M → F, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F) ∞ G ∧
      EqOn G f (_root_.Set.Icc a b ×ˢ _root_.Set.univ) := by
  rcases lt_trichotomy a b with hab | hab | hab
  · let g : ℝ × M → F := fun q => f (q.1 + a, q.2)
    have hg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F) ∞ g
        (_root_.Set.Icc 0 (b - a) ×ˢ _root_.Set.univ) := by
      refine hf.comp ((contMDiff_fst.add contMDiff_const).prodMk
        contMDiff_snd).contMDiffOn ?_
      intro q hq
      exact ⟨⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩, _root_.Set.mem_univ _⟩
    obtain ⟨G, hG, hGe⟩ := exists_contMDiff_extension_Icc_zero (sub_pos.mpr hab) hg
    refine ⟨fun q => G (q.1 - a, q.2),
      hG.comp ((contMDiff_fst.sub contMDiff_const).prodMk contMDiff_snd), ?_⟩
    intro q hq
    have hmem : (q.1 - a, q.2) ∈ _root_.Set.Icc 0 (b - a) ×ˢ (_root_.Set.univ : Set M) :=
      ⟨⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩, _root_.Set.mem_univ _⟩
    simpa only [g, sub_add_cancel] using hGe hmem
  · subst b
    have hslice : ContMDiff I 𝓘(ℝ, F) ∞ (fun x => f (a, x)) := by
      rw [← contMDiffOn_univ]
      exact hf.comp (contMDiff_const.prodMk contMDiff_id).contMDiffOn
        (fun x _ => ⟨⟨le_rfl, le_rfl⟩, _root_.Set.mem_univ x⟩)
    refine ⟨fun q => f (a, q.2), hslice.comp contMDiff_snd, ?_⟩
    intro q hq
    change f (a, q.2) = f (q.1, q.2)
    rw [show q.1 = a from le_antisymm hq.1.2 hq.1.1]
  · refine ⟨0, contMDiff_const, ?_⟩
    simp only [_root_.Set.Icc_eq_empty_of_lt hab, _root_.Set.empty_prod, _root_.Set.eqOn_empty]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.exists_contMDiff_extension_Icc then
    throwError "Refusing to shadow existing declaration Manifold.exists_contMDiff_extension_Icc"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.exists_contMDiff_extension_Icc ``Submission.Manifold.exists_contMDiff_extension_Icc

end Manifold

namespace Manifold

open _root_.Set _root_.Filter

section

variable {d : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (d + 1)) M] [IsManifold (𝓡∂ (d + 1)) ∞ M]
  [T2Space M] [SigmaCompactSpace M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

private theorem exists_contMDiff_extension_Icc_halfspace_of_lt
    {f : ℝ × M → F} {a b : ℝ} (hab : a < b)
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡∂ (d + 1))) 𝓘(ℝ, F) ∞ f (_root_.Set.Icc a b ×ˢ _root_.Set.univ)) :
    ∃ G : ℝ × M → F, ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ (d + 1))) 𝓘(ℝ, F) ∞ G ∧
      EqOn G f (_root_.Set.Icc a b ×ˢ _root_.Set.univ) := by
  apply exists_contMDiff_extension_Icc_of_local
  intro q₀
  let I := 𝓡∂ (d + 1)
  let x := q₀.2
  let A : Set (EuclideanSpace ℝ (Fin (d + 1))) :=
    I.symm ⁻¹' (chartAt (EuclideanHalfSpace (d + 1)) x).target
  have hA : IsOpen A :=
    (chartAt (EuclideanHalfSpace (d + 1)) x).open_target.preimage I.continuous_symm
  have hxA : extChartAt I x x ∈ A := by
    have hm := mem_extChartAt_target (I := I) x
    rw [extChartAt_target] at hm
    exact hm.1
  let g : ℝ × EuclideanSpace ℝ (Fin (d + 1)) → F :=
    fun q => f (q.1, (extChartAt I x).symm q.2)
  have hΨ : ContMDiffOn 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin (d + 1)))
      (𝓘(ℝ, ℝ).prod I) ∞
      (fun q : ℝ × EuclideanSpace ℝ (Fin (d + 1)) =>
        (q.1, (extChartAt I x).symm q.2)) (_root_.Set.Icc a b ×ˢ (extChartAt I x).target) :=
    contDiff_fst.contMDiff.contMDiffOn.prodMk
      ((contMDiffOn_extChartAt_symm (I := I) (n := ∞) x).comp
        contDiff_snd.contMDiff.contMDiffOn (fun _ hq => hq.2))
  have hread' : ContDiffOn ℝ ∞ g (_root_.Set.Icc a b ×ˢ (extChartAt I x).target) :=
    (hf.comp hΨ (fun _ hq => ⟨hq.1, _root_.Set.mem_univ _⟩)).contDiffOn
  have hread : ContDiffOn ℝ ∞ g ((_root_.Set.Icc a b ×ˢ _root_.Set.range I) ∩ (_root_.Set.univ ×ˢ A)) := by
    apply hread'.mono
    intro q hq
    refine ⟨hq.1.1, ?_⟩
    rw [extChartAt_target]
    exact ⟨hq.2.2, hq.1.2⟩
  obtain ⟨G₀, hG₀, hG₀eq⟩ :=
    DifferentialGeometry.Analysis.exists_contDiff_extension_Icc_halfspace_local
      hab (isOpen_univ.prod hA) hread
      (show (q₀.1, extChartAt I x x) ∈ _root_.Set.univ ×ˢ A from ⟨mem_univ _, hxA⟩)
  let G : ℝ × M → F := fun q => G₀ (q.1, extChartAt I x q.2)
  let D : Set (ℝ × M) := _root_.Set.univ ×ˢ (chartAt (EuclideanHalfSpace (d + 1)) x).source
  have hD : IsOpen D :=
    isOpen_univ.prod (chartAt (EuclideanHalfSpace (d + 1)) x).open_source
  have hqD : q₀ ∈ D := ⟨mem_univ _, mem_chart_source (EuclideanHalfSpace (d + 1)) x⟩
  have hΦ : ContMDiffOn (𝓘(ℝ, ℝ).prod I)
      𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin (d + 1))) ∞
      (fun q : ℝ × M => (q.1, extChartAt I x q.2)) D :=
    contMDiffOn_fst.prodMk_space
      ((contMDiffOn_extChartAt (I := I) (n := ∞) (x := x)).comp
        contMDiffOn_snd (fun _ hq => hq.2))
  have hG : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F) ∞ G D :=
    hG₀.contMDiff.comp_contMDiffOn hΦ
  have ht : _root_.Filter.Tendsto (fun q : ℝ × M => (q.1, extChartAt I x q.2))
      (𝓝[_root_.Set.Icc a b ×ˢ _root_.Set.univ] q₀) (𝓝[_root_.Set.Icc a b ×ˢ _root_.Set.range I] (q₀.1, extChartAt I x x)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨(continuousAt_fst.prodMk
      ((continuousAt_extChartAt (I := I) x).comp continuousAt_snd)).mono_left
        nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with q hq
    exact ⟨hq.1, _root_.Set.mem_range_self ((chartAt (EuclideanHalfSpace (d + 1)) x) q.2)⟩
  have hmatch : G =ᶠ[𝓝[_root_.Set.Icc a b ×ˢ _root_.Set.univ] q₀] f := by
    filter_upwards [hG₀eq.comp_tendsto ht,
      mem_nhdsWithin_of_mem_nhds (hD.mem_nhds hqD)] with q hq hqD
    change G₀ (q.1, extChartAt I x q.2) = f q
    change G₀ (q.1, extChartAt I x q.2) =
      f (q.1, (extChartAt I x).symm (extChartAt I x q.2)) at hq
    rwa [(extChartAt I x).left_inv (by rw [extChartAt_source]; exact hqD.2)] at hq
  have hnear : ∀ᶠ q in 𝓝 q₀, q.1 ∈ _root_.Set.Icc a b → G q = f q := by
    filter_upwards [eventually_nhdsWithin_iff.mp hmatch] with q hq htime
    exact hq ⟨htime, _root_.Set.mem_univ _⟩
  let B : Set (ℝ × M) := {q | q.1 ∈ _root_.Set.Icc a b → G q = f q}
  have hqB : q₀ ∈ interior B := mem_interior_iff_mem_nhds.mpr hnear
  refine ⟨D ∩ interior B, (hD.inter isOpen_interior).mem_nhds ⟨hqD, hqB⟩,
    G, hG.mono _root_.Set.inter_subset_left, ?_⟩
  intro q hq htime
  have hqB : q ∈ B := interior_subset hq.2
  exact hqB htime

run_cmd do
  let target := ``Submission.Manifold.exists_contMDiff_extension_Icc_halfspace_of_lt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Manifold.exists_contMDiff_extension_Icc_halfspace_of_lt target :: scope.openDecls } }

theorem exists_contMDiff_extension_Icc_halfspace
    {f : ℝ × M → F} {a b : ℝ}
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡∂ (d + 1))) 𝓘(ℝ, F) ∞ f (_root_.Set.Icc a b ×ˢ _root_.Set.univ)) :
    ∃ G : ℝ × M → F, ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ (d + 1))) 𝓘(ℝ, F) ∞ G ∧
      EqOn G f (_root_.Set.Icc a b ×ˢ _root_.Set.univ) := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exact exists_contMDiff_extension_Icc_halfspace_of_lt hab hf
  · subst b
    have hslice : ContMDiff (𝓡∂ (d + 1)) 𝓘(ℝ, F) ∞ (fun x => f (a, x)) := by
      rw [← contMDiffOn_univ]
      exact hf.comp (contMDiff_const.prodMk contMDiff_id).contMDiffOn
        (fun x _ => ⟨⟨le_rfl, le_rfl⟩, _root_.Set.mem_univ x⟩)
    refine ⟨fun q => f (a, q.2), hslice.comp contMDiff_snd, ?_⟩
    intro q hq
    change f (a, q.2) = f (q.1, q.2)
    rw [show q.1 = a from le_antisymm hq.1.2 hq.1.1]
  · refine ⟨0, contMDiff_const, ?_⟩
    simp only [_root_.Set.Icc_eq_empty_of_lt hab, _root_.Set.empty_prod, _root_.Set.eqOn_empty]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.exists_contMDiff_extension_Icc_halfspace then
    throwError "Refusing to shadow existing declaration Manifold.exists_contMDiff_extension_Icc_halfspace"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.exists_contMDiff_extension_Icc_halfspace ``Submission.Manifold.exists_contMDiff_extension_Icc_halfspace

end

end Manifold

noncomputable section

open _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace Manifold

variable {E H X F E' H' Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
  [T2Space X] [CompactSpace X]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace Y] [ChartedSpace H' Y]

theorem exists_contMDiff_extension_Icc_of_retraction
    {a b : ℝ} {f : ℝ × X → Y} {e : Y → F}
    (he : ContMDiff J 𝓘(ℝ, F) ∞ e)
    (r : F → Y) (U : Set F) (hU : IsOpen U) (heU : _root_.Set.range e ⊆ U)
    (hr : ContMDiffOn 𝓘(ℝ, F) J ∞ r U) (hre : Function.LeftInverse r e)
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod I) J ∞ f (_root_.Set.Icc a b ×ˢ _root_.Set.univ)) :
    ∃ G : ℝ × X → Y, ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ G ∧
      EqOn G f (_root_.Set.Icc a b ×ˢ _root_.Set.univ) := by
  rcases lt_trichotomy a b with hab | hab | hab
  · obtain ⟨G, hG, hGeq⟩ := exists_contMDiff_extension_Icc (he.comp_contMDiffOn hf)
    have htrace : _root_.Set.Icc a b ×ˢ (_root_.Set.univ : Set X) ⊆ G ⁻¹' U := by
      intro q hq
      rw [_root_.Set.mem_preimage, hGeq hq]
      exact heU ⟨f q, rfl⟩
    obtain ⟨V, W, hV, _, hseg, hW, hVW⟩ := generalized_tube_lemma _root_.CompactIccSpace.isCompact_Icc
      (isCompact_univ (X := X)) (hU.preimage hG.continuous) htrace
    obtain ⟨ρ, lo, hi, hlo, hhi, hρ, hρid, _, hρV⟩ :=
      DifferentialGeometry.exists_smooth_time_clamp_range_subset hV hab hseg
    let ψ : ℝ × X → ℝ × X := fun q => (ρ q.1, q.2)
    have hψ : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞ ψ :=
      (hρ.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd
    have hGU : _root_.Set.MapsTo (G ∘ ψ) _root_.Set.univ U := by
      intro q _
      exact hVW ⟨hρV q.1, hW (_root_.Set.mem_univ q.2)⟩
    refine ⟨r ∘ G ∘ ψ, ?_, ?_⟩
    · rw [← contMDiffOn_univ]
      exact hr.comp (hG.comp hψ).contMDiffOn hGU
    · intro q hq
      have hρq : ρ q.1 = q.1 := hρid ⟨hlo.le.trans hq.1.1, hq.1.2.trans hhi.le⟩
      change r (G (ρ q.1, q.2)) = f q
      rw [hρq, hGeq hq]
      exact hre (f q)
  · subst b
    have hslice : ContMDiff I J ∞ (fun x => f (a, x)) := by
      rw [← contMDiffOn_univ]
      exact hf.comp (contMDiff_const.prodMk contMDiff_id).contMDiffOn
        (fun x _ => ⟨⟨le_rfl, le_rfl⟩, _root_.Set.mem_univ x⟩)
    refine ⟨fun q => f (a, q.2), hslice.comp contMDiff_snd, ?_⟩
    intro q hq
    change f (a, q.2) = f (q.1, q.2)
    rw [show q.1 = a from le_antisymm hq.1.2 hq.1.1]
  · rcases isEmpty_or_nonempty X with hX | hX
    · let _ := hX
      refine ⟨f, ?_, ?_⟩
      · intro q
        exact isEmptyElim q.2
      · simp only [_root_.Set.Icc_eq_empty_of_lt hab, _root_.Set.empty_prod, _root_.Set.eqOn_empty]
    · let _ := hX
      refine ⟨fun _ => f (a, Classical.arbitrary X), contMDiff_const, ?_⟩
      simp only [_root_.Set.Icc_eq_empty_of_lt hab, _root_.Set.empty_prod, _root_.Set.eqOn_empty]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.exists_contMDiff_extension_Icc_of_retraction then
    throwError "Refusing to shadow existing declaration Manifold.exists_contMDiff_extension_Icc_of_retraction"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.exists_contMDiff_extension_Icc_of_retraction ``Submission.Manifold.exists_contMDiff_extension_Icc_of_retraction

end Manifold

end
