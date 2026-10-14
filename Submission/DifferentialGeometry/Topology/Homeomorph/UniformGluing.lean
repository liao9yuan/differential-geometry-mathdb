/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.Homeomorph.DisjointGluing
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Topology.MetricSpace.Bounded

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Filter _root_.Topology _root_.Uniformity

namespace Homeomorph
open _root_.Homeomorph

variable {X ι : Type*} [UniformSpace X]

open _root_.Homeomorph in
private theorem continuous_gluing (f : ι → X ≃ₜ X) (U : ι → Set X)
    (hfix : ∀ i, _root_.Set.EqOn (f i) id (U i)ᶜ) (hdis : Pairwise fun i j => Disjoint (U i) (U j))
    (hsmall : TendstoUniformly (fun i => (f i : X → X)) id _root_.Filter.cofinite)
    {g : X → X} (hg : ∀ i, _root_.Set.EqOn g (f i) (U i)) (hgfix : _root_.Set.EqOn g id (⋃ i, U i)ᶜ) :
    Continuous g := by
  classical
  have hfinite (s : Finset ι) := exists_gluing_of_pairwise_disjoint
    (fun i : s => f i) (fun i : s => U i) (fun i => hfix i)
    (fun i j hij => hdis (fun heq => hij (Subtype.ext heq)))
  choose G hG hGfix using hfinite
  have hlim : TendstoUniformly (fun s : Finset ι => (G s : X → X)) g atTop := by
    intro V hV
    have hbad := eventually_cofinite.mp (hsmall (Prod.swap ⁻¹' V) (symm_le_uniformity hV))
    filter_upwards [_root_.Filter.eventually_ge_atTop hbad.toFinset] with s hs x
    by_cases hx : x ∈ ⋃ i, U i
    · obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
      rw [hg i hxi]
      by_cases hi : i ∈ s
      · rw [hG s ⟨i, hi⟩ hxi]
        exact refl_mem_uniformity hV
      · have hxout : x ∉ ⋃ j : s, U j := by
          intro hxu
          obtain ⟨j, hxj⟩ := mem_iUnion.mp hxu
          have hij : i ≠ j.1 := fun heq => hi (heq.symm ▸ j.2)
          exact disjoint_left.mp (hdis hij) hxi hxj
        rw [hGfix s hxout]
        have hgood : ∀ y, (y, f i y) ∈ Prod.swap ⁻¹' V := by
          by_contra hnot
          exact hi (hs (hbad.mem_toFinset.mpr hnot))
        exact hgood x
    · rw [hgfix hx, hGfix s (fun hxu => hx (by
        obtain ⟨i, hxi⟩ := mem_iUnion.mp hxu
        exact mem_iUnion.mpr ⟨i.1, hxi⟩))]
      exact refl_mem_uniformity hV
  exact hlim.continuous (Eventually.of_forall fun s => (G s).continuous).frequently

run_cmd do
  let target := ``Submission.Homeomorph.continuous_gluing
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Homeomorph.continuous_gluing target :: scope.openDecls } }

open _root_.Homeomorph in
theorem exists_gluing_of_pairwise_disjoint_of_tendstoUniformly
    (f : ι → X ≃ₜ X) (U : ι → Set X)
    (hfix : ∀ i, _root_.Set.EqOn (f i) id (U i)ᶜ) (hdis : Pairwise fun i j => Disjoint (U i) (U j))
    (hsmall : TendstoUniformly (fun i => (f i : X → X)) id _root_.Filter.cofinite) :
    ∃ g : X ≃ₜ X, (∀ i, _root_.Set.EqOn g (f i) (U i)) ∧ _root_.Set.EqOn g id (⋃ i, U i)ᶜ := by
  classical
  let F (a : ι → X → X) (x : X) := if hx : ∃ i, x ∈ U i then a hx.choose x else x
  have hF (a : ι → X → X) (i : ι) : _root_.Set.EqOn (F a) (a i) (U i) := by
    intro x hx
    have hex : ∃ j, x ∈ U j := ⟨i, hx⟩
    dsimp only [F]
    rw [dif_pos hex]
    have heq : hex.choose = i := by
      by_contra hne
      exact disjoint_left.mp (hdis hne) hex.choose_spec hx
    rw [heq]
  have hFfix (a : ι → X → X) : _root_.Set.EqOn (F a) id (⋃ i, U i)ᶜ := by
    intro x hx
    dsimp only [F]
    rw [dif_neg (fun hex => hx (mem_iUnion.mpr hex))]
    rfl
  have hfixsymm (i : ι) : _root_.Set.EqOn (f i).symm id (U i)ᶜ := by
    intro x hx
    apply (f i).injective
    simpa only [_root_.Homeomorph.apply_symm_apply, id_eq] using (hfix i hx).symm
  have hmaps (a : X ≃ₜ X) (i : ι) (ha : _root_.Set.EqOn a id (U i)ᶜ) : _root_.Set.MapsTo a (U i) (U i) := by
    intro x hx
    by_contra hnot
    have heq : a x = x := a.injective (ha hnot)
    exact hnot (heq.symm ▸ hx)
  have hsmallinv : TendstoUniformly (fun i => ((f i).symm : X → X)) id cofinite := by
    intro V hV
    filter_upwards [hsmall (Prod.swap ⁻¹' V) (symm_le_uniformity hV)] with i hi x
    simpa only [_root_.Set.mem_preimage, id_eq, Prod.swap_prod_mk, _root_.Homeomorph.apply_symm_apply]
      using hi ((f i).symm x)
  let g := F (fun i => (f i : X → X))
  let k := F (fun i => ((f i).symm : X → X))
  have hg : ∀ i, _root_.Set.EqOn g (f i) (U i) := hF (fun i => (f i : X → X))
  have hk : ∀ i, _root_.Set.EqOn k (f i).symm (U i) := hF (fun i => ((f i).symm : X → X))
  have hgfix : _root_.Set.EqOn g id (⋃ i, U i)ᶜ := hFfix (fun i => (f i : X → X))
  have hkfix : _root_.Set.EqOn k id (⋃ i, U i)ᶜ := hFfix (fun i => ((f i).symm : X → X))
  have hleft : Function.LeftInverse k g := by
    intro x
    by_cases hx : x ∈ ⋃ i, U i
    · obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
      rw [hg i hxi, hk i (hmaps (f i) i (hfix i) hxi), _root_.Homeomorph.symm_apply_apply]
    · rw [hgfix hx, id_eq, hkfix hx]
      rfl
  have hright : Function.RightInverse k g := by
    intro x
    by_cases hx : x ∈ ⋃ i, U i
    · obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
      rw [hk i hxi, hg i (hmaps (f i).symm i (hfixsymm i) hxi), _root_.Homeomorph.apply_symm_apply]
    · rw [hkfix hx, id_eq, hgfix hx]
      rfl
  let e : X ≃ₜ X :=
    { toFun := g
      invFun := k
      left_inv := hleft
      right_inv := hright
      continuous_toFun := continuous_gluing f U hfix hdis hsmall hg hgfix
      continuous_invFun := continuous_gluing (fun i => (f i).symm) U hfixsymm hdis
        hsmallinv hk hkfix }
  exact ⟨e, hg, hgfix⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Homeomorph.exists_gluing_of_pairwise_disjoint_of_tendstoUniformly then
    throwError "Refusing to shadow existing declaration Homeomorph.exists_gluing_of_pairwise_disjoint_of_tendstoUniformly"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.exists_gluing_of_pairwise_disjoint_of_tendstoUniformly ``Submission.Homeomorph.exists_gluing_of_pairwise_disjoint_of_tendstoUniformly

end Homeomorph

namespace Homeomorph
open _root_.Homeomorph

variable {X ι : Type*} [PseudoMetricSpace X]

open _root_.Homeomorph in
theorem exists_gluing_dist_lt_of_tendstoUniformly (f : ι → X ≃ₜ X) (U : ι → Set X)
    (hfix : ∀ i, _root_.Set.EqOn (f i) id (U i)ᶜ) (hdis : Pairwise fun i j => Disjoint (U i) (U j))
    (hsmall : TendstoUniformly (fun i => (f i : X → X)) id _root_.Filter.cofinite)
    {ε : X → ℝ} (hε : ∀ x, 0 < ε x) (hdist : ∀ i, ∀ x ∈ U i, _root_.Dist.dist (f i x) x < ε x) :
    ∃ g : X ≃ₜ X, (∀ i, _root_.Set.EqOn g (f i) (U i)) ∧ _root_.Set.EqOn g id (⋃ i, U i)ᶜ ∧
      ∀ x, _root_.Dist.dist (g x) x < ε x := by
  obtain ⟨g, hg, hgfix⟩ :=
    exists_gluing_of_pairwise_disjoint_of_tendstoUniformly f U hfix hdis hsmall
  refine ⟨g, hg, hgfix, ?_⟩
  intro x
  by_cases hx : x ∈ ⋃ i, U i
  · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    rw [hg i hi]
    exact hdist i x hi
  · rw [hgfix hx, id_eq, dist_self]
    exact hε x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Homeomorph.exists_gluing_dist_lt_of_tendstoUniformly then
    throwError "Refusing to shadow existing declaration Homeomorph.exists_gluing_dist_lt_of_tendstoUniformly"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.exists_gluing_dist_lt_of_tendstoUniformly ``Submission.Homeomorph.exists_gluing_dist_lt_of_tendstoUniformly

open _root_.Homeomorph in
theorem tendstoUniformly_id_of_tendsto_diam (f : ι → X ≃ₜ X) (U : ι → Set X)
    (hfix : ∀ i, _root_.Set.EqOn (f i) id (U i)ᶜ) (hbounded : ∀ i, Bornology.IsBounded (U i))
    (hdiam : _root_.Filter.Tendsto (fun i => Metric.diam (U i)) _root_.Filter.cofinite (𝓝 0)) :
    TendstoUniformly (fun i => (f i : X → X)) id cofinite := by
  refine Metric.tendstoUniformly_iff.mpr fun ε hε => ?_
  filter_upwards [hdiam.eventually (gt_mem_nhds hε)] with i hi x
  by_cases hx : x ∈ U i
  · have hfx : f i x ∈ U i := by
      by_contra hnot
      have heq : f i x = x := (f i).injective (hfix i hnot)
      exact hnot (heq.symm ▸ hx)
    exact (Metric.dist_le_diam_of_mem (hbounded i) hx hfx).trans_lt hi
  · simpa only [hfix i hx, id_eq, dist_self] using hε

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Homeomorph.tendstoUniformly_id_of_tendsto_diam then
    throwError "Refusing to shadow existing declaration Homeomorph.tendstoUniformly_id_of_tendsto_diam"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.tendstoUniformly_id_of_tendsto_diam ``Submission.Homeomorph.tendstoUniformly_id_of_tendsto_diam

open _root_.Homeomorph in
theorem exists_gluing_of_pairwise_disjoint_of_tendsto_diam
    (f : ι → X ≃ₜ X) (U : ι → Set X)
    (hfix : ∀ i, _root_.Set.EqOn (f i) id (U i)ᶜ) (hdis : Pairwise fun i j => Disjoint (U i) (U j))
    (hbounded : ∀ i, Bornology.IsBounded (U i))
    (hdiam : _root_.Filter.Tendsto (fun i => Metric.diam (U i)) _root_.Filter.cofinite (𝓝 0)) :
    ∃ g : X ≃ₜ X, (∀ i, _root_.Set.EqOn g (f i) (U i)) ∧ _root_.Set.EqOn g id (⋃ i, U i)ᶜ :=
  exists_gluing_of_pairwise_disjoint_of_tendstoUniformly f U hfix hdis
    (tendstoUniformly_id_of_tendsto_diam f U hfix hbounded hdiam)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Homeomorph.exists_gluing_of_pairwise_disjoint_of_tendsto_diam then
    throwError "Refusing to shadow existing declaration Homeomorph.exists_gluing_of_pairwise_disjoint_of_tendsto_diam"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.exists_gluing_of_pairwise_disjoint_of_tendsto_diam ``Submission.Homeomorph.exists_gluing_of_pairwise_disjoint_of_tendsto_diam

end Homeomorph
