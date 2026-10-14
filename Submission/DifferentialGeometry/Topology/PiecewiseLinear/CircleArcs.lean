import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PolygonalSchoenflies
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BallFrontier
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphTopology

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem IsPLHomeomorphOn.image_Ioo_eq_sdiff_endpoints {a b : ℝ} (hab : a < b)
    {γ : ℝ → E} {A : Set E} (hγ : IsPLHomeomorphOn γ (_root_.Set.Icc a b) A) :
    γ '' _root_.Set.Ioo a b = A \ {γ a, γ b} := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨hγ.bijOn.mapsTo ⟨ht.1.le, ht.2.le⟩, ?_⟩
    rintro (h | h)
    · exact ht.1.ne' (hγ.bijOn.injOn ⟨ht.1.le, ht.2.le⟩ ⟨le_rfl, hab.le⟩ h)
    · exact ht.2.ne (hγ.bijOn.injOn ⟨ht.1.le, ht.2.le⟩ ⟨hab.le, le_rfl⟩ h)
  · rintro ⟨hx, hxends⟩
    obtain ⟨t, ht, rfl⟩ := hγ.bijOn.surjOn hx
    have hta : t ≠ a := fun h => hxends (Or.inl (congrArg γ h))
    have htb : t ≠ b := fun h => hxends (Or.inr (congrArg γ h))
    exact ⟨t, ⟨lt_of_le_of_ne ht.1 hta.symm, lt_of_le_of_ne ht.2 htb⟩, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.image_Ioo_eq_sdiff_endpoints then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.image_Ioo_eq_sdiff_endpoints"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.image_Ioo_eq_sdiff_endpoints ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.image_Ioo_eq_sdiff_endpoints

theorem IsPLHomeomorphOn.isConnected_sdiff_endpoints {a b : ℝ} (hab : a < b)
    {γ : ℝ → E} {A : Set E} (hγ : IsPLHomeomorphOn γ (_root_.Set.Icc a b) A) :
    IsConnected (A \ {γ a, γ b}) := by
  rw [← hγ.image_Ioo_eq_sdiff_endpoints hab]
  exact (isConnected_Ioo hab).image γ (hγ.isPiecewiseAffineOn.continuousOn.mono _root_.Set.Ioo_subset_Icc_self)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.isConnected_sdiff_endpoints then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.isConnected_sdiff_endpoints"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.isConnected_sdiff_endpoints ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.isConnected_sdiff_endpoints

theorem IsPLHomeomorphOn.closure_sdiff_endpoints {a b : ℝ} (hab : a < b)
    {γ : ℝ → E} {A : Set E} (hγ : IsPLHomeomorphOn γ (_root_.Set.Icc a b) A) :
    closure (A \ {γ a, γ b}) = A := by
  rw [← hγ.image_Ioo_eq_sdiff_endpoints hab,
    ← hγ.image_closure _root_.CompactIccSpace.isCompact_Icc _root_.Set.Ioo_subset_Icc_self, closure_Ioo hab.ne, hγ.image_eq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.closure_sdiff_endpoints then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.closure_sdiff_endpoints"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.closure_sdiff_endpoints ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.closure_sdiff_endpoints

private theorem exists_planar_circle_coordinates [FiniteDimensional ℝ E]
    {S : Set E} (hS : IsPLSphere 1 S) :
    ∃ (C : Set (EuclideanSpace ℝ (Fin 2))) (f : E → EuclideanSpace ℝ (Fin 2)),
      IsPLSphere 1 C ∧ IsPLHomeomorphOn f S C := by
  obtain ⟨T, hT, hcard, -, -, -⟩ := exists_affineIndependent_openSimplex_subset
    (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 1 + 1)
    (0 : EuclideanSpace ℝ (Fin 2)) (Filter.univ_mem : _root_.Set.univ ∈ nhds (0 : EuclideanSpace ℝ (Fin 2)))
  have hC := (isPLBall_convexHull_of_affineIndependent T hT hcard).isPLSphere_frontier
  obtain ⟨u, hu⟩ := hS
  obtain ⟨v, hv⟩ := hC
  exact ⟨_, _, ⟨v, hv⟩, hu.symm.trans hv⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_planar_circle_coordinates
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.exists_planar_circle_coordinates target :: scope.openDecls } }

theorem exists_arc_decomposition_of_isPLSphere_one [FiniteDimensional ℝ E]
    {S : Set E} (hS : IsPLSphere 1 S) {p q : E} (hp : p ∈ S) (hq : q ∈ S) (hpq : p ≠ q) :
    ∃ (A B : Set E) (γ δ : ℝ → E),
      IsPLHomeomorphOn γ (_root_.Set.Icc 0 1) A ∧ IsPLHomeomorphOn δ (_root_.Set.Icc 0 1) B ∧
        γ 0 = p ∧ γ 1 = q ∧ δ 0 = p ∧ δ 1 = q ∧ A ∪ B = S ∧ A ∩ B = {p, q} := by
  obtain ⟨C, f, hC, hf⟩ := exists_planar_circle_coordinates hS
  let g := Function.invFunOn f S
  have hg : IsPLHomeomorphOn g C S := hf.symm
  obtain ⟨A, B, hcut, hA, hB⟩ := exists_isCutPair_isPLBall_of_isPLSphere_one hC
    (hf.bijOn.mapsTo hp) (hf.bijOn.mapsTo hq) (fun h => hpq (hf.bijOn.injOn hp hq h))
  obtain ⟨γ, hγ, hγ0, hγ1⟩ := exists_isPLHomeomorphOn_Icc_of_isArcBetween hA hcut.fst
  obtain ⟨δ, hδ, hδ0, hδ1⟩ := exists_isPLHomeomorphOn_Icc_of_isArcBetween hB hcut.snd
  have hgp : g (f p) = p := hf.bijOn.invOn_invFunOn.1 hp
  have hgq : g (f q) = q := hf.bijOn.invOn_invFunOn.1 hq
  refine ⟨g '' A, g '' B, g ∘ γ, g ∘ δ,
    hγ.trans (hg.restrict hA.isPolyhedron hcut.fst_subset),
    hδ.trans (hg.restrict hB.isPolyhedron hcut.snd_subset), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change g (γ 0) = p
    rw [hγ0, hgp]
  · change g (γ 1) = q
    rw [hγ1, hgq]
  · change g (δ 0) = p
    rw [hδ0, hgp]
  · change g (δ 1) = q
    rw [hδ1, hgq]
  · rw [← _root_.Set.image_union, hcut.union_eq, hg.image_eq]
  · rw [← hg.bijOn.injOn.image_inter hcut.fst_subset hcut.snd_subset,
      hcut.inter_eq, _root_.Set.image_pair, hgp, hgq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_arc_decomposition_of_isPLSphere_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_arc_decomposition_of_isPLSphere_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_arc_decomposition_of_isPLSphere_one ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_arc_decomposition_of_isPLSphere_one

theorem exists_isPLHomeomorphOn_Icc_inter_of_fiber_pair [FiniteDimensional ℝ E]
    {S : Set E} (hS : IsPLSphere 1 S) {ℓ : E → ℝ} (hℓ : ContinuousOn ℓ S)
    {r : ℝ} {p q : E} (hfiber : S ∩ {x | ℓ x = r} = {p, q}) (hpq : p ≠ q)
    (hpos : ∃ x ∈ S, r < ℓ x) (hneg : ∃ x ∈ S, ℓ x < r) :
    ∃ γ δ : ℝ → E,
      IsPLHomeomorphOn γ (_root_.Set.Icc 0 1) (S ∩ {x | r ≤ ℓ x}) ∧
        IsPLHomeomorphOn δ (_root_.Set.Icc 0 1) (S ∩ {x | ℓ x ≤ r}) ∧
        γ 0 = p ∧ γ 1 = q ∧ δ 0 = p ∧ δ 1 = q := by
  have hp := hfiber.symm.subset (show p ∈ ({p, q} : Set E) by simp)
  have hq := hfiber.symm.subset (show q ∈ ({p, q} : Set E) by simp)
  have hpr : ℓ p = r := hp.2
  have hqr : ℓ q = r := hq.2
  have hends : ∀ x ∈ ({p, q} : Set E), ℓ x = r := by
    rintro x (rfl | rfl)
    · exact hpr
    · exact hqr
  have hside {T : Set E} (hTS : T ⊆ S) (hconn : IsConnected (T \ {p, q})) :
      (∀ x ∈ T \ {p, q}, r < ℓ x) ∨ (∀ x ∈ T \ {p, q}, ℓ x < r) := by
    have himage := hconn.image ℓ (hℓ.mono (sdiff_subset.trans hTS))
    have hcover : ℓ '' (T \ {p, q}) ⊆ _root_.Set.Ioi r ∪ _root_.Set.Iio r := by
      rintro z ⟨x, hx, rfl⟩
      have hne : ℓ x ≠ r := fun h => hx.2 (hfiber.subset ⟨hTS hx.1, h⟩)
      exact (lt_or_gt_of_ne hne).symm
    have hsplit := IsPreconnected.subset_or_subset isOpen_Ioi isOpen_Iio
      (disjoint_left.mpr fun x hx hy => (lt_asymm hx hy)) hcover himage.isPreconnected
    exact hsplit.imp (fun h x hx => h ⟨x, hx, rfl⟩) (fun h x hx => h ⟨x, hx, rfl⟩)
  have finish {A B : Set E} {γ δ : ℝ → E}
      (hγ : IsPLHomeomorphOn γ (_root_.Set.Icc 0 1) A) (hδ : IsPLHomeomorphOn δ (_root_.Set.Icc 0 1) B)
      (hγ0 : γ 0 = p) (hγ1 : γ 1 = q) (hδ0 : δ 0 = p) (hδ1 : δ 1 = q)
      (hunion : A ∪ B = S)
      (hApos : ∀ x ∈ A \ {p, q}, r < ℓ x) (hBneg : ∀ x ∈ B \ {p, q}, ℓ x < r) :
      ∃ γ δ : ℝ → E,
        IsPLHomeomorphOn γ (_root_.Set.Icc 0 1) (S ∩ {x | r ≤ ℓ x}) ∧
          IsPLHomeomorphOn δ (_root_.Set.Icc 0 1) (S ∩ {x | ℓ x ≤ r}) ∧
          γ 0 = p ∧ γ 1 = q ∧ δ 0 = p ∧ δ 1 = q := by
    have hpqA : ({p, q} : Set E) ⊆ A := by
      refine _root_.Set.pair_subset ?_ ?_
      · exact hγ0 ▸ hγ.bijOn.mapsTo (show (0 : ℝ) ∈ _root_.Set.Icc 0 1 by norm_num)
      · exact hγ1 ▸ hγ.bijOn.mapsTo (show (1 : ℝ) ∈ _root_.Set.Icc 0 1 by norm_num)
    have hpqB : ({p, q} : Set E) ⊆ B := by
      refine _root_.Set.pair_subset ?_ ?_
      · exact hδ0 ▸ hδ.bijOn.mapsTo (show (0 : ℝ) ∈ _root_.Set.Icc 0 1 by norm_num)
      · exact hδ1 ▸ hδ.bijOn.mapsTo (show (1 : ℝ) ∈ _root_.Set.Icc 0 1 by norm_num)
    have hAeq : A = S ∩ {x | r ≤ ℓ x} := by
      ext x
      constructor
      · intro hx
        refine ⟨hunion.subset (Or.inl hx), ?_⟩
        by_cases hxends : x ∈ ({p, q} : Set E)
        · exact (hends x hxends).ge
        · exact (hApos x ⟨hx, hxends⟩).le
      · rintro ⟨hxS, hxℓ⟩
        rcases hunion.symm.subset hxS with hxA | hxB
        · exact hxA
        · by_cases hxends : x ∈ ({p, q} : Set E)
          · exact hpqA hxends
          · exact (not_lt_of_ge hxℓ (hBneg x ⟨hxB, hxends⟩)).elim
    have hBeq : B = S ∩ {x | ℓ x ≤ r} := by
      ext x
      constructor
      · intro hx
        refine ⟨hunion.subset (Or.inr hx), ?_⟩
        by_cases hxends : x ∈ ({p, q} : Set E)
        · exact (hends x hxends).le
        · exact (hBneg x ⟨hx, hxends⟩).le
      · rintro ⟨hxS, hxℓ⟩
        rcases hunion.symm.subset hxS with hxA | hxB
        · by_cases hxends : x ∈ ({p, q} : Set E)
          · exact hpqB hxends
          · exact (not_lt_of_ge hxℓ (hApos x ⟨hxA, hxends⟩)).elim
        · exact hxB
    exact ⟨γ, δ, hAeq ▸ hγ, hBeq ▸ hδ, hγ0, hγ1, hδ0, hδ1⟩
  obtain ⟨A, B, γ, δ, hγ, hδ, hγ0, hγ1, hδ0, hδ1, hunion, -⟩ :=
    exists_arc_decomposition_of_isPLSphere_one hS hp.1 hq.1 hpq
  have hconnA : IsConnected (A \ {p, q}) := by
    rw [← hγ0, ← hγ1]
    exact hγ.isConnected_sdiff_endpoints (by norm_num : (0 : ℝ) < 1)
  have hconnB : IsConnected (B \ {p, q}) := by
    rw [← hδ0, ← hδ1]
    exact hδ.isConnected_sdiff_endpoints (by norm_num : (0 : ℝ) < 1)
  rcases hside (subset_union_left.trans hunion.subset) hconnA with hApos | hAneg <;>
    rcases hside (subset_union_right.trans hunion.subset) hconnB with hBpos | hBneg
  · obtain ⟨x, hxS, hxlt⟩ := hneg
    have hxends : x ∉ ({p, q} : Set E) := fun h => hxlt.ne (hends x h)
    rcases hunion.symm.subset hxS with hxA | hxB
    · exact (lt_asymm (hApos x ⟨hxA, hxends⟩) hxlt).elim
    · exact (lt_asymm (hBpos x ⟨hxB, hxends⟩) hxlt).elim
  · exact finish hγ hδ hγ0 hγ1 hδ0 hδ1 hunion hApos hBneg
  · exact finish hδ hγ hδ0 hδ1 hγ0 hγ1 ((_root_.Set.union_comm B A).trans hunion) hBpos hAneg
  · obtain ⟨x, hxS, hxgt⟩ := hpos
    have hxends : x ∉ ({p, q} : Set E) := fun h => hxgt.ne' (hends x h)
    rcases hunion.symm.subset hxS with hxA | hxB
    · exact (lt_asymm hxgt (hAneg x ⟨hxA, hxends⟩)).elim
    · exact (lt_asymm hxgt (hBneg x ⟨hxB, hxends⟩)).elim

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_Icc_inter_of_fiber_pair then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_Icc_inter_of_fiber_pair"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_Icc_inter_of_fiber_pair ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_Icc_inter_of_fiber_pair

end DifferentialGeometry.Topology.PiecewiseLinear
