import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CollarInwardMap
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLPiece
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralSeparation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*}

noncomputable def bicollarInwardMap (g : E → ℝ) (a : ℝ) (x : E × ℝ) : E × ℝ :=
  (x.1, _root_.Max.max x.2 (_root_.Min.min (x.2 + g x.1) (_root_.Min.min ((x.2 + a) / 2) (2 * x.2 + a))))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.bicollarInwardMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.bicollarInwardMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.bicollarInwardMap ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.bicollarInwardMap

noncomputable def bicollarOutwardMap (g : E → ℝ) (a : ℝ) (x : E × ℝ) : E × ℝ :=
  (x.1, _root_.Min.min x.2 (_root_.Max.max (x.2 - g x.1) (_root_.Max.max (2 * x.2 - a) ((x.2 - a) / 2))))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.bicollarOutwardMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.bicollarOutwardMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.bicollarOutwardMap ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.bicollarOutwardMap

private theorem bicollar_height_le_iff (a u t s : ℝ) :
    _root_.Max.max t (_root_.Min.min (t + u) (_root_.Min.min ((t + a) / 2) (2 * t + a))) ≤ s ↔
      t ≤ _root_.Min.min s (_root_.Max.max (s - u) (_root_.Max.max (2 * s - a) ((s - a) / 2))) := by
  simp only [max_le_iff, min_le_iff, le_min_iff, le_max_iff]
  constructor
  · rintro ⟨h, h1 | h2 | h3⟩
    · exact ⟨h, Or.inl (by linarith)⟩
    · exact ⟨h, Or.inr (Or.inl (by linarith))⟩
    · exact ⟨h, Or.inr (Or.inr (by linarith))⟩
  · rintro ⟨h, h1 | h2 | h3⟩
    · exact ⟨h, Or.inl (by linarith)⟩
    · exact ⟨h, Or.inr (Or.inl (by linarith))⟩
    · exact ⟨h, Or.inr (Or.inr (by linarith))⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.bicollar_height_le_iff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.bicollar_height_le_iff target :: scope.openDecls } }

private theorem bicollar_height_lt_iff (a u t s : ℝ) :
    _root_.Max.max t (_root_.Min.min (t + u) (_root_.Min.min ((t + a) / 2) (2 * t + a))) < s ↔
      t < _root_.Min.min s (_root_.Max.max (s - u) (_root_.Max.max (2 * s - a) ((s - a) / 2))) := by
  simp only [max_lt_iff, min_lt_iff, lt_min_iff, lt_max_iff]
  constructor
  · rintro ⟨h, h1 | h2 | h3⟩
    · exact ⟨h, Or.inl (by linarith)⟩
    · exact ⟨h, Or.inr (Or.inl (by linarith))⟩
    · exact ⟨h, Or.inr (Or.inr (by linarith))⟩
  · rintro ⟨h, h1 | h2 | h3⟩
    · exact ⟨h, Or.inl (by linarith)⟩
    · exact ⟨h, Or.inr (Or.inl (by linarith))⟩
    · exact ⟨h, Or.inr (Or.inr (by linarith))⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.bicollar_height_lt_iff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.bicollar_height_lt_iff target :: scope.openDecls } }

theorem bicollarOutwardMap_bicollarInwardMap (g : E → ℝ) (a : ℝ) (x : E × ℝ) :
    bicollarOutwardMap g a (bicollarInwardMap g a x) = x := by
  refine Prod.ext rfl ?_
  apply le_antisymm
  · exact le_of_not_gt fun h =>
      (lt_irrefl _) ((bicollar_height_lt_iff a (g x.1) x.2 _).mpr h)
  · exact (bicollar_height_le_iff a (g x.1) x.2 _).mp le_rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.bicollarOutwardMap_bicollarInwardMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.bicollarOutwardMap_bicollarInwardMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.bicollarOutwardMap_bicollarInwardMap ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.bicollarOutwardMap_bicollarInwardMap

theorem bicollarInwardMap_bicollarOutwardMap (g : E → ℝ) (a : ℝ) (x : E × ℝ) :
    bicollarInwardMap g a (bicollarOutwardMap g a x) = x := by
  refine Prod.ext rfl ?_
  apply le_antisymm
  · exact (bicollar_height_le_iff a (g x.1) _ x.2).mpr le_rfl
  · exact le_of_not_gt fun h =>
      (lt_irrefl _) ((bicollar_height_lt_iff a (g x.1) _ x.2).mp h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.bicollarInwardMap_bicollarOutwardMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.bicollarInwardMap_bicollarOutwardMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.bicollarInwardMap_bicollarOutwardMap ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.bicollarInwardMap_bicollarOutwardMap

@[simp]
theorem bicollarInwardMap_fst (g : E → ℝ) (a : ℝ) (x : E × ℝ) :
    (bicollarInwardMap g a x).1 = x.1 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.bicollarInwardMap_fst then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.bicollarInwardMap_fst"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.bicollarInwardMap_fst ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.bicollarInwardMap_fst

theorem bicollarInwardMap_eq_self_of_le (g : E → ℝ) {a : ℝ} {x : E × ℝ}
    (hx : a ≤ x.2) : bicollarInwardMap g a x = x := by
  refine Prod.ext rfl ?_
  exact max_eq_left ((min_le_right _ _).trans ((min_le_left _ _).trans (by linarith)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.bicollarInwardMap_eq_self_of_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.bicollarInwardMap_eq_self_of_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.bicollarInwardMap_eq_self_of_le ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.bicollarInwardMap_eq_self_of_le

theorem bicollarInwardMap_eq_self_of_le_neg (g : E → ℝ) {a : ℝ} {x : E × ℝ}
    (hx : x.2 ≤ -a) : bicollarInwardMap g a x = x := by
  refine Prod.ext rfl ?_
  exact max_eq_left ((min_le_right _ _).trans ((min_le_right _ _).trans (by linarith)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.bicollarInwardMap_eq_self_of_le_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.bicollarInwardMap_eq_self_of_le_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.bicollarInwardMap_eq_self_of_le_neg ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.bicollarInwardMap_eq_self_of_le_neg

theorem bicollarInwardMap_eq_self_of_eq_zero {g : E → ℝ} (a : ℝ) {x : E × ℝ}
    (hx : g x.1 = 0) : bicollarInwardMap g a x = x := by
  refine Prod.ext rfl ?_
  change _root_.Max.max x.2 (_root_.Min.min (x.2 + g x.1) _) = x.2
  rw [hx, add_zero, max_eq_left (min_le_left _ _)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.bicollarInwardMap_eq_self_of_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.bicollarInwardMap_eq_self_of_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.bicollarInwardMap_eq_self_of_eq_zero ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.bicollarInwardMap_eq_self_of_eq_zero

theorem bicollarInwardMap_eq_self_of_le_abs (g : E → ℝ) {a : ℝ} {x : E × ℝ}
    (hx : a ≤ |x.2|) : bicollarInwardMap g a x = x := by
  rcases le_abs.mp hx with hx | hx
  · exact bicollarInwardMap_eq_self_of_le g hx
  · exact bicollarInwardMap_eq_self_of_le_neg g (by linarith)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.bicollarInwardMap_eq_self_of_le_abs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.bicollarInwardMap_eq_self_of_le_abs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.bicollarInwardMap_eq_self_of_le_abs ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.bicollarInwardMap_eq_self_of_le_abs

theorem bicollarInwardMap_eqOn (g : E → ℝ) (a : ℝ) :
    EqOn (bicollarInwardMap g a) id {x | g x.1 ≠ 0 ∧ |x.2| < a}ᶜ := by
  intro x hx
  by_cases hg : g x.1 = 0
  · exact bicollarInwardMap_eq_self_of_eq_zero a hg
  · exact bicollarInwardMap_eq_self_of_le_abs g (not_lt.mp fun ht => hx ⟨hg, ht⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.bicollarInwardMap_eqOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.bicollarInwardMap_eqOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.bicollarInwardMap_eqOn ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.bicollarInwardMap_eqOn

theorem le_bicollarInwardMap_snd (g : E → ℝ) (a : ℝ) (x : E × ℝ) :
    x.2 ≤ (bicollarInwardMap g a x).2 := le_max_left _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.le_bicollarInwardMap_snd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.le_bicollarInwardMap_snd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.le_bicollarInwardMap_snd ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.le_bicollarInwardMap_snd

theorem bicollarInwardMap_snd_pos {g : E → ℝ} {a : ℝ} (ha : 0 < a) {x : E × ℝ}
    (hx : 0 ≤ x.2) (hg : 0 < g x.1) : 0 < (bicollarInwardMap g a x).2 := by
  exact (lt_min (by linarith) (lt_min (by linarith) (by linarith))).trans_le
    (le_max_right _ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.bicollarInwardMap_snd_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.bicollarInwardMap_snd_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.bicollarInwardMap_snd_pos ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.bicollarInwardMap_snd_pos

theorem bicollarInwardMap_snd_eq_zero_iff {g : E → ℝ} {a : ℝ} (ha : 0 < a)
    {x : E × ℝ} (hg : 0 ≤ g x.1) (hx : 0 ≤ x.2) :
    (bicollarInwardMap g a x).2 = 0 ↔ x.2 = 0 ∧ g x.1 = 0 := by
  constructor
  · intro h
    refine ⟨le_antisymm (h ▸ le_bicollarInwardMap_snd g a x) hx, ?_⟩
    by_contra hne
    have := bicollarInwardMap_snd_pos ha hx (lt_of_le_of_ne hg (Ne.symm hne))
    rw [h] at this
    exact (lt_irrefl _) this
  · rintro ⟨ht, hg⟩
    rw [bicollarInwardMap_eq_self_of_eq_zero a hg, ht]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.bicollarInwardMap_snd_eq_zero_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.bicollarInwardMap_snd_eq_zero_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.bicollarInwardMap_snd_eq_zero_iff ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.bicollarInwardMap_snd_eq_zero_iff

theorem bicollarInwardMap_mapsTo_prod_Icc (g : E → ℝ) {a b c : ℝ} (hab : a ≤ b)
    (B : Set E) : _root_.Set.MapsTo (bicollarInwardMap g a) (B ×ˢ _root_.Set.Icc c b) (B ×ˢ _root_.Set.Icc c b) := by
  intro x hx
  refine ⟨hx.1, hx.2.1.trans (le_bicollarInwardMap_snd g a x), ?_⟩
  exact max_le hx.2.2 ((min_le_right _ _).trans
    ((min_le_left _ _).trans (by linarith [hx.2.2])))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.bicollarInwardMap_mapsTo_prod_Icc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.bicollarInwardMap_mapsTo_prod_Icc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.bicollarInwardMap_mapsTo_prod_Icc ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.bicollarInwardMap_mapsTo_prod_Icc

theorem bicollarOutwardMap_mapsTo_prod_Icc (g : E → ℝ) {a b c : ℝ} (hac : c ≤ -a)
    (B : Set E) : _root_.Set.MapsTo (bicollarOutwardMap g a) (B ×ˢ _root_.Set.Icc c b) (B ×ˢ _root_.Set.Icc c b) := by
  intro x hx
  refine ⟨hx.1, ?_, (min_le_left _ _).trans hx.2.2⟩
  apply (bicollar_height_le_iff a (g x.1) c x.2).mp
  change (bicollarInwardMap g a (x.1, c)).2 ≤ x.2
  rw [bicollarInwardMap_eq_self_of_le_neg g hac]
  exact hx.2.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.bicollarOutwardMap_mapsTo_prod_Icc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.bicollarOutwardMap_mapsTo_prod_Icc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.bicollarOutwardMap_mapsTo_prod_Icc ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.bicollarOutwardMap_mapsTo_prod_Icc

noncomputable def bicollarInwardHomeomorph [TopologicalSpace E] {g : E → ℝ}
    (hg : Continuous g) (a : ℝ) : (E × ℝ) ≃ₜ (E × ℝ) where
  toFun := bicollarInwardMap g a
  invFun := bicollarOutwardMap g a
  left_inv := bicollarOutwardMap_bicollarInwardMap g a
  right_inv := bicollarInwardMap_bicollarOutwardMap g a
  continuous_toFun := by unfold bicollarInwardMap; fun_prop
  continuous_invFun := by unfold bicollarOutwardMap; fun_prop

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.bicollarInwardHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.bicollarInwardHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.bicollarInwardHomeomorph ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.bicollarInwardHomeomorph

theorem isPiecewiseAffineOn_bicollarInwardMap [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {g : E → ℝ} (hg : IsPiecewiseAffineOn g _root_.Set.univ) (a : ℝ) :
    IsPiecewiseAffineOn (bicollarInwardMap g a) univ := by
  have hfst : IsPiecewiseAffineOn (Prod.fst : E × ℝ → E) univ :=
    isPiecewiseAffineOn_of_affine (LinearMap.fst ℝ E ℝ).toAffineMap isOpen_univ
  have hsnd : IsPiecewiseAffineOn (Prod.snd : E × ℝ → ℝ) univ :=
    isPiecewiseAffineOn_of_affine (LinearMap.snd ℝ E ℝ).toAffineMap isOpen_univ
  have hgfst : IsPiecewiseAffineOn (fun x : E × ℝ => g x.1) univ := by
    simpa only [_root_.Set.preimage_univ, _root_.Set.inter_univ, Function.comp_def] using hg.comp hfst
  let A : (E × ℝ) →ᵃ[ℝ] ℝ :=
    (1 / 2 : ℝ) • ((LinearMap.snd ℝ E ℝ).toAffineMap + AffineMap.const ℝ (E × ℝ) a)
  have hA : IsPiecewiseAffineOn (fun x : E × ℝ => (x.2 + a) / 2) univ := by
    convert isPiecewiseAffineOn_of_affine A isOpen_univ using 1
    ext x
    change (x.2 + a) / 2 = (1 / 2 : ℝ) * (x.2 + a)
    ring
  let B : (E × ℝ) →ᵃ[ℝ] ℝ :=
    (2 : ℝ) • (LinearMap.snd ℝ E ℝ).toAffineMap + AffineMap.const ℝ (E × ℝ) a
  have hB : IsPiecewiseAffineOn (fun x : E × ℝ => 2 * x.2 + a) univ :=
    isPiecewiseAffineOn_of_affine B isOpen_univ
  exact hfst.prod_mk (hsnd.max ((hsnd.add hgfst).min (hA.min hB)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_bicollarInwardMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_bicollarInwardMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_bicollarInwardMap ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_bicollarInwardMap

theorem isPLHomeomorphOn_bicollarInwardMap [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {g : E → ℝ} (hg : IsPiecewiseAffineOn g _root_.Set.univ) (a : ℝ) :
    IsPLHomeomorphOn (bicollarInwardMap g a) _root_.Set.univ univ := by
  let H := bicollarInwardHomeomorph (continuousOn_univ.mp hg.continuousOn) a
  have hpl : IsPiecewiseAffineOn H univ := isPiecewiseAffineOn_bicollarInwardMap hg a
  have hinv : IsPiecewiseAffineOn H.symm univ :=
    IsPiecewiseAffineOn.symm (e := H.toOpenPartialHomeomorph) hpl
  have hbij : _root_.Set.BijOn H _root_.Set.univ univ :=
    ⟨mapsTo_univ _ _, H.injective.injOn, fun y _ =>
      ⟨H.symm y, _root_.Set.mem_univ _, H.apply_symm_apply y⟩⟩
  refine ⟨hbij, hpl, hinv.congr fun y hy => ?_⟩
  apply H.injective
  exact (hbij.invOn_invFunOn.2 hy).trans (H.apply_symm_apply y).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_bicollarInwardMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_bicollarInwardMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_bicollarInwardMap ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_bicollarInwardMap

open _root_.Classical in
theorem IsPLHomeomorphOn.exists_relative_bicollar_inward_below [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {B W R A : Set E} {ρ : E × ℝ → E}
    (hρ : IsPLHomeomorphOn ρ (B ×ˢ _root_.Set.Icc (-1 : ℝ) 1) W)
    (hW : IsPolyhedron W) (hR : IsPolyhedron R) (hBR : Disjoint B R)
    (hbottom : ∀ x ∈ B, ρ (x, 0) = x) (hA : IsPolyhedron A) (hAB : A ⊆ B)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ f : E → E, IsPLHomeomorphOn f (W ∪ R) (W ∪ R) ∧ _root_.Set.EqOn f id (A ∪ R) ∧
      _root_.Set.MapsTo f (ρ '' (B ×ˢ _root_.Set.Icc (0 : ℝ) 1)) (ρ '' (B ×ˢ _root_.Set.Icc (0 : ℝ) 1)) ∧
      (∀ x ∈ ρ '' (B ×ˢ _root_.Set.Icc (0 : ℝ) 1), f x ∈ B ↔ x ∈ A) ∧
      _root_.Set.EqOn f id (ρ '' (A ×ˢ _root_.Set.Icc (-1 : ℝ) 1)) ∧ _root_.Set.EqOn f id Wᶜ ∧
      ∀ x ∈ W, δ ≤ |(Function.invFunOn ρ (B ×ˢ _root_.Set.Icc (-1 : ℝ) 1) x).2| → f x = x := by
  let U := B ×ˢ _root_.Set.Icc (-1 : ℝ) 1
  let τ := Function.invFunOn ρ U
  have hτ : _root_.Set.MapsTo τ W U := hρ.symm.bijOn.mapsTo
  have hleft : _root_.Set.LeftInvOn τ ρ U := hρ.bijOn.invOn_invFunOn.1
  have hright : _root_.Set.RightInvOn τ ρ W := hρ.bijOn.invOn_invFunOn.2
  have hBW : B ⊆ W := fun x hx =>
    hbottom x hx ▸ hρ.bijOn.mapsTo ⟨hx, by norm_num, by norm_num⟩
  have hτbottom : ∀ x ∈ B, τ x = (x, 0) := by
    intro x hx
    have h : τ (ρ (x, 0)) = (x, 0) := hleft ⟨hx, by norm_num, by norm_num⟩
    rwa [hbottom x hx] at h
  have hboundary : ∀ z ∈ U, ρ z ∈ B ↔ z.2 = 0 := by
    intro z hz
    constructor
    · intro hB
      have heq : z = (ρ z, 0) := hρ.bijOn.injOn hz
        ⟨hB, by norm_num, by norm_num⟩ (hbottom _ hB).symm
      exact congrArg Prod.snd heq
    · intro hzero
      rw [show z = (z.1, 0) from Prod.ext rfl hzero, hbottom _ hz.1]
      exact hz.1
  have hheight : ∀ x ∈ W ∩ R, 0 < |(τ x).2| := by
    intro x hx
    apply abs_pos.mpr
    intro hzero
    have hxB : x ∈ B := by
      rw [← hright hx.1]
      exact (hboundary _ (hτ hx.1)).mpr hzero
    exact Set.disjoint_left.mp hBR hxB hx.2
  obtain ⟨r, hr, hrheight⟩ :
      ∃ r : ℝ, 0 < r ∧ ∀ x ∈ W ∩ R, r ≤ |(τ x).2| := by
    by_cases hne : (W ∩ R).Nonempty
    · obtain ⟨x, hx, hmin⟩ := (hW.isCompact.inter_right hR.isClosed).exists_isMinOn hne
        (hρ.isPiecewiseAffineOn_invFunOn.continuousOn.snd.abs.mono _root_.Set.inter_subset_left)
      exact ⟨|(τ x).2|, hheight x hx, fun y hy => hmin hy⟩
    · exact ⟨1, zero_lt_one, fun x hx => False.elim (hne ⟨x, hx⟩)⟩
  let a := _root_.Min.min r (_root_.Min.min δ 1)
  have ha : 0 < a := lt_min hr (lt_min hδ zero_lt_one)
  have haone : a ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  have haδ : a ≤ δ := (min_le_right _ _).trans (min_le_left _ _)
  have hthin : ∀ x ∈ W ∩ R, a ≤ |(τ x).2| :=
    fun x hx => (min_le_left _ _).trans (hrheight x hx)
  obtain ⟨g, hg, hgpos, hgzero⟩ := hA.exists_nonneg_piecewiseAffine_zero_set
  let H := bicollarInwardMap g a
  let J := bicollarOutwardMap g a
  have hHU : _root_.Set.MapsTo H U U := bicollarInwardMap_mapsTo_prod_Icc g haone B
  have hJU : _root_.Set.MapsTo J U U := bicollarOutwardMap_mapsTo_prod_Icc g (by linarith) B
  let Q : E → E := ρ ∘ H ∘ τ
  have hQW : _root_.Set.MapsTo Q W W := hρ.bijOn.mapsTo.comp (hHU.comp hτ)
  have hQpl : IsPiecewiseAffineOn Q W := by
    have hHτ : IsPiecewiseAffineOn (H ∘ τ) W := by
      have h := (isPiecewiseAffineOn_bicollarInwardMap hg a).comp
        hρ.isPiecewiseAffineOn_invFunOn
      simpa only [_root_.Set.preimage_univ, _root_.Set.inter_univ] using h
    have h := hρ.isPiecewiseAffineOn.comp hHτ
    have hinter : W ∩ (H ∘ τ) ⁻¹' U = W := inter_eq_left.mpr (hHU.comp hτ)
    rwa [hinter] at h
  have hQbij : _root_.Set.BijOn Q W W := by
    refine ⟨hQW, ?_, ?_⟩
    · intro x hx y hy hxy
      apply hρ.symm.bijOn.injOn hx hy
      have h := hρ.bijOn.injOn (hHU (hτ hx)) (hHU (hτ hy)) hxy
      have := congrArg J h
      simpa only [J, H, bicollarOutwardMap_bicollarInwardMap] using this
    · intro y hy
      refine ⟨ρ (J (τ y)), hρ.bijOn.mapsTo (hJU (hτ hy)), ?_⟩
      change ρ (H (τ (ρ (J (τ y))))) = y
      rw [hleft (hJU (hτ hy))]
      exact (congrArg ρ (bicollarInwardMap_bicollarOutwardMap g a (τ y))).trans
        (hright hy)
  have hQR : _root_.Set.EqOn Q id (W ∩ R) := by
    intro x hx
    change ρ (bicollarInwardMap g a (τ x)) = x
    rw [bicollarInwardMap_eq_self_of_le_abs g (hthin x hx)]
    exact hright hx.1
  have hQA : _root_.Set.EqOn Q id A := by
    intro x hx
    change ρ (bicollarInwardMap g a (τ x)) = x
    rw [hτbottom x (hAB hx), bicollarInwardMap_eq_self_of_eq_zero a ((hgzero x).mpr hx)]
    exact hbottom x (hAB hx)
  let f := W.piecewise Q id
  have hfW : _root_.Set.EqOn f Q W := W.piecewise_eqOn Q id
  have hfR : _root_.Set.EqOn f id R := by
    intro x hx
    by_cases hxW : x ∈ W
    · rw [hfW hxW]
      exact hQR ⟨hxW, hx⟩
    · exact _root_.Set.piecewise_eq_of_notMem W Q id hxW
  have hQhomeo := isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hW hQpl hQbij
  have hf : IsPLHomeomorphOn f (W ∪ R) (W ∪ R) :=
    hQhomeo.piecewise hR.isPLHomeomorphOn_id hW hR hQR
      (hQR.image_eq.trans (_root_.Set.image_id _))
  have hhalf : B ×ˢ _root_.Set.Icc (0 : ℝ) 1 ⊆ U :=
    fun z hz => ⟨hz.1, (by linarith [hz.2.1]), hz.2.2⟩
  refine ⟨f, hf, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rcases hx with hx | hx
    · rw [hfW (hBW (hAB hx))]
      exact hQA hx
    · exact hfR hx
  · rintro _ ⟨z, hz, rfl⟩
    rw [hfW (hρ.bijOn.mapsTo (hhalf hz))]
    change ρ (H (τ (ρ z))) ∈ ρ '' (B ×ˢ _root_.Set.Icc (0 : ℝ) 1)
    rw [hleft (hhalf hz)]
    exact ⟨H z, bicollarInwardMap_mapsTo_prod_Icc g haone B hz, rfl⟩
  · rintro _ ⟨z, hz, rfl⟩
    rw [hfW (hρ.bijOn.mapsTo (hhalf hz))]
    change ρ (H (τ (ρ z))) ∈ B ↔ ρ z ∈ A
    rw [hleft (hhalf hz), hboundary _ (hHU (hhalf hz))]
    rw [bicollarInwardMap_snd_eq_zero_iff ha (hgpos _) hz.2.1]
    constructor
    · rintro ⟨ht, hgz⟩
      rw [show z = (z.1, 0) from Prod.ext rfl ht, hbottom _ hz.1]
      exact (hgzero _).mp hgz
    · intro hzA
      have ht := (hboundary z (hhalf hz)).mp (hAB hzA)
      refine ⟨ht, (hgzero _).mpr ?_⟩
      rwa [show z = (z.1, 0) from Prod.ext rfl ht, hbottom _ hz.1] at hzA
  · rintro _ ⟨z, hz, rfl⟩
    have hzU : z ∈ U := ⟨hAB hz.1, hz.2⟩
    rw [hfW (hρ.bijOn.mapsTo hzU)]
    change ρ (H (τ (ρ z))) = ρ z
    rw [hleft hzU]
    exact congrArg ρ (bicollarInwardMap_eq_self_of_eq_zero a ((hgzero _).mpr hz.1))
  · intro x hx
    exact _root_.Set.piecewise_eq_of_notMem W Q id hx
  · intro x hx hheight
    rw [hfW hx]
    change ρ (bicollarInwardMap g a (τ x)) = x
    rw [bicollarInwardMap_eq_self_of_le_abs g (haδ.trans hheight)]
    exact hright hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.exists_relative_bicollar_inward_below then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.exists_relative_bicollar_inward_below"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.exists_relative_bicollar_inward_below ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.exists_relative_bicollar_inward_below

theorem IsPLHomeomorphOn.exists_relative_bicollar_inward [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {B W R A : Set E} {ρ : E × ℝ → E}
    (hρ : IsPLHomeomorphOn ρ (B ×ˢ _root_.Set.Icc (-1 : ℝ) 1) W)
    (hW : IsPolyhedron W) (hR : IsPolyhedron R) (hBR : Disjoint B R)
    (hbottom : ∀ x ∈ B, ρ (x, 0) = x) (hA : IsPolyhedron A) (hAB : A ⊆ B) :
    ∃ f : E → E, IsPLHomeomorphOn f (W ∪ R) (W ∪ R) ∧ _root_.Set.EqOn f id (A ∪ R) ∧
      _root_.Set.MapsTo f (ρ '' (B ×ˢ _root_.Set.Icc (0 : ℝ) 1)) (ρ '' (B ×ˢ _root_.Set.Icc (0 : ℝ) 1)) ∧
      (∀ x ∈ ρ '' (B ×ˢ _root_.Set.Icc (0 : ℝ) 1), f x ∈ B ↔ x ∈ A) ∧
      EqOn f id (ρ '' (A ×ˢ _root_.Set.Icc (-1 : ℝ) 1)) ∧ _root_.Set.EqOn f id Wᶜ := by
  obtain ⟨f, hf, hfix, hmap, hB, hfib, hoff, -⟩ :=
    hρ.exists_relative_bicollar_inward_below hW hR hBR hbottom hA hAB zero_lt_one
  exact ⟨f, hf, hfix, hmap, hB, hfib, hoff⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.exists_relative_bicollar_inward then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.exists_relative_bicollar_inward"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.exists_relative_bicollar_inward ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.exists_relative_bicollar_inward

end DifferentialGeometry.Topology.PiecewiseLinear
