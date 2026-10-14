import Submission.DifferentialGeometry.Topology.Handle.CylinderCorner
import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Submission.DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph
import Submission.DifferentialGeometry.Topology.Manifold.InverseFunction.ContDiffOn

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Metric
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold

namespace EuclideanGeometry

variable {E : Type*} [NormedAddCommGroup E]

noncomputable def halfBallCylinderMap [NormedSpace ℝ E] (p : E × ℝ) : E × ℝ :=
  (Real.sqrt (1 + p.2 ^ 2 / Real.smoothMax (1 / 4) (1 / 2) (‖p.1‖ ^ 2)) • p.1, p.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `EuclideanGeometry.halfBallCylinderMap then
    throwError "Refusing to shadow existing declaration EuclideanGeometry.halfBallCylinderMap"
  Lean.modifyEnv fun env => Lean.addAlias env `EuclideanGeometry.halfBallCylinderMap ``Submission.EuclideanGeometry.halfBallCylinderMap

private theorem halfBallCylinder_denominator_pos (x : E) :
    0 < Real.smoothMax (1 / 4) (1 / 2) (‖x‖ ^ 2) :=
  (by norm_num : (0 : ℝ) < 1 / 2).trans_le
    ((le_max_left _ _).trans (Real.smoothMax.max_le (by norm_num) _ _))

run_cmd do
  let target := ``Submission.EuclideanGeometry.halfBallCylinder_denominator_pos
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `EuclideanGeometry.halfBallCylinder_denominator_pos target :: scope.openDecls } }

theorem contDiff_halfBallCylinderMap [InnerProductSpace ℝ E] :
    ContDiff ℝ ∞ (halfBallCylinderMap (E := E)) := by
  have hden : ContDiff ℝ ∞ (fun p : E × ℝ => Real.smoothMax (1 / 4) (1 / 2) (‖p.1‖ ^ 2)) :=
    (Real.smoothMax.contDiff _).comp (contDiff_const.prodMk ((contDiff_norm_sq ℝ).comp contDiff_fst))
  exact (((contDiff_const.add ((contDiff_snd.pow 2).div hden
    (fun p => (halfBallCylinder_denominator_pos p.1).ne'))).sqrt (fun p => by
      change 1 + p.2 ^ 2 / Real.smoothMax (1 / 4) (1 / 2) (‖p.1‖ ^ 2) ≠ 0
      have := div_nonneg (sq_nonneg p.2) (halfBallCylinder_denominator_pos p.1).le
      linarith)).smul contDiff_fst).prodMk contDiff_snd

run_cmd do
  let env ← Lean.getEnv
  if env.contains `EuclideanGeometry.contDiff_halfBallCylinderMap then
    throwError "Refusing to shadow existing declaration EuclideanGeometry.contDiff_halfBallCylinderMap"
  Lean.modifyEnv fun env => Lean.addAlias env `EuclideanGeometry.contDiff_halfBallCylinderMap ``Submission.EuclideanGeometry.contDiff_halfBallCylinderMap

@[simp] theorem halfBallCylinderMap_apply_zero [NormedSpace ℝ E] (x : E) :
    halfBallCylinderMap (x, 0) = (x, 0) := by
  simp [halfBallCylinderMap]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `EuclideanGeometry.halfBallCylinderMap_apply_zero then
    throwError "Refusing to shadow existing declaration EuclideanGeometry.halfBallCylinderMap_apply_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `EuclideanGeometry.halfBallCylinderMap_apply_zero ``Submission.EuclideanGeometry.halfBallCylinderMap_apply_zero

theorem hasFDerivAt_halfBallCylinderMap_zero [InnerProductSpace ℝ E] (x : E) :
    HasFDerivAt halfBallCylinderMap (ContinuousLinearMap.id ℝ (E × ℝ)) (x, 0) := by
  let d : E × ℝ → ℝ := fun p => Real.smoothMax (1 / 4) (1 / 2) (‖p.1‖ ^ 2)
  have hd : ContDiff ℝ ∞ d :=
    (Real.smoothMax.contDiff _).comp (contDiff_const.prodMk ((contDiff_norm_sq ℝ).comp contDiff_fst))
  have ht : HasFDerivAt (𝕜 := ℝ) (fun p : E × ℝ => p.2 ^ 2) (0 : (E × ℝ) →L[ℝ] ℝ) (x, 0) := by
    simpa using ((hasFDerivAt_snd (𝕜 := ℝ) (p := (x, (0 : ℝ)))).pow 2)
  have hdi := (((hd.inv (fun p => (halfBallCylinder_denominator_pos p.1).ne')).differentiable
    (by simp)) (x, 0)).hasFDerivAt
  have hratio : HasFDerivAt (𝕜 := ℝ) (fun p : E × ℝ => p.2 ^ 2 / d p)
      (0 : (E × ℝ) →L[ℝ] ℝ) (x, 0) := by
    convert! ht.mul hdi using 1
    simp
  have hsum : HasFDerivAt (𝕜 := ℝ) (fun p : E × ℝ => 1 + p.2 ^ 2 / d p)
      (0 : (E × ℝ) →L[ℝ] ℝ) (x, 0) := by
    convert! (hasFDerivAt_const (1 : ℝ) (x, (0 : ℝ))).add hratio using 1
    simp
  have hsqrt : HasFDerivAt (𝕜 := ℝ) (fun p : E × ℝ => Real.sqrt (1 + p.2 ^ 2 / d p))
      (0 : (E × ℝ) →L[ℝ] ℝ) (x, 0) := by
    convert! hsum.sqrt (by simp) using 1
    simp
  convert! (hsqrt.smul (hasFDerivAt_fst (𝕜 := ℝ) (p := (x, (0 : ℝ))))).prodMk
    (hasFDerivAt_snd (𝕜 := ℝ) (p := (x, (0 : ℝ)))) using 1
  simp [d]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `EuclideanGeometry.hasFDerivAt_halfBallCylinderMap_zero then
    throwError "Refusing to shadow existing declaration EuclideanGeometry.hasFDerivAt_halfBallCylinderMap_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `EuclideanGeometry.hasFDerivAt_halfBallCylinderMap_zero ``Submission.EuclideanGeometry.hasFDerivAt_halfBallCylinderMap_zero

theorem norm_sq_halfBallCylinderMap_fst [NormedSpace ℝ E] (p : E × ℝ) :
    ‖(halfBallCylinderMap p).1‖ ^ 2 =
      (1 + p.2 ^ 2 / Real.smoothMax (1 / 4) (1 / 2) (‖p.1‖ ^ 2)) * ‖p.1‖ ^ 2 := by
  rw [halfBallCylinderMap, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt]
  have := div_nonneg (sq_nonneg p.2) (halfBallCylinder_denominator_pos p.1).le
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `EuclideanGeometry.norm_sq_halfBallCylinderMap_fst then
    throwError "Refusing to shadow existing declaration EuclideanGeometry.norm_sq_halfBallCylinderMap_fst"
  Lean.modifyEnv fun env => Lean.addAlias env `EuclideanGeometry.norm_sq_halfBallCylinderMap_fst ``Submission.EuclideanGeometry.norm_sq_halfBallCylinderMap_fst

theorem halfBallCylinderMap_eq_of_norm_sq_ge [NormedSpace ℝ E]
    {p : E × ℝ} (hp : 3 / 4 ≤ ‖p.1‖ ^ 2) :
    halfBallCylinderMap p = (Real.sqrt (1 + p.2 ^ 2 / ‖p.1‖ ^ 2) • p.1, p.2) := by
  have hm : Real.smoothMax (1 / 4) (1 / 2) (‖p.1‖ ^ 2) = ‖p.1‖ ^ 2 := by
    rw [Real.smoothMax.eq_max_of_le (by norm_num), max_eq_right (by linarith)]
    rw [abs_of_nonpos (by linarith)]
    linarith
  simp only [halfBallCylinderMap, hm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `EuclideanGeometry.halfBallCylinderMap_eq_of_norm_sq_ge then
    throwError "Refusing to shadow existing declaration EuclideanGeometry.halfBallCylinderMap_eq_of_norm_sq_ge"
  Lean.modifyEnv fun env => Lean.addAlias env `EuclideanGeometry.halfBallCylinderMap_eq_of_norm_sq_ge ``Submission.EuclideanGeometry.halfBallCylinderMap_eq_of_norm_sq_ge

private theorem halfBallCylinderMap_norm_sq_bounds [NormedSpace ℝ E]
    {p : E × ℝ} (hp : |p.2| < 1 / 4) :
    ‖(halfBallCylinderMap p).1‖ ^ 2 = ‖p.1‖ ^ 2 + p.2 ^ 2 ∨
      (‖(halfBallCylinderMap p).1‖ ^ 2 < 1 ∧ ‖p.1‖ ^ 2 + p.2 ^ 2 < 1) := by
  have ht : p.2 ^ 2 < 1 / 16 := by
    obtain ⟨hl, hu⟩ := abs_lt.mp hp
    nlinarith
  have hs : 0 ≤ ‖p.1‖ ^ 2 := sq_nonneg _
  by_cases hlarge : 3 / 4 ≤ ‖p.1‖ ^ 2
  · left
    rw [halfBallCylinderMap_eq_of_norm_sq_ge hlarge, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      Real.sq_sqrt (by have := div_nonneg (sq_nonneg p.2) hs; linarith)]
    have hn : ‖p.1‖ ^ 2 ≠ 0 := by linarith
    rw [add_mul, one_mul, div_mul_cancel₀ _ hn]
  · have hsmall : ‖p.1‖ ^ 2 < 3 / 4 := lt_of_not_ge hlarge
    have hden : 1 / 2 ≤ Real.smoothMax (1 / 4) (1 / 2) (‖p.1‖ ^ 2) :=
      (le_max_left _ _).trans (Real.smoothMax.max_le (by norm_num) _ _)
    have hratio : p.2 ^ 2 / Real.smoothMax (1 / 4) (1 / 2) (‖p.1‖ ^ 2) < 1 / 8 := by
      apply (div_lt_iff₀ (halfBallCylinder_denominator_pos p.1)).mpr
      nlinarith
    have hnew : ‖(halfBallCylinderMap p).1‖ ^ 2 < 1 := by
      rw [norm_sq_halfBallCylinderMap_fst]
      nlinarith
    exact Or.inr ⟨hnew, by linarith⟩

run_cmd do
  let target := ``Submission.EuclideanGeometry.halfBallCylinderMap_norm_sq_bounds
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `EuclideanGeometry.halfBallCylinderMap_norm_sq_bounds target :: scope.openDecls } }

theorem halfBallCylinderMap_norm_sq_le_iff [NormedSpace ℝ E]
    {p : E × ℝ} (hp : |p.2| < 1 / 4) :
    ‖(halfBallCylinderMap p).1‖ ^ 2 ≤ 1 ↔ ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ 1 := by
  rcases halfBallCylinderMap_norm_sq_bounds hp with h | ⟨hl, hr⟩
  · rw [h]
  · exact iff_of_true hl.le hr.le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `EuclideanGeometry.halfBallCylinderMap_norm_sq_le_iff then
    throwError "Refusing to shadow existing declaration EuclideanGeometry.halfBallCylinderMap_norm_sq_le_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `EuclideanGeometry.halfBallCylinderMap_norm_sq_le_iff ``Submission.EuclideanGeometry.halfBallCylinderMap_norm_sq_le_iff

theorem halfBallCylinderMap_norm_sq_lt_iff [NormedSpace ℝ E]
    {p : E × ℝ} (hp : |p.2| < 1 / 4) :
    ‖(halfBallCylinderMap p).1‖ ^ 2 < 1 ↔ ‖p.1‖ ^ 2 + p.2 ^ 2 < 1 := by
  rcases halfBallCylinderMap_norm_sq_bounds hp with h | ⟨hl, hr⟩
  · rw [h]
  · exact iff_of_true hl hr

run_cmd do
  let env ← Lean.getEnv
  if env.contains `EuclideanGeometry.halfBallCylinderMap_norm_sq_lt_iff then
    throwError "Refusing to shadow existing declaration EuclideanGeometry.halfBallCylinderMap_norm_sq_lt_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `EuclideanGeometry.halfBallCylinderMap_norm_sq_lt_iff ``Submission.EuclideanGeometry.halfBallCylinderMap_norm_sq_lt_iff

theorem halfBallCylinderMap_norm_sq_ge_iff [NormedSpace ℝ E]
    {p : E × ℝ} (hp : |p.2| < 1 / 4) :
    1 ≤ ‖(halfBallCylinderMap p).1‖ ^ 2 ↔ 1 ≤ ‖p.1‖ ^ 2 + p.2 ^ 2 := by
  simpa only [not_lt] using (halfBallCylinderMap_norm_sq_lt_iff hp).not

run_cmd do
  let env ← Lean.getEnv
  if env.contains `EuclideanGeometry.halfBallCylinderMap_norm_sq_ge_iff then
    throwError "Refusing to shadow existing declaration EuclideanGeometry.halfBallCylinderMap_norm_sq_ge_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `EuclideanGeometry.halfBallCylinderMap_norm_sq_ge_iff ``Submission.EuclideanGeometry.halfBallCylinderMap_norm_sq_ge_iff

theorem halfBallCylinderMap_norm_sq_eq_iff [NormedSpace ℝ E]
    {p : E × ℝ} (hp : |p.2| < 1 / 4) :
    ‖(halfBallCylinderMap p).1‖ ^ 2 = 1 ↔ ‖p.1‖ ^ 2 + p.2 ^ 2 = 1 := by
  rw [le_antisymm_iff, le_antisymm_iff, halfBallCylinderMap_norm_sq_le_iff hp,
    halfBallCylinderMap_norm_sq_ge_iff hp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `EuclideanGeometry.halfBallCylinderMap_norm_sq_eq_iff then
    throwError "Refusing to shadow existing declaration EuclideanGeometry.halfBallCylinderMap_norm_sq_eq_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `EuclideanGeometry.halfBallCylinderMap_norm_sq_eq_iff ``Submission.EuclideanGeometry.halfBallCylinderMap_norm_sq_eq_iff

theorem halfBallCylinderMap_mem_cylinder_iff [NormedSpace ℝ E]
    {p : E × ℝ} (hp : |p.2| < 1 / 4) :
    (‖(halfBallCylinderMap p).1‖ ^ 2 ≤ 1 ∧ 0 ≤ (halfBallCylinderMap p).2) ↔
      ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ 1 ∧ 0 ≤ p.2 :=
  (halfBallCylinderMap_norm_sq_le_iff hp).and Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `EuclideanGeometry.halfBallCylinderMap_mem_cylinder_iff then
    throwError "Refusing to shadow existing declaration EuclideanGeometry.halfBallCylinderMap_mem_cylinder_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `EuclideanGeometry.halfBallCylinderMap_mem_cylinder_iff ``Submission.EuclideanGeometry.halfBallCylinderMap_mem_cylinder_iff

theorem cylinderCorner_halfBallCylinderMap [InnerProductSpace ℝ E]
    {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]
    (v : _root_.Metric.sphere (0 : E) 1) {p : E × ℝ} (hp : 3 / 4 ≤ ‖p.1‖ ^ 2) :
    PartialDiffeomorph.cylinderCorner (n := n) 1 v (halfBallCylinderMap p) =
      PartialDiffeomorph.halfBallCorner (n := n) 1 v p := by
  have hs : 0 < ‖p.1‖ ^ 2 := by linarith
  have hx : p.1 ≠ 0 := by intro hh; simp [hh] at hp; norm_num at hp
  let k := Real.sqrt (1 + p.2 ^ 2 / ‖p.1‖ ^ 2)
  have hk : 0 < k := Real.sqrt_pos.mpr (by have := div_nonneg (sq_nonneg p.2) hs.le; linarith)
  have hnorm : ‖(halfBallCylinderMap p).1‖ ^ 2 = ‖p.1‖ ^ 2 + p.2 ^ 2 := by
    rw [halfBallCylinderMap_eq_of_norm_sq_ge hp, norm_smul, Real.norm_eq_abs,
      abs_of_pos hk, mul_pow, Real.sq_sqrt (by have := div_nonneg (sq_nonneg p.2) hs.le; linarith),
      add_mul, one_mul, div_mul_cancel₀ _ hs.ne']
  have hdir : DifferentialGeometry.Topology.Manifold.sphereDirection v (halfBallCylinderMap p).1 =
      DifferentialGeometry.Topology.Manifold.sphereDirection v p.1 := by
    let θ := DifferentialGeometry.Topology.Manifold.sphereDirection v p.1
    have hθ : ‖p.1‖ • θ.val = p.1 :=
      DifferentialGeometry.Topology.Manifold.norm_smul_sphereDirection v hx
    rw [halfBallCylinderMap_eq_of_norm_sq_ge hp]
    change DifferentialGeometry.Topology.Manifold.sphereDirection v (k • p.1) = θ
    calc
      _ = DifferentialGeometry.Topology.Manifold.sphereDirection v (k • (‖p.1‖ • θ.val)) :=
        congrArg (fun y => DifferentialGeometry.Topology.Manifold.sphereDirection v (k • y)) hθ.symm
      _ = θ := by
        rw [smul_smul]
        exact DifferentialGeometry.Topology.Manifold.sphereDirection_pos_smul v θ
          (mul_pos hk (norm_pos_iff.mpr hx))
  rw [PartialDiffeomorph.cylinderCorner_apply]
  change (_, _, _) = (DifferentialGeometry.Topology.Manifold.sphereDirection v p.1,
    1 ^ 2 - ‖p.1‖ ^ 2 - p.2 ^ 2, p.2)
  refine Prod.ext hdir (Prod.ext ?_ rfl)
  change 1 ^ 2 - ‖(halfBallCylinderMap p).1‖ ^ 2 = 1 ^ 2 - ‖p.1‖ ^ 2 - p.2 ^ 2
  rw [hnorm]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `EuclideanGeometry.cylinderCorner_halfBallCylinderMap then
    throwError "Refusing to shadow existing declaration EuclideanGeometry.cylinderCorner_halfBallCylinderMap"
  Lean.modifyEnv fun env => Lean.addAlias env `EuclideanGeometry.cylinderCorner_halfBallCylinderMap ``Submission.EuclideanGeometry.cylinderCorner_halfBallCylinderMap

end EuclideanGeometry

namespace PartialDiffeomorph
open _root_.PartialDiffeomorph

open _root_.PartialDiffeomorph in
theorem exists_halfBall_cylinder_collar
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    ∃ c : PartialDiffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞,
      _root_.Metric.closedBall (0 : E) 1 ×ˢ {(0 : ℝ)} ⊆ c.source ∧
      c.source ⊆ {p | |p.2| < 1 / 4} ∧
      (c : E × ℝ → E × ℝ) = EuclideanGeometry.halfBallCylinderMap ∧
      c.toOpenPartialHomeomorph.IsImage
        {p : E × ℝ | ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ 1 ∧ 0 ≤ p.2}
        {p : E × ℝ | ‖p.1‖ ^ 2 ≤ 1 ∧ 0 ≤ p.2} := by
  let _ : CompleteSpace (E × ℝ) := FiniteDimensional.complete ℝ (E × ℝ)
  let f := EuclideanGeometry.halfBallCylinderMap (E := E)
  let K := _root_.Metric.closedBall (0 : E) 1 ×ˢ {(0 : ℝ)}
  have hlocal : IsLocalDiffeomorphOn 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) ∞ f K := by
    intro p
    have hp : p.val.2 = 0 := p.property.2
    have heq : p.val = (p.val.1, 0) := Prod.ext rfl hp
    rw [heq]
    exact DifferentialGeometry.Topology.Manifold.isLocalDiffeomorphAt_of_contMDiffOn_of_hasMFDerivAt_equiv
      f EuclideanGeometry.contDiff_halfBallCylinderMap.contMDiff.contMDiffOn isOpen_univ
      (p.val.1, 0) (_root_.Set.mem_univ _) (ContinuousLinearEquiv.refl ℝ (E × ℝ))
      (EuclideanGeometry.hasFDerivAt_halfBallCylinderMap_zero p.val.1).hasMFDerivAt
  have hfix : _root_.Set.EqOn f id K := by
    rintro ⟨x, t⟩ ⟨_, ht⟩
    have ht' : t = 0 := ht
    subst t
    exact EuclideanGeometry.halfBallCylinderMap_apply_zero x
  obtain ⟨c, hKc, hcf⟩ :=
    DifferentialGeometry.IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_isCompact hlocal
      ((_root_.ProperSpace.isCompact_closedBall (0 : E) 1).prod isCompact_singleton)
      ⟨(0, 0), _root_.Metric.mem_closedBall_self zero_le_one, rfl⟩
      (fun p hp q hq hpq => (hfix hp).symm.trans (hpq.trans (hfix hq)))
  let U : Set (E × ℝ) := {p | |p.2| < 1 / 4}
  have hU : IsOpen U := isOpen_lt (continuous_snd.abs) continuous_const
  let C := DifferentialGeometry.Topology.PartialDiffeomorph.restrict c U hU
  refine ⟨C, ?_, fun _ hp => hp.2, hcf, ?_⟩
  · intro p hp
    refine ⟨hKc hp, ?_⟩
    change |p.2| < 1 / 4
    have ht : p.2 = 0 := hp.2
    rw [ht, abs_zero]
    norm_num
  · intro p hp
    change (‖(C p).1‖ ^ 2 ≤ 1 ∧ 0 ≤ (C p).2) ↔ _
    rw [show C p = f p from congrFun hcf p]
    exact EuclideanGeometry.halfBallCylinderMap_mem_cylinder_iff hp.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.exists_halfBall_cylinder_collar then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.exists_halfBall_cylinder_collar"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.exists_halfBall_cylinder_collar ``Submission.PartialDiffeomorph.exists_halfBall_cylinder_collar

end PartialDiffeomorph
