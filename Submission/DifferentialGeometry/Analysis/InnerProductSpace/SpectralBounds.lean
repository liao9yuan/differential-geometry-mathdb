import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.Convex.Function

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace ContinuousLinearMap
open _root_.ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

open _root_.ContinuousLinearMap in
private theorem bddBelow_rayleighQuotient_nonzero (T : E →L[𝕜] E) :
    BddBelow (Set.range fun x : {x : E // x ≠ 0} => T.rayleighQuotient x) := by
  refine ⟨-‖T‖, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact (abs_le.mp (T.rayleighQuotient_le_norm x)).1

run_cmd do
  let target := ``Submission.ContinuousLinearMap.bddBelow_rayleighQuotient_nonzero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `ContinuousLinearMap.bddBelow_rayleighQuotient_nonzero target :: scope.openDecls } }

open _root_.ContinuousLinearMap in
theorem iInf_rayleighQuotient_le (T : E →L[𝕜] E) {x : E} (hx : x ≠ 0) :
    (⨅ v : {v : E // v ≠ 0}, T.rayleighQuotient v) ≤ T.rayleighQuotient x :=
  ciInf_le (bddBelow_rayleighQuotient_nonzero T) ⟨x, hx⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousLinearMap.iInf_rayleighQuotient_le then
    throwError "Refusing to shadow existing declaration ContinuousLinearMap.iInf_rayleighQuotient_le"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousLinearMap.iInf_rayleighQuotient_le ``Submission.ContinuousLinearMap.iInf_rayleighQuotient_le

open _root_.ContinuousLinearMap in
theorem iInf_rayleighQuotient_eq_sInf_inner_sphere (T : E →L[𝕜] E) :
    (⨅ v : {v : E // v ≠ 0}, T.rayleighQuotient v) =
      sInf ((fun v : E => RCLike.re (_root_.Inner.inner 𝕜 (T v) v)) '' Metric.sphere 0 1) := by
  rw [T.iInf_rayleigh_eq_iInf_rayleigh_sphere zero_lt_one, ← sInf_image']
  congr 1
  apply Set.image_congr
  intro v hv
  have hv' : ‖v‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hv
  simp only [_root_.ContinuousLinearMap.rayleighQuotient, _root_.ContinuousLinearMap.reApplyInnerSelf_apply, hv', one_pow, div_one]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousLinearMap.iInf_rayleighQuotient_eq_sInf_inner_sphere then
    throwError "Refusing to shadow existing declaration ContinuousLinearMap.iInf_rayleighQuotient_eq_sInf_inner_sphere"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousLinearMap.iInf_rayleighQuotient_eq_sInf_inner_sphere ``Submission.ContinuousLinearMap.iInf_rayleighQuotient_eq_sInf_inner_sphere

open _root_.ContinuousLinearMap in
private theorem rayleighQuotient_sub (T S : E →L[𝕜] E) (x : E) :
    (T - S).rayleighQuotient x = T.rayleighQuotient x - S.rayleighQuotient x := by
  simp only [sub_eq_add_neg, _root_.ContinuousLinearMap.rayleighQuotient_add, _root_.ContinuousLinearMap.rayleighQuotient_neg_apply]

run_cmd do
  let target := ``Submission.ContinuousLinearMap.rayleighQuotient_sub
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `ContinuousLinearMap.rayleighQuotient_sub target :: scope.openDecls } }

open _root_.ContinuousLinearMap in
private theorem iInf_rayleighQuotient_le_add_norm_sub [Nontrivial E]
    (T S : E →L[𝕜] E) :
    (⨅ v : {v : E // v ≠ 0}, T.rayleighQuotient v) ≤
      (⨅ v : {v : E // v ≠ 0}, S.rayleighQuotient v) + ‖T - S‖ := by
  let : Nonempty {v : E // v ≠ 0} := by
    obtain ⟨v, hv⟩ := exists_ne (0 : E)
    exact ⟨⟨v, hv⟩⟩
  apply sub_le_iff_le_add.mp
  apply le_ciInf
  intro v
  have h := (abs_le.mp ((T - S).rayleighQuotient_le_norm v)).2
  rw [rayleighQuotient_sub] at h
  have hi := T.iInf_rayleighQuotient_le v.property
  linarith

run_cmd do
  let target := ``Submission.ContinuousLinearMap.iInf_rayleighQuotient_le_add_norm_sub
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `ContinuousLinearMap.iInf_rayleighQuotient_le_add_norm_sub target :: scope.openDecls } }

open _root_.ContinuousLinearMap in
theorem lipschitzWith_iInf_rayleighQuotient :
    LipschitzWith 1 (fun T : E →L[𝕜] E =>
      ⨅ v : {v : E // v ≠ 0}, T.rayleighQuotient v) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · have hzero : ∀ T : E →L[𝕜] E, T = 0 := fun T => Subsingleton.elim T 0
    apply LipschitzWith.of_le_add
    intro T S
    simp only [hzero T, hzero S, dist_self, add_zero, le_refl]
  · apply LipschitzWith.of_le_add
    intro T S
    simpa only [dist_eq_norm] using iInf_rayleighQuotient_le_add_norm_sub T S

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousLinearMap.lipschitzWith_iInf_rayleighQuotient then
    throwError "Refusing to shadow existing declaration ContinuousLinearMap.lipschitzWith_iInf_rayleighQuotient"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousLinearMap.lipschitzWith_iInf_rayleighQuotient ``Submission.ContinuousLinearMap.lipschitzWith_iInf_rayleighQuotient

open _root_.ContinuousLinearMap in
theorem abs_iInf_rayleighQuotient_sub_le (T S : E →L[𝕜] E) :
    |(⨅ v : {v : E // v ≠ 0}, T.rayleighQuotient v) -
      (⨅ v : {v : E // v ≠ 0}, S.rayleighQuotient v)| ≤ ‖T - S‖ := by
  simpa only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_one, one_mul] using
    (lipschitzWith_iInf_rayleighQuotient (𝕜 := 𝕜) (E := E)).dist_le_mul T S

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousLinearMap.abs_iInf_rayleighQuotient_sub_le then
    throwError "Refusing to shadow existing declaration ContinuousLinearMap.abs_iInf_rayleighQuotient_sub_le"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousLinearMap.abs_iInf_rayleighQuotient_sub_le ``Submission.ContinuousLinearMap.abs_iInf_rayleighQuotient_sub_le

open _root_.ContinuousLinearMap in
theorem continuous_iInf_rayleighQuotient :
    Continuous (fun T : E →L[𝕜] E =>
      ⨅ v : {v : E // v ≠ 0}, T.rayleighQuotient v) :=
  lipschitzWith_iInf_rayleighQuotient.continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousLinearMap.continuous_iInf_rayleighQuotient then
    throwError "Refusing to shadow existing declaration ContinuousLinearMap.continuous_iInf_rayleighQuotient"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousLinearMap.continuous_iInf_rayleighQuotient ``Submission.ContinuousLinearMap.continuous_iInf_rayleighQuotient

section Real

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

open _root_.ContinuousLinearMap in
private theorem rayleighQuotient_real_smul (a : ℝ) (T : F →L[ℝ] F) (x : F) :
    (a • T).rayleighQuotient x = a * T.rayleighQuotient x := by
  simp only [_root_.ContinuousLinearMap.rayleighQuotient, _root_.ContinuousLinearMap.reApplyInnerSelf_apply, smul_apply, real_inner_smul_left,
    RCLike.re_to_real, mul_div_assoc]

run_cmd do
  let target := ``Submission.ContinuousLinearMap.rayleighQuotient_real_smul
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `ContinuousLinearMap.rayleighQuotient_real_smul target :: scope.openDecls } }

open _root_.ContinuousLinearMap in
theorem concaveOn_iInf_rayleighQuotient :
    ConcaveOn ℝ Set.univ (fun T : F →L[ℝ] F =>
      ⨅ v : {v : F // v ≠ 0}, T.rayleighQuotient v) := by
  rcases subsingleton_or_nontrivial F with hE | hE
  · have hconst : (fun T : F →L[ℝ] F =>
        ⨅ v : {v : F // v ≠ 0}, T.rayleighQuotient v) =
        fun _ => ⨅ v : {v : F // v ≠ 0}, (0 : F →L[ℝ] F).rayleighQuotient v := by
      funext T
      rw [Subsingleton.elim T 0]
    rw [hconst]
    exact concaveOn_const _ convex_univ
  · let : Nonempty {v : F // v ≠ 0} := by
      obtain ⟨v, hv⟩ := exists_ne (0 : F)
      exact ⟨⟨v, hv⟩⟩
    refine ⟨convex_univ, ?_⟩
    intro T _ S _ a b ha hb _
    apply le_ciInf
    intro v
    simp only [smul_eq_mul, _root_.ContinuousLinearMap.rayleighQuotient_add, rayleighQuotient_real_smul]
    exact add_le_add (mul_le_mul_of_nonneg_left (T.iInf_rayleighQuotient_le v.property) ha)
      (mul_le_mul_of_nonneg_left (S.iInf_rayleighQuotient_le v.property) hb)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousLinearMap.concaveOn_iInf_rayleighQuotient then
    throwError "Refusing to shadow existing declaration ContinuousLinearMap.concaveOn_iInf_rayleighQuotient"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousLinearMap.concaveOn_iInf_rayleighQuotient ``Submission.ContinuousLinearMap.concaveOn_iInf_rayleighQuotient

end Real

variable [FiniteDimensional 𝕜 E]

open _root_.ContinuousLinearMap in
theorem exists_mem_sphere_eq_iInf_rayleighQuotient [Nontrivial E] (T : E →L[𝕜] E) :
    ∃ v ∈ Metric.sphere (0 : E) 1,
      RCLike.re (_root_.Inner.inner 𝕜 (T v) v) =
        ⨅ w : {w : E // w ≠ 0}, T.rayleighQuotient w := by
  have := FiniteDimensional.proper_rclike 𝕜 E
  rw [iInf_rayleighQuotient_eq_sInf_inner_sphere]
  exact ((isCompact_sphere (0 : E) 1).image T.reApplyInnerSelf_continuous).sInf_mem
    ((Set.nonempty_coe_sort.mp
      (NormedSpace.sphere_nonempty_rclike (𝕜 := 𝕜) (E := E) zero_le_one)).image _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousLinearMap.exists_mem_sphere_eq_iInf_rayleighQuotient then
    throwError "Refusing to shadow existing declaration ContinuousLinearMap.exists_mem_sphere_eq_iInf_rayleighQuotient"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousLinearMap.exists_mem_sphere_eq_iInf_rayleighQuotient ``Submission.ContinuousLinearMap.exists_mem_sphere_eq_iInf_rayleighQuotient

open _root_.ContinuousLinearMap in
theorem finrank_mul_iInf_rayleighQuotient_le_re_trace (T : E →L[𝕜] E) :
    (Module.finrank 𝕜 E : ℝ) * (⨅ v : {v : E // v ≠ 0}, T.rayleighQuotient v) ≤
      RCLike.re (LinearMap.trace 𝕜 E T.toLinearMap) := by
  classical
  let b := stdOrthonormalBasis 𝕜 E
  rw [LinearMap.trace_eq_sum_inner T.toLinearMap b, map_sum]
  calc
    _ = ∑ _ : Fin (Module.finrank 𝕜 E),
        ⨅ v : {v : E // v ≠ 0}, T.rayleighQuotient v := by simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      have hnorm : ‖b i‖ = 1 := b.orthonormal.norm_eq_one i
      have hne : b i ≠ 0 := (norm_ne_zero_iff).mp (hnorm.trans_ne one_ne_zero)
      have hi := T.iInf_rayleighQuotient_le hne
      rw [inner_re_symm]
      change (⨅ v : {v : E // v ≠ 0}, T.rayleighQuotient v) ≤
        RCLike.re (_root_.Inner.inner 𝕜 (T (b i)) (b i))
      simpa only [_root_.ContinuousLinearMap.rayleighQuotient, _root_.ContinuousLinearMap.reApplyInnerSelf_apply, hnorm, one_pow, div_one,
        ContinuousLinearMap.coe_coe] using hi

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousLinearMap.finrank_mul_iInf_rayleighQuotient_le_re_trace then
    throwError "Refusing to shadow existing declaration ContinuousLinearMap.finrank_mul_iInf_rayleighQuotient_le_re_trace"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousLinearMap.finrank_mul_iInf_rayleighQuotient_le_re_trace ``Submission.ContinuousLinearMap.finrank_mul_iInf_rayleighQuotient_le_re_trace

end ContinuousLinearMap

namespace LinearMap.IsSymmetric
open _root_.LinearMap _root_.LinearMap.IsSymmetric

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {T : E →L[𝕜] E}

open _root_.LinearMap _root_.LinearMap.IsSymmetric in
theorem iInf_rayleighQuotient_eq_eigenvalues_last {n : ℕ}
    (hT : T.toLinearMap.IsSymmetric) (hn : Module.finrank 𝕜 E = n + 1) :
    (⨅ v : {v : E // v ≠ 0}, T.rayleighQuotient v) =
      hT.eigenvalues hn (Fin.last n) := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := 𝕜) (M := E) (by omega)
  apply le_antisymm
  · let v := hT.eigenvectorBasis hn (Fin.last n)
    have hnorm : ‖v‖ = 1 := (hT.eigenvectorBasis hn).orthonormal.norm_eq_one _
    have hne : v ≠ 0 := by intro h; simp [h] at hnorm
    have heig : T v = (hT.eigenvalues hn (Fin.last n) : 𝕜) • v :=
      hT.apply_eigenvectorBasis hn (Fin.last n)
    have hi := T.iInf_rayleighQuotient_le hne
    simpa only [ContinuousLinearMap.rayleighQuotient,
      ContinuousLinearMap.reApplyInnerSelf_apply, heig, inner_smul_left,
      RCLike.conj_ofReal, inner_self_eq_norm_sq_to_K, hnorm, one_pow,
      RCLike.ofReal_one, mul_one, RCLike.ofReal_re, div_one] using hi
  · have heig := hT.hasEigenvalue_iInf_of_finiteDimensional
    obtain ⟨i, hi⟩ := hT.exists_eigenvalues_eq hn heig
    have hi' : hT.eigenvalues hn i =
        ⨅ v : {v : E // v ≠ 0}, T.rayleighQuotient v := by
      exact_mod_cast hi
    rw [← hi']
    exact hT.eigenvalues_antitone hn (Fin.le_last i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LinearMap.IsSymmetric.iInf_rayleighQuotient_eq_eigenvalues_last then
    throwError "Refusing to shadow existing declaration LinearMap.IsSymmetric.iInf_rayleighQuotient_eq_eigenvalues_last"
  Lean.modifyEnv fun env => Lean.addAlias env `LinearMap.IsSymmetric.iInf_rayleighQuotient_eq_eigenvalues_last ``Submission.LinearMap.IsSymmetric.iInf_rayleighQuotient_eq_eigenvalues_last

open _root_.LinearMap _root_.LinearMap.IsSymmetric in
theorem abs_eigenvalues_last_sub_le {n : ℕ} {S : E →L[𝕜] E}
    (hT : T.toLinearMap.IsSymmetric) (hS : S.toLinearMap.IsSymmetric)
    (hn : Module.finrank 𝕜 E = n + 1) :
    |hT.eigenvalues hn (Fin.last n) - hS.eigenvalues hn (Fin.last n)| ≤ ‖T - S‖ := by
  rw [← hT.iInf_rayleighQuotient_eq_eigenvalues_last hn,
    ← hS.iInf_rayleighQuotient_eq_eigenvalues_last hn]
  exact T.abs_iInf_rayleighQuotient_sub_le S

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LinearMap.IsSymmetric.abs_eigenvalues_last_sub_le then
    throwError "Refusing to shadow existing declaration LinearMap.IsSymmetric.abs_eigenvalues_last_sub_le"
  Lean.modifyEnv fun env => Lean.addAlias env `LinearMap.IsSymmetric.abs_eigenvalues_last_sub_le ``Submission.LinearMap.IsSymmetric.abs_eigenvalues_last_sub_le

open _root_.LinearMap _root_.LinearMap.IsSymmetric in
theorem finrank_mul_eigenvalues_last_le_re_trace {n : ℕ}
    (hT : T.toLinearMap.IsSymmetric) (hn : Module.finrank 𝕜 E = n + 1) :
    (Module.finrank 𝕜 E : ℝ) * hT.eigenvalues hn (Fin.last n) ≤
      RCLike.re (LinearMap.trace 𝕜 E T.toLinearMap) := by
  rw [← hT.iInf_rayleighQuotient_eq_eigenvalues_last hn]
  exact T.finrank_mul_iInf_rayleighQuotient_le_re_trace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LinearMap.IsSymmetric.finrank_mul_eigenvalues_last_le_re_trace then
    throwError "Refusing to shadow existing declaration LinearMap.IsSymmetric.finrank_mul_eigenvalues_last_le_re_trace"
  Lean.modifyEnv fun env => Lean.addAlias env `LinearMap.IsSymmetric.finrank_mul_eigenvalues_last_le_re_trace ``Submission.LinearMap.IsSymmetric.finrank_mul_eigenvalues_last_le_re_trace

end LinearMap.IsSymmetric
