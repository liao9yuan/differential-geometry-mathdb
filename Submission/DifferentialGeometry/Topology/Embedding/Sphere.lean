import Submission.DifferentialGeometry.Topology.Manifold.AddCircle.Circle
import Submission.DifferentialGeometry.Topology.Manifold.LocalDiffeomorphImmersion
import Submission.DifferentialGeometry.Topology.Manifold.SmoothEmbeddingComposition
import Submission.DifferentialGeometry.Topology.Embedding.Diffeomorph
import Submission.DifferentialGeometry.Topology.Embedding.LinearEquiv
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Geometry.Euclidean.Inversion.Calculus
import Mathlib.Analysis.Normed.Module.Span

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.RealInnerProductSpace

noncomputable section

open _root_.EuclideanGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private def inversionChart (v : E) : OpenPartialHomeomorph E E where
  toFun := _root_.EuclideanGeometry.inversion v 2
  invFun := _root_.EuclideanGeometry.inversion v 2
  source := {v}ᶜ
  target := {v}ᶜ
  map_source' x hx := by simpa using hx
  map_target' x hx := by simpa using hx
  left_inv' x _ := _root_.EuclideanGeometry.inversion_inversion v (by norm_num) x
  right_inv' x _ := _root_.EuclideanGeometry.inversion_inversion v (by norm_num) x
  open_source := isOpen_compl_singleton
  open_target := isOpen_compl_singleton
  continuousOn_toFun := continuousOn_const.inversion continuousOn_const continuousOn_id
    (fun x hx => hx)
  continuousOn_invFun := continuousOn_const.inversion continuousOn_const continuousOn_id
    (fun x hx => hx)

run_cmd do
  let target := ``Submission.inversionChart
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `inversionChart target :: scope.openDecls } }

private def sphereFlattening (v : E) : OpenPartialHomeomorph E E :=
  (inversionChart v).trans (Homeomorph.addRight v).toOpenPartialHomeomorph

run_cmd do
  let target := ``Submission.sphereFlattening
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `sphereFlattening target :: scope.openDecls } }

private theorem sphereFlattening_mem_maximalAtlas (v : E) :
    sphereFlattening v ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ E := by
  apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
  · apply ContDiffOn.contMDiffOn
    change ContDiffOn ℝ ∞ (fun x => _root_.EuclideanGeometry.inversion v 2 x + v) _
    exact (contDiffOn_const.inversion contDiffOn_const contDiffOn_id
      (fun x hx => hx.1)).add contDiffOn_const
  · apply ContDiffOn.contMDiffOn
    change ContDiffOn ℝ ∞ (fun x => _root_.EuclideanGeometry.inversion v 2 (x + -v)) _
    exact contDiffOn_const.inversion contDiffOn_const
      (contDiffOn_id.add contDiffOn_const) (fun x hx => hx.2)

run_cmd do
  let target := ``Submission.sphereFlattening_mem_maximalAtlas
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `sphereFlattening_mem_maximalAtlas target :: scope.openDecls } }

private theorem sphereFlattening_apply (v x : Metric.sphere (0 : E) 1) (hx : x ≠ v) :
    sphereFlattening (v : E) (x : E) = (stereoToFun (v : E) x : E) := by
  have hv : ‖(v : E)‖ = 1 := norm_eq_of_mem_sphere v
  have hxx : ‖(x : E)‖ = 1 := norm_eq_of_mem_sphere x
  have hne : (x : E) ≠ (v : E) := fun h => hx (Subtype.ext h)
  have hd : _root_.Dist.dist (x : E) (v : E) ^ 2 = 2 * (1 - _root_.Inner.inner ℝ (v : E) (x : E)) := by
    rw [dist_eq_norm, norm_sub_sq_real, hxx, hv, real_inner_comm]
    ring
  have hs : (x : E) = _root_.Inner.inner ℝ (v : E) (x : E) • (v : E) +
      ((ℝ ∙ (v : E))ᗮ.orthogonalProjectionOnto x : E) := by
    calc
      (x : E) = (ℝ ∙ (v : E)).starProjection x +
          (ℝ ∙ (v : E))ᗮ.starProjection x :=
        ((ℝ ∙ (v : E)).starProjection_add_starProjection_orthogonal (x : E)).symm
      _ = _ := by rw [Submodule.starProjection_unit_singleton ℝ hv]; rfl
  have ha : 1 - _root_.Inner.inner ℝ (v : E) (x : E) ≠ 0 := by
    have := (inner_lt_one_iff_real_of_norm_eq_one hv hxx).mpr hne.symm
    linarith
  change _root_.EuclideanGeometry.inversion (v : E) 2 (x : E) + v = _
  simp only [_root_.EuclideanGeometry.inversion, vsub_eq_sub, vadd_eq_add, div_pow, hd, stereoToFun,
    Submodule.coe_smul_of_tower, innerSL_apply_apply]
  calc
    ((2 : ℝ) ^ 2 / (2 * (1 - _root_.Inner.inner ℝ (v : E) (x : E)))) • ((x : E) - (v : E)) + (v : E) + (v : E) =
        ((2 : ℝ) ^ 2 / (2 * (1 - _root_.Inner.inner ℝ (v : E) (x : E)))) •
          ((_root_.Inner.inner ℝ (v : E) (x : E) • (v : E) +
            ((ℝ ∙ (v : E))ᗮ.orthogonalProjectionOnto x : E)) - (v : E)) + (v : E) + (v : E) := by
      rw [← hs]
    _ = _ := by
      match_scalars
      all_goals field_simp
      all_goals ring

run_cmd do
  let target := ``Submission.sphereFlattening_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `sphereFlattening_apply target :: scope.openDecls } }

def sphereChartEquiv {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]
    (v : Metric.sphere (0 : E) 1) : (EuclideanSpace ℝ (Fin n) × ℝ) ≃L[ℝ] E := by
  letI : FiniteDimensional ℝ E := FiniteDimensional.of_fact_finrank_eq_succ n
  let U := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) n
    (ne_zero_of_mem_unit_sphere v)).repr
  let V := ContinuousLinearEquiv.toSpanNonzeroSingleton ℝ (v : E)
    (ne_zero_of_mem_unit_sphere v)
  exact ((U.symm.toLinearEquiv.prodCongr V.toLinearEquiv).trans
    ((ℝ ∙ (v : E))ᗮ.prodEquivOfIsCompl (ℝ ∙ (v : E))
      (Submodule.isCompl_orthogonal (ℝ ∙ (v : E))).symm)).toContinuousLinearEquiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `sphereChartEquiv then
    throwError "Refusing to shadow existing declaration sphereChartEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `sphereChartEquiv ``Submission.sphereChartEquiv

theorem sphereChartEquiv_apply {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]
    (v : Metric.sphere (0 : E) 1) (p : EuclideanSpace ℝ (Fin n) × ℝ) :
    sphereChartEquiv v p =
      (((OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) n
        (ne_zero_of_mem_unit_sphere v)).repr.symm p.1 : (ℝ ∙ (v : E))ᗮ) : E) + p.2 • v := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `sphereChartEquiv_apply then
    throwError "Refusing to shadow existing declaration sphereChartEquiv_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `sphereChartEquiv_apply ``Submission.sphereChartEquiv_apply

theorem sphereChartEquiv_norm_sq {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]
    (v : Metric.sphere (0 : E) 1) (p : EuclideanSpace ℝ (Fin n) × ℝ) :
    ‖sphereChartEquiv v p‖ ^ 2 = ‖p.1‖ ^ 2 + p.2 ^ 2 := by
  let U := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) n
    (ne_zero_of_mem_unit_sphere v)).repr
  have ho : _root_.Inner.inner ℝ (U.symm p.1 : E) (p.2 • (v : E)) = 0 := by
    rw [inner_smul_right,
      Submodule.mem_orthogonal_singleton_iff_inner_left.mp (U.symm p.1).property, _root_.MulZeroClass.mul_zero]
  rw [sphereChartEquiv_apply]
  calc
    _ = ‖(U.symm p.1 : E)‖ ^ 2 + ‖p.2 • (v : E)‖ ^ 2 := by
      simpa only [← sq] using norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ ho
    _ = _ := by simp [← Submodule.coe_norm, norm_smul, sq_abs]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `sphereChartEquiv_norm_sq then
    throwError "Refusing to shadow existing declaration sphereChartEquiv_norm_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `sphereChartEquiv_norm_sq ``Submission.sphereChartEquiv_norm_sq


private theorem sphereChartEquiv_apply_zero {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]
    (v : Metric.sphere (0 : E) 1) (u : EuclideanSpace ℝ (Fin n)) :
    sphereChartEquiv v (u, 0) =
      (((OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) n
        (ne_zero_of_mem_unit_sphere v)).repr.symm u : (ℝ ∙ (v : E))ᗮ) : E) := by
  simp [sphereChartEquiv]

run_cmd do
  let target := ``Submission.sphereChartEquiv_apply_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `sphereChartEquiv_apply_zero target :: scope.openDecls } }

theorem isSmoothEmbedding_coe_sphere {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)] :
    Manifold.IsSmoothEmbedding (𝓡 n) 𝓘(ℝ, E) ∞
      (Subtype.val : Metric.sphere (0 : E) 1 → E) := by
  refine ⟨?_, .subtypeVal⟩
  apply Manifold.IsImmersionOfComplement.isImmersion (F := ℝ)
  intro x
  apply Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
    continuous_subtype_val.continuousAt (sphereChartEquiv (-x))
    (stereographic' n (-x)) (sphereFlattening (-x : E))
  · simpa using ne_neg_of_mem_unit_sphere ℝ x
  · change (x : E) ∈ (inversionChart (-x : E)).source ∧ _
    exact ⟨fun h => (ne_neg_of_mem_unit_sphere ℝ x) (Subtype.ext h), Set.mem_univ _⟩
  · apply IsManifold.subset_maximalAtlas
    exact ⟨-x, rfl⟩
  · exact sphereFlattening_mem_maximalAtlas (-x : E)
  · intro u hu
    change sphereFlattening (-x : E) (((stereographic' n (-x)).symm u) : E) =
      sphereChartEquiv (-x) (u, 0)
    have hy : (stereographic' n (-x)).symm u ≠ -x := by
      have hmem := (stereographic' n (-x)).map_target (show u ∈ _ by simp)
      simpa using hmem
    have hflat := sphereFlattening_apply (-x) ((stereographic' n (-x)).symm u) hy
    rw [coe_neg_sphere] at hflat
    rw [hflat, sphereChartEquiv_apply_zero]
    change ((stereographic (norm_eq_of_mem_sphere (-x)))
      ((stereographic' n (-x)).symm u) : E) = _
    let U := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) n
      (ne_zero_of_mem_unit_sphere (-x))).repr
    change ((stereographic (norm_eq_of_mem_sphere (-x)))
      ((stereographic (norm_eq_of_mem_sphere (-x))).symm (U.symm u)) : E) =
        (U.symm u : E)
    exact congrArg (Subtype.val : (ℝ ∙ (-x : E))ᗮ → E)
      (stereo_right_inv (norm_eq_of_mem_sphere (-x)) (U.symm u))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `isSmoothEmbedding_coe_sphere then
    throwError "Refusing to shadow existing declaration isSmoothEmbedding_coe_sphere"
  Lean.modifyEnv fun env => Lean.addAlias env `isSmoothEmbedding_coe_sphere ``Submission.isSmoothEmbedding_coe_sphere

end

open _root_.Set _root_.Metric in
theorem exists_isSmoothEmbedding_addCircle_range_eq_sphere
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (hdim : Module.finrank ℝ E = 2) (x : E) {r : ℝ} (hr : 0 < r) :
    ∃ γ : AddCircle (1 : ℝ) → E,
      Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ ∧
      range γ = _root_.Metric.sphere x r := by
  let _ : FiniteDimensional ℝ E := FiniteDimensional.of_finrank_pos (by omega)
  let _ : Fact (Module.finrank ℝ ℂ = 1 + 1) := ⟨by norm_num⟩
  let L : ℂ ≃ₗᵢ[ℝ] E := Complex.orthonormalBasisOneI.repr.trans
    ((stdOrthonormalBasis ℝ E).reindex (finCongr hdim)).repr.symm
  let S : E ≃L[ℝ] E := (LinearEquiv.smulOfNeZero ℝ E r hr.ne').toContinuousLinearEquiv
  let T : E ≃ₘ[ℝ] E :=
    { toEquiv := (Homeomorph.addLeft x).toEquiv
      contMDiff_toFun := (contDiff_const.add contDiff_id).contMDiff
      contMDiff_invFun := (contDiff_const.add contDiff_id).contMDiff }
  let γ := fun t : AddCircle (1 : ℝ) => x + r • L (AddCircle.diffeomorphCircle t).val
  have hc : Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) (𝓡 1) ∞ AddCircle.diffeomorphCircle :=
    DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_of_isLocalDiffeomorph_of_injective
      AddCircle.diffeomorphCircle.isLocalDiffeomorph AddCircle.diffeomorphCircle.injective
  have hcoe := isSmoothEmbedding_coe_sphere (E := ℂ) (n := 1)
  have hγ := (((hcoe.comp hc (by simp)).continuousLinearEquiv_comp
    L.toContinuousLinearEquiv).continuousLinearEquiv_comp S).diffeomorph_comp T
  refine ⟨γ, hγ, ?_⟩
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    rw [mem_sphere_iff_norm]
    dsimp [γ]
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hr, L.norm_map,
      (AddCircle.diffeomorphCircle t).norm_coe, mul_one]
  · intro hz
    have hnorm : ‖r⁻¹ • (z - x)‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), mem_sphere_iff_norm.mp hz,
        inv_mul_cancel₀ hr.ne']
    let w : Circle := ⟨L.symm (r⁻¹ • (z - x)), by
      apply mem_sphere_zero_iff_norm.mpr
      rw [L.symm.norm_map, hnorm]⟩
    refine ⟨AddCircle.diffeomorphCircle.symm w, ?_⟩
    dsimp [γ]
    rw [AddCircle.diffeomorphCircle.apply_symm_apply]
    change x + r • L (L.symm (r⁻¹ • (z - x))) = z
    rw [L.apply_symm_apply, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    exact add_sub_cancel _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `exists_isSmoothEmbedding_addCircle_range_eq_sphere then
    throwError "Refusing to shadow existing declaration exists_isSmoothEmbedding_addCircle_range_eq_sphere"
  Lean.modifyEnv fun env => Lean.addAlias env `exists_isSmoothEmbedding_addCircle_range_eq_sphere ``Submission.exists_isSmoothEmbedding_addCircle_range_eq_sphere
