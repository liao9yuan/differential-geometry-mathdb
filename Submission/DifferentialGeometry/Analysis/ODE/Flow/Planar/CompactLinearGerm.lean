import Submission.DifferentialGeometry.Analysis.ODE.Flow.Planar.CompactFlowGerm
import Mathlib.LinearAlgebra.Matrix.Transvection

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Metric _root_.Filter _root_.Topology
open scoped _root_.ContDiff _root_.Manifold _root_.Matrix

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def RealizesGerm (f : E → E) (K : Set E) : Prop :=
  f 0 = 0 ∧ IsCompact K ∧
    ∃ D : ℝ → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      ContDiff ℝ ∞ (fun q : ℝ × E ↦ D q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × E ↦ (D q.1).symm q.2) ∧
      D 0 = Diffeomorph.refl 𝓘(ℝ, E) E ∞ ∧
      (D 1 : E → E) =ᶠ[𝓝 0] f ∧
      ∀ p z, z ∉ K → D p z = z ∧ (D p).symm z = z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.RealizesGerm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.RealizesGerm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.RealizesGerm ``Submission.DifferentialGeometry.Analysis.RealizesGerm

omit [FiniteDimensional ℝ E] in
theorem RealizesGerm.mono {f : E → E} {K K' : Set E} (h : RealizesGerm f K) (hKK' : K ⊆ K')
    (hK' : IsCompact K') : RealizesGerm f K' :=
  ⟨h.1, hK', h.2.2.imp fun _ hD => ⟨hD.1, hD.2.1, hD.2.2.1, hD.2.2.2.1,
    fun p z hz => hD.2.2.2.2 p z fun hk => hz (hKK' hk)⟩⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Analysis.RealizesGerm
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.RealizesGerm.mono then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.RealizesGerm.mono"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.RealizesGerm.mono ``Submission.DifferentialGeometry.Analysis.RealizesGerm.mono

omit [FiniteDimensional ℝ E] in
theorem RealizesGerm.refl (K : Set E) (hK : IsCompact K) :
    RealizesGerm (id : E → E) K :=
  ⟨rfl, hK, fun _ => Diffeomorph.refl 𝓘(ℝ, E) E ∞, contDiff_snd, contDiff_snd, rfl,
    Filter.EventuallyEq.refl _ _, fun _ _ _ => ⟨rfl, rfl⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.RealizesGerm.refl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.RealizesGerm.refl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.RealizesGerm.refl ``Submission.DifferentialGeometry.Analysis.RealizesGerm.refl

omit [FiniteDimensional ℝ E] in
theorem RealizesGerm.comp {f g : E → E} {Kf Kg : Set E}
    (hf : RealizesGerm f Kf) (hg : RealizesGerm g Kg) :
    RealizesGerm (f ∘ g) (Kf ∪ Kg) := by
  obtain ⟨hf0, hKf, Df, hDf, hDfi, hDf0, hDfg, hDfK⟩ := hf
  obtain ⟨hg0, hKg, Dg, hDg, hDgi, hDg0, hDgg, hDgK⟩ := hg
  let D : ℝ → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞ := fun p => (Dg p).trans (Df p)
  refine ⟨by simp only [Function.comp_apply, hg0, hf0], hKf.union hKg, D, ?_, ?_, ?_, ?_, ?_⟩
  · exact hDf.comp (contDiff_fst.prodMk hDg)
  · exact hDgi.comp (contDiff_fst.prodMk hDfi)
  · simp only [D, hDg0, hDf0, Diffeomorph.refl_trans]
  · have hz0 : (Dg 1) 0 = 0 := hDgg.eq_of_nhds.trans hg0
    have htend : _root_.Filter.Tendsto (Dg 1) (𝓝 0) (𝓝 ((Dg 1) 0)) :=
      (Dg 1).continuous.continuousAt (x := (0 : E))
    have htend' : _root_.Filter.Tendsto (Dg 1) (𝓝 0) (𝓝 0) := by simpa only [hz0] using htend
    refine (hDfg.comp_tendsto htend').trans ?_
    filter_upwards [hDgg] with z hz
    exact congrArg f hz
  · intro p z hz
    have hzf : z ∉ Kf := fun h => hz (Or.inl h)
    have hzg : z ∉ Kg := fun h => hz (Or.inr h)
    have h1 := hDfK p z hzf
    have h2 := hDgK p z hzg
    have hfix : D p z = z := by
      change ((Dg p).trans (Df p)) z = z
      simp only [Diffeomorph.coe_trans, Function.comp_apply]
      rw [h2.1, h1.1]
    refine ⟨hfix, ?_⟩
    apply (D p).injective
    exact ((D p).apply_symm_apply z).trans hfix.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.RealizesGerm.comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.RealizesGerm.comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.RealizesGerm.comp ``Submission.DifferentialGeometry.Analysis.RealizesGerm.comp

theorem RealizesGerm.exp (X : E →L[ℝ] E) (r : ℝ) (hr : 0 < r) :
    RealizesGerm (fun x => NormedSpace.exp X x) (Metric.closedBall 0 (2 * r)) := by
  obtain ⟨D, hD, hDi, hD0, hDg, hfix⟩ :=
    exists_compact_isotopy_realizing_exp_germ X r hr
  exact ⟨by simp, _root_.ProperSpace.isCompact_closedBall _ _, D, hD, hDi, hD0, hDg, hfix⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.RealizesGerm.exp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.RealizesGerm.exp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.RealizesGerm.exp ``Submission.DifferentialGeometry.Analysis.RealizesGerm.exp


variable {n : ℕ}

def matEnd (M : Matrix (Fin n) (Fin n) ℝ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap.comp
    (((Matrix.toLin' M).toContinuousLinearMap).comp
      (EuclideanSpace.equiv (Fin n) ℝ).toContinuousLinearMap)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.matEnd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.matEnd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.matEnd ``Submission.DifferentialGeometry.Analysis.matEnd

theorem matEnd_apply (M : Matrix (Fin n) (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    matEnd M x = WithLp.toLp 2 (M *ᵥ WithLp.ofLp x) := by
  simp only [matEnd, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    PiLp.coe_continuousLinearEquiv, PiLp.coe_symm_continuousLinearEquiv]
  simp [Matrix.toLin'_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.matEnd_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.matEnd_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.matEnd_apply ``Submission.DifferentialGeometry.Analysis.matEnd_apply

theorem matEnd_mul (M N : Matrix (Fin n) (Fin n) ℝ) :
    matEnd (M * N) = matEnd M * matEnd N := by
  refine ContinuousLinearMap.ext fun x => ?_
  rw [matEnd_apply, mul_apply_eq_comp, matEnd_apply, matEnd_apply, Matrix.mulVec_mulVec]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.matEnd_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.matEnd_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.matEnd_mul ``Submission.DifferentialGeometry.Analysis.matEnd_mul

theorem matEnd_one : matEnd (1 : Matrix (Fin n) (Fin n) ℝ) = 1 := by
  refine ContinuousLinearMap.ext fun x => ?_
  rw [matEnd_apply, Matrix.one_mulVec]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.matEnd_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.matEnd_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.matEnd_one ``Submission.DifferentialGeometry.Analysis.matEnd_one

theorem matEnd_zero : matEnd (0 : Matrix (Fin n) (Fin n) ℝ) = 0 := by
  refine ContinuousLinearMap.ext fun x => ?_
  rw [matEnd_apply, Matrix.zero_mulVec]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.matEnd_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.matEnd_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.matEnd_zero ``Submission.DifferentialGeometry.Analysis.matEnd_zero

theorem matEnd_add (M N : Matrix (Fin n) (Fin n) ℝ) :
    matEnd (M + N) = matEnd M + matEnd N := by
  refine ContinuousLinearMap.ext fun x => ?_
  rw [matEnd_apply, add_apply, matEnd_apply, matEnd_apply, Matrix.add_mulVec]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.matEnd_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.matEnd_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.matEnd_add ``Submission.DifferentialGeometry.Analysis.matEnd_add

theorem matEnd_smul (a : ℝ) (M : Matrix (Fin n) (Fin n) ℝ) :
    matEnd (a • M) = a • matEnd M := by
  refine ContinuousLinearMap.ext fun x => ?_
  rw [matEnd_apply, smul_apply, matEnd_apply, Matrix.smul_mulVec]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.matEnd_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.matEnd_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.matEnd_smul ``Submission.DifferentialGeometry.Analysis.matEnd_smul

theorem matEnd_neg (M : Matrix (Fin n) (Fin n) ℝ) : matEnd (-M) = -matEnd M := by
  rw [← neg_one_smul ℝ M, matEnd_smul]
  exact neg_one_smul ℝ (matEnd M)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.matEnd_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.matEnd_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.matEnd_neg ``Submission.DifferentialGeometry.Analysis.matEnd_neg

theorem matEnd_sub (M N : Matrix (Fin n) (Fin n) ℝ) :
    matEnd (M - N) = matEnd M - matEnd N := by
  rw [sub_eq_add_neg, matEnd_add, matEnd_neg, sub_eq_add_neg]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.matEnd_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.matEnd_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.matEnd_sub ``Submission.DifferentialGeometry.Analysis.matEnd_sub

def coordProjM (i : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (Pi.single i (1 : ℝ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.coordProjM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.coordProjM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.coordProjM ``Submission.DifferentialGeometry.Analysis.coordProjM

def planeProjM (i j : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.single i i (1 : ℝ) + Matrix.single j j (1 : ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.planeProjM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.planeProjM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.planeProjM ``Submission.DifferentialGeometry.Analysis.planeProjM

def planeSymM (i j : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.single i j (1 : ℝ) - Matrix.single j i (1 : ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.planeSymM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.planeSymM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.planeSymM ``Submission.DifferentialGeometry.Analysis.planeSymM

theorem coordProjM_mul_self (i : Fin n) : coordProjM i * coordProjM i = coordProjM i := by
  rw [coordProjM, Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  by_cases hk : k = i <;> simp [hk]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.coordProjM_mul_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.coordProjM_mul_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.coordProjM_mul_self ``Submission.DifferentialGeometry.Analysis.coordProjM_mul_self

theorem planeProjM_mul_self {i j : Fin n} (hij : i ≠ j) :
    planeProjM i j * planeProjM i j = planeProjM i j := by
  have h : Matrix.single i i (1 : ℝ) * Matrix.single j j (1 : ℝ) = 0 :=
    Matrix.single_mul_single_of_ne (1 : ℝ) i i j hij (1 : ℝ)
  have h' : Matrix.single j j (1 : ℝ) * Matrix.single i i (1 : ℝ) = 0 :=
    Matrix.single_mul_single_of_ne (1 : ℝ) j j i hij.symm (1 : ℝ)
  have hii : Matrix.single i i (1 : ℝ) * Matrix.single i i (1 : ℝ) = Matrix.single i i (1 : ℝ) := by
    rw [Matrix.single_mul_single_same (1 : ℝ) i i i (1 : ℝ)]; norm_num
  have hjj : Matrix.single j j (1 : ℝ) * Matrix.single j j (1 : ℝ) = Matrix.single j j (1 : ℝ) := by
    rw [Matrix.single_mul_single_same (1 : ℝ) j j j (1 : ℝ)]; norm_num
  rw [planeProjM]
  simp only [Matrix.add_mul, Matrix.mul_add, hii, h, h', hjj, add_zero, zero_add]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.planeProjM_mul_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.planeProjM_mul_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.planeProjM_mul_self ``Submission.DifferentialGeometry.Analysis.planeProjM_mul_self

theorem planeSymM_mul_self {i j : Fin n} (hij : i ≠ j) :
    planeSymM i j * planeSymM i j = - planeProjM i j := by
  have h0 : Matrix.single i j (1 : ℝ) * Matrix.single i j (1 : ℝ) = 0 :=
    Matrix.single_mul_single_of_ne (1 : ℝ) i j i hij.symm (1 : ℝ)
  have h0' : Matrix.single j i (1 : ℝ) * Matrix.single j i (1 : ℝ) = 0 :=
    Matrix.single_mul_single_of_ne (1 : ℝ) j i j hij (1 : ℝ)
  have h1 : Matrix.single i j (1 : ℝ) * Matrix.single j i (1 : ℝ) = Matrix.single i i (1 : ℝ) := by
    rw [Matrix.single_mul_single_same (1 : ℝ) i j i (1 : ℝ)]; norm_num
  have h2 : Matrix.single j i (1 : ℝ) * Matrix.single i j (1 : ℝ) = Matrix.single j j (1 : ℝ) := by
    rw [Matrix.single_mul_single_same (1 : ℝ) j i j (1 : ℝ)]; norm_num
  rw [planeSymM, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, h0, h1, h2, h0', planeProjM]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.planeSymM_mul_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.planeSymM_mul_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.planeSymM_mul_self ``Submission.DifferentialGeometry.Analysis.planeSymM_mul_self

theorem planeSymM_mul_planeProjM {i j : Fin n} (hij : i ≠ j) :
    planeSymM i j * planeProjM i j = planeSymM i j := by
  have h1 : Matrix.single i j (1 : ℝ) * Matrix.single i i (1 : ℝ) = 0 :=
    Matrix.single_mul_single_of_ne (1 : ℝ) i j i hij.symm (1 : ℝ)
  have h2 : Matrix.single i j (1 : ℝ) * Matrix.single j j (1 : ℝ) = Matrix.single i j (1 : ℝ) := by
    rw [Matrix.single_mul_single_same (1 : ℝ) i j j (1 : ℝ)]; norm_num
  have h3 : Matrix.single j i (1 : ℝ) * Matrix.single i i (1 : ℝ) = Matrix.single j i (1 : ℝ) := by
    rw [Matrix.single_mul_single_same (1 : ℝ) j i i (1 : ℝ)]; norm_num
  have h4 : Matrix.single j i (1 : ℝ) * Matrix.single j j (1 : ℝ) = 0 :=
    Matrix.single_mul_single_of_ne (1 : ℝ) j i j hij (1 : ℝ)
  rw [planeSymM, planeProjM]
  simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_add, h1, h2, h3, h4, sub_zero]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.planeSymM_mul_planeProjM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.planeSymM_mul_planeProjM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.planeSymM_mul_planeProjM ``Submission.DifferentialGeometry.Analysis.planeSymM_mul_planeProjM

theorem realizesGerm_matEnd_transvection {i j : Fin n} (hij : i ≠ j) (c : ℝ) :
    RealizesGerm (fun x => matEnd (Matrix.transvection i j c) x) (Metric.closedBall 0 2) := by
  have hsq : Matrix.single i j c * Matrix.single i j c = 0 :=
    Matrix.single_mul_single_of_ne c i j i hij.symm c
  let N : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) := matEnd (Matrix.single i j c)
  have hNN : N * N = 0 := by
    rw [← matEnd_mul, hsq, matEnd_zero]
  have hNzero (y : EuclideanSpace ℝ (Fin n)) : N (N y) = 0 := by
    have h2 : (N * N) y = 0 := by rw [hNN]; rfl
    rwa [mul_apply_eq_comp] at h2
  have hv : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin n) => N x) := N.contDiff
  have hΓ : Continuous (fun q : EuclideanSpace ℝ (Fin n) × ℝ => q.1 + q.2 • N q.1) :=
    continuous_fst.add (continuous_snd.smul (N.continuous.comp continuous_fst))
  have hΓzero : ∀ x : EuclideanSpace ℝ (Fin n), x + (0 : ℝ) • N x = x := by
    intro x; simp
  have hΓfix : ∀ t ∈ _root_.Set.Icc (0 : ℝ) 1, (0 : EuclideanSpace ℝ (Fin n)) + t • N 0 = 0 := by
    intro t _; simp
  have hΓderiv : ∀ x t, t ∈ _root_.Set.Icc (0 : ℝ) 1 →
      HasDerivAt (fun s : ℝ => x + s • N x) (N (x + t • N x)) t := by
    intro x t _
    have h1 : HasDerivAt (fun s : ℝ => x + s • N x) (N x) t := by
      simpa using ((hasDerivAt_id t).smul_const (N x)).const_add x
    have h2 : N (x + t • N x) = N x := by
      rw [map_add, map_smul, hNzero x, smul_zero, add_zero]
    rw [h2]
    exact h1
  obtain ⟨D, hD, hDi, hD0, hDg, hfix⟩ :=
    exists_compact_isotopy_realizing_flow_germ (v := fun x : EuclideanSpace ℝ (Fin n) => N x)
      hv (fun q : EuclideanSpace ℝ (Fin n) × ℝ => q.1 + q.2 • N q.1) hΓ hΓzero hΓfix hΓderiv
      1 (by norm_num)
  refine ⟨by simp, _root_.ProperSpace.isCompact_closedBall _ _, D, hD, hDi, hD0, ?_,
    fun p z hz => hfix p z (by simpa using hz)⟩
  refine hDg.trans (Filter.EventuallyEq.of_eq ?_)
  funext x
  change x + (1 : ℝ) • N x = matEnd (Matrix.transvection i j c) x
  rw [Matrix.transvection, matEnd_add, matEnd_one, add_apply]
  simp only [one_apply_eq_self, one_smul]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.realizesGerm_matEnd_transvection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.realizesGerm_matEnd_transvection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.realizesGerm_matEnd_transvection ``Submission.DifferentialGeometry.Analysis.realizesGerm_matEnd_transvection

theorem realizesGerm_matEnd_coordScale (i : Fin n) (c : ℝ) (hc : 0 < c) :
    RealizesGerm (fun x => matEnd (1 + (c - 1) • coordProjM i) x) (Metric.closedBall 0 2) := by
  let P : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) := matEnd (coordProjM i)
  have hPP : P * P = P := by
    rw [← matEnd_mul, coordProjM_mul_self]
  have hPP' (y : EuclideanSpace ℝ (Fin n)) : P (P y) = P y := by
    have h2 : (P * P) y = P y := by rw [hPP]
    rwa [mul_apply_eq_comp] at h2
  have hv : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin n) => (Real.log c) • P x) := by
    fun_prop
  have hΓ : Continuous (fun q : EuclideanSpace ℝ (Fin n) × ℝ =>
      q.1 + (Real.exp (q.2 * Real.log c) - 1) • P q.1) := by fun_prop
  have hΓzero : ∀ x : EuclideanSpace ℝ (Fin n), x + (Real.exp (0 * Real.log c) - 1) • P x = x := by
    intro x; simp
  have hΓfix : ∀ t ∈ _root_.Set.Icc (0 : ℝ) 1,
      (0 : EuclideanSpace ℝ (Fin n)) + (Real.exp (t * Real.log c) - 1) • P 0 = 0 := by
    intro t _; simp
  have hΓderiv : ∀ x t, t ∈ _root_.Set.Icc (0 : ℝ) 1 →
      HasDerivAt (fun s : ℝ => x + (Real.exp (s * Real.log c) - 1) • P x)
        ((Real.log c) • P (x + (Real.exp (t * Real.log c) - 1) • P x)) t := by
    intro x t _
    have h1 : HasDerivAt (fun s : ℝ => Real.exp (s * Real.log c) - 1)
        (Real.exp (t * Real.log c) * Real.log c) t := by
      simpa using ((((hasDerivAt_id t).mul_const (Real.log c)).exp).sub_const 1)
    have h2 := (h1.smul_const (P x)).const_add x
    have h3 : (Real.log c) • P (x + (Real.exp (t * Real.log c) - 1) • P x)
        = (Real.exp (t * Real.log c) * Real.log c) • P x := by
      rw [map_add, map_smul, hPP' x, smul_add]
      rw [smul_smul]
      rw [← add_smul]
      congr 1
      ring
    rw [h3]
    exact h2
  obtain ⟨D, hD, hDi, hD0, hDg, hfix⟩ :=
    exists_compact_isotopy_realizing_flow_germ
      (v := fun x : EuclideanSpace ℝ (Fin n) => (Real.log c) • P x) hv
      (fun q : EuclideanSpace ℝ (Fin n) × ℝ => q.1 + (Real.exp (q.2 * Real.log c) - 1) • P q.1)
      hΓ hΓzero hΓfix hΓderiv 1 (by norm_num)
  refine ⟨by simp, _root_.ProperSpace.isCompact_closedBall _ _, D, hD, hDi, hD0, ?_,
    fun p z hz => hfix p z (by simpa using hz)⟩
  refine hDg.trans (Filter.EventuallyEq.of_eq ?_)
  funext x
  change x + (Real.exp (1 * Real.log c) - 1) • P x = matEnd (1 + (c - 1) • coordProjM i) x
  rw [one_mul, Real.exp_log hc, matEnd_add, matEnd_one, matEnd_smul, add_apply]
  simp only [one_apply_eq_self]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.realizesGerm_matEnd_coordScale then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.realizesGerm_matEnd_coordScale"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.realizesGerm_matEnd_coordScale ``Submission.DifferentialGeometry.Analysis.realizesGerm_matEnd_coordScale

theorem realizesGerm_matEnd_planeFlip {i j : Fin n} (hij : i ≠ j) :
    RealizesGerm (fun x => x - 2 • (matEnd (planeProjM i j) x)) (Metric.closedBall 0 2) := by
  let J : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) := matEnd (planeSymM i j)
  let P : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) := matEnd (planeProjM i j)
  have hJJ : J * J = -P := by rw [← matEnd_mul, planeSymM_mul_self hij, matEnd_neg]
  have hJP : J * P = J := by rw [← matEnd_mul, planeSymM_mul_planeProjM hij]
  have hJJ' (y : EuclideanSpace ℝ (Fin n)) : J (J y) = - P y := by
    have h2 : (J * J) y = (-P) y := by rw [hJJ]
    rwa [mul_apply_eq_comp] at h2
  have hJP' (y : EuclideanSpace ℝ (Fin n)) : J (P y) = J y := by
    have h2 : (J * P) y = J y := by rw [hJP]
    rwa [mul_apply_eq_comp] at h2
  have hv : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin n) => Real.pi • (J x)) := by fun_prop
  have hΓ : Continuous (fun q : EuclideanSpace ℝ (Fin n) × ℝ =>
      q.1 - P q.1 + Real.cos (Real.pi * q.2) • P q.1 +
        Real.sin (Real.pi * q.2) • (J q.1)) := by fun_prop
  have hΓzero : ∀ x : EuclideanSpace ℝ (Fin n),
      x - P x + Real.cos (Real.pi * 0) • P x + Real.sin (Real.pi * 0) • (J x) = x := by
    intro x; simp
  have hΓfix : ∀ t ∈ _root_.Set.Icc (0 : ℝ) 1,
      (0 : EuclideanSpace ℝ (Fin n)) - P 0 + Real.cos (Real.pi * t) • P 0 +
        Real.sin (Real.pi * t) • (J 0) = 0 := by
    intro t _; simp
  have hΓderiv : ∀ x t, t ∈ _root_.Set.Icc (0 : ℝ) 1 →
      HasDerivAt (fun s : ℝ => x - P x + Real.cos (Real.pi * s) • P x +
          Real.sin (Real.pi * s) • (J x))
        (Real.pi • (J (x - P x + Real.cos (Real.pi * t) • P x +
          Real.sin (Real.pi * t) • (J x)))) t := by
    intro x t _
    have hcos : HasDerivAt (fun s : ℝ => Real.cos (Real.pi * s) • P x)
        ((-(Real.sin (Real.pi * t)) * Real.pi) • P x) t := by
      have h := (Real.hasDerivAt_cos (Real.pi * t)).comp t
        ((hasDerivAt_id t).const_mul Real.pi)
      simpa [mul_comm] using h.smul_const (P x)
    have hsin : HasDerivAt (fun s : ℝ => Real.sin (Real.pi * s) • (J x))
        ((Real.cos (Real.pi * t) * Real.pi) • (J x)) t := by
      have h := (Real.hasDerivAt_sin (Real.pi * t)).comp t
        ((hasDerivAt_id t).const_mul Real.pi)
      simpa [mul_comm] using h.smul_const (J x)
    have h3 : HasDerivAt (fun s : ℝ => x - P x + Real.cos (Real.pi * s) • P x +
          Real.sin (Real.pi * s) • (J x))
        ((-(Real.sin (Real.pi * t)) * Real.pi) • P x +
          (Real.cos (Real.pi * t) * Real.pi) • (J x)) t :=
      (hcos.const_add (x - P x)).add hsin
    have h4 : Real.pi • (J (x - P x + Real.cos (Real.pi * t) • P x +
          Real.sin (Real.pi * t) • (J x)))
        = (-(Real.sin (Real.pi * t)) * Real.pi) • P x +
          (Real.cos (Real.pi * t) * Real.pi) • (J x) := by
      rw [map_add, map_add, map_sub, map_smul, map_smul, hJP' x, hJJ' x]
      module
    rw [h4]
    exact h3
  obtain ⟨D, hD, hDi, hD0, hDg, hfix⟩ :=
    exists_compact_isotopy_realizing_flow_germ
      (v := fun x : EuclideanSpace ℝ (Fin n) => Real.pi • (J x)) hv
      (fun q : EuclideanSpace ℝ (Fin n) × ℝ =>
        q.1 - P q.1 + Real.cos (Real.pi * q.2) • P q.1 +
          Real.sin (Real.pi * q.2) • (J q.1))
      hΓ hΓzero hΓfix hΓderiv 1 (by norm_num)
  refine ⟨by simp, _root_.ProperSpace.isCompact_closedBall _ _, D, hD, hDi, hD0, ?_,
    fun p z hz => hfix p z (by simpa using hz)⟩
  refine hDg.trans (Filter.EventuallyEq.of_eq ?_)
  funext x
  change x - P x + Real.cos (Real.pi * 1) • P x + Real.sin (Real.pi * 1) • (J x)
    = x - 2 • P x
  simp only [mul_one, Real.cos_pi, Real.sin_pi]
  module

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.realizesGerm_matEnd_planeFlip then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.realizesGerm_matEnd_planeFlip"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.realizesGerm_matEnd_planeFlip ``Submission.DifferentialGeometry.Analysis.realizesGerm_matEnd_planeFlip


omit [FiniteDimensional ℝ E] in
theorem RealizesGerm.congr {f g : E → E} {K : Set E} (hfg : f = g) (h : RealizesGerm f K) :
    RealizesGerm g K := by
  rw [← hfg]
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.RealizesGerm.congr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.RealizesGerm.congr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.RealizesGerm.congr ``Submission.DifferentialGeometry.Analysis.RealizesGerm.congr

theorem realizesGerm_matEnd_prod (l : List (Matrix (Fin n) (Fin n) ℝ))
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (h : ∀ m ∈ l, RealizesGerm (fun x => matEnd m x) K) :
    RealizesGerm (fun x => matEnd l.prod x) K := by
  induction l with
  | nil =>
      rw [List.prod_nil, matEnd_one]
      exact RealizesGerm.refl K hK
  | cons m l ih =>
      have hm : RealizesGerm (fun x => matEnd m x) K := h m (List.mem_cons_self ..)
      have hl : RealizesGerm (fun x => matEnd l.prod x) K :=
        ih (fun m' hm' => h m' (List.mem_cons_of_mem _ hm'))
      have hcomp : RealizesGerm ((fun x => matEnd m x) ∘ fun x => matEnd l.prod x) K :=
        (hm.comp hl).mono (by intro x hx; exact hx.elim id id) hK
      refine RealizesGerm.congr ?_ hcomp
      funext x
      simp only [Function.comp_apply]
      rw [List.prod_cons, matEnd_mul, mul_apply_eq_comp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.realizesGerm_matEnd_prod then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.realizesGerm_matEnd_prod"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.realizesGerm_matEnd_prod ``Submission.DifferentialGeometry.Analysis.realizesGerm_matEnd_prod


theorem coordProjM_mul_self' (i : Fin n) : coordProjM i * coordProjM i = coordProjM i := by
  rw [coordProjM, Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  by_cases hk : k = i <;> simp [hk]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.coordProjM_mul_self' then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.coordProjM_mul_self'"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.coordProjM_mul_self' ``Submission.DifferentialGeometry.Analysis.coordProjM_mul_self'

theorem coordProjM_mul_diagonal (i : Fin n) (d : Fin n → ℝ) :
    coordProjM i * Matrix.diagonal d = Matrix.diagonal (Pi.single i (d i)) := by
  rw [coordProjM, Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  by_cases hk : k = i <;> simp [hk]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.coordProjM_mul_diagonal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.coordProjM_mul_diagonal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.coordProjM_mul_diagonal ``Submission.DifferentialGeometry.Analysis.coordProjM_mul_diagonal

def coordScaleM (i : Fin n) (c : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  1 + (c - 1) • coordProjM i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.coordScaleM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.coordScaleM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.coordScaleM ``Submission.DifferentialGeometry.Analysis.coordScaleM

theorem coordScaleM_mul_diagonal (i : Fin n) (c : ℝ) (d : Fin n → ℝ) :
    coordScaleM i c * Matrix.diagonal d = Matrix.diagonal (Function.update d i (c * d i)) := by
  rw [coordScaleM, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, coordProjM_mul_diagonal,
    ← Matrix.diagonal_smul, Matrix.diagonal_add, Matrix.diagonal_injective.eq_iff]
  funext k
  by_cases hk : k = i
  · subst hk
    simp [Function.update_self, Pi.single_eq_same]
    ring
  · rw [Pi.smul_apply, Pi.single_eq_of_ne hk, smul_zero, add_zero, Function.update_of_ne hk]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.coordScaleM_mul_diagonal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.coordScaleM_mul_diagonal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.coordScaleM_mul_diagonal ``Submission.DifferentialGeometry.Analysis.coordScaleM_mul_diagonal

theorem prod_coordScaleM (l : List (Fin n)) (hl : l.Nodup) (c d : Fin n → ℝ) :
    (l.map (fun i => coordScaleM i (c i))).prod * Matrix.diagonal d
      = Matrix.diagonal (fun k => if k ∈ l then c k * d k else d k) := by
  induction l with
  | nil => simp
  | cons i l ih =>
      have hil : i ∉ l := (List.nodup_cons.mp hl).1
      have hl' : l.Nodup := (List.nodup_cons.mp hl).2
      rw [List.map_cons, List.prod_cons, Matrix.mul_assoc, ih hl', coordScaleM_mul_diagonal]
      congr 1
      funext k
      by_cases hki : k = i
      · subst hki
        simp [hil]
      · by_cases hkl : k ∈ l
        · simp only [Function.update_of_ne hki, hkl, ↓reduceIte, List.mem_cons_of_mem i hkl]
        · simp only [Function.update_of_ne hki, hkl, ↓reduceIte,
            if_neg (fun h => (List.mem_cons.mp h).elim (fun h' => hki h') hkl)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.prod_coordScaleM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.prod_coordScaleM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.prod_coordScaleM ``Submission.DifferentialGeometry.Analysis.prod_coordScaleM

theorem prod_coordScaleM_finRange (c : Fin n → ℝ) :
    ((List.finRange n).map (fun i => coordScaleM i (c i))).prod = Matrix.diagonal c := by
  have h := prod_coordScaleM (List.finRange n) (List.nodup_finRange n) c (fun _ => (1 : ℝ))
  have h1 : Matrix.diagonal (fun _ : Fin n => (1 : ℝ)) = 1 := Matrix.diagonal_one'
  have h' : (fun k => if k ∈ List.finRange n then c k * 1 else 1) = c := by
    funext k
    rw [if_pos (List.mem_finRange ..), mul_one]
  rw [h1, Matrix.mul_one, h'] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.prod_coordScaleM_finRange then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.prod_coordScaleM_finRange"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.prod_coordScaleM_finRange ``Submission.DifferentialGeometry.Analysis.prod_coordScaleM_finRange

theorem realizesGerm_matEnd_diagonal_pos (c : Fin n → ℝ) (hc : ∀ i, 0 < c i) :
    RealizesGerm (fun x => matEnd (Matrix.diagonal c) x) (Metric.closedBall 0 2) := by
  have hlist : ∀ m ∈ (List.finRange n).map (fun i => coordScaleM i (c i)),
      RealizesGerm (fun x => matEnd m x) (Metric.closedBall 0 2) := by
    intro m hm
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hm
    exact realizesGerm_matEnd_coordScale i (c i) (hc i)
  refine RealizesGerm.congr ?_
    (realizesGerm_matEnd_prod ((List.finRange n).map (fun i => coordScaleM i (c i)))
      (_root_.ProperSpace.isCompact_closedBall _ _) hlist)
  funext x
  rw [prod_coordScaleM_finRange]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.realizesGerm_matEnd_diagonal_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.realizesGerm_matEnd_diagonal_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.realizesGerm_matEnd_diagonal_pos ``Submission.DifferentialGeometry.Analysis.realizesGerm_matEnd_diagonal_pos

end DifferentialGeometry.Analysis
