import Submission.DifferentialGeometry.Analysis.ODE.Flow.CompactSupport
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Compactness.Compact

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace Diffeomorph
open _root_.Diffeomorph

open _root_.Submission.DifferentialGeometry.Analysis.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  (v : (x : M) → TangentSpace I x)
  (hv : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
  (hsupp : IsCompact (tsupport v))

open _root_.Diffeomorph in
noncomputable def compactSupportFlow (t : ℝ) : Diffeomorph I I M M ∞ := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let hc := exists_globalIntegralCurve_of_compactSupport v hv hsupp
  have hv1 : CMDiff 1 (fun x : M => (⟨x, v x⟩ : TangentBundle I M)) := hv.of_le (by simp)
  have hj := contMDiff_globalFlow_joint_of_compactSupport v hv hsupp
  refine
    { toEquiv :=
        { toFun := fun x => curveAt v hc x t
          invFun := fun x => curveAt v hc x (-t)
          left_inv := ?_
          right_inv := ?_ }
      contMDiff_toFun := hj.comp (contMDiff_const.prodMk contMDiff_id)
      contMDiff_invFun := hj.comp (contMDiff_const.prodMk contMDiff_id) }
  · intro x
    dsimp only
    rw [← curveAt_add v hv1 hc, add_neg_cancel, curveAt_zero]
  · intro x
    dsimp only
    rw [← curveAt_add v hv1 hc, neg_add_cancel, curveAt_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.compactSupportFlow then
    throwError "Refusing to shadow existing declaration Diffeomorph.compactSupportFlow"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.compactSupportFlow ``Submission.Diffeomorph.compactSupportFlow

open _root_.Diffeomorph in
theorem compactSupportFlow_apply (t : ℝ) (x : M) :
    compactSupportFlow v hv hsupp t x =
      curveAt v (by
        let : CompleteSpace E := FiniteDimensional.complete ℝ E
        exact exists_globalIntegralCurve_of_compactSupport v hv hsupp) x t := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.compactSupportFlow_apply then
    throwError "Refusing to shadow existing declaration Diffeomorph.compactSupportFlow_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.compactSupportFlow_apply ``Submission.Diffeomorph.compactSupportFlow_apply

open _root_.Diffeomorph in
theorem isMIntegralCurve_compactSupportFlow (x : M) :
    IsMIntegralCurve (fun t => compactSupportFlow v hv hsupp t x) v := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact curveAt_integralCurve v (exists_globalIntegralCurve_of_compactSupport v hv hsupp) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.isMIntegralCurve_compactSupportFlow then
    throwError "Refusing to shadow existing declaration Diffeomorph.isMIntegralCurve_compactSupportFlow"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.isMIntegralCurve_compactSupportFlow ``Submission.Diffeomorph.isMIntegralCurve_compactSupportFlow

open _root_.Diffeomorph in
@[simp] theorem compactSupportFlow_zero :
    compactSupportFlow v hv hsupp 0 = Diffeomorph.refl I M ∞ := by
  apply Diffeomorph.ext
  intro x
  exact curveAt_zero v _ x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.compactSupportFlow_zero then
    throwError "Refusing to shadow existing declaration Diffeomorph.compactSupportFlow_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.compactSupportFlow_zero ``Submission.Diffeomorph.compactSupportFlow_zero

open _root_.Diffeomorph in
theorem compactSupportFlow_add (s t : ℝ) :
    compactSupportFlow v hv hsupp (s + t) =
      (compactSupportFlow v hv hsupp s).trans (compactSupportFlow v hv hsupp t) := by
  apply Diffeomorph.ext
  intro x
  exact curveAt_add v (hv.of_le (by simp)) _ x s t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.compactSupportFlow_add then
    throwError "Refusing to shadow existing declaration Diffeomorph.compactSupportFlow_add"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.compactSupportFlow_add ``Submission.Diffeomorph.compactSupportFlow_add

open _root_.Diffeomorph in
@[simp] theorem compactSupportFlow_symm (t : ℝ) :
    (compactSupportFlow v hv hsupp t).symm = compactSupportFlow v hv hsupp (-t) := by
  apply Diffeomorph.ext
  intro x
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.compactSupportFlow_symm then
    throwError "Refusing to shadow existing declaration Diffeomorph.compactSupportFlow_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.compactSupportFlow_symm ``Submission.Diffeomorph.compactSupportFlow_symm

open _root_.Diffeomorph in
theorem contMDiff_compactSupportFlow :
    ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞
      (fun p : ℝ × M => compactSupportFlow v hv hsupp p.1 p.2) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact contMDiff_globalFlow_joint_of_compactSupport v hv hsupp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.contMDiff_compactSupportFlow then
    throwError "Refusing to shadow existing declaration Diffeomorph.contMDiff_compactSupportFlow"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.contMDiff_compactSupportFlow ``Submission.Diffeomorph.contMDiff_compactSupportFlow

open _root_.Diffeomorph in
theorem contMDiff_compactSupportFlow_symm :
    ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞
      (fun p : ℝ × M => (compactSupportFlow v hv hsupp p.1).symm p.2) := by
  have hj := contMDiff_compactSupportFlow v hv hsupp
  have hn : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞
      (fun p : ℝ × M => (-p.1, p.2)) :=
    (contMDiff_neg 𝓘(ℝ, ℝ) ∞ |>.comp contMDiff_fst).prodMk contMDiff_snd
  exact hj.comp hn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.contMDiff_compactSupportFlow_symm then
    throwError "Refusing to shadow existing declaration Diffeomorph.contMDiff_compactSupportFlow_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.contMDiff_compactSupportFlow_symm ``Submission.Diffeomorph.contMDiff_compactSupportFlow_symm

open _root_.Diffeomorph in
theorem compactSupportFlow_apply_eq_self_of_eq_zero {x : M} (hx : v x = 0) (t : ℝ) :
    compactSupportFlow v hv hsupp t x = x := by
  exact curveAt_eq_self_of_eq_zero v (hv.of_le (by simp)) _ hx t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.compactSupportFlow_apply_eq_self_of_eq_zero then
    throwError "Refusing to shadow existing declaration Diffeomorph.compactSupportFlow_apply_eq_self_of_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.compactSupportFlow_apply_eq_self_of_eq_zero ``Submission.Diffeomorph.compactSupportFlow_apply_eq_self_of_eq_zero

open _root_.Diffeomorph in
theorem compactSupportFlow_symm_apply_eq_self_of_eq_zero {x : M} (hx : v x = 0) (t : ℝ) :
    (compactSupportFlow v hv hsupp t).symm x = x := by
  rw [compactSupportFlow_symm]
  exact compactSupportFlow_apply_eq_self_of_eq_zero v hv hsupp hx (-t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.compactSupportFlow_symm_apply_eq_self_of_eq_zero then
    throwError "Refusing to shadow existing declaration Diffeomorph.compactSupportFlow_symm_apply_eq_self_of_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.compactSupportFlow_symm_apply_eq_self_of_eq_zero ``Submission.Diffeomorph.compactSupportFlow_symm_apply_eq_self_of_eq_zero

open _root_.Diffeomorph in
theorem compactSupportFlow_eqOn_compl_tsupport (t : ℝ) :
    Set.EqOn (compactSupportFlow v hv hsupp t) id (tsupport v)ᶜ ∧
      Set.EqOn (compactSupportFlow v hv hsupp t).symm id (tsupport v)ᶜ := by
  constructor
  · intro x hx
    exact compactSupportFlow_apply_eq_self_of_eq_zero v hv hsupp
      (image_eq_zero_of_notMem_tsupport hx) t
  · intro x hx
    exact compactSupportFlow_symm_apply_eq_self_of_eq_zero v hv hsupp
      (image_eq_zero_of_notMem_tsupport hx) t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.compactSupportFlow_eqOn_compl_tsupport then
    throwError "Refusing to shadow existing declaration Diffeomorph.compactSupportFlow_eqOn_compl_tsupport"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.compactSupportFlow_eqOn_compl_tsupport ``Submission.Diffeomorph.compactSupportFlow_eqOn_compl_tsupport

open _root_.Diffeomorph in
theorem exists_pos_compactSupportFlow_height
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    (X : (x : M) → TangentSpace I x)
    (hX : ContMDiff I I.tangent ∞ (fun x => (X x : TangentBundle I M)))
    (hXc : HasCompactSupport X) (g : M → ℝ)
    {B U : Set M} (hB : IsCompact B) (hU : IsOpen U) (hBU : B ⊆ U)
    (hrate : ∀ x ∈ U,
      NormedSpace.fromTangentSpace (g x) (mfderiv I 𝓘(ℝ) g x (X x)) = 1) :
    ∃ δ > 0, ∀ x ∈ B, ∀ t ∈ Set.Ioo (-δ) δ,
      compactSupportFlow X hX hXc t x ∈ U ∧
      g (compactSupportFlow X hX hXc t x) = g x + t := by
  let Φ := compactSupportFlow X hX hXc
  have hΦ : Continuous (fun p : ℝ × M => Φ p.1 p.2) :=
    (contMDiff_compactSupportFlow X hX hXc).continuous
  have hzero (x : M) : Φ 0 x = x :=
    DFunLike.congr_fun (compactSupportFlow_zero X hX hXc) x
  have hslice : ({0} : Set ℝ) ×ˢ B ⊆ (fun p : ℝ × M => Φ p.1 p.2) ⁻¹' U := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    have ht0 : t = 0 := Set.mem_singleton_iff.mp ht
    subst t
    change Φ 0 x ∈ U
    rw [hzero]
    exact hBU hx
  obtain ⟨T, V, hT, _, h0T, hBV, hTV⟩ :=
    generalized_tube_lemma isCompact_singleton hB (hU.preimage hΦ) hslice
  obtain ⟨δ, hδ, hδT⟩ := Metric.isOpen_iff.mp hT 0 (h0T (by simp))
  have hstay (x : M) (hx : x ∈ B) (t : ℝ) (ht : t ∈ Set.Ioo (-δ) δ) :
      Φ t x ∈ U := by
    have htT : t ∈ T := hδT (by
      simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using abs_lt.mpr ht)
    exact hTV (show (t, x) ∈ T ×ˢ V from ⟨htT, hBV hx⟩)
  refine ⟨δ, hδ, ?_⟩
  intro x hx t ht
  refine ⟨hstay x hx t ht, ?_⟩
  have hheight {s : ℝ} (hs : s ∈ Set.Ioo (-δ) δ) :
      HasDerivAt (fun r => g (Φ r x)) 1 s := by
    have hr := hrate (Φ s x) (hstay x hx s hs)
    have hg : MDifferentiableAt I 𝓘(ℝ) g (Φ s x) := by
      by_contra hn
      have hz : NormedSpace.fromTangentSpace (g (Φ s x))
          (mfderiv I 𝓘(ℝ) g (Φ s x) (X (Φ s x))) = 0 :=
        congrArg (fun A : TangentSpace I (Φ s x) →L[ℝ] ℝ => A (X (Φ s x)))
          (mfderiv_zero_of_not_mdifferentiableAt hn)
      exact zero_ne_one (hz.symm.trans hr)
    have hfd : HasFDerivAt (fun r => g (Φ r x))
        ((mfderiv I 𝓘(ℝ) g (Φ s x)).comp
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X (Φ s x)))) s :=
      hasMFDerivAt_iff_hasFDerivAt.mp (hg.hasMFDerivAt.comp s
        (isMIntegralCurve_compactSupportFlow X hX hXc x s))
    apply hasDerivAt_iff_hasFDerivAt.mpr
    apply hfd.congr_fderiv
    apply ContinuousLinearMap.ext
    intro r
    change mfderiv I 𝓘(ℝ) g (Φ s x) (r • X (Φ s x)) = r • (1 : ℝ)
    rw [map_smul]
    exact congrArg (fun z : ℝ => r • z) hr
  have hlinear (s : ℝ) : HasDerivAt (fun r : ℝ => g x + r) 1 s :=
    (hasDerivAt_id s).const_add (g x)
  have heq : Set.EqOn (fun s => g (Φ s x)) (fun s => g x + s) (Set.Ioo (-δ) δ) :=
    isOpen_Ioo.eqOn_of_deriv_eq (convex_Ioo (-δ) δ).isPreconnected
      (fun s hs => (hheight hs).differentiableAt.differentiableWithinAt)
      (fun s _ => (hlinear s).differentiableAt.differentiableWithinAt)
      (fun s hs => by rw [(hheight hs).deriv, (hlinear s).deriv])
      (show (0 : ℝ) ∈ Set.Ioo (-δ) δ from ⟨by linarith, hδ⟩)
      (by rw [hzero]; exact (add_zero (g x)).symm)
  exact heq ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.exists_pos_compactSupportFlow_height then
    throwError "Refusing to shadow existing declaration Diffeomorph.exists_pos_compactSupportFlow_height"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.exists_pos_compactSupportFlow_height ``Submission.Diffeomorph.exists_pos_compactSupportFlow_height


end Diffeomorph
