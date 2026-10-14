import Submission.DifferentialGeometry.Geometry.Comparison.Variation.Curve.ArcLength
import Mathlib.Geometry.Manifold.Riemannian.PathELength

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Filter _root_.MeasureTheory _root_.intervalIntegral
open scoped _root_.Manifold _root_.Topology _root_.ContDiff

namespace DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

lemma continuousOn_velocityWithin_totalSpace_of_contMDiffOn
    {η : ℝ → M} {a b : ℝ} (hab : a < b)
    (hη : ContMDiffOn 𝓘(ℝ, ℝ) I 1 η (Set.Icc a b)) :
    ContinuousOn
      (fun t : ℝ =>
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (η t)
          (mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc a b) t (1 : ℝ)) : TangentBundle I M))
      (Set.Icc a b) := by
  have hUnique : UniqueMDiffOn 𝓘(ℝ, ℝ) (Set.Icc a b) := by
    intro x hx
    rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
    exact (uniqueDiffOn_Icc hab) x hx
  have hTan := hη.continuousOn_tangentMapWithin (le_refl 1) hUnique
  have hLift : Continuous (fun t : ℝ =>
      (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) := by
    have h_homeo :
        Continuous ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm :
          ModelProd ℝ ℝ → TangentBundle 𝓘(ℝ, ℝ) ℝ) :=
      (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm.continuous
    exact h_homeo.comp (continuous_id.prodMk continuous_const)
  have hMaps : Set.MapsTo (fun t : ℝ => (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ))
      (Set.Icc a b) (Bundle.TotalSpace.proj ⁻¹' (Set.Icc a b)) := by
    intro t ht
    simpa using ht
  have hComp : ContinuousOn
      (fun t : ℝ => tangentMapWithin 𝓘(ℝ, ℝ) I η (Set.Icc a b)
        (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ))
      (Set.Icc a b) :=
    hTan.comp hLift.continuousOn hMaps
  refine hComp.congr ?_
  intro t _ht
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Geodesic.continuousOn_velocityWithin_totalSpace_of_contMDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Geodesic.continuousOn_velocityWithin_totalSpace_of_contMDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Geodesic.continuousOn_velocityWithin_totalSpace_of_contMDiffOn ``Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic.continuousOn_velocityWithin_totalSpace_of_contMDiffOn

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private lemma continuousOn_g_speedSq_velocityWithin
    (g : SmoothRiemannianMetric I M) {η : ℝ → M} {a b : ℝ}
    (hVW : ContinuousOn
      (fun t : ℝ =>
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (η t)
          (mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc a b) t (1 : ℝ)) : TangentBundle I M))
      (Set.Icc a b)) :
    ContinuousOn
      (fun t : ℝ =>
        g.inner (η t)
          (mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc a b) t (1 : ℝ))
          (mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc a b) t (1 : ℝ)))
      (Set.Icc a b) := by
  let cg : Bundle.ContinuousRiemannianMetric E (TangentSpace I : M → Type _) :=
    g.toContinuousRiemannianMetric
  let rb : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨cg.toRiemannianMetric⟩
  have h := ContinuousOn.inner_bundle (F := E) (B := M)
    (E := (TangentSpace I : M → Type _))
    (b := η)
    (v := fun t : ℝ => mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc a b) t (1 : ℝ))
    (w := fun t : ℝ => mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc a b) t (1 : ℝ))
    (s := Set.Icc a b) hVW hVW
  refine h.congr ?_
  intro t _ht
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic.continuousOn_g_speedSq_velocityWithin
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.Geodesic.continuousOn_g_speedSq_velocityWithin target :: scope.openDecls } }

lemma speedSqrt_integrableOn_Icc_of_C1
    (g : SmoothRiemannianMetric I M) {η : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hη : ContMDiffOn 𝓘(ℝ, ℝ) I 1 η (Set.Icc a b)) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => Real.sqrt
        (g.inner (η t)
          (mfderiv 𝓘(ℝ, ℝ) I η t (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) I η t (1 : ℝ))))
      (Set.Icc a b) MeasureTheory.volume := by
  classical
  rcases eq_or_lt_of_le hab with hab_eq | hab_lt
  · subst hab_eq
    rw [Set.Icc_self, MeasureTheory.integrableOn_singleton_iff]
    exact Or.inr (by simp)
  · have hVW := continuousOn_velocityWithin_totalSpace_of_contMDiffOn (I := I) (M := M)
      hab_lt hη
    have hSpeedSq := continuousOn_g_speedSq_velocityWithin (I := I) (M := M) g hVW
    have hSqrtW : ContinuousOn
        (fun t : ℝ => Real.sqrt
          (g.inner (η t)
            (mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc a b) t (1 : ℝ))
            (mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc a b) t (1 : ℝ))))
        (Set.Icc a b) :=
      Real.continuous_sqrt.comp_continuousOn hSpeedSq
    have hIntW : MeasureTheory.IntegrableOn
        (fun t : ℝ => Real.sqrt
          (g.inner (η t)
            (mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc a b) t (1 : ℝ))
            (mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc a b) t (1 : ℝ))))
        (Set.Icc a b) MeasureTheory.volume :=
      hSqrtW.integrableOn_Icc
    have hAgree : ∀ t ∈ Set.Ioo a b,
        Real.sqrt
            (g.inner (η t)
              (mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc a b) t (1 : ℝ))
              (mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc a b) t (1 : ℝ)))
          = Real.sqrt
            (g.inner (η t)
              (mfderiv 𝓘(ℝ, ℝ) I η t (1 : ℝ))
              (mfderiv 𝓘(ℝ, ℝ) I η t (1 : ℝ))) := by
      intro t ht
      have hmem : Set.Icc a b ∈ nhds t :=
        Icc_mem_nhds ht.1 ht.2
      rw [mfderivWithin_of_mem_nhds hmem]
    have hae : (fun t : ℝ => Real.sqrt
          (g.inner (η t)
            (mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc a b) t (1 : ℝ))
            (mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc a b) t (1 : ℝ))))
        =ᵐ[MeasureTheory.volume.restrict (Set.Icc a b)]
        (fun t : ℝ => Real.sqrt
          (g.inner (η t)
            (mfderiv 𝓘(ℝ, ℝ) I η t (1 : ℝ))
            (mfderiv 𝓘(ℝ, ℝ) I η t (1 : ℝ)))) := by
      have hIoo_ae : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc a b)),
          t ∈ Set.Ioo a b := by
        rw [← MeasureTheory.restrict_Ioo_eq_restrict_Icc]
        exact MeasureTheory.ae_restrict_mem measurableSet_Ioo
      filter_upwards [hIoo_ae] with t ht
      exact hAgree t ht
    exact hIntW.congr hae

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Geodesic.speedSqrt_integrableOn_Icc_of_C1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Geodesic.speedSqrt_integrableOn_Icc_of_C1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Geodesic.speedSqrt_integrableOn_Icc_of_C1 ``Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic.speedSqrt_integrableOn_Icc_of_C1

section ENorm

variable [(x : M) → ENorm (TangentSpace I x)]

theorem pathELength_eq_arcLength_of_enorm_eq
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hγint : _root_.MeasureTheory.IntegrableOn (fun t : ℝ => Real.sqrt
      (g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)))) (_root_.Set.Ioo a b))
    (hEnorm : ∀ t ∈ _root_.Set.Ioo a b, ‖mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)‖ₑ =
      ENNReal.ofReal (Real.sqrt (g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))))) :
    pathELength I γ a b = ENNReal.ofReal (Variation.arcLength (I := I) g γ a b) := by
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Ioo]
  unfold Variation.arcLength
  rw [intervalIntegral.integral_of_le hab, _root_.MeasureTheory.integral_Ioc_eq_integral_Ioo,
    _root_.MeasureTheory.ofReal_integral_eq_lintegral_ofReal hγint
      (_root_.MeasureTheory.ae_of_all _ (fun _ => Real.sqrt_nonneg _))]
  exact _root_.MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo hEnorm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Geodesic.pathELength_eq_arcLength_of_enorm_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Geodesic.pathELength_eq_arcLength_of_enorm_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Geodesic.pathELength_eq_arcLength_of_enorm_eq ``Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic.pathELength_eq_arcLength_of_enorm_eq

theorem riemannianEDist_le_arcLength_of_enorm_eq
    [(x : M) → ENormSMulClass ℝ (TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (_root_.Set.Icc a b))
    (hEnorm : ∀ t ∈ _root_.Set.Ioo a b, ‖mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)‖ₑ =
      ENNReal.ofReal (Real.sqrt (g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))))) :
    riemannianEDist I (γ a) (γ b) ≤ ENNReal.ofReal (Variation.arcLength (I := I) g γ a b) := by
  exact (_root_.Manifold.riemannianEDist_le_pathELength hγ rfl rfl hab).trans_eq
    (pathELength_eq_arcLength_of_enorm_eq (I := I) g hab
      ((speedSqrt_integrableOn_Icc_of_C1 (I := I) g hab hγ).mono_set _root_.Set.Ioo_subset_Icc_self)
      hEnorm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Geodesic.riemannianEDist_le_arcLength_of_enorm_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Geodesic.riemannianEDist_le_arcLength_of_enorm_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Geodesic.riemannianEDist_le_arcLength_of_enorm_eq ``Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic.riemannianEDist_le_arcLength_of_enorm_eq

end ENorm

theorem pathELength_eq_arcLength
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {a b : ℝ}
    (hab : a ≤ b)
    (hγ_int : MeasureTheory.IntegrableOn
      (fun t : ℝ => Real.sqrt
        (g.inner (γ t)
          (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)))) (Set.Icc a b) MeasureTheory.volume)
    (hEnorm : ∀ t ∈ Set.Icc a b,
        ‖mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)‖ₑ
          = ENNReal.ofReal (Real.sqrt
              (g.inner (γ t)
                (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
                (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))))) :
    _root_.Manifold.pathELength I γ a b
      = ENNReal.ofReal
        (DifferentialGeometry.Geometry.Riemannian.Variation.arcLength (I := I) g γ a b) := by
  exact pathELength_eq_arcLength_of_enorm_eq (I := I) g hab
    (hγ_int.mono_set _root_.Set.Ioo_subset_Icc_self) (fun t ht => hEnorm t (_root_.Set.Ioo_subset_Icc_self ht))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Geodesic.pathELength_eq_arcLength then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Geodesic.pathELength_eq_arcLength"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Geodesic.pathELength_eq_arcLength ``Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic.pathELength_eq_arcLength

section RiemannianBundle

variable [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem pathELength_eq_arcLength_riemannianBundle
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {a b : ℝ}
    (hab : a ≤ b)
    (hγ_int : MeasureTheory.IntegrableOn
      (fun t : ℝ => Real.sqrt
        (g.inner (γ t)
          (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)))) (Set.Icc a b) MeasureTheory.volume)
    (hEnorm : ∀ t ∈ Set.Icc a b,
        ‖mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)‖ₑ
          = ENNReal.ofReal (Real.sqrt
              (g.inner (γ t)
                (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
                (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))))) :
    _root_.Manifold.pathELength I γ a b
      = ENNReal.ofReal
        (DifferentialGeometry.Geometry.Riemannian.Variation.arcLength (I := I) g γ a b) := by
  exact pathELength_eq_arcLength_of_enorm_eq (I := I) g hab
    (hγ_int.mono_set _root_.Set.Ioo_subset_Icc_self) (fun t ht => hEnorm t (_root_.Set.Ioo_subset_Icc_self ht))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Geodesic.pathELength_eq_arcLength_riemannianBundle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Geodesic.pathELength_eq_arcLength_riemannianBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Geodesic.pathELength_eq_arcLength_riemannianBundle ``Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic.pathELength_eq_arcLength_riemannianBundle

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianEDist_le_arcLength
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Set.Icc a b))
    (hEnorm : ∀ t ∈ Set.Icc a b,
        ‖mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)‖ₑ
          = ENNReal.ofReal (Real.sqrt
              (g.inner (γ t)
                (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
                (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))))) :
    _root_.Manifold.riemannianEDist I (γ a) (γ b)
      ≤ ENNReal.ofReal
        (DifferentialGeometry.Geometry.Riemannian.Variation.arcLength (I := I) g γ a b) := by
  exact riemannianEDist_le_arcLength_of_enorm_eq (I := I) g hab hγ
    (fun t ht => hEnorm t (_root_.Set.Ioo_subset_Icc_self ht))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Geodesic.riemannianEDist_le_arcLength then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Geodesic.riemannianEDist_le_arcLength"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Geodesic.riemannianEDist_le_arcLength ``Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic.riemannianEDist_le_arcLength

end RiemannianBundle

end DifferentialGeometry.Geometry.Riemannian.Geodesic
