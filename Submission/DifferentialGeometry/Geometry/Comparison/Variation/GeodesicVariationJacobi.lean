import Submission.DifferentialGeometry.Geometry.Comparison.Variation.Covariant.Jets

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Function _root_.Filter _root_.Manifold _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Topology _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.AlongCurve
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [I.Boundaryless]
  [T2Space M] in
theorem covDerivAlong_varFst_eq_covDerivAlong_varSnd
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M)
    (hf : IsSmoothVariation (I := I) f) (s t : ℝ) :
    covSnd (I := I) g f (fun r v => varFst (I := I) f r v) s t =
      covFst (I := I) g f (fun r v => varSnd (I := I) f r v) s t := by
  have h := congrFun (commute_ds_dt_intrinsic_shifted (I := I) g f hf t) s
  exact h.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.covDerivAlong_varFst_eq_covDerivAlong_varSnd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.covDerivAlong_varFst_eq_covDerivAlong_varSnd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.covDerivAlong_varFst_eq_covDerivAlong_varSnd ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.covDerivAlong_varFst_eq_covDerivAlong_varSnd

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [FiniteDimensional ℝ E]
  [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
private theorem slice_contMDiff (f : ℝ → ℝ → M)
    (hf : IsSmoothVariation (I := I) f) (s : ℝ) :
    ContMDiff 𝓘(ℝ, ℝ) I (8 : ℕ) (fun v : ℝ => f s v) := by
  have hincl : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (8 : ℕ)
      (fun v : ℝ => (s, v)) := contMDiff_const.prodMk contMDiff_id
  exact (hf : ContMDiff _ _ _ _).comp hincl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.slice_contMDiff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.Variation.slice_contMDiff target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem isJacobiAlong_varFst_of_isGeodesic
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M)
    (hf : IsSmoothVariation (I := I) f)
    (hgeo : ∀ s : ℝ, IsGeodesic (I := I) g (fun v : ℝ => f s v)) :
    IsJacobiAlong (I := I) g (fun v : ℝ => f 0 v)
      (fun v : ℝ => varFst (I := I) f 0 v) := by
  classical
  intro t₀
  have hslice_acc : ∀ s : ℝ,
      covDerivAlong (I := I) g (fun v : ℝ => f s v)
        (fun v : ℝ => mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ => f s u) v (1 : ℝ)) t₀ = 0 := by
    intro s
    have hsliceC2 : ContMDiffAt 𝓘(ℝ, ℝ) I 2 (fun v : ℝ => f s v) t₀ :=
      (slice_contMDiff (I := I) f hf s).contMDiffAt.of_le (by norm_num)
    exact covDerivAlong_velocity_eq_zero_of_hasGeodesicEquationAt_C2
      (I := I) g _ t₀ hsliceC2 ((hgeo s).hasGeodesicEquationAt t₀)
  have houterL : DifferentiableAt ℝ
      (chartRepAt (I := I) (fun s : ℝ => f s t₀)
        (fun s : ℝ => covDerivAlong (I := I) g (fun v : ℝ => f s v)
          (fun v : ℝ => mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ => f s u) v (1 : ℝ)) t₀) 0) 0 := by
    have hzero : (chartRepAt (I := I) (fun s : ℝ => f s t₀)
        (fun s : ℝ => covDerivAlong (I := I) g (fun v : ℝ => f s v)
          (fun v : ℝ => mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ => f s u) v (1 : ℝ)) t₀) 0)
        =ᶠ[𝓝 (0 : ℝ)] (fun _ : ℝ => (0 : E)) := by
      filter_upwards with s
      rw [chartRepAt_apply, hslice_acc s]
      exact map_zero _
    exact (hzero.differentiableAt_iff).mpr (differentiableAt_const _)
  have hfields : (fun v : ℝ => covDerivAlong (I := I) g (fun u : ℝ => f u v)
      (fun u : ℝ => mfderiv 𝓘(ℝ, ℝ) I (fun u' : ℝ => f u u') v (1 : ℝ)) 0)
      = (fun v : ℝ => covDerivAlong (I := I) g (fun v' : ℝ => f 0 v')
        (fun v' : ℝ => mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ => f u v') 0 (1 : ℝ)) v) :=
    funext fun v => commute_ds_dt_intrinsic (I := I) g f hf v
  have houterR : DifferentiableAt ℝ
      (chartRepAt (I := I) (fun v : ℝ => f 0 v)
        (fun v : ℝ => covDerivAlong (I := I) g (fun u : ℝ => f u v)
          (fun u : ℝ => mfderiv 𝓘(ℝ, ℝ) I (fun u' : ℝ => f u u') v (1 : ℝ)) 0) t₀) t₀ := by
    rw [hfields]
    exact variationField_covDeriv_chartRep_differentiableAt (I := I) g f hf t₀
  have hcomm := commute_ds_dt_curvature (I := I) g f hf t₀ houterL houterR
  have hT1 : covDerivAlong (I := I) g (fun s : ℝ => f s t₀)
      (fun s : ℝ => covDerivAlong (I := I) g (fun v : ℝ => f s v)
        (fun v : ℝ => mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ => f s u) v (1 : ℝ)) t₀) 0 = 0 := by
    have hfun : (fun s : ℝ => covDerivAlong (I := I) g (fun v : ℝ => f s v)
        (fun v : ℝ => mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ => f s u) v (1 : ℝ)) t₀)
        = (fun s : ℝ => (0 : TangentSpace I ((fun s' : ℝ => f s' t₀) s))) :=
      funext hslice_acc
    rw [hfun]
    exact covDerivAlong_zero (I := I) g (fun s' : ℝ => f s' t₀) 0
  rw [hT1, hfields, zero_sub, neg_eq_iff_eq_neg] at hcomm
  change covDerivAlong (I := I) g (fun v : ℝ => f 0 v)
      (fun v : ℝ => covDerivAlong (I := I) g (fun v' : ℝ => f 0 v')
        (fun v' : ℝ => mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ => f u v') 0 (1 : ℝ)) v) t₀
    + (riemannOp (LeviCivita (I := I) g) (f 0 t₀))
        (mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ => f u t₀) 0 (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ => f 0 u) t₀ (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ => f 0 u) t₀ (1 : ℝ)) = 0
  linear_combination (norm := module) hcomm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.isJacobiAlong_varFst_of_isGeodesic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.isJacobiAlong_varFst_of_isGeodesic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.isJacobiAlong_varFst_of_isGeodesic ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.isJacobiAlong_varFst_of_isGeodesic

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem isJacobiAlong_varFst_of_isGeodesic_at
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M)
    (hf : IsSmoothVariation (I := I) f)
    (hgeo : ∀ s : ℝ, IsGeodesic (I := I) g (fun v : ℝ => f s v)) (s₀ : ℝ) :
    IsJacobiAlong (I := I) g (fun v : ℝ => f s₀ v)
      (fun v : ℝ => varFst (I := I) f s₀ v) := by
  classical
  set fsh : ℝ → ℝ → M := fun a v => f (s₀ + a) v with hfsh
  have hfsh_smooth : IsSmoothVariation (I := I) fsh := by
    have hshift : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (8 : ℕ)
        (fun q : ℝ × ℝ => (s₀ + q.1, q.2)) :=
      (contMDiff_const.add contMDiff_fst).prodMk contMDiff_snd
    exact (hf : ContMDiff _ _ _ _).comp hshift
  have hgeosh : ∀ a : ℝ, IsGeodesic (I := I) g (fun v : ℝ => fsh a v) :=
    fun a => hgeo (s₀ + a)
  have hbase := isJacobiAlong_varFst_of_isGeodesic (I := I) g fsh hfsh_smooth hgeosh
  have hcurve : (fun v : ℝ => fsh 0 v) = fun v : ℝ => f s₀ v := by
    funext v
    change f (s₀ + 0) v = f s₀ v
    rw [add_zero]
  have hfield : ∀ v : ℝ, varFst (I := I) fsh 0 v = varFst (I := I) f s₀ v :=
    fun v => varFst_shift (I := I) f hf s₀ v
  intro t
  have ht := hbase t
  rw [hcurve] at ht
  have hfieldfun : (fun v : ℝ => varFst (I := I) fsh 0 v)
      = fun v : ℝ => varFst (I := I) f s₀ v := funext hfield
  rw [hfieldfun] at ht
  exact ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.isJacobiAlong_varFst_of_isGeodesic_at then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.isJacobiAlong_varFst_of_isGeodesic_at"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.isJacobiAlong_varFst_of_isGeodesic_at ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.isJacobiAlong_varFst_of_isGeodesic_at

end Variation
end Riemannian
end Geometry
end DifferentialGeometry

end
