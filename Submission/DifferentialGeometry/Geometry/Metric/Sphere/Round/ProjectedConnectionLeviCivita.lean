import Submission.DifferentialGeometry.Geometry.Metric.Sphere.Round.ProjectedConnection
import Submission.DifferentialGeometry.Geometry.Connection.Realization.Embedding
import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.Koszul.Basic
import Submission.DifferentialGeometry.Geometry.Curvature.Metric.Defs
import Mathlib.Analysis.InnerProductSpace.Calculus

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


open _root_.Submission.DifferentialGeometry.Geometry.Connection.Realization
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Metric _root_.Module _root_.Submission.Module _root_.VectorField
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.RealInnerProductSpace

namespace DifferentialGeometry
namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {n : ℕ} [Fact (finrank ℝ E = n + 1)]


noncomputable def innerCoordFun (w : E) : C^∞⟮𝓡 n, _root_.Metric.sphere (0 : E) 1; ℝ⟯ :=
  ⟨fun p => ⟪w, (↑p : E)⟫, ((innerSL ℝ w).contMDiff).comp contMDiff_coe_sphere⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.innerCoordFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.innerCoordFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.innerCoordFun ``Submission.DifferentialGeometry.Geometry.innerCoordFun

omit [FiniteDimensional ℝ E] in
theorem mfderiv_innerCoordFun (w : E) (p : _root_.Metric.sphere (0 : E) 1) (v : TangentSpace (𝓡 n) p) :
    mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (innerCoordFun (E := E) (n := n) w) p v = ⟪w, dIncl (n := n) p v⟫ := by
  have : InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, E) (↑p : E)) :=
    inferInstanceAs (InnerProductSpace ℝ E)
  have hιC : ContMDiffAt (𝓡 n) 𝓘(ℝ, E) ∞ ((↑) : _root_.Metric.sphere (0 : E) 1 → E) p :=
    contMDiff_coe_sphere.contMDiffAt
  have hι : HasMFDerivAt (𝓡 n) 𝓘(ℝ, E) ((↑) : _root_.Metric.sphere (0 : E) 1 → E) p (dIncl (n := n) p) :=
    (hιC.mdifferentiableAt (by simp)).hasMFDerivAt
  have hL : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (innerSL ℝ w) ((↑p : E)) (innerSL ℝ w) :=
    (innerSL ℝ w).hasFDerivAt.hasMFDerivAt
  have hfun : (⇑(innerCoordFun (E := E) (n := n) w)) = (innerSL ℝ w) ∘
    ((↑) : _root_.Metric.sphere (0 : E) 1 → E) := by
    funext q
    rfl
  have hcomp : HasMFDerivAt (𝓡 n) 𝓘(ℝ, ℝ) ((innerSL ℝ w) ∘ ((↑) : _root_.Metric.sphere (0 : E) 1 → E)) p
      ((innerSL ℝ w).comp (dIncl (n := n) p)) := hL.comp p hι
  rw [hfun, hcomp.mfderiv]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.mfderiv_innerCoordFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.mfderiv_innerCoordFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.mfderiv_innerCoordFun ``Submission.DifferentialGeometry.Geometry.mfderiv_innerCoordFun

omit [FiniteDimensional ℝ E] in
theorem mfderiv_inner_left (w : E) {F : _root_.Metric.sphere (0 : E) 1 → E} {x : _root_.Metric.sphere (0 : E) 1}
    (hF : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) F x) (v : TangentSpace (𝓡 n) x) :
    mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (fun p => ⟪w, F p⟫) x v
      = ⟪w, mfderiv (𝓡 n) 𝓘(ℝ, E) F x v⟫ := by
  have : InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, E) (F x)) :=
    inferInstanceAs (InnerProductSpace ℝ E)
  have hL : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (innerSL ℝ w) (F x) (innerSL ℝ w) :=
    (innerSL ℝ w).hasFDerivAt.hasMFDerivAt
  have hcomp : HasMFDerivAt (𝓡 n) 𝓘(ℝ, ℝ) ((innerSL ℝ w) ∘ F) x
      ((innerSL ℝ w).comp (mfderiv (𝓡 n) 𝓘(ℝ, E) F x)) := hL.comp x hF.hasMFDerivAt
  have hfun : (fun p => ⟪w, F p⟫) = (innerSL ℝ w) ∘ F := by
    funext q; simp
  rw [hfun, hcomp.mfderiv]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.mfderiv_inner_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.mfderiv_inner_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.mfderiv_inner_left ``Submission.DifferentialGeometry.Geometry.mfderiv_inner_left

omit [FiniteDimensional ℝ E] in
theorem mvfderiv_inner_left (w : E) {F : _root_.Metric.sphere (0 : E) 1 → E} {x : _root_.Metric.sphere (0 : E) 1}
    (hF : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) F x) (v : TangentSpace (𝓡 n) x) :
    mvfderiv (𝓡 n) (fun p => ⟪w, F p⟫) x v
      = ⟪w, mvfderiv (𝓡 n) F x v⟫ := by
  rw [DifferentialGeometry.mvfderiv_real_eq_mfderiv]
  rw [mfderiv_inner_left w hF v]
  simp [mvfderiv, NormedSpace.fromTangentSpace]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.mvfderiv_inner_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.mvfderiv_inner_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.mvfderiv_inner_left ``Submission.DifferentialGeometry.Geometry.mvfderiv_inner_left

omit [FiniteDimensional ℝ E] in
theorem mfderiv_inner {F G : _root_.Metric.sphere (0 : E) 1 → E} {x : _root_.Metric.sphere (0 : E) 1}
    (hF : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) F x) (hG : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) G x)
    (v : TangentSpace (𝓡 n) x) :
    mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (fun b => ⟪F b, G b⟫) x v
      = ⟪mfderiv (𝓡 n) 𝓘(ℝ, E) F x v, G x⟫ + ⟪F x, mfderiv (𝓡 n) 𝓘(ℝ, E) G x v⟫ := by
  have hB : HasMFDerivAt 𝓘(ℝ, E × E) 𝓘(ℝ, ℝ) (fun p : E × E => ⟪p.1, p.2⟫) (F x, G x)
      (fderivInnerCLM ℝ (F x, G x)) :=
    (isBoundedBilinearMap_inner (𝕜 := ℝ) (E := E) |>.hasFDerivAt (F x, G x)).hasMFDerivAt
  have hpair : HasMFDerivAt (𝓡 n) 𝓘(ℝ, E × E) (fun b => (F b, G b)) x
      ((mfderiv (𝓡 n) 𝓘(ℝ, E) F x).prod (mfderiv (𝓡 n) 𝓘(ℝ, E) G x)) :=
    hF.hasMFDerivAt.prodMk hG.hasMFDerivAt
  have hcomp := (hB.comp x hpair).mfderiv
  rw [show (fun b => ⟪F b, G b⟫) = (fun p : E × E => ⟪p.1, p.2⟫) ∘ (fun b => (F b, G b)) from rfl,
    hcomp]
  change ⟪F x, mfderiv (𝓡 n) 𝓘(ℝ, E) G x v⟫ + ⟪mfderiv (𝓡 n) 𝓘(ℝ, E) F x v, G x⟫
    = ⟪mfderiv (𝓡 n) 𝓘(ℝ, E) F x v, G x⟫ + ⟪F x, mfderiv (𝓡 n) 𝓘(ℝ, E) G x v⟫
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.mfderiv_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.mfderiv_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.mfderiv_inner ``Submission.DifferentialGeometry.Geometry.mfderiv_inner

omit [FiniteDimensional ℝ E] in
theorem dIncl_mlieBracket
    (X Y : Cₛ^∞⟮𝓡 n; EuclideanSpace ℝ (Fin n), (TangentSpace (𝓡 n) : _root_.Metric.sphere (0 : E) 1 → Type _)⟯)
    (x : _root_.Metric.sphere (0 : E) 1) :
    dIncl (n := n) x (_root_.VectorField.mlieBracket (𝓡 n) (⇑X) (⇑Y) x)
      = ambDeriv (n := n) (⇑Y) x (X x) - ambDeriv (n := n) (⇑X) x (Y x) := by
  refine ext_inner_left ℝ fun w => ?_
  have hbr := embedDeriv_mlieBracket (I := 𝓡 n) (M := _root_.Metric.sphere (0 : E) 1) X Y (innerCoordFun w)
  have hact : ∀ (Z : Cₛ^∞⟮𝓡 n; EuclideanSpace ℝ (Fin n),
    (TangentSpace (𝓡 n) : _root_.Metric.sphere (0 : E) 1 → Type _)⟯)
      (p : _root_.Metric.sphere (0 : E) 1),
      (embedDeriv (𝓡 n) (_root_.Metric.sphere (0 : E) 1) Z (innerCoordFun w) : _root_.Metric.sphere (0 : E) 1 → ℝ) p
        = ⟪w, dIncl (n := n) p (Z p)⟫ := by
    intro Z p
    change vectorFieldAction (𝓡 n) (_root_.Metric.sphere (0 : E) 1) Z (innerCoordFun w) p = _
    simp only [vectorFieldAction]
    rw [show mvfderiv (I := 𝓡 n) (innerCoordFun w) p (Z p)
          = mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (innerCoordFun (E := E) (n := n) w) p (Z p) from rfl,
      mfderiv_innerCoordFun]
  have hsecond : ∀ (Z W : Cₛ^∞⟮𝓡 n; EuclideanSpace ℝ (Fin n),
    (TangentSpace (𝓡 n) : _root_.Metric.sphere (0 : E) 1 → Type _)⟯),
      (embedDeriv (𝓡 n) (_root_.Metric.sphere (0 : E) 1) W
        (embedDeriv (𝓡 n) (_root_.Metric.sphere (0 : E) 1) Z (innerCoordFun w))
        : _root_.Metric.sphere (0 : E) 1 → ℝ) x = ⟪w, ambDeriv (n := n) (⇑Z) x (W x)⟫ := by
    intro Z W
    have hZC : ContMDiffAt (𝓡 n) (𝓡 n).tangent ∞
        (fun y => (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y (Z y))) x := Z.contMDiff.contMDiffAt
    have hZdiff := hZC.mdifferentiableAt (by simp)
    have hg : (⇑(embedDeriv (𝓡 n) (_root_.Metric.sphere (0 : E) 1) Z (innerCoordFun w)) : _root_.Metric.sphere (0 : E) 1 → ℝ)
        = fun p => ⟪w, dInclField (n := n) (⇑Z) p⟫ := by
      funext p; rw [hact Z p]; rfl
    change vectorFieldAction (𝓡 n) (_root_.Metric.sphere (0 : E) 1) W
      (embedDeriv (𝓡 n) (_root_.Metric.sphere (0 : E) 1) Z (innerCoordFun w)) x = _
    simp only [vectorFieldAction]
    rw [show mvfderiv (I := 𝓡 n) (embedDeriv (𝓡 n) (_root_.Metric.sphere (0 : E) 1) Z (innerCoordFun w)) x
      (W x)
          = mfderiv (𝓡 n) 𝓘(ℝ, ℝ)
              (⇑(embedDeriv (𝓡 n) (_root_.Metric.sphere (0 : E) 1) Z (innerCoordFun w))) x (W x) from rfl,
      hg, mfderiv_inner_left w (dInclField_mdifferentiableAt (n := n) hZdiff) (W x), ambDeriv_apply]
    simp [mvfderiv, NormedSpace.fromTangentSpace]
    rfl
  have hbrx : (embedDeriv (𝓡 n) (_root_.Metric.sphere (0 : E) 1)
        (mlieBracketSection (𝓡 n) (_root_.Metric.sphere (0 : E) 1) X Y) (innerCoordFun w) : _root_.Metric.sphere (0 : E) 1 → ℝ)
          x
      = (embedDeriv (𝓡 n) (_root_.Metric.sphere (0 : E) 1) X
          (embedDeriv (𝓡 n) (_root_.Metric.sphere (0 : E) 1) Y (innerCoordFun w)) : _root_.Metric.sphere (0 : E) 1 → ℝ) x
        - (embedDeriv (𝓡 n) (_root_.Metric.sphere (0 : E) 1) Y
            (embedDeriv (𝓡 n) (_root_.Metric.sphere (0 : E) 1) X (innerCoordFun w)) : _root_.Metric.sphere (0 : E) 1 → ℝ)
              x := by
    have h := DFunLike.congr_fun hbr x
    simpa using h
  rw [hact (mlieBracketSection (𝓡 n) (_root_.Metric.sphere (0 : E) 1) X Y) x, hsecond Y X, hsecond X Y] at hbrx
  rw [inner_sub_right]
  exact hbrx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.dIncl_mlieBracket then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.dIncl_mlieBracket"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.dIncl_mlieBracket ``Submission.DifferentialGeometry.Geometry.dIncl_mlieBracket


omit [FiniteDimensional ℝ E] in
theorem projConn_torsion :
    (projConnCD (E := E) (n := n)).torsion = 0 := by
  have : IsManifold (𝓡 n) ∞ (_root_.Metric.sphere (0 : E) 1) :=
    EuclideanSpace.instIsManifoldSphere.of_le le_top
  funext x
  ext u v
  obtain ⟨X, hX⟩ : ∃ σ : Cₛ^∞⟮𝓡 n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (𝓡 n) : _root_.Metric.sphere (0 : E) 1 → Type _)⟯, σ x = u :=
    ContMDiffSection.exists_eq_at x u
  obtain ⟨Y, hY⟩ : ∃ σ : Cₛ^∞⟮𝓡 n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (𝓡 n) : _root_.Metric.sphere (0 : E) 1 → Type _)⟯, σ x = v :=
    ContMDiffSection.exists_eq_at x v
  have hXd : MDifferentiableAt (𝓡 n) (𝓡 n).tangent
      (fun y => (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y (X y))) x :=
    X.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hYd : MDifferentiableAt (𝓡 n) (𝓡 n).tangent
      (fun y => (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y (Y y))) x :=
    Y.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  simp only [Pi.zero_apply, zero_apply]
  rw [← hX, ← hY, (projConnCD (E := E) (n := n)).torsion_apply hXd hYd, sub_eq_zero]
  refine injective_mvfderiv_subtypeVal_sphere x ?_
  change dIncl (n := n) x (projConn (n := n) (⇑Y) x (X x) - projConn (n := n) (⇑X) x (Y x))
    = dIncl (n := n) x (_root_.VectorField.mlieBracket (𝓡 n) (⇑X) (⇑Y) x)
  rw [map_sub, dIncl_projConn, dIncl_projConn]
  have hmem : dIncl (n := n) x (_root_.VectorField.mlieBracket (𝓡 n) (⇑X) (⇑Y) x) ∈ (ℝ ∙ (↑x : E))ᗮ := by
    rw [← range_mvfderiv_subtypeVal (n := n) x]; exact ⟨_, rfl⟩
  rw [← Submodule.coe_sub, ← map_sub, ← dIncl_mlieBracket X Y x,
    ← Submodule.starProjection_apply, Submodule.starProjection_eq_self_iff.mpr hmem]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.projConn_torsion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.projConn_torsion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.projConn_torsion ``Submission.DifferentialGeometry.Geometry.projConn_torsion

omit [FiniteDimensional ℝ E] in
theorem projConn_metricCompat :
    DifferentialGeometry.Geometry.Connection.IsMetricCompatible (projConnCD (E := E) (n := n))
      (roundMetric (E := E) (n := n)) := by
  intro Y Z x hY hZ _ v
  have hYd := dInclField_mdifferentiableAt (n := n) hY
  have hZd := dInclField_mdifferentiableAt (n := n) hZ
  have hmemZ : dIncl (n := n) x (Z x) ∈ (ℝ ∙ (↑x : E))ᗮ := by
    rw [← range_mvfderiv_subtypeVal (n := n) x]; exact ⟨Z x, rfl⟩
  have hmemY : dIncl (n := n) x (Y x) ∈ (ℝ ∙ (↑x : E))ᗮ := by
    rw [← range_mvfderiv_subtypeVal (n := n) x]; exact ⟨Y x, rfl⟩
  have horth : ∀ (w u : E), u ∈ (ℝ ∙ (↑x : E))ᗮ →
      ⟪w, u⟫ = ⟪(↑(((ℝ ∙ (↑x : E))ᗮ).orthogonalProjectionOnto w) : E), u⟫ := by
    intro w u hu
    rw [← Submodule.starProjection_apply]
    have h0 := Submodule.starProjection_inner_eq_zero (K := (ℝ ∙ (↑x : E))ᗮ) w u hu
    rw [inner_sub_left, sub_eq_zero] at h0
    exact h0
  have horth_right : ∀ (w u : E), u ∈ (ℝ ∙ (↑x : E))ᗮ →
      ⟪u, w⟫ = ⟪u, (↑(((ℝ ∙ (↑x : E))ᗮ).orthogonalProjectionOnto w) : E)⟫ := by
    intro w u hu
    rw [← Submodule.starProjection_apply]
    have h0 := Submodule.starProjection_inner_eq_zero (K := (ℝ ∙ (↑x : E))ᗮ) w u hu
    rw [real_inner_comm, inner_sub_right, sub_eq_zero] at h0
    exact h0
  have hfun : (fun b => (roundMetric (E := E) (n := n)).inner b (Y b) (Z b))
      = fun b => ⟪dInclField (n := n) Y b, dInclField (n := n) Z b⟫ := by
    funext b; rw [roundMetric_inner]; rfl
  have hmf := mfderiv_inner (n := n) hYd hZd v
  rw [hfun]
  erw [hmf]
  simp only [roundMetric_inner]
  erw [dIncl_projConn, dIncl_projConn]
  simp only [ambDeriv_apply, dInclField_apply]
  congr 1
  · exact horth _ _ hmemZ
  · exact horth_right _ _ hmemY

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.projConn_metricCompat then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.projConn_metricCompat"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.projConn_metricCompat ``Submission.DifferentialGeometry.Geometry.projConn_metricCompat


omit [FiniteDimensional ℝ E] in
theorem projConn_eq_metricCov
    {Y : ∀ x : _root_.Metric.sphere (0 : E) 1, TangentSpace (𝓡 n) x} {x : _root_.Metric.sphere (0 : E) 1}
    (hY : MDifferentiableAt (𝓡 n) (𝓡 n).tangent
      (fun y => (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y (Y y))) x)
    (v : TangentSpace (𝓡 n) x) :
    projConn (n := n) Y x v
      = DifferentialGeometry.Geometry.Curvature.metricCov (roundMetric (E := E)
        (n := n)) Y x v := by
  have : IsManifold (𝓡 n) ∞ (_root_.Metric.sphere (0 : E) 1) :=
    EuclideanSpace.instIsManifoldSphere.of_le le_top
  have htor₂ : (DifferentialGeometry.Geometry.Curvature.metricCov (roundMetric (E := E)
    (n := n))).torsion = 0 :=
    funext fun y =>
      DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_isTorsionFree
        (roundMetric (E := E) (n := n)) y
  have hMC₂ : DifferentialGeometry.Geometry.Connection.IsMetricCompatible
      (DifferentialGeometry.Geometry.Curvature.metricCov (roundMetric (E := E) (n := n)))
      (roundMetric (E := E) (n := n)) :=
    DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_isMetricCompatible
      (roundMetric (E := E) (n := n))
  exact DifferentialGeometry.Geometry.Connection.koszul_levi_civita_unique_of_torsionFree_metricCompatible
    (projConnCD (E := E) (n := n)) (DifferentialGeometry.Geometry.Curvature.metricCov
      (roundMetric (E := E) (n := n)))
    projConn_torsion htor₂ projConn_metricCompat hMC₂ hY v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.projConn_eq_metricCov then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.projConn_eq_metricCov"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.projConn_eq_metricCov ``Submission.DifferentialGeometry.Geometry.projConn_eq_metricCov

end Geometry
end DifferentialGeometry
