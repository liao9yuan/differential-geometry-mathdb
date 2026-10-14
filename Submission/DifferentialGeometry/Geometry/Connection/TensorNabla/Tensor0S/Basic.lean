import Submission.DifferentialGeometry.Geometry.Connection.Realization.Tensor0SBridge
import Submission.DifferentialGeometry.Geometry.Connection.HomBundle.Basic
import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.Multilinear

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Submission.DifferentialGeometry.Geometry.Connection.Realization


noncomputable section


open scoped _root_.Manifold _root_.ContDiff _root_.Topology
open _root_.Bundle _root_.Submission.Bundle _root_.CovariantDerivative _root_.Submission.CovariantDerivative
open _root_.Submission.DifferentialGeometry.Tensor0SBundle

namespace DifferentialGeometry
namespace Tensor0SNabla

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

noncomputable def tensor0SCovariantDerivativeZeroFun
    (T : Π x : M, Tensor0SSpace 0 I x) (x : M) :
    TangentSpace I x →L[ℝ] Tensor0SSpace 0 I x :=
  ((tensor0Iso I M x).symm.toContinuousLinearMap).comp
    (mvfderiv (I := I) (scalarFn I M T) x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivativeZeroFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivativeZeroFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivativeZeroFun ``Submission.DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivativeZeroFun

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem tensor0SCovariantDerivative_zero_fun_apply
    (T : Π x : M, Tensor0SSpace 0 I x) (x : M) (v : TangentSpace I x) :
    tensor0SCovariantDerivativeZeroFun I M T x v =
      (tensor0Iso I M x).symm (mvfderiv (I := I) (scalarFn I M T) x v) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivative_zero_fun_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivative_zero_fun_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivative_zero_fun_apply ``Submission.DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivative_zero_fun_apply

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem tensor0SCovariantDerivative_zero_fun_add_section
    (T₁ T₂ : Π x : M, Tensor0SSpace 0 I x)
    {x : M}
    (h₁ : MDifferentiableAt I 𝓘(ℝ, ℝ) (scalarFn I M T₁) x)
    (h₂ : MDifferentiableAt I 𝓘(ℝ, ℝ) (scalarFn I M T₂) x) :
    tensor0SCovariantDerivativeZeroFun I M (T₁ + T₂) x =
      tensor0SCovariantDerivativeZeroFun I M T₁ x +
      tensor0SCovariantDerivativeZeroFun I M T₂ x := by
  refine ContinuousLinearMap.ext (fun v => ?_)
  change (tensor0Iso I M x).symm (mvfderiv (I := I) (scalarFn I M (T₁ + T₂)) x v) =
    (tensor0Iso I M x).symm (mvfderiv (I := I) (scalarFn I M T₁) x v) +
    (tensor0Iso I M x).symm (mvfderiv (I := I) (scalarFn I M T₂) x v)
  rw [scalarFn_add I M T₁ T₂, mvfderiv_add h₁ h₂]
  change (tensor0Iso I M x).symm
    ((mvfderiv (I := I) (scalarFn I M T₁) x v +
     mvfderiv (I := I) (scalarFn I M T₂) x v : ℝ)) = _
  exact map_add (tensor0Iso I M x).symm _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivative_zero_fun_add_section then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivative_zero_fun_add_section"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivative_zero_fun_add_section ``Submission.DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivative_zero_fun_add_section

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem tensor0SCovariantDerivative_zero_fun_leibniz_section
    (T : Π x : M, Tensor0SSpace 0 I x) (g : M → ℝ) {x : M}
    (hT : MDifferentiableAt I 𝓘(ℝ, ℝ) (scalarFn I M T) x)
    (hg : MDifferentiableAt I 𝓘(ℝ, ℝ) g x) :
    tensor0SCovariantDerivativeZeroFun I M (g • T) x =
      g x • tensor0SCovariantDerivativeZeroFun I M T x +
      (mvfderiv (I := I) g x).smulRight (T x) := by
  refine ContinuousLinearMap.ext (fun v => ?_)
  change (tensor0Iso I M x).symm (mvfderiv (I := I) (scalarFn I M (g • T)) x v) =
    (g x • tensor0SCovariantDerivativeZeroFun I M T x +
      (mvfderiv (I := I) g x).smulRight (T x)) v
  rw [scalarFn_smul]
  rw [mvfderiv_smul hg hT]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
  rw [map_add, map_smul, map_smul, tensor0Iso_symm_scalarFn]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivative_zero_fun_leibniz_section then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivative_zero_fun_leibniz_section"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivative_zero_fun_leibniz_section ``Submission.DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivative_zero_fun_leibniz_section
noncomputable def tensor0SCovariantDerivativeSuccFun {s : ℕ}
    (cov_TM : CovariantDerivative I E (TangentSpace I : M → Type _))
    (cov_s : CovariantDerivative I (Tensor0SModel s ℝ E)
      (fun x : M => Tensor0SSpace s I x))
    (T : Π x : M, Tensor0SSpace (s+1) I x) (x : M) :
    TangentSpace I x →L[ℝ] Tensor0SSpace (s+1) I x :=
  ((tensor0SCurry (I := I) (M := M) s x).symm.toContinuousLinearMap).comp
    (HomConnection.homBundleCovariantDerivativeFun I M E (TangentSpace I)
      (Tensor0SModel s ℝ E) (fun x : M => Tensor0SSpace s I x)
      cov_TM cov_s (curriedSection I M T) x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivativeSuccFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivativeSuccFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivativeSuccFun ``Submission.DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivativeSuccFun

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem tensor0SCovariantDerivative_succ_fun_apply {s : ℕ}
    (cov_TM : CovariantDerivative I E (TangentSpace I : M → Type _))
    (cov_s : CovariantDerivative I (Tensor0SModel s ℝ E)
      (fun x : M => Tensor0SSpace s I x))
    (T : Π x : M, Tensor0SSpace (s+1) I x) (x : M) (v : TangentSpace I x) :
    tensor0SCovariantDerivativeSuccFun I M cov_TM cov_s T x v =
      (tensor0SCurry (I := I) (M := M) s x).symm
        (HomConnection.homBundleCovariantDerivativeFun I M E (TangentSpace I)
          (Tensor0SModel s ℝ E) (fun x : M => Tensor0SSpace s I x)
          cov_TM cov_s (curriedSection I M T) x v) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivative_succ_fun_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivative_succ_fun_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivative_succ_fun_apply ``Submission.DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivative_succ_fun_apply
noncomputable def tensor0SCovariantDerivativeZero
    :
    CovariantDerivative I (Tensor0SModel 0 ℝ E) (fun x : M => Tensor0SSpace 0 I x) where
  toFun := tensor0SCovariantDerivativeZeroFun I M
  isCovariantDerivativeOnUniv := {
    add := by
      intro T₁ T₂ x hT₁ hT₂ _hx
      have hT₁_scalar : MDifferentiableAt I 𝓘(ℝ, ℝ) (scalarFn I M T₁) x :=
        (mdifferentiableAt_scalarFn_iff_section I M T₁).mpr hT₁
      have hT₂_scalar : MDifferentiableAt I 𝓘(ℝ, ℝ) (scalarFn I M T₂) x :=
        (mdifferentiableAt_scalarFn_iff_section I M T₂).mpr hT₂
      exact tensor0SCovariantDerivative_zero_fun_add_section I M T₁ T₂ hT₁_scalar hT₂_scalar
    leibniz := by
      intro T g x hT hg _hx
      have hT_scalar : MDifferentiableAt I 𝓘(ℝ, ℝ) (scalarFn I M T) x :=
        (mdifferentiableAt_scalarFn_iff_section I M T).mpr hT
      exact tensor0SCovariantDerivative_zero_fun_leibniz_section I M T g hT_scalar hg
  }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivativeZero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivativeZero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivativeZero ``Submission.DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivativeZero

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem tensor0SCov_zero_scalar_at_Y
    (T : Π x : M, Tensor0SSpace 0 I x)
    (hT : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 0 ℝ E)) ∞
      (fun y => TotalSpace.mk' (Tensor0SModel 0 ℝ E)
        (E := fun x : M => Tensor0SSpace 0 I x) y (T y)))
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x => mvfderiv (I := I) (scalarFn I M T) x (Y x)) := by
  have hscalar : ContMDiff I 𝓘(ℝ, ℝ) ∞ (scalarFn I M T) :=
    (contMDiff_scalarFn_iff_section I M T).mpr hT
  let fscalar : C^∞⟮I, M; ℝ⟯ := ⟨scalarFn I M T, fun x => hscalar.contMDiffAt⟩
  have h_extDeriv_section :
      ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun x : M => (TangentSpace I x →L[ℝ] (Bundle.Trivial M ℝ) x))
        x (mvfderiv (I := I) fscalar x)) :=
    contMDiff_mvfderiv_section I M fscalar
  let d_fscalar : Cₛ^∞⟮I; E →L[ℝ] ℝ, (Bundle.dual ℝ (TangentSpace I : M → Type _))⟯ :=
    ⟨fun x => mvfderiv (I := I) (scalarFn I M T) x, h_extDeriv_section⟩
  have := contMDiff_dual_apply_section I M d_fscalar Y
  simpa [d_fscalar] using this

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor0SNabla.tensor0SCov_zero_scalar_at_Y
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor0SNabla.tensor0SCov_zero_scalar_at_Y target :: scope.openDecls } }

noncomputable instance tensor0SCovariantDerivative_zero_contMDiff
    :
    _root_.CovariantDerivative.ContMDiffCovariantDerivative (tensor0SCovariantDerivativeZero I M) ∞ where
  contMDiff := {
    contMDiff := by
      intro T hT
      have hT_smooth : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 0 ℝ E)) ∞
          (fun x => TotalSpace.mk' (Tensor0SModel 0 ℝ E)
            (E := fun x : M => Tensor0SSpace 0 I x) x (T x)) := by
        rw [show (∞ : WithTop ℕ∞) = ∞ + 1 from by simp] at hT
        rwa [← contMDiffOn_univ]
      rw [contMDiffOn_univ]
      apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
        (V₁ := TangentSpace I)
        (V₂ := fun x : M => Tensor0SSpace 0 I x)
        (φ := fun x => tensor0SCovariantDerivativeZeroFun I M T x)
      intro Y
      have h_scalar_at_Y := tensor0SCov_zero_scalar_at_Y I M T hT_smooth Y
      let f : C^∞⟮I, M; ℝ⟯ :=
        ⟨fun x => mvfderiv (I := I) (scalarFn I M T) x (Y x),
         fun x => h_scalar_at_Y.contMDiffAt⟩
      have h_iso_scalar : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 0 ℝ E)) ∞
          (fun x => TotalSpace.mk' (Tensor0SModel 0 ℝ E)
            (E := fun x : M => Tensor0SSpace 0 I x) x
            (tensor0SCovariantDerivativeZeroFun I M T x (Y x))) := by
        let S : Π x : M, Tensor0SSpace 0 I x :=
          fun x => tensor0SCovariantDerivativeZeroFun I M T x (Y x)
        have h_scalarFn_eq : scalarFn I M S = (f : M → ℝ) := by
          funext x
          change tensor0Iso I M x ((tensor0Iso I M x).symm
            (mvfderiv (I := I) (scalarFn I M T) x (Y x))) = _
          exact (tensor0Iso I M x).apply_symm_apply
            (mvfderiv (I := I) (scalarFn I M T) x (Y x))
        have h_scalarFn_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ (scalarFn I M S) := by
          rw [h_scalarFn_eq]; exact f.contMDiff
        exact (contMDiff_scalarFn_iff_section (I := I) (M := M) S).mp h_scalarFn_smooth
      exact h_iso_scalar
  }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivative_zero_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivative_zero_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivative_zero_contMDiff ``Submission.DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivative_zero_contMDiff

noncomputable def tensor0SCovariantDerivativeSucc {s : ℕ}
    (cov_TM : CovariantDerivative I E (TangentSpace I : M → Type _))
    (cov_s : CovariantDerivative I (Tensor0SModel s ℝ E)
      (fun x : M => Tensor0SSpace s I x))
    :
    letI _h_top : TopologicalSpace (_root_.Bundle.TotalSpace (Tensor0SModel (s + 1) ℝ E)
        (fun x : M => Tensor0SSpace (s + 1) I x)) :=
      tensor0SBundleTopology (s + 1)
    letI _h_fib : FiberBundle (Tensor0SModel (s + 1) ℝ E)
        (fun x : M => Tensor0SSpace (s + 1) I x) :=
      tensor0SBundleFiber (s + 1)
    CovariantDerivative I (Tensor0SModel (s+1) ℝ E)
      (fun x : M => Tensor0SSpace (s+1) I x) :=
  { toFun := tensor0SCovariantDerivativeSuccFun I M cov_TM cov_s
    isCovariantDerivativeOnUniv := {
    add := by
      intro T₁ T₂ x hT₁ hT₂ _hx
      have hC₁ := (mdifferentiableAt_curriedSection_iff_section I M T₁).mp hT₁
      have hC₂ := (mdifferentiableAt_curriedSection_iff_section I M T₂).mp hT₂
      have h_curried_add : curriedSection I M (T₁ + T₂) =
          curriedSection I M T₁ + curriedSection I M T₂ :=
        curriedSection_add (I := I) (M := M) T₁ T₂
      have h_homAdd := (HomConnection.homBundleCovariantDerivative I M E (TangentSpace I)
        (Tensor0SModel s ℝ E) (fun x : M => Tensor0SSpace s I x)
        cov_TM cov_s).isCovariantDerivativeOnUniv.add hC₁ hC₂
      refine ContinuousLinearMap.ext (fun v => ?_)
      simp only [tensor0SCovariantDerivative_succ_fun_apply, add_apply]
      rw [h_curried_add]
      have h_hom_add_apply :
          HomConnection.homBundleCovariantDerivativeFun I M E (TangentSpace I)
            (Tensor0SModel s ℝ E) (fun x : M => Tensor0SSpace s I x)
            cov_TM cov_s (curriedSection I M T₁ + curriedSection I M T₂) x =
          HomConnection.homBundleCovariantDerivativeFun I M E (TangentSpace I)
            (Tensor0SModel s ℝ E) (fun x : M => Tensor0SSpace s I x)
            cov_TM cov_s (curriedSection I M T₁) x +
          HomConnection.homBundleCovariantDerivativeFun I M E (TangentSpace I)
            (Tensor0SModel s ℝ E) (fun x : M => Tensor0SSpace s I x)
            cov_TM cov_s (curriedSection I M T₂) x := h_homAdd
      rw [h_hom_add_apply]
      rw [add_apply]
      exact map_add (tensor0SCurry (I := I) (M := M) s x).symm _ _
    leibniz := by
      intro T g x hT hg _hx
      have hC := (mdifferentiableAt_curriedSection_iff_section I M T).mp hT
      have h_homLeib := (HomConnection.homBundleCovariantDerivative I M E (TangentSpace I)
        (Tensor0SModel s ℝ E) (fun x : M => Tensor0SSpace s I x)
        cov_TM cov_s).isCovariantDerivativeOnUniv.leibniz hC hg
      have h_curried_smul : curriedSection I M (g • T) = g • curriedSection I M T :=
        curriedSection_smul (I := I) (M := M) g T
      refine ContinuousLinearMap.ext (fun v => ?_)
      simp only [tensor0SCovariantDerivative_succ_fun_apply]
      rw [h_curried_smul]
      have h_hom_leib_apply :
          HomConnection.homBundleCovariantDerivativeFun I M E (TangentSpace I)
            (Tensor0SModel s ℝ E) (fun x : M => Tensor0SSpace s I x)
            cov_TM cov_s (g • curriedSection I M T) x =
          g x • HomConnection.homBundleCovariantDerivativeFun I M E (TangentSpace I)
            (Tensor0SModel s ℝ E) (fun x : M => Tensor0SSpace s I x)
            cov_TM cov_s (curriedSection I M T) x +
          (mvfderiv (I := I) g x).smulRight (curriedSection I M T x) := h_homLeib
      rw [h_hom_leib_apply]
      rw [add_apply, smul_apply,
        ContinuousLinearMap.smulRight_apply]
      rw [map_add, map_smul]
      rw [add_apply, smul_apply,
        ContinuousLinearMap.smulRight_apply]
      congr 1
      rw [map_smul]
      congr 1
      change (tensor0SCurry (I := I) (M := M) s x).symm
          (tensor0SCurry (I := I) (M := M) s x (T x)) = T x
      exact (tensor0SCurry (I := I) (M := M) s x).symm_apply_apply (T x)
  } }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivativeSucc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivativeSucc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivativeSucc ``Submission.DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivativeSucc

omit [CompleteSpace E] [SigmaCompactSpace M] in
private theorem contMDiff_tensor0SCov_succ_section {s : ℕ}
    (cov_TM : CovariantDerivative I E (TangentSpace I : M → Type _))
    [_root_.CovariantDerivative.ContMDiffCovariantDerivative cov_TM ∞]
    (cov_s : CovariantDerivative I (Tensor0SModel s ℝ E)
      (fun x : M => Tensor0SSpace s I x))
    [_root_.CovariantDerivative.ContMDiffCovariantDerivative cov_s ∞]
    (T : Π x : M, Tensor0SSpace (s+1) I x)
    (hT : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (s+1) ℝ E)) ∞
      (fun y => TotalSpace.mk' (Tensor0SModel (s+1) ℝ E)
        (E := fun x : M => Tensor0SSpace (s+1) I x) y (T y))) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel (s+1) ℝ E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] Tensor0SModel (s+1) ℝ E)
        (E := fun x : M => (TangentSpace I x →L[ℝ] Tensor0SSpace (s+1) I x))
        x (tensor0SCovariantDerivativeSuccFun I M cov_TM cov_s T x)) := by
  have hCurried : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel s ℝ E)) ∞
      (fun y => TotalSpace.mk' (E →L[ℝ] Tensor0SModel s ℝ E)
        (E := fun y : M => TangentSpace I y →L[ℝ] Tensor0SSpace s I y)
        y (curriedSection I M T y)) :=
    (contMDiff_curriedSection_iff_section I M T).mp hT
  let τ_section : Cₛ^∞⟮I; E →L[ℝ] Tensor0SModel s ℝ E,
      (fun y : M => TangentSpace I y →L[ℝ] Tensor0SSpace s I y)⟯ :=
    ⟨curriedSection I M T, hCurried⟩
  have h_hom_smooth :
      ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] Tensor0SModel s ℝ E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] Tensor0SModel s ℝ E)
        (E := fun x : M =>
          TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] Tensor0SSpace s I x))
        x (HomConnection.homBundleCovariantDerivativeFun I M E (TangentSpace I)
          (Tensor0SModel s ℝ E) (fun x : M => Tensor0SSpace s I x)
          cov_TM cov_s (curriedSection I M T) x)) := by
    have hτ_plus : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel s ℝ E)) (∞ + 1)
        (fun x => TotalSpace.mk' (E →L[ℝ] Tensor0SModel s ℝ E)
          (E := fun y : M => TangentSpace I y →L[ℝ] Tensor0SSpace s I y)
          x (τ_section x)) := by
      rw [show (∞ : WithTop ℕ∞) + 1 = ∞ from by simp]
      exact τ_section.contMDiff
    have : _root_.CovariantDerivative.ContMDiffCovariantDerivative
      (HomConnection.homBundleCovariantDerivative I M E (TangentSpace I)
        (Tensor0SModel s ℝ E) (fun x : M => Tensor0SSpace s I x)
        cov_TM cov_s) ∞ :=
      HomConnection.homBundleCovariantDerivative_contMDiff I M E (TangentSpace I)
        (Tensor0SModel s ℝ E) (fun x : M => Tensor0SSpace s I x) cov_TM cov_s
    have h_hom_cov :=
      (‹ContMDiffCovariantDerivative
        (HomConnection.homBundleCovariantDerivative I M E (TangentSpace I)
          (Tensor0SModel s ℝ E) (fun x : M => Tensor0SSpace s I x)
          cov_TM cov_s) ∞›).contMDiff.contMDiff hτ_plus.contMDiffOn
    rwa [← contMDiffOn_univ]
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (V₁ := TangentSpace I)
    (V₂ := fun x : M => Tensor0SSpace (s+1) I x)
    (φ := fun x => tensor0SCovariantDerivativeSuccFun I M cov_TM cov_s T x)
  intro Y
  have h_hom_at_Y :
      ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel s ℝ E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] Tensor0SModel s ℝ E)
        (E := fun x : M => TangentSpace I x →L[ℝ] Tensor0SSpace s I x)
        x (HomConnection.homBundleCovariantDerivativeFun I M E (TangentSpace I)
            (Tensor0SModel s ℝ E) (fun x : M => Tensor0SSpace s I x)
            cov_TM cov_s (curriedSection I M T) x (Y x))) :=
    ContMDiff.clm_bundle_apply (b := id) h_hom_smooth Y.contMDiff
  let S : Π x : M, Tensor0SSpace (s+1) I x :=
    fun x => tensor0SCovariantDerivativeSuccFun I M cov_TM cov_s T x (Y x)
  have h_curried_S :
      (fun x => TotalSpace.mk' (E →L[ℝ] Tensor0SModel s ℝ E)
        (E := fun x : M => TangentSpace I x →L[ℝ] Tensor0SSpace s I x)
        x (curriedSection I M S x)) =
      (fun x => TotalSpace.mk' (E →L[ℝ] Tensor0SModel s ℝ E)
        (E := fun x : M => TangentSpace I x →L[ℝ] Tensor0SSpace s I x)
        x (HomConnection.homBundleCovariantDerivativeFun I M E (TangentSpace I)
            (Tensor0SModel s ℝ E) (fun x : M => Tensor0SSpace s I x)
            cov_TM cov_s (curriedSection I M T) x (Y x))) := by
    funext x
    have h_S_val : tensor0SCurry (I := I) (M := M) s x (S x) =
      HomConnection.homBundleCovariantDerivativeFun I M E (TangentSpace I)
        (Tensor0SModel s ℝ E) (fun x : M => Tensor0SSpace s I x)
        cov_TM cov_s (curriedSection I M T) x (Y x) := by
      change tensor0SCurry (I := I) (M := M) s x
        ((tensor0SCurry (I := I) (M := M) s x).symm
          (HomConnection.homBundleCovariantDerivativeFun I M E (TangentSpace I)
            (Tensor0SModel s ℝ E) (fun x : M => Tensor0SSpace s I x)
            cov_TM cov_s (curriedSection I M T) x (Y x))) = _
      exact (tensor0SCurry (I := I) (M := M) s x).apply_symm_apply _
    change TotalSpace.mk' (E →L[ℝ] Tensor0SModel s ℝ E)
        (E := fun x : M => TangentSpace I x →L[ℝ] Tensor0SSpace s I x)
        x (curriedSection I M S x) =
      TotalSpace.mk' (E →L[ℝ] Tensor0SModel s ℝ E)
        (E := fun x : M => TangentSpace I x →L[ℝ] Tensor0SSpace s I x)
        x (HomConnection.homBundleCovariantDerivativeFun I M E (TangentSpace I)
            (Tensor0SModel s ℝ E) (fun x : M => Tensor0SSpace s I x)
            cov_TM cov_s (curriedSection I M T) x (Y x))
    rw [← h_S_val]
    rfl
  rw [← h_curried_S] at h_hom_at_Y
  exact (contMDiff_curriedSection_iff_section I M S).mpr h_hom_at_Y

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor0SNabla.contMDiff_tensor0SCov_succ_section
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor0SNabla.contMDiff_tensor0SCov_succ_section target :: scope.openDecls } }

noncomputable instance tensor0SCovariantDerivative_succ_contMDiff {s : ℕ}
    (cov_TM : CovariantDerivative I E (TangentSpace I : M → Type _))
    [_root_.CovariantDerivative.ContMDiffCovariantDerivative cov_TM ∞]
    (cov_s : CovariantDerivative I (Tensor0SModel s ℝ E)
      (fun x : M => Tensor0SSpace s I x))
    [_root_.CovariantDerivative.ContMDiffCovariantDerivative cov_s ∞] :
    _root_.CovariantDerivative.ContMDiffCovariantDerivative
      (tensor0SCovariantDerivativeSucc I M cov_TM cov_s) ∞ where
  contMDiff := {
    contMDiff := by
      intro T hT
      have hT_smooth : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (s+1) ℝ E)) ∞
          (fun x => TotalSpace.mk' (Tensor0SModel (s+1) ℝ E)
            (E := fun x : M => Tensor0SSpace (s+1) I x) x (T x)) := by
        rw [show (∞ : WithTop ℕ∞) = ∞ + 1 from by simp] at hT
        rwa [← contMDiffOn_univ]
      rw [contMDiffOn_univ]
      exact contMDiff_tensor0SCov_succ_section I M cov_TM cov_s T hT_smooth
  }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivative_succ_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivative_succ_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivative_succ_contMDiff ``Submission.DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivative_succ_contMDiff

omit [SigmaCompactSpace M] in
private structure SmoothCov (s : ℕ)
    (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [T2Space M] where
  toCov : CovariantDerivative I (Tensor0SModel s ℝ E)
    (fun x : M => Tensor0SSpace s I x)
  smooth : _root_.CovariantDerivative.ContMDiffCovariantDerivative toCov ∞

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor0SNabla.SmoothCov
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor0SNabla.SmoothCov target :: scope.openDecls } }

omit [SigmaCompactSpace M] in
private noncomputable def tensor0SCovariantDerivative_aux
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [_root_.CovariantDerivative.ContMDiffCovariantDerivative cov ∞] :
    (s : ℕ) → SmoothCov (E := E) s I M
  | 0 => ⟨tensor0SCovariantDerivativeZero I M, inferInstance⟩
  | n + 1 =>
    let prev := tensor0SCovariantDerivative_aux cov n
    haveI : _root_.CovariantDerivative.ContMDiffCovariantDerivative prev.toCov ∞ := prev.smooth
    ⟨tensor0SCovariantDerivativeSucc I M cov prev.toCov, inferInstance⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivative_aux
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivative_aux target :: scope.openDecls } }

omit [SigmaCompactSpace M] in
noncomputable def tensor0SCovariantDerivative (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [_root_.CovariantDerivative.ContMDiffCovariantDerivative cov ∞] :
    CovariantDerivative I (Tensor0SModel s ℝ E)
      (fun x : M => Tensor0SSpace s I x) :=
  (tensor0SCovariantDerivative_aux I M cov s).toCov

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivative ``Submission.DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivative

omit [SigmaCompactSpace M] in
noncomputable instance tensor0SCovariantDerivative_contMDiff (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [_root_.CovariantDerivative.ContMDiffCovariantDerivative cov ∞] :
    ContMDiffCovariantDerivative (tensor0SCovariantDerivative I M s cov) ∞ :=
  (tensor0SCovariantDerivative_aux I M cov s).smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivative_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivative_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivative_contMDiff ``Submission.DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivative_contMDiff

omit [CompleteSpace E] [SigmaCompactSpace M] in
theorem tensor0SCovariantDerivative_zero_eq
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [_root_.CovariantDerivative.ContMDiffCovariantDerivative cov ∞] :
    tensor0SCovariantDerivative I M 0 cov =
      tensor0SCovariantDerivativeZero I M := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivative_zero_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivative_zero_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivative_zero_eq ``Submission.DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivative_zero_eq

omit [CompleteSpace E] [SigmaCompactSpace M] in
theorem tensor0SCovariantDerivative_succ_eq {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [_root_.CovariantDerivative.ContMDiffCovariantDerivative cov ∞] :
    tensor0SCovariantDerivative I M (s+1) cov =
      tensor0SCovariantDerivativeSucc I M cov
        (tensor0SCovariantDerivative I M s cov) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivative_succ_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivative_succ_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivative_succ_eq ``Submission.DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivative_succ_eq

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem tensor0SCovariantDerivative_zero_apply
    (T : Π x : M, Tensor0SSpace 0 I x) (x : M) (v : TangentSpace I x) :
    tensor0SCovariantDerivativeZero I M T x v =
      (tensor0Iso I M x).symm (mvfderiv (I := I) (scalarFn I M T) x v) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivative_zero_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivative_zero_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivative_zero_apply ``Submission.DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivative_zero_apply

omit [CompleteSpace E] [SigmaCompactSpace M] in
theorem tensor0SCovariantDerivative_succ_apply {s : ℕ}
    (cov_TM : CovariantDerivative I E (TangentSpace I : M → Type _))
    (cov_s : CovariantDerivative I (Tensor0SModel s ℝ E)
      (fun x : M => Tensor0SSpace s I x))
    (T : Π x : M, Tensor0SSpace (s+1) I x) (x : M) (v : TangentSpace I x) :
    tensor0SCovariantDerivativeSucc I M cov_TM cov_s T x v =
      (tensor0SCurry (I := I) (M := M) s x).symm
        (HomConnection.homBundleCovariantDerivativeFun I M E (TangentSpace I)
          (Tensor0SModel s ℝ E) (fun x : M => Tensor0SSpace s I x)
          cov_TM cov_s (curriedSection I M T) x v) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivative_succ_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivative_succ_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivative_succ_apply ``Submission.DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivative_succ_apply

omit [CompleteSpace E] [SigmaCompactSpace M] in
theorem tensor0SCovariantDerivative_apply_zero
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [_root_.CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (T : Π x : M, Tensor0SSpace 0 I x) (x : M) (v : TangentSpace I x) :
    tensor0SCovariantDerivative I M 0 cov T x v =
      (tensor0Iso I M x).symm (mvfderiv (I := I) (scalarFn I M T) x v) := by
  rw [tensor0SCovariantDerivative_zero_eq]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivative_apply_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivative_apply_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivative_apply_zero ``Submission.DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivative_apply_zero

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem scalarFn_unitZero :
    scalarFn I M
        (fun _ : M => Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ))) =
      fun _ : M => (1 : ℝ) := by
  funext y
  rw [scalarFn_apply]
  change (tensor0SSpaceContinuousLinearEquiv (I := I) 0 y).trans
      (continuousMultilinearCurryFin0 ℝ E ℝ).toContinuousLinearEquiv
      ((tensor0SSpaceContinuousLinearEquiv (I := I) 0 y).symm
        (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ))) = (1 : ℝ)
  rw [ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.apply_symm_apply]
  change (continuousMultilinearCurryFin0 ℝ E ℝ)
      (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)) = (1 : ℝ)
  rw [continuousMultilinearCurryFin0_apply, ContinuousMultilinearMap.constOfIsEmpty_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SNabla.scalarFn_unitZero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SNabla.scalarFn_unitZero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SNabla.scalarFn_unitZero ``Submission.DifferentialGeometry.Tensor0SNabla.scalarFn_unitZero

omit [CompleteSpace E] [SigmaCompactSpace M] in
theorem tensor0SCovariantDerivative_unitZero_eq_zero
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [_root_.CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (x : M) (v : TangentSpace I x) :
    tensor0SCovariantDerivative I M 0 cov
        (fun _ : M => Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)))
        x v = 0 := by
  rw [tensor0SCovariantDerivative_apply_zero, scalarFn_unitZero]
  have hext : mvfderiv (I := I) (fun _ : M => (1 : ℝ)) x = 0 := by
    unfold mvfderiv
    simp [mfderiv_const]
  rw [hext]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivative_unitZero_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivative_unitZero_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivative_unitZero_eq_zero ``Submission.DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivative_unitZero_eq_zero

omit [CompleteSpace E] [SigmaCompactSpace M] in
theorem tensor0SCovariantDerivative_eq_multilinear (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [_root_.CovariantDerivative.ContMDiffCovariantDerivative cov ∞] :
    tensor0SCovariantDerivative I M s cov = cov.multilinear s := by
  induction s with
  | zero =>
    ext T x X v
    change mvfderiv (I := I) (scalarFn I M T) x X =
      mvfderiv (I := I) (fun y => T y 0) x X
    congr 2
  | succ s ih =>
    rw [tensor0SCovariantDerivative_succ_eq, ih]
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivative_eq_multilinear then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivative_eq_multilinear"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivative_eq_multilinear ``Submission.DifferentialGeometry.Tensor0SNabla.tensor0SCovariantDerivative_eq_multilinear

end Tensor0SNabla

end DifferentialGeometry
end
