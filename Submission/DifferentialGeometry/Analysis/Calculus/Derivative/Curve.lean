import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Submission.DifferentialGeometry.Geometry.Operator.Scalar.Calculus
import Submission.DifferentialGeometry.Analysis.TimeInterval

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Filter _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Analysis.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

inductive PiecewiseContMDiffOn (I : ModelWithCorners ℝ E H) (n : ℕ∞ω)
    (gamma : ℝ → M) : ℝ → ℝ → Prop where
  | of_contMDiffOn {a b : ℝ}
      (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) I n gamma (_root_.Set.Icc a b)) :
      PiecewiseContMDiffOn I n gamma a b
  | trans {a b c : ℝ} (hab : a < b) (hbc : b < c)
      (habgamma : PiecewiseContMDiffOn I n gamma a b)
      (hbcgamma : PiecewiseContMDiffOn I n gamma b c) :
      PiecewiseContMDiffOn I n gamma a c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Calculus.PiecewiseContMDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Calculus.PiecewiseContMDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Calculus.PiecewiseContMDiffOn ``Submission.DifferentialGeometry.Analysis.Calculus.PiecewiseContMDiffOn

def realTangentOne (t : ℝ) : TangentSpace 𝓘(ℝ, ℝ) t :=
  (NormedSpace.fromTangentSpace (𝕜 := ℝ) t).symm 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Calculus.realTangentOne then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Calculus.realTangentOne"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Calculus.realTangentOne ``Submission.DifferentialGeometry.Analysis.Calculus.realTangentOne

@[simp] lemma fromTangentSpace_realTangentOne (t : ℝ) :
    NormedSpace.fromTangentSpace (𝕜 := ℝ) t (realTangentOne t) = 1 :=
  (NormedSpace.fromTangentSpace (𝕜 := ℝ) t).apply_symm_apply 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Calculus.fromTangentSpace_realTangentOne then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Calculus.fromTangentSpace_realTangentOne"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Calculus.fromTangentSpace_realTangentOne ``Submission.DifferentialGeometry.Analysis.Calculus.fromTangentSpace_realTangentOne

omit [FiniteDimensional ℝ E] in
theorem hasDerivWithinAt_comp_mfderivWithin
    (I : ModelWithCorners ℝ E H) (f : M → ℝ) (gamma : ℝ → M)
    (s : Set ℝ) (t : ℝ)
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f (gamma t))
    (hgamma : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I gamma s t) :
    HasDerivWithinAt (fun r => f (gamma r))
      (NormedSpace.fromTangentSpace (f (gamma t))
        (mfderiv I 𝓘(ℝ, ℝ) f (gamma t)
          (mfderivWithin 𝓘(ℝ, ℝ) I gamma s t (1 : ℝ)))) s t := by
  rw [hasDerivWithinAt_iff_hasFDerivWithinAt]
  have hcomp := hf.hasMFDerivAt.comp_hasMFDerivWithinAt t
    hgamma.hasMFDerivWithinAt
  have hcomp' := hcomp.hasFDerivWithinAt
  refine hcomp'.congr_fderiv ?_
  ext
  let z : ℝ :=
    mfderiv I 𝓘(ℝ, ℝ) f (gamma t)
      (mfderivWithin 𝓘(ℝ, ℝ) I gamma s t (1 : ℝ))
  change z = (ContinuousLinearMap.toSpanSingleton ℝ z) 1
  change z = 1 * z
  rw [one_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Calculus.hasDerivWithinAt_comp_mfderivWithin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Calculus.hasDerivWithinAt_comp_mfderivWithin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Calculus.hasDerivWithinAt_comp_mfderivWithin ``Submission.DifferentialGeometry.Analysis.Calculus.hasDerivWithinAt_comp_mfderivWithin

omit [FiniteDimensional ℝ E] in
theorem hasDerivAt_comp_mfderiv_along
    (I : ModelWithCorners ℝ E H) (f : M → ℝ) (gamma : ℝ → M) (t : ℝ)
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f (gamma t))
    (hgamma : MDifferentiableAt 𝓘(ℝ, ℝ) I gamma t) :
    HasDerivAt (fun s => f (gamma s))
      (NormedSpace.fromTangentSpace (f (gamma t))
        (mfderiv I 𝓘(ℝ, ℝ) f (gamma t)
          (mfderiv 𝓘(ℝ, ℝ) I gamma t (realTangentOne t)))) t := by
  have hmd : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (f ∘ gamma) t :=
    hf.comp t hgamma
  refine hmd.differentiableAt.hasDerivAt.congr_deriv ?_
  calc
    deriv (f ∘ gamma) t =
        mvfderiv (I := 𝓘(ℝ, ℝ)) (f ∘ gamma) t (realTangentOne t) := by
      unfold mvfderiv
      rw [mfderiv_eq_fderiv]
      change deriv (f ∘ gamma) t =
        fderiv ℝ (f ∘ gamma) t
          (NormedSpace.fromTangentSpace (𝕜 := ℝ) t (realTangentOne t))
      rw [fromTangentSpace_realTangentOne, fderiv_apply_one_eq_deriv]
    _ = mvfderiv (I := I) f (gamma t)
        (mfderiv 𝓘(ℝ, ℝ) I gamma t (realTangentOne t)) :=
      _root_.mvfderiv_comp_apply t hf hgamma (realTangentOne t)
    _ = NormedSpace.fromTangentSpace (f (gamma t))
        (mfderiv I 𝓘(ℝ, ℝ) f (gamma t)
          (mfderiv 𝓘(ℝ, ℝ) I gamma t (realTangentOne t))) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Calculus.hasDerivAt_comp_mfderiv_along then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Calculus.hasDerivAt_comp_mfderiv_along"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Calculus.hasDerivAt_comp_mfderiv_along ``Submission.DifferentialGeometry.Analysis.Calculus.hasDerivAt_comp_mfderiv_along

omit [FiniteDimensional ℝ E] in
theorem deriv_comp_mfderiv_along
    (I : ModelWithCorners ℝ E H) (f : M → ℝ) (gamma : ℝ → M) (t : ℝ)
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f (gamma t))
    (hgamma : MDifferentiableAt 𝓘(ℝ, ℝ) I gamma t) :
    deriv (fun s => f (gamma s)) t =
      NormedSpace.fromTangentSpace (f (gamma t))
        (mfderiv I 𝓘(ℝ, ℝ) f (gamma t)
          (mfderiv 𝓘(ℝ, ℝ) I gamma t (realTangentOne t))) :=
  (hasDerivAt_comp_mfderiv_along I f gamma t hf hgamma).deriv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Calculus.deriv_comp_mfderiv_along then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Calculus.deriv_comp_mfderiv_along"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Calculus.deriv_comp_mfderiv_along ``Submission.DifferentialGeometry.Analysis.Calculus.deriv_comp_mfderiv_along

theorem hasDerivAt_along_curve
    (g : SmoothRiemannianMetric I M)
    {F : ℝ → M → ℝ} {gamma : ℝ → M} {t timeDeriv : ℝ}
    (hF : MDifferentiableAt ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ)
      (fun p : ℝ × M => F p.1 p.2) (t, gamma t))
    (hgamma : MDifferentiableAt 𝓘(ℝ, ℝ) I gamma t)
    (htime : HasDerivAt (fun s : ℝ => F s (gamma t)) timeDeriv t) :
    HasDerivAt (fun s => F s (gamma s))
      (timeDeriv +
        g.inner (gamma t) (gradientFun (I := I) g (F t) (gamma t))
          (mfderiv 𝓘(ℝ, ℝ) I gamma t (1 : ℝ))) t := by
  have hJmd : MDifferentiableAt 𝓘(ℝ, ℝ) ((𝓘(ℝ, ℝ)).prod I)
      (fun s : ℝ => (s, gamma s)) t :=
    mdifferentiableAt_id.prodMk hgamma
  have hJderiv :
      (mfderiv 𝓘(ℝ, ℝ) ((𝓘(ℝ, ℝ)).prod I)
        (fun s : ℝ => (s, gamma s)) t) (1 : ℝ) =
        ((1 : ℝ), (mfderiv 𝓘(ℝ, ℝ) I gamma t) (1 : ℝ)) := by
    have hJhas : HasMFDerivAt 𝓘(ℝ, ℝ) ((𝓘(ℝ, ℝ)).prod I)
        (fun s : ℝ => (s, gamma s)) t
        ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => s) t).prod
          (mfderiv 𝓘(ℝ, ℝ) I gamma t)) :=
      HasMFDerivAt.prodMk mdifferentiableAt_id.hasMFDerivAt
        hgamma.hasMFDerivAt
    rw [hJhas.mfderiv]
    simp [mfderiv_eq_fderiv]
    rfl
  have hcurve0Within : HasDerivWithinAt (fun s => F s (gamma s))
      (NormedSpace.fromTangentSpace (F t (gamma t))
        (mfderiv ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ)
          (fun p : ℝ × M => F p.1 p.2) (t, gamma t)
          (mfderiv 𝓘(ℝ, ℝ) ((𝓘(ℝ, ℝ)).prod I)
            (fun s : ℝ => (s, gamma s)) t (1 : ℝ)))) Set.univ t := by
    simpa only [mfderivWithin_univ, Prod.fst, Prod.snd] using
      hasDerivWithinAt_comp_mfderivWithin ((𝓘(ℝ, ℝ)).prod I)
        (fun p : ℝ × M => F p.1 p.2) (fun s : ℝ => (s, gamma s)) Set.univ t hF
          hJmd.mdifferentiableWithinAt
  have hcurve0 : HasDerivAt (fun s => F s (gamma s))
      (NormedSpace.fromTangentSpace (F t (gamma t))
        (mfderiv ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ)
          (fun p : ℝ × M => F p.1 p.2) (t, gamma t)
          (mfderiv 𝓘(ℝ, ℝ) ((𝓘(ℝ, ℝ)).prod I)
            (fun s : ℝ => (s, gamma s)) t (1 : ℝ)))) t := by
    simpa only [hasDerivWithinAt_univ, mfderivWithin_univ] using hcurve0Within
  have hcurve : HasDerivAt (fun s => F s (gamma s))
      (NormedSpace.fromTangentSpace (F t (gamma t))
        (mfderiv ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ)
          (fun p : ℝ × M => F p.1 p.2) (t, gamma t)
          ((1 : ℝ), mfderiv 𝓘(ℝ, ℝ) I gamma t (1 : ℝ)))) t := by
    convert hcurve0 using 1
    rw [hJderiv]
    rfl
  apply hcurve.congr_deriv
  have hdec := mfderiv_prod_eq_add_apply
    (I := 𝓘(ℝ, ℝ)) (I' := I) (I'' := 𝓘(ℝ, ℝ))
    (f := fun p : ℝ × M => F p.1 p.2) (p := (t, gamma t))
    (v := ((1 : ℝ), mfderiv 𝓘(ℝ, ℝ) I gamma t (1 : ℝ))) hF
  rw [hdec]
  have hlin : NormedSpace.fromTangentSpace (F t (gamma t))
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => F s (gamma t)) t
            (1 : ℝ) +
          mfderiv I 𝓘(ℝ, ℝ) (F t) (gamma t)
            (mfderiv 𝓘(ℝ, ℝ) I gamma t (1 : ℝ))) =
      NormedSpace.fromTangentSpace (F t (gamma t))
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => F s (gamma t)) t
          (1 : ℝ)) +
      NormedSpace.fromTangentSpace (F t (gamma t))
        (mfderiv I 𝓘(ℝ, ℝ) (F t) (gamma t)
          (mfderiv 𝓘(ℝ, ℝ) I gamma t (1 : ℝ))) := by
    simp [NormedSpace.fromTangentSpace, map_add]
  rw [hlin]
  congr 1
  · have hd : deriv (fun s : ℝ => F s (gamma t)) t =
        NormedSpace.fromTangentSpace (F t (gamma t))
          (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => F s (gamma t)) t
            (1 : ℝ)) := by
      rw [mfderiv_eq_fderiv]
      change deriv (fun s : ℝ => F s (gamma t)) t =
        (fderiv ℝ (fun s : ℝ => F s (gamma t)) t) (1 : ℝ)
      rw [fderiv_apply_one_eq_deriv]
    exact hd.symm.trans htime.deriv
  · exact (inner_gradientFun (I := I) g (F t) (gamma t)
      (mfderiv 𝓘(ℝ, ℝ) I gamma t (1 : ℝ))).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Calculus.hasDerivAt_along_curve then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Calculus.hasDerivAt_along_curve"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Calculus.hasDerivAt_along_curve ``Submission.DifferentialGeometry.Analysis.Calculus.hasDerivAt_along_curve

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem hasDerivAt_diag0
    {F : ℝ → M → ℝ} {alpha : ℝ → M} {s q : ℝ}
    (hF : MDifferentiableAt ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ)
      (fun p : ℝ × M => F p.1 p.2) (s, alpha s))
    (halpha : MDifferentiableAt 𝓘(ℝ, ℝ) I alpha s)
    (hzero : (fun x : M => F s x) =ᶠ[𝓝 (alpha s)] fun _ => 0)
    (hfixed : HasDerivAt (fun r => F r (alpha s)) q s) :
    HasDerivAt (fun r => F r (alpha r)) q s := by
  let J : ℝ → ℝ × M := fun r => (r, alpha r)
  have hJmd : MDifferentiableAt 𝓘(ℝ, ℝ) ((𝓘(ℝ, ℝ)).prod I) J s :=
    mdifferentiableAt_id.prodMk halpha
  have hJderiv :
      (mfderiv 𝓘(ℝ, ℝ) ((𝓘(ℝ, ℝ)).prod I) J s) (realTangentOne s) =
        (realTangentOne s,
          (mfderiv 𝓘(ℝ, ℝ) I alpha s) (realTangentOne s)) := by
    have hJhas : HasMFDerivAt 𝓘(ℝ, ℝ) ((𝓘(ℝ, ℝ)).prod I) J s
        ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun r : ℝ => r) s).prod
          (mfderiv 𝓘(ℝ, ℝ) I alpha s)) :=
      HasMFDerivAt.prodMk mdifferentiableAt_id.hasMFDerivAt
        halpha.hasMFDerivAt
    rw [hJhas.mfderiv]
    simp [mfderiv_eq_fderiv]
    rfl
  have hdiag0 : HasDerivAt (fun r => F r (alpha r))
      (NormedSpace.fromTangentSpace (F s (alpha s))
        (mfderiv ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ)
          (fun p : ℝ × M => F p.1 p.2) (s, alpha s)
        ((mfderiv 𝓘(ℝ, ℝ) ((𝓘(ℝ, ℝ)).prod I) J s)
          (realTangentOne s)))) s := by
    simpa only [J, Function.comp_apply] using
      hasDerivAt_comp_mfderiv_along ((𝓘(ℝ, ℝ)).prod I)
        (fun p : ℝ × M => F p.1 p.2) J s hF hJmd
  have hspace : mfderiv I 𝓘(ℝ, ℝ) (fun x => F s x) (alpha s) = 0 := by
    rw [hzero.mfderiv_eq (I := I) (I' := 𝓘(ℝ, ℝ)), mfderiv_const]
    rfl
  have hdec := mfderiv_prod_eq_add_apply
    (I := 𝓘(ℝ, ℝ)) (I' := I) (I'' := 𝓘(ℝ, ℝ))
    (f := fun p : ℝ × M => F p.1 p.2) (p := (s, alpha s))
    (v := (realTangentOne s,
      (mfderiv 𝓘(ℝ, ℝ) I alpha s) (realTangentOne s))) hF
  have htime :
      NormedSpace.fromTangentSpace (F s (alpha s))
          (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
            (fun r : ℝ => F r (alpha s)) s (realTangentOne s)) = q := by
    have hd : deriv (fun r : ℝ => F r (alpha s)) s =
        NormedSpace.fromTangentSpace (F s (alpha s))
          (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
            (fun r : ℝ => F r (alpha s)) s (realTangentOne s)) := by
      rw [mfderiv_eq_fderiv]
      change deriv (fun r : ℝ => F r (alpha s)) s =
        (fderiv ℝ (fun r : ℝ => F r (alpha s)) s)
          (NormedSpace.fromTangentSpace (𝕜 := ℝ) s (realTangentOne s))
      rw [fromTangentSpace_realTangentOne, fderiv_apply_one_eq_deriv]
    rw [← hd, hfixed.deriv]
  apply hdiag0.congr_deriv
  rw [hJderiv]
  have hdec' := congrArg
    (NormedSpace.fromTangentSpace (F s (alpha s))) hdec
  rw [hspace] at hdec'
  have hdec'' :
      NormedSpace.fromTangentSpace (F s (alpha s))
          (mfderiv ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ)
            (fun p : ℝ × M => F p.1 p.2) (s, alpha s)
            (realTangentOne s,
              (mfderiv 𝓘(ℝ, ℝ) I alpha s) (realTangentOne s))) =
        NormedSpace.fromTangentSpace (F s (alpha s))
          (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
            (fun r : ℝ => F r (alpha s)) s (realTangentOne s)) := by
    simpa only [zero_apply, add_zero] using hdec'
  exact hdec''.trans htime

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Calculus.hasDerivAt_diag0 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Calculus.hasDerivAt_diag0"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Calculus.hasDerivAt_diag0 ``Submission.DifferentialGeometry.Analysis.Calculus.hasDerivAt_diag0

theorem deriv_along_curve_eq
    (g : SmoothRiemannianMetric I M)
    {F : ℝ → M → ℝ}
    (hF : ContMDiff ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × M => F p.1 p.2))
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    {t : ℝ} :
    deriv (fun s => F s (γ s)) t =
      deriv (fun s => F s (γ t)) t +
        g.inner (γ t) (gradientFun (I := I) g (F t) (γ t))
          (mfderiv 𝓘(ℝ, ℝ) I γ t (realTangentOne t)) := by
  classical
  have hJ : ContMDiff 𝓘(ℝ, ℝ) ((𝓘(ℝ, ℝ)).prod I) ∞ (fun s : ℝ => (s, γ s)) :=
    contMDiff_id.prodMk hγ
  have hFmd : MDifferentiableAt ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ)
      (fun p : ℝ × M => F p.1 p.2) (t, γ t) :=
    hF.mdifferentiableAt (x := (t, γ t)) (by norm_num)
  have hJmd : MDifferentiableAt 𝓘(ℝ, ℝ) ((𝓘(ℝ, ℝ)).prod I)
      (fun s : ℝ => (s, γ s)) t :=
    hJ.mdifferentiableAt (x := t) (by norm_num)
  have hJderiv0 : (mfderiv 𝓘(ℝ, ℝ) ((𝓘(ℝ, ℝ)).prod I)
      (fun s : ℝ => (s, γ s)) t) (realTangentOne t) =
      (realTangentOne t, mfderiv 𝓘(ℝ, ℝ) I γ t (realTangentOne t)) := by
    have hid : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => s) t :=
      (contMDiff_id (n := ∞) : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun s : ℝ => s)).mdifferentiableAt
        (by norm_num)
    have hJhas : HasMFDerivAt 𝓘(ℝ, ℝ) ((𝓘(ℝ, ℝ)).prod I)
        (fun s : ℝ => (s, γ s)) t
        ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => s) t).prod
          (mfderiv 𝓘(ℝ, ℝ) I γ t)) := by
      exact HasMFDerivAt.prodMk hid.hasMFDerivAt
        (hγ.mdifferentiableAt (x := t) (by simp)).hasMFDerivAt
    have hJderiv := hJhas.mfderiv
    rw [hJderiv]
    simp [mfderiv_eq_fderiv]
    rfl
  have hcurve0 : HasDerivAt (fun s => F s (γ s))
      (NormedSpace.fromTangentSpace (F t (γ t))
        (mfderiv ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ)
          (fun p : ℝ × M => F p.1 p.2) (t, γ t)
          (mfderiv 𝓘(ℝ, ℝ) ((𝓘(ℝ, ℝ)).prod I)
            (fun s : ℝ => (s, γ s)) t (realTangentOne t)))) t := by
    exact hasDerivAt_comp_mfderiv_along ((𝓘(ℝ, ℝ)).prod I)
      (fun p : ℝ × M => F p.1 p.2) (fun s : ℝ => (s, γ s)) t hFmd hJmd
  have hcurve : HasDerivAt (fun s => F s (γ s))
      (NormedSpace.fromTangentSpace (F t (γ t))
        (mfderiv ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ)
          (fun p : ℝ × M => F p.1 p.2) (t, γ t)
          (realTangentOne t,
            mfderiv 𝓘(ℝ, ℝ) I γ t (realTangentOne t)))) t := by
    convert hcurve0 using 1
    rw [hJderiv0]
    rfl
  have hmain' : deriv (fun s => F s (γ s)) t =
      NormedSpace.fromTangentSpace (F t (γ t))
        (mfderiv ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ)
          (fun p : ℝ × M => F p.1 p.2) (t, γ t)
          (realTangentOne t,
            mfderiv 𝓘(ℝ, ℝ) I γ t (realTangentOne t))) :=
    hcurve.deriv
  rw [hmain']
  have hdec := mfderiv_prod_eq_add_apply
    (I := 𝓘(ℝ, ℝ)) (I' := I) (I'' := 𝓘(ℝ, ℝ))
    (f := fun p : ℝ × M => F p.1 p.2) (p := (t, γ t))
    (v := (realTangentOne t,
      mfderiv 𝓘(ℝ, ℝ) I γ t (realTangentOne t)))
    (hF.mdifferentiableAt (x := (t, γ t)) (by simp))
  rw [hdec]
  have hlin : NormedSpace.fromTangentSpace (F t (γ t))
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => F s (γ t)) t
            (realTangentOne t) +
          mfderiv I 𝓘(ℝ, ℝ) (F t) (γ t)
            (mfderiv 𝓘(ℝ, ℝ) I γ t (realTangentOne t))) =
      NormedSpace.fromTangentSpace (F t (γ t))
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => F s (γ t)) t
          (realTangentOne t)) +
      NormedSpace.fromTangentSpace (F t (γ t))
        (mfderiv I 𝓘(ℝ, ℝ) (F t) (γ t)
          (mfderiv 𝓘(ℝ, ℝ) I γ t (realTangentOne t))) := by
    simp [NormedSpace.fromTangentSpace, map_add]
  rw [hlin]
  congr 1
  · have hslice : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => F s (γ t)) t :=
      (hF.comp (contMDiff_id.prodMk (contMDiff_const (c := γ t)))).mdifferentiableAt
        (x := t) (by norm_num)
    have hd : deriv (fun s : ℝ => F s (γ t)) t =
        NormedSpace.fromTangentSpace (F t (γ t))
          (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => F s (γ t)) t
            (realTangentOne t)) := by
      rw [mfderiv_eq_fderiv]
      change deriv (fun s : ℝ => F s (γ t)) t =
        (fderiv ℝ (fun s : ℝ => F s (γ t)) t) (1 : ℝ)
      rw [fderiv_apply_one_eq_deriv (f := fun s : ℝ => F s (γ t)) (x := t)]
    exact hd.symm
  · have hinner := inner_gradientFun (I := I) g (F t) (γ t)
      (mfderiv 𝓘(ℝ, ℝ) I γ t (realTangentOne t))
    symm
    exact hinner

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Calculus.deriv_along_curve_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Calculus.deriv_along_curve_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Calculus.deriv_along_curve_eq ``Submission.DifferentialGeometry.Analysis.Calculus.deriv_along_curve_eq

theorem deriv_along_curve_eq_on
    {D : RealTimeInterval}
    (g : SmoothRiemannianMetric I M)
    {F : ℝ → M → ℝ}
    (hF : ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × M => F p.1 p.2)
      (D.regular ×ˢ _root_.Set.univ))
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    {t : ℝ} (ht : t ∈ D.regular) :
    deriv (fun s => F s (γ s)) t =
      deriv (fun s => F s (γ t)) t +
        g.inner (γ t) (gradientFun (I := I) g (F t) (γ t))
          (mfderiv 𝓘(ℝ, ℝ) I γ t (realTangentOne t)) := by
  classical
  have hJ : ContMDiff 𝓘(ℝ, ℝ) ((𝓘(ℝ, ℝ)).prod I) ∞ (fun s : ℝ => (s, γ s)) :=
    contMDiff_id.prodMk hγ
  have hFmd : MDifferentiableAt ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ)
      (fun p : ℝ × M => F p.1 p.2) (t, γ t) := by
    have hnh : D.regular ×ˢ _root_.Set.univ ∈ 𝓝 (t, γ t) :=
      (IsOpen.prod D.regular_isOpen isOpen_univ).mem_nhds ⟨ht, trivial⟩
    exact (hF.contMDiffAt hnh).mdifferentiableAt (by norm_num)
  have hJmd : MDifferentiableAt 𝓘(ℝ, ℝ) ((𝓘(ℝ, ℝ)).prod I)
      (fun s : ℝ => (s, γ s)) t :=
    hJ.mdifferentiableAt (x := t) (by norm_num)
  have hJderiv0 : (mfderiv 𝓘(ℝ, ℝ) ((𝓘(ℝ, ℝ)).prod I)
      (fun s : ℝ => (s, γ s)) t) (realTangentOne t) =
      (realTangentOne t, mfderiv 𝓘(ℝ, ℝ) I γ t (realTangentOne t)) := by
    have hid : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => s) t :=
      (contMDiff_id (n := ∞) : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun s : ℝ => s)).mdifferentiableAt
        (by norm_num)
    have hJhas : HasMFDerivAt 𝓘(ℝ, ℝ) ((𝓘(ℝ, ℝ)).prod I)
        (fun s : ℝ => (s, γ s)) t
        ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => s) t).prod
          (mfderiv 𝓘(ℝ, ℝ) I γ t)) := by
      exact HasMFDerivAt.prodMk hid.hasMFDerivAt
        (hγ.mdifferentiableAt (x := t) (by simp)).hasMFDerivAt
    have hJderiv := hJhas.mfderiv
    rw [hJderiv]
    simp [mfderiv_eq_fderiv]
    rfl
  have hcurve0 : HasDerivAt (fun s => F s (γ s))
      (NormedSpace.fromTangentSpace (F t (γ t))
        (mfderiv ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ)
          (fun p : ℝ × M => F p.1 p.2) (t, γ t)
          (mfderiv 𝓘(ℝ, ℝ) ((𝓘(ℝ, ℝ)).prod I)
            (fun s : ℝ => (s, γ s)) t (realTangentOne t)))) t := by
    exact hasDerivAt_comp_mfderiv_along ((𝓘(ℝ, ℝ)).prod I)
      (fun p : ℝ × M => F p.1 p.2) (fun s : ℝ => (s, γ s)) t hFmd hJmd
  have hcurve : HasDerivAt (fun s => F s (γ s))
      (NormedSpace.fromTangentSpace (F t (γ t))
        (mfderiv ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ)
          (fun p : ℝ × M => F p.1 p.2) (t, γ t)
          (realTangentOne t,
            mfderiv 𝓘(ℝ, ℝ) I γ t (realTangentOne t)))) t := by
    convert hcurve0 using 1
    rw [hJderiv0]
    rfl
  have hmain' : deriv (fun s => F s (γ s)) t =
      NormedSpace.fromTangentSpace (F t (γ t))
        (mfderiv ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ)
          (fun p : ℝ × M => F p.1 p.2) (t, γ t)
          (realTangentOne t,
            mfderiv 𝓘(ℝ, ℝ) I γ t (realTangentOne t))) :=
    hcurve.deriv
  rw [hmain']
  have hdec := mfderiv_prod_eq_add_apply
    (I := 𝓘(ℝ, ℝ)) (I' := I) (I'' := 𝓘(ℝ, ℝ))
    (f := fun p : ℝ × M => F p.1 p.2) (p := (t, γ t))
    (v := (realTangentOne t,
      mfderiv 𝓘(ℝ, ℝ) I γ t (realTangentOne t)))
    hFmd
  rw [hdec]
  have hlin : NormedSpace.fromTangentSpace (F t (γ t))
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => F s (γ t)) t
            (realTangentOne t) +
          mfderiv I 𝓘(ℝ, ℝ) (F t) (γ t)
            (mfderiv 𝓘(ℝ, ℝ) I γ t (realTangentOne t))) =
      NormedSpace.fromTangentSpace (F t (γ t))
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => F s (γ t)) t
          (realTangentOne t)) +
      NormedSpace.fromTangentSpace (F t (γ t))
        (mfderiv I 𝓘(ℝ, ℝ) (F t) (γ t)
          (mfderiv 𝓘(ℝ, ℝ) I γ t (realTangentOne t))) := by
    simp [NormedSpace.fromTangentSpace, map_add]
  rw [hlin]
  congr 1
  · have hslice : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => F s (γ t)) t := by
      have hnh : D.regular ×ˢ _root_.Set.univ ∈ 𝓝 (t, γ t) :=
        (IsOpen.prod D.regular_isOpen isOpen_univ).mem_nhds ⟨ht, trivial⟩
      have hFat : ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × M => F p.1 p.2) (t, γ t) := hF.contMDiffAt hnh
      have hsliceAt : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun s : ℝ => F s (γ t)) t :=
        hFat.comp (x := t) (contMDiffAt_id.prodMk contMDiffAt_const)
      exact ContMDiffAt.mdifferentiableAt hsliceAt (by norm_num)
    have hd : deriv (fun s : ℝ => F s (γ t)) t =
        NormedSpace.fromTangentSpace (F t (γ t))
          (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => F s (γ t)) t
            (realTangentOne t)) := by
      rw [mfderiv_eq_fderiv]
      change deriv (fun s : ℝ => F s (γ t)) t =
        (fderiv ℝ (fun s : ℝ => F s (γ t)) t) (1 : ℝ)
      rw [fderiv_apply_one_eq_deriv (f := fun s : ℝ => F s (γ t)) (x := t)]
    exact hd.symm
  · have hinner := inner_gradientFun (I := I) g (F t) (γ t)
      (mfderiv 𝓘(ℝ, ℝ) I γ t (realTangentOne t))
    symm
    exact hinner

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Calculus.deriv_along_curve_eq_on then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Calculus.deriv_along_curve_eq_on"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Calculus.deriv_along_curve_eq_on ``Submission.DifferentialGeometry.Analysis.Calculus.deriv_along_curve_eq_on

end DifferentialGeometry.Analysis.Calculus

end
