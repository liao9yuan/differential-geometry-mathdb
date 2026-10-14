import Submission.DifferentialGeometry.External.DeGiorgi.Localization
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.ZeroExtension

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory _root_.Set
open scoped _root_.ENNReal _root_.NNReal

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

private noncomputable def zeroExtendTestWitness
    {Omega W : Set E} (hOmega : IsOpen Omega) (hW : IsOpen W)
    {v : E → ℝ} (hv0 : MemH01 v W)
    (hv : MemW1pWitness 2 v W) :
    MemW1pWitness 2 (W.indicator v) Omega := by
  let hv0Real : MemW01p (ENNReal.ofReal (2 : ℝ)) v W := by
    simpa using hv0
  let hvReal : MemW1pWitness (ENNReal.ofReal (2 : ℝ)) v W :=
    { memLp := by simpa using hv.memLp
      weakGrad := hv.weakGrad
      weakGrad_component_memLp := by
        intro i
        simpa using hv.weakGrad_component_memLp i
      isWeakGrad := hv.isWeakGrad }
  let hExtRaw : MemW1pWitness (ENNReal.ofReal (2 : ℝ))
      (W.indicator v) Set.univ :=
    zeroExtendMemW1pWitnessP (d := d) hW
      (p := 2) (by norm_num) hv0Real hvReal
  let hExt := hExtRaw.restrict hOmega (Set.subset_univ Omega)
  exact
    { memLp := by simpa using hExt.memLp
      weakGrad := hExt.weakGrad
      weakGrad_component_memLp := by
        intro i
        simpa using hExt.weakGrad_component_memLp i
      isWeakGrad := hExt.isWeakGrad }

run_cmd do
  let target := ``Submission.DeGiorgi.zeroExtendTestWitness
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DeGiorgi.zeroExtendTestWitness target :: scope.openDecls } }

@[simp] private theorem zeroExtendTestWitness_weakGrad_apply
    {Omega W : Set E} (hOmega : IsOpen Omega) (hW : IsOpen W)
    {v : E → ℝ} (hv0 : MemH01 v W)
    (hv : MemW1pWitness 2 v W) (x : E) (i : Fin d) :
    (zeroExtendTestWitness (d := d) hOmega hW hv0 hv).weakGrad x i =
      W.indicator (fun y => hv.weakGrad y i) x := by
  simp [zeroExtendTestWitness, zeroExtendMemW1pWitnessP, MemW1pWitness.restrict]

run_cmd do
  let target := ``Submission.DeGiorgi.zeroExtendTestWitness_weakGrad_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DeGiorgi.zeroExtendTestWitness_weakGrad_apply target :: scope.openDecls } }

private theorem bilinFormOfCoeff_restrict_eq_zeroExtend
    {Omega W : Set E} (hOmega : IsOpen Omega) (hW : IsOpen W)
    (hsub : W ⊆ Omega) (A : EllipticCoeff d Omega)
    {u v : E → ℝ} (hu : MemW1pWitness 2 u Omega)
    (hv0 : MemH01 v W)
    (hv : MemW1pWitness 2 v W) :
    bilinFormOfCoeff (A.restrict hsub)
        (hu.restrict hW hsub) hv =
      bilinFormOfCoeff A hu
        (zeroExtendTestWitness (d := d) hOmega hW hv0 hv) := by
  let hExt : MemW1pWitness 2 (W.indicator v) Omega :=
    zeroExtendTestWitness (d := d) hOmega hW hv0 hv
  let A' : EllipticCoeff d W := A.restrict hsub
  let hu' : MemW1pWitness 2 u W := hu.restrict hW hsub
  let small : E → ℝ := fun x =>
    bilinFormIntegrandOfCoeff A' hu' hv x
  have hEq : (W.indicator small) =ᵐ[(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E).restrict Omega]
      fun x => bilinFormIntegrandOfCoeff A hu hExt x := by
    filter_upwards with x
    by_cases hx : x ∈ W
    · have hgrad : hExt.weakGrad x = hv.weakGrad x := by
        apply PiLp.ext
        intro i
        simp [hExt, zeroExtendTestWitness_weakGrad_apply, hx]
      simp [A', hu', small, hExt, hgrad, EllipticCoeff.restrict,
        MemW1pWitness.restrict, hx,
        bilinFormIntegrandOfCoeff]
    · have hgrad : hExt.weakGrad x = 0 := by
        apply PiLp.ext
        intro i
        simp [hExt, zeroExtendTestWitness_weakGrad_apply, hx]
      simp [A', hu', small, hExt, hgrad, EllipticCoeff.restrict,
        MemW1pWitness.restrict, hx,
        bilinFormIntegrandOfCoeff]
  calc
    bilinFormOfCoeff A' hu' hv =
        ∫ x in W, small x ∂((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E).restrict Omega) := by
          simp [bilinFormOfCoeff, small,
            Measure.restrict_restrict_of_subset hsub]
    _ = ∫ x, W.indicator small x ∂((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E).restrict Omega) := by
          symm
          exact _root_.MeasureTheory.integral_indicator hW.measurableSet
    _ = ∫ x, bilinFormIntegrandOfCoeff A hu hExt x
          ∂((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E).restrict Omega) := _root_.MeasureTheory.integral_congr_ae hEq
    _ = bilinFormOfCoeff A hu hExt := rfl

run_cmd do
  let target := ``Submission.DeGiorgi.bilinFormOfCoeff_restrict_eq_zeroExtend
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DeGiorgi.bilinFormOfCoeff_restrict_eq_zeroExtend target :: scope.openDecls } }

theorem bilinFormOfCoeff_restrict_eq_integral
    {Omega W : Set E} (hOmega : IsOpen Omega) (hW : IsOpen W)
    (hsub : W ⊆ Omega)
    {A : EllipticCoeff d Omega} {u f v : E → ℝ}
    (hu : MemW1pWitness 2 u Omega)
    (hweak : ∀ z, MemH01 z Omega →
      ∀ hz : MemW1pWitness 2 z Omega,
        bilinFormOfCoeff A hu hz =
          ∫ x in Omega, f x * z x ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E))
    (hv0 : MemH01 v W)
    (hv : MemW1pWitness 2 v W) :
    bilinFormOfCoeff (A.restrict hsub)
        (hu.restrict hW hsub) hv =
      ∫ x in W, f x * v x ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) := by
  let hExt : MemW1pWitness 2 (W.indicator v) Omega :=
    zeroExtendTestWitness (d := d) hOmega hW hv0 hv
  have hExt0 : MemH01 (W.indicator v) Omega :=
    MemH01.indicator_of_subset hOmega hW hsub hv0
  calc
    bilinFormOfCoeff (A.restrict hsub)
        (hu.restrict hW hsub) hv =
        bilinFormOfCoeff A hu hExt :=
      bilinFormOfCoeff_restrict_eq_zeroExtend (d := d) hOmega hW hsub A hu hv0 hv
    _ = ∫ x in Omega, f x * W.indicator v x
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) := hweak _ hExt0 hExt
    _ = ∫ x, W.indicator (fun y => f y * v y) x
          ∂((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E).restrict Omega) := by
      refine _root_.MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      by_cases hx : x ∈ W <;> simp [hx]
    _ = ∫ x in W, f x * v x ∂((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E).restrict Omega) :=
      _root_.MeasureTheory.integral_indicator hW.measurableSet
    _ = ∫ x in W, f x * v x ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) := by
      rw [Measure.restrict_restrict_of_subset hsub]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.bilinFormOfCoeff_restrict_eq_integral then
    throwError "Refusing to shadow existing declaration DeGiorgi.bilinFormOfCoeff_restrict_eq_integral"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.bilinFormOfCoeff_restrict_eq_integral ``Submission.DeGiorgi.bilinFormOfCoeff_restrict_eq_integral

end DeGiorgi
