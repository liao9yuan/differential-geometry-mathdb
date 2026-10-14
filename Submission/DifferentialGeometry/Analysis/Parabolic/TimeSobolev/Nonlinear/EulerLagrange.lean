import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Nonlinear.Action

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X : Type*}
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [FiniteDimensional ℝ X]
variable {T : ℝ}

def timeCoeffPot
    (B : ℝ → X → X →L[ℝ] X) (V : ℝ → X → ℝ)
    (u : timeH1 X T) : ℝ :=
  timeCoeffAction B u + timeNlinPot V u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeCoeffPot then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeCoeffPot"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeCoeffPot ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeCoeffPot

omit [FiniteDimensional ℝ X] in
theorem coeffForce_norm
    (DB : X →L[ℝ] (X →L[ℝ] X)) (p : X) :
    ‖coeffForce DB p‖ ≤ ‖DB‖ * ‖p‖ ^ 2 := by
  rw [← (InnerProductSpace.toDual ℝ X).norm_map]
  simp only [coeffForce, (InnerProductSpace.toDual ℝ X).apply_symm_apply]
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (norm_nonneg DB) (sq_nonneg ‖p‖)) ?_
  intro w
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
    innerSL_apply_apply]
  calc
    ‖inner ℝ p ((DB w) p)‖ ≤ ‖p‖ * ‖(DB w) p‖ := norm_inner_le_norm _ _
    _ ≤ ‖p‖ * (‖DB w‖ * ‖p‖) := by
      gcongr
      exact (DB w).le_opNorm p
    _ ≤ ‖p‖ * ((‖DB‖ * ‖w‖) * ‖p‖) := by
      gcongr
      exact DB.le_opNorm w
    _ = (‖DB‖ * ‖p‖ ^ 2) * ‖w‖ := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.coeffForce_norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.coeffForce_norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.coeffForce_norm ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.coeffForce_norm

omit [FiniteDimensional ℝ X] in
private theorem coeffQuad_at
    (B : X → X →L[ℝ] X)
    (DB : X → X →L[ℝ] (X →L[ℝ] X))
    (x p w q : X) (c : ℝ)
    (hB : HasFDerivAt B (DB (x + c • w)) (x + c • w))
    (hself : IsSelfAdjoint (B (x + c • w))) :
    HasDerivAt
      (fun z : ℝ ↦
        _root_.Inner.inner ℝ (B (x + z • w) (p + z • q)) (p + z • q))
      (_root_.Inner.inner ℝ (((DB (x + c • w)) w) (p + c • q)) (p + c • q) +
        2 * _root_.Inner.inner ℝ (B (x + c • w) (p + c • q)) q) c := by
  let xc : ℝ → X := fun z ↦ x + z • w
  let pc : ℝ → X := fun z ↦ p + z • q
  have hxc : HasDerivAt xc w c := by
    change HasDerivAt (fun z : ℝ => x + id z • w) w c
    simpa only [one_smul] using ((hasDerivAt_id c).smul_const w).const_add x
  have hpc : HasDerivAt pc q c := by
    change HasDerivAt (fun z : ℝ => p + id z • q) q c
    simpa only [one_smul] using ((hasDerivAt_id c).smul_const q).const_add p
  have hBc : HasDerivAt (fun z ↦ B (xc z)) ((DB (xc c)) w) c := by
    change HasDerivAt (B ∘ xc) ((DB (xc c)) w) c
    exact hB.comp_hasDerivAt c hxc
  have hBpc : HasDerivAt (fun z ↦ B (xc z) (pc z))
      (((DB (xc c)) w) (pc c) + B (xc c) q) c := hBc.clm_apply hpc
  have hinner := hBpc.inner ℝ hpc
  have hsym : _root_.Inner.inner ℝ (B (xc c) q) (pc c) =
      inner ℝ (B (xc c) (pc c)) q := by
    calc
      _root_.Inner.inner ℝ (B (xc c) q) (pc c) =
          inner ℝ (pc c) (B (xc c) q) := real_inner_comm _ _
      _ = _root_.Inner.inner ℝ (B (xc c) (pc c)) q := by
        exact (hself.isSymmetric (pc c) q).symm
  simpa only [xc, pc, inner_add_left, hsym, two_mul, add_assoc, add_comm,
    add_left_comm] using hinner

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.coeffQuad_at
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.coeffQuad_at target :: scope.openDecls } }

omit [FiniteDimensional ℝ X] in
theorem timeCoeff_line_on
    (hT : 0 ≤ T)
    (B : ℝ → X → X →L[ℝ] X)
    (DB : ℝ → X → X →L[ℝ] (X →L[ℝ] X))
    (u v : timeH1 X T)
    (hB_on : ∀ᵐ t ∂volume, t ∈ _root_.Set.uIoc (0 : ℝ) T →
      ∀ c ∈ _root_.Set.Icc (-1 : ℝ) 1,
        HasFDerivAt (B t) (DB t (u.toFun t + c • v.toFun t))
          (u.toFun t + c • v.toFun t))
    (hself_on : ∀ᵐ t ∂volume, t ∈ _root_.Set.uIoc (0 : ℝ) T →
      ∀ c ∈ _root_.Set.Icc (-1 : ℝ) 1,
        IsSelfAdjoint (B t (u.toFun t + c • v.toFun t)))
    (bound : ℝ → ℝ)
    (hmeas : ∀ᶠ c in nhds (0 : ℝ),
      _root_.MeasureTheory.AEStronglyMeasurable (coeffLineLag B u v c)
        (volume.restrict (_root_.Set.uIoc (0 : ℝ) T)))
    (hint : IntervalIntegrable (coeffLineLag B u v 0) _root_.MeasureTheory.MeasureSpace.volume 0 T)
    (hdmeas : _root_.MeasureTheory.AEStronglyMeasurable (coeffLineDeriv B DB u v 0)
      (volume.restrict (_root_.Set.uIoc (0 : ℝ) T)))
    (hbound : ∀ᵐ t ∂volume, t ∈ _root_.Set.uIoc (0 : ℝ) T →
      ∀ c ∈ _root_.Set.Icc (-1 : ℝ) 1, ‖coeffLineDeriv B DB u v c t‖ ≤ bound t)
    (hboundInt : IntervalIntegrable bound _root_.MeasureTheory.MeasureSpace.volume 0 T) :
    IntervalIntegrable (coeffLineDeriv B DB u v 0) _root_.MeasureTheory.MeasureSpace.volume 0 T ∧
      HasDerivAt (fun c : ℝ ↦ timeCoeffAction B (u + c • v))
        (∫ t in (0 : ℝ)..T, coeffLineDeriv B DB u v 0 t) 0 := by
  have hdiff : ∀ᵐ t ∂volume, t ∈ _root_.Set.uIoc (0 : ℝ) T →
      ∀ c ∈ _root_.Set.Icc (-1 : ℝ) 1,
        HasDerivAt (fun z : ℝ ↦ coeffLineLag B u v z t)
          (coeffLineDeriv B DB u v c t) c := by
    filter_upwards [hB_on, hself_on] with t hBt hst
    intro ht c hc
    have h := coeffQuad_at (B t) (DB t) (u.toFun t) (u.deriv t)
      (v.toFun t) (v.deriv t) c (hBt ht c hc) (hst ht c hc)
    simpa only [coeffLineLag, coeffLineDeriv, coeffForce_apply] using h
  have hparam :=
    intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := coeffLineLag B u v) (F' := coeffLineDeriv B DB u v)
      (x₀ := (0 : ℝ)) (μ := _root_.MeasureTheory.MeasureSpace.volume) (s := _root_.Set.Icc (-1 : ℝ) 1)
      (a := (0 : ℝ)) (b := T) (bound := bound)
      (Icc_mem_nhds (by norm_num) (by norm_num)) hmeas hint hdmeas hbound
      hboundInt hdiff
  refine ⟨hparam.1, ?_⟩
  have hlineEq (c : ℝ) : timeCoeffAction B (u + c • v) =
      ∫ t in (0 : ℝ)..T, coeffLineLag B u v c t := by
    unfold timeCoeffAction
    have hderiv : ⇑((u + c • v).deriv) =ᵐ[timeMeasure T]
        fun t ↦ u.deriv t + c • v.deriv t := by
      rw [timeH1.deriv_add, timeH1.deriv_smul]
      filter_upwards [Lp.coeFn_add u.deriv (c • v.deriv),
        Lp.coeFn_smul c v.deriv] with t hadd hsmul
      calc
        (u.deriv + c • v.deriv) t = u.deriv t + (c • v.deriv) t := by
          simpa only [Pi.add_apply] using hadd
        _ = u.deriv t + c • v.deriv t := congrArg (fun z ↦ u.deriv t + z)
          (by simpa only [Pi.smul_apply] using hsmul)
    have hderiv' : ⇑((u + c • v).deriv) =ᵐ[volume.restrict (_root_.Set.uIoc (0 : ℝ) T)]
        fun t ↦ u.deriv t + c • v.deriv t := by
      have hsub : _root_.Set.uIoc (0 : ℝ) T ⊆ _root_.Set.Icc (0 : ℝ) T := by
        simpa only [_root_.Set.uIcc_of_le hT] using
          (_root_.Set.uIoc_subset_uIcc : _root_.Set.uIoc (0 : ℝ) T ⊆ _root_.Set.uIcc (0 : ℝ) T)
      have hm := hderiv.filter_mono
        (_root_.MeasureTheory.ae_mono (Measure.restrict_mono hsub le_rfl))
      simpa only [timeMeasure] using hm
    apply intervalIntegral.integral_congr_ae_restrict
    filter_upwards [hderiv', _root_.MeasureTheory.ae_restrict_mem measurableSet_uIoc] with t hd ht
    have ht' : t ∈ _root_.Set.Icc (0 : ℝ) T := by
      simpa only [_root_.Set.uIcc_of_le hT] using _root_.Set.uIoc_subset_uIcc ht
    change _root_.Inner.inner ℝ (B t ((u + c • v).toFun t) ((u + c • v).deriv t))
      ((u + c • v).deriv t) = coeffLineLag B u v c t
    rw [timeH1.toFun_add u (c • v) ht', timeH1.toFun_smul c v ht', hd]
    rfl
  exact hparam.2.congr_of_eventuallyEq (Eventually.of_forall hlineEq)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeCoeff_line_on then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeCoeff_line_on"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeCoeff_line_on ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeCoeff_line_on

omit [FiniteDimensional ℝ X] in
private theorem coeffForce_cont : Continuous
    (fun q : (X →L[ℝ] (X →L[ℝ] X)) × X ↦ coeffForce q.1 q.2) := by
  unfold coeffForce
  fun_prop

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.coeffForce_cont
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.coeffForce_cont target :: scope.openDecls } }

omit [FiniteDimensional ℝ X] in
theorem timeCoeff_euler
    (hT : 0 < T)
    (B : ℝ → X → X →L[ℝ] X)
    (DB : ℝ → X → X →L[ℝ] (X →L[ℝ] X))
    (V : ℝ → X → ℝ) (G : ℝ → X → X)
    (hVcont : Continuous (fun p : ℝ × X ↦ V p.1 p.2))
    (hGcont : Continuous (fun p : ℝ × X ↦ G p.1 p.2))
    (hgrad : ∀ t x, HasFDerivAt (V t) (innerSL ℝ (G t x)) x)
    (u : timeH1 X T)
    (hA : _root_.MeasureTheory.AEStronglyMeasurable (fun t ↦ B t (u.toFun t)) (timeMeasure T))
    (C : NNReal)
    (hC : ∀ᵐ t ∂timeMeasure T, ‖B t (u.toFun t)‖ ≤ (C : ℝ))
    (hDBm : _root_.MeasureTheory.AEStronglyMeasurable (fun t ↦ DB t (u.toFun t)) (timeMeasure T))
    (D : NNReal)
    (hD : ∀ᵐ t ∂timeMeasure T, ‖DB t (u.toFun t)‖ ≤ (D : ℝ))
    (hactInt : IntervalIntegrable
      (fun t ↦ _root_.Inner.inner ℝ (B t (u.toFun t) (u.deriv t)) (u.deriv t))
      _root_.MeasureTheory.MeasureSpace.volume 0 T)
    (scale : timeH1 X T → ℝ)
    (hscale : ∀ v, 0 < scale v)
    (lineBound : timeH1 X T → ℝ → ℝ)
    (hlineMeas : ∀ v, ∀ᶠ c in nhds (0 : ℝ),
      _root_.MeasureTheory.AEStronglyMeasurable (coeffLineLag B u (scale v • v) c)
        (volume.restrict (_root_.Set.uIoc (0 : ℝ) T)))
    (hdlineMeas : ∀ v,
      _root_.MeasureTheory.AEStronglyMeasurable (coeffLineDeriv B DB u (scale v • v) 0)
      (volume.restrict (_root_.Set.uIoc (0 : ℝ) T)))
    (hB_on : ∀ v, ∀ᵐ t ∂volume, t ∈ _root_.Set.uIoc (0 : ℝ) T →
      ∀ c ∈ _root_.Set.Icc (-1 : ℝ) 1,
        HasFDerivAt
          (B t) (DB t (u.toFun t + c • (scale v • v).toFun t))
          (u.toFun t + c • (scale v • v).toFun t))
    (hself_on : ∀ v, ∀ᵐ t ∂volume, t ∈ _root_.Set.uIoc (0 : ℝ) T →
      ∀ c ∈ _root_.Set.Icc (-1 : ℝ) 1,
        IsSelfAdjoint (B t (u.toFun t + c • (scale v • v).toFun t)))
    (hlineDom : ∀ v, ∀ᵐ t ∂volume, t ∈ _root_.Set.uIoc (0 : ℝ) T →
      ∀ c ∈ _root_.Set.Icc (-1 : ℝ) 1,
        ‖coeffLineDeriv B DB u (scale v • v) c t‖ ≤ lineBound v t)
    (hlineInt : ∀ v, IntervalIntegrable (lineBound v) _root_.MeasureTheory.MeasureSpace.volume 0 T)
    (hmin : IsLocalMinOn (timeCoeffPot B V) (sameTimeEnds u) u) :
    let A : ℝ → X →L[ℝ] X := fun t ↦ B t (u.toFun t)
    let F : ℝ → X := fun t ↦
      coeffForce (DB t (u.toFun t)) (u.deriv t) + G t (u.toFun t)
    _root_.MeasureTheory.IntegrableOn F (_root_.Set.Icc (0 : ℝ) T) _root_.MeasureTheory.MeasureSpace.volume ∧
      ∀ v : timeH1 X T, v.initial = 0 → v.toFun T = 0 →
        2 * _root_.Inner.inner ℝ (timeOp A hA C hC u.deriv) v.deriv +
          ∫ t in _root_.Set.Icc (0 : ℝ) T, _root_.Inner.inner ℝ (F t) (v.toFun t) = 0 := by
  dsimp only
  let A : ℝ → X →L[ℝ] X := fun t ↦ B t (u.toFun t)
  let Fc : ℝ → X := fun t ↦ coeffForce (DB t (u.toFun t)) (u.deriv t)
  let Fp : ℝ → X := fun t ↦ G t (u.toFun t)
  let F : ℝ → X := fun t ↦ Fc t + Fp t
  have hFcMeas : _root_.MeasureTheory.AEStronglyMeasurable Fc (timeMeasure T) := by
    have hp : _root_.MeasureTheory.AEStronglyMeasurable
        (fun t ↦ (DB t (u.toFun t), u.deriv t)) (timeMeasure T) :=
      hDBm.prodMk (Lp.aestronglyMeasurable u.deriv)
    have hc := (coeffForce_cont (X := X)).comp_aestronglyMeasurable hp
    simpa only [Fc] using hc
  have hsq : _root_.MeasureTheory.Integrable (fun t ↦ ‖u.deriv t‖ ^ 2) (timeMeasure T) :=
    (_root_.MeasureTheory.memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u.deriv)).mp
      (Lp.memLp u.deriv)
  have hFc : _root_.MeasureTheory.Integrable Fc (timeMeasure T) := by
    refine Integrable.mono' (hsq.const_mul (D : ℝ)) hFcMeas ?_
    filter_upwards [hD] with t ht
    calc
      ‖Fc t‖ ≤ ‖DB t (u.toFun t)‖ * ‖u.deriv t‖ ^ 2 :=
        coeffForce_norm _ _
      _ ≤ (D : ℝ) * ‖u.deriv t‖ ^ 2 := by gcongr
  have huCont := u.continuousOn_toFun
  have hFpCont : ContinuousOn Fp (_root_.Set.Icc (0 : ℝ) T) := by
    apply hGcont.continuousOn.comp (continuousOn_id.prodMk huCont)
    exact Set.mapsTo_univ _ _
  have hFp : _root_.MeasureTheory.Integrable Fp (timeMeasure T) := by
    change _root_.MeasureTheory.IntegrableOn Fp (_root_.Set.Icc (0 : ℝ) T)
    exact hFpCont.integrableOn_Icc
  have hF : _root_.MeasureTheory.Integrable F (timeMeasure T) := hFc.add hFp
  change _root_.MeasureTheory.IntegrableOn F (_root_.Set.Icc (0 : ℝ) T) at hF
  refine ⟨by simpa only [F, Fc, Fp] using hF, ?_⟩
  intro v hv0 hvT
  let r : ℝ := scale v
  let w : timeH1 X T := r • v
  have hr : 0 < r := hscale v
  have hw0 : w.initial = 0 := by
    simp only [w, timeH1.initial_smul, hv0, smul_zero]
  have hwT : w.toFun T = 0 := by
    simp only [w]
    rw [timeH1.toFun_smul r v ⟨hT.le, le_rfl⟩, hvT, smul_zero]
  let line : ℝ → timeH1 X T := fun c ↦ u + c • w
  have hline0 : line 0 = u := by simp only [line, zero_smul, add_zero]
  have hmaps : _root_.Set.univ ⊆ line ⁻¹' sameTimeEnds u := by
    intro c _
    constructor
    · simp only [line, timeH1.initial_add, timeH1.initial_smul, hw0, smul_zero, add_zero]
    · change (u + c • w).toFun T = u.toFun T
      rw [timeH1.toFun_add u (c • w) ⟨hT.le, le_rfl⟩,
        timeH1.toFun_smul c w ⟨hT.le, le_rfl⟩, hwT, smul_zero, add_zero]
  have hscalar : IsLocalMin (timeCoeffPot B V ∘ line) 0 := by
    rw [← isLocalMinOn_univ_iff]
    have hmin' : IsLocalMinOn (timeCoeffPot B V) (sameTimeEnds u) (line 0) := by
      simpa only [hline0] using hmin
    exact hmin'.comp_continuousOn hmaps
      (continuous_const.add (continuous_id.smul continuous_const)).continuousOn
      (_root_.Set.mem_univ (0 : ℝ))
  have hint : IntervalIntegrable (coeffLineLag B u w 0) _root_.MeasureTheory.MeasureSpace.volume 0 T := by
    refine hactInt.congr ?_
    intro t _
    simp [coeffLineLag]
  have hcoeff := (timeCoeff_line_on hT.le B DB u w
    (by simpa only [w] using hB_on v)
    (by simpa only [w] using hself_on v)
    (lineBound v) (by simpa only [w] using hlineMeas v) hint
    (by simpa only [w] using hdlineMeas v)
    (by simpa only [w] using hlineDom v) (hlineInt v)).2
  have hpot := timeNlinPot_line hT.le V G hVcont hGcont hgrad u w
  have henergy : HasDerivAt (timeCoeffPot B V ∘ line)
      ((∫ t in (0 : ℝ)..T, coeffLineDeriv B DB u w 0 t) +
        ∫ t in (0 : ℝ)..T, _root_.Inner.inner ℝ (Fp t) (w.toFun t)) 0 := by
    rw [show timeCoeffPot B V ∘ line =
      ((fun c : ℝ => timeCoeffAction B (u + c • w)) +
        fun c : ℝ => timeNlinPot V (u + c • w)) by rfl]
    simpa only [Fp] using hcoeff.add hpot
  have hzero := hscalar.deriv_eq_zero
  rw [henergy.deriv] at hzero
  have hFpPair : IntervalIntegrable (fun t ↦ _root_.Inner.inner ℝ (Fp t) (w.toFun t))
      volume 0 T := by
    have hc : ContinuousOn (fun t ↦ _root_.Inner.inner ℝ (Fp t) (w.toFun t))
        (_root_.Set.uIcc (0 : ℝ) T) := by
      simpa only [_root_.Set.uIcc_of_le hT.le] using hFpCont.inner w.continuousOn_toFun
    exact hc.intervalIntegrable
  have hmomPair : IntervalIntegrable
      (fun t ↦ 2 * _root_.Inner.inner ℝ (A t (u.deriv t)) (w.deriv t)) _root_.MeasureTheory.MeasureSpace.volume 0 T := by
    have hmomTime : _root_.MeasureTheory.Integrable
        (fun t ↦ 2 * _root_.Inner.inner ℝ (A t (u.deriv t)) (w.deriv t))
        (timeMeasure T) := by
      refine ((L2.integrable_inner (timeOp A hA C hC u.deriv) w.deriv).const_mul 2).congr ?_
      filter_upwards [timeOp_apply_ae A hA C hC u.deriv] with t ht
      rw [ht]
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hT.le]
    change _root_.MeasureTheory.IntegrableOn
      (fun t ↦ 2 * _root_.Inner.inner ℝ (A t (u.deriv t)) (w.deriv t)) (_root_.Set.Icc (0 : ℝ) T)
      at hmomTime
    exact hmomTime
  have hFcPair : IntervalIntegrable (fun t ↦ _root_.Inner.inner ℝ (Fc t) (w.toFun t))
      volume 0 T := by
    have hd := (timeCoeff_line_on hT.le B DB u w
      (by simpa only [w] using hB_on v)
      (by simpa only [w] using hself_on v)
      (lineBound v) (by simpa only [w] using hlineMeas v) hint
      (by simpa only [w] using hdlineMeas v)
      (by simpa only [w] using hlineDom v) (hlineInt v)).1
    have hsum : IntervalIntegrable
        (fun t ↦ _root_.Inner.inner ℝ (Fc t) (w.toFun t) +
          2 * _root_.Inner.inner ℝ (A t (u.deriv t)) (w.deriv t)) _root_.MeasureTheory.MeasureSpace.volume 0 T := by
      refine hd.congr ?_
      intro t _
      simp [coeffLineDeriv, Fc, A]
    simpa only [add_sub_cancel_right] using hsum.sub hmomPair
  have hsplit :
      (∫ t in (0 : ℝ)..T, coeffLineDeriv B DB u w 0 t) =
        (∫ t in (0 : ℝ)..T, _root_.Inner.inner ℝ (Fc t) (w.toFun t)) +
          ∫ t in (0 : ℝ)..T,
            2 * _root_.Inner.inner ℝ (A t (u.deriv t)) (w.deriv t) := by
    rw [← intervalIntegral.integral_add hFcPair hmomPair]
    apply intervalIntegral.integral_congr
    intro t _
    simp only [coeffLineDeriv, Fc, A, zero_smul, add_zero]
  rw [hsplit] at hzero
  have hmom :
      2 * _root_.Inner.inner ℝ (timeOp A hA C hC u.deriv) w.deriv =
        ∫ t in (0 : ℝ)..T,
          2 * _root_.Inner.inner ℝ (A t (u.deriv t)) (w.deriv t) := by
    rw [L2.inner_def, intervalIntegral.integral_of_le hT.le,
      ← _root_.MeasureTheory.integral_Icc_eq_integral_Ioc, ← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [timeOp_apply_ae A hA C hC u.deriv] with t ht
    rw [ht]
  have hforceSplit :
      (∫ t in (0 : ℝ)..T, _root_.Inner.inner ℝ (F t) (w.toFun t)) =
        (∫ t in (0 : ℝ)..T, _root_.Inner.inner ℝ (Fc t) (w.toFun t)) +
          ∫ t in (0 : ℝ)..T, _root_.Inner.inner ℝ (Fp t) (w.toFun t) := by
    rw [← intervalIntegral.integral_add hFcPair hFpPair]
    apply intervalIntegral.integral_congr
    intro t _
    simp only [F, inner_add_left]
  have hscaled :
      2 * _root_.Inner.inner ℝ (timeOp A hA C hC u.deriv) w.deriv +
        ∫ t in _root_.Set.Icc (0 : ℝ) T, _root_.Inner.inner ℝ (F t) (w.toFun t) = 0 := by
    rw [hmom, _root_.MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hT.le, hforceSplit]
    linarith
  have hderivScale : w.deriv = r • v.deriv := by
    simp only [w, timeH1.deriv_smul]
  have hforceScale :
      (∫ t in _root_.Set.Icc (0 : ℝ) T, _root_.Inner.inner ℝ (F t) (w.toFun t)) =
        r * ∫ t in _root_.Set.Icc (0 : ℝ) T, _root_.Inner.inner ℝ (F t) (v.toFun t) := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [_root_.MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht
    simp only [w]
    rw [timeH1.toFun_smul r v ht]
    simp only [real_inner_smul_right]
  rw [hderivScale, real_inner_smul_right, hforceScale] at hscaled
  nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeCoeff_euler then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeCoeff_euler"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeCoeff_euler ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeCoeff_euler

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev

end
