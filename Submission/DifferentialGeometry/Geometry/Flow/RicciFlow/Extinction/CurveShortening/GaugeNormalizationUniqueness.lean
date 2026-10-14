import Submission.DifferentialGeometry.Analysis.ODE.TimeDependentFlow.AddCircleUniqueness
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.GaugeNormalization
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Reparametrization
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ParabolicGaugeLocalExistence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductSolutionLift

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Filter _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem normalizing_localLift_hasDerivWithinAt
    {c : CurveMap M} {g : ℝ → SmoothRiemannianMetric I M} {J : Set ℝ}
    {α : ℝ → ℝ → ℝ} (hc : c.IsGeometricSolutionOn g J α)
    (φ : CircleReparametrization J)
    (hnormal : CurveMap.IsSolutionOn (I := I) (fun z t => c (φ.map t z) t) g J)
    {x t : ℝ} (ht : t ∈ J) (hJ : UniqueDiffWithinAt ℝ J t)
    {l : ℝ × ℝ → ℝ} (hl : ContDiffWithinAt ℝ ∞ l (_root_.Set.univ ×ˢ J) (x, t))
    (hleq : ∀ᶠ p in 𝓝[_root_.Set.univ ×ˢ J] (x, t),
      (l p : AddCircle (1 : ℝ)) = φ.map p.2 (p.1 : AddCircle (1 : ℝ))) :
    HasDerivWithinAt (fun s => l (x, s))
      (-(α (l (x, t)) t) / c.speed g (l (x, t)) t) J t := by
  let d : CurveMap M := fun z t => c (φ.map t z) t
  have hspaceMaps : _root_.Set.MapsTo (fun y : ℝ => (y, t)) _root_.Set.univ (_root_.Set.univ ×ˢ J) :=
    fun _ _ => ⟨mem_univ _, ht⟩
  have hls : ContDiffAt ℝ ∞ (fun y => l (y, t)) x :=
    contDiffWithinAt_univ.mp (hl.comp x
      (contDiff_id.prodMk contDiff_const).contDiffWithinAt hspaceMaps)
  have hspace : ∀ᶠ y in 𝓝 x,
      (l (y, t) : AddCircle (1 : ℝ)) = φ.map t (y : AddCircle (1 : ℝ)) := by
    exact (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (continuous_id.prodMk continuous_const).continuousAt
      (Filter.Eventually.of_forall (fun _ => hspaceMaps trivial))).eventually hleq
  have htimeMaps : _root_.Set.MapsTo (fun s : ℝ => (x, s)) J (_root_.Set.univ ×ˢ J) :=
    fun _ hs => ⟨mem_univ _, hs⟩
  have htime : ∀ᶠ s in 𝓝[J] t,
      (l (x, s) : AddCircle (1 : ℝ)) = φ.map s (x : AddCircle (1 : ℝ)) :=
    ((continuous_const.prodMk continuous_id).continuousWithinAt.tendsto_nhdsWithin
      htimeMaps).eventually hleq
  have hlt : DifferentiableWithinAt ℝ (fun s => l (x, s)) J t :=
    (hl.comp t (contDiff_const.prodMk contDiff_id).contDiffWithinAt
      htimeMaps).differentiableWithinAt (by simp)
  have heqtime : (fun s : ℝ => d.lift x s) =ᶠ[𝓝[J] t]
      (fun s => c.lift (l (x, s)) s) := by
    filter_upwards [htime] with s hs
    exact congrArg (fun z => c z s) hs.symm
  have heqspace : (fun y : ℝ => d.lift y t) =ᶠ[𝓝 x]
      (fun y => c.lift (l (y, t)) t) := by
    filter_upwards [hspace] with y hy
    exact congrArg (fun z => c z t) hy.symm
  have hcurv := CurveMap.curvatureVector_reparam c d g heqspace hc.smooth hc.immersed ht
    (hls.of_le (by simp)) (φ.deriv_localLift_ne_zero ht hl hleq)
  have hv : d.velocity (I := I) J x t =
      derivWithin (fun s => l (x, s)) J t • c.X (I := I) (l (x, t)) t +
        c.velocity (I := I) J (l (x, t)) t := by
    change mfderivWithin 𝓘(ℝ, ℝ) I (fun s => d.lift x s) J t (1 : ℝ) = _
    have hdv := congrArg (fun A : ℝ →L[ℝ] E => A 1)
      (heqtime.mfderivWithin_eq_of_mem (I := 𝓘(ℝ, ℝ)) (I' := I) ht)
    exact hdv.trans (CurveMap.mfderivWithin_lift_comp_time hc.smooth ht hJ hlt)
  have hnormalEq := hnormal.equation x t ht
  change d.velocity (I := I) J x t = d.curvatureVector g x t at hnormalEq
  rw [hv, hcurv, hc.equation (l (x, t)) t ht] at hnormalEq
  have hzero :
      (derivWithin (fun s => l (x, s)) J t +
        α (l (x, t)) t / c.speed g (l (x, t)) t) •
          (c.X (I := I) (l (x, t)) t : E) = 0 := by
    rw [add_smul, div_eq_mul_inv, _root_.SemigroupAction.mul_smul]
    apply add_right_cancel (b := c.curvatureVector g (l (x, t)) t)
    rw [zero_add]
    calc
      _ = derivWithin (fun s => l (x, s)) J t • c.X (I := I) (l (x, t)) t +
          (c.curvatureVector g (l (x, t)) t +
            α (l (x, t)) t • c.unitTangent g (l (x, t)) t) := by
        simp only [CurveMap.unitTangent]
        abel
      _ = _ := hnormalEq
  have hscalar := (smul_eq_zero.mp hzero).resolve_right (hc.immersed _ _ ht)
  have hderiv : derivWithin (fun s => l (x, s)) J t =
      -(α (l (x, t)) t) / c.speed g (l (x, t)) t := by
    rw [neg_div]
    linarith
  rw [← hderiv]
  exact hlt.hasDerivWithinAt

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.normalizing_localLift_hasDerivWithinAt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.normalizing_localLift_hasDerivWithinAt target :: scope.openDecls } }

theorem CurveMap.IsGeometricSolutionOn.reparametrization_eqOn
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g)
    {a b : ℝ} (hJ : _root_.Set.Icc a b ⊆ D.regular)
    {c : CurveMap M} {α : ℝ → ℝ → ℝ}
    (hc : c.IsGeometricSolutionOn g (_root_.Set.Icc a b) α)
    (φ ψ : CircleReparametrization (_root_.Set.Icc a b))
    (hφ : CurveMap.IsSolutionOn (I := I) (fun z t => c (φ.map t z) t) g (_root_.Set.Icc a b))
    (hψ : CurveMap.IsSolutionOn (I := I) (fun z t => c (ψ.map t z) t) g (_root_.Set.Icc a b))
    (hstart : ∀ z, φ.map a z = ψ.map a z) : _root_.Set.EqOn φ.map ψ.map (_root_.Set.Icc a b) := by
  rcases lt_or_ge a b with hab | hba
  swap
  · intro t ht
    have hta : t = a := le_antisymm (ht.2.trans hba) ht.1
    subst t
    ext z
    exact hstart z
  let β : ℝ → ℝ → ℝ := fun t x => -(α x t / c.speed g x t)
  have hspeed := CurveMap.Field.smoothOn_speed g hG hJ c hc.smooth hc.immersed
  have hβraw : ContDiffOn ℝ ∞
      (fun p : ℝ × ℝ => -(α p.1 p.2 / c.speed g p.1 p.2))
      (_root_.Set.univ ×ˢ _root_.Set.Icc a b) :=
    (hc.tangentSmooth.div hspeed
      (fun p hp => (c.speed_pos g hc.immersed p.1 p.2 hp.2).ne')).neg
  have hβ : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => β p.1 p.2)
      (_root_.Set.Icc a b ×ˢ _root_.Set.univ) :=
    hβraw.comp (contDiff_snd.prodMk contDiff_fst).contDiffOn
      (fun p hp => ⟨hp.2, hp.1⟩)
  have hper : ∀ t ∈ _root_.Set.Icc a b, Function.Periodic (β t) 1 :=
    fun _ ht => hc.neg_tangent_div_speed_periodic ht
  have hdata (θ : CircleReparametrization (_root_.Set.Icc a b))
      (hθ : CurveMap.IsSolutionOn (I := I) (fun z t => c (θ.map t z) t) g (_root_.Set.Icc a b))
      (x : ℝ) : ∀ t ∈ _root_.Set.Icc a b, ∃ l : ℝ → ℝ,
        (fun s => (l s : AddCircle (1 : ℝ))) =ᶠ[𝓝[_root_.Set.Icc a b] t]
          (fun s => θ.map s (x : AddCircle (1 : ℝ))) ∧
        HasDerivWithinAt l (β t (l t)) (_root_.Set.Icc a b) t := by
    intro t ht
    obtain ⟨l, hl, hleq⟩ := θ.smooth x t ht
    refine ⟨fun s => l (x, s), ?_, ?_⟩
    · have hm : _root_.Set.MapsTo (fun s : ℝ => (x, s)) (_root_.Set.Icc a b) (_root_.Set.univ ×ˢ _root_.Set.Icc a b) :=
        fun _ hs => ⟨mem_univ _, hs⟩
      exact ((continuous_const.prodMk continuous_id).continuousWithinAt.tendsto_nhdsWithin
        hm).eventually hleq
    · simpa only [β, neg_div] using
        normalizing_localLift_hasDerivWithinAt hc θ hθ ht (uniqueDiffOn_Icc hab t ht) hl hleq
  intro t ht
  ext z
  obtain ⟨x, hx⟩ : ∃ x : ℝ, (x : AddCircle (1 : ℝ)) = z :=
    ⟨_, AddCircle.coe_equivIco (p := (1 : ℝ)) (a := (0 : ℝ))⟩
  rw [← hx]
  exact AddCircle.eqOn_of_periodic_ode hβ hper (hdata φ hφ x) (hdata ψ hψ x)
    (hstart (x : AddCircle (1 : ℝ))) ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.IsGeometricSolutionOn.reparametrization_eqOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.IsGeometricSolutionOn.reparametrization_eqOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.IsGeometricSolutionOn.reparametrization_eqOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.IsGeometricSolutionOn.reparametrization_eqOn

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end

noncomputable section

open _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem CurveMap.IsSolutionOn.eqOn_of_parabolic_reparametrizations
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g)
    {a b : ℝ} (hJD : _root_.Set.Icc a b ⊆ D.regular)
    {c₁ c₂ d : CurveMap M}
    (hc₁ : c₁.IsSolutionOn g (_root_.Set.Icc a b)) (hc₂ : c₂.IsSolutionOn g (_root_.Set.Icc a b))
    (hdequation : ∀ x t, t ∈ _root_.Set.Icc a b → d.velocity (I := I) (_root_.Set.Icc a b) x t =
      d.speed g x t ^ (-2 : ℤ) • d.Dx g d.X x t)
    (P Q : CircleReparametrization (_root_.Set.Icc a b))
    (hP : ∀ z t, t ∈ _root_.Set.Icc a b → d z t = c₁ (P.map t z) t)
    (hQ : ∀ z t, t ∈ _root_.Set.Icc a b → d z t = c₂ (Q.map t z) t)
    (hstart : P.map a = Q.map a) :
    ∀ z t, t ∈ _root_.Set.Icc a b → c₁ z t = c₂ z t := by
  have hPinverse (z : AddCircle (1 : ℝ)) (t : ℝ) (ht : t ∈ _root_.Set.Icc a b) :
      d (P.symm.map t z) t = c₁ z t := by
    rw [CircleReparametrization.symm_map, hP _ _ ht, Homeomorph.apply_symm_apply]
  have hQinverse (z : AddCircle (1 : ℝ)) (t : ℝ) (ht : t ∈ _root_.Set.Icc a b) :
      d (Q.symm.map t z) t = c₂ z t := by
    rw [CircleReparametrization.symm_map, hQ _ _ ht, Homeomorph.apply_symm_apply]
  rcases lt_or_ge a b with hab | hba
  swap
  · intro z t ht
    have hta : t = a := le_antisymm (ht.2.trans hba) ht.1
    subst t
    rw [← hPinverse z a ht, ← hQinverse z a ht]
    simp only [CircleReparametrization.symm_map, hstart]
  have hnormalP : CurveMap.IsSolutionOn (I := I)
      (fun z t => d (P.symm.map t z) t) g (_root_.Set.Icc a b) :=
    CurveMap.isSolutionOn_congr
      (fun x t ht => hPinverse (x : AddCircle (1 : ℝ)) t ht) hc₁
  have hnormalQ : CurveMap.IsSolutionOn (I := I)
      (fun z t => d (Q.symm.map t z) t) g (_root_.Set.Icc a b) :=
    CurveMap.isSolutionOn_congr
      (fun x t ht => hQinverse (x : AddCircle (1 : ℝ)) t ht) hc₂
  have hd : d.SmoothOn (I := I) (_root_.Set.Icc a b) :=
    (hc₁.smooth.reparam P).congr
      (fun p hp => hP (p.1 : AddCircle (1 : ℝ)) p.2 hp.2)
  have hdi : d.ImmersedOn (I := I) (_root_.Set.Icc a b) := by
    intro x t ht
    rw [CurveMap.X_congr (c := d) (d := fun z s => c₁ (P.map s z) s)
      (t := t) (fun y => hP (y : AddCircle (1 : ℝ)) t ht) x]
    exact (hc₁.immersed.reparam hc₁.smooth P) x t ht
  have hgeo := CurveMap.isGeometricSolutionOn_of_parabolicGauge hG
    (uniqueDiffOn_Icc hab) hJD hd hdi hdequation
  have hmaps := hgeo.reparametrization_eqOn hG hJD P.symm Q.symm hnormalP hnormalQ
    (fun z => by simp only [CircleReparametrization.symm_map, hstart])
  intro z t ht
  rw [← hPinverse z t ht, ← hQinverse z t ht, hmaps ht]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.IsSolutionOn.eqOn_of_parabolic_reparametrizations then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.IsSolutionOn.eqOn_of_parabolic_reparametrizations"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.IsSolutionOn.eqOn_of_parabolic_reparametrizations ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.IsSolutionOn.eqOn_of_parabolic_reparametrizations

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
