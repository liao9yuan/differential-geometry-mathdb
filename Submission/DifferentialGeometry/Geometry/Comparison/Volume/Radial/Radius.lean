import Submission.DifferentialGeometry.Geometry.Comparison.Volume.Radial.JacobiScaling

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section

open _root_.Set
open scoped _root_.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace VolumeComparison

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.AlongCurve
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

section Radial

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
  [T2Space (TangentBundle I M)]

open _root_.Bundle _root_.Submission.Bundle in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
def Rm04DataAt
    (g : SmoothRiemannianMetric I M) (p : M) (r : ℝ) : Prop :=
  ∀ x w : E, ‖x‖ < r → ‖w‖ < r →
    ∀ {K R Vb b : ℝ}, 0 ≤ K → 0 ≤ Vb → b ≤ 1 →
    Real.sqrt (g.inner p x x) ≤ Vb →
    Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : ℝ)) *
        R * Vb ^ 2 ≤ K →
    (∀ t (_ht : t ∈ _root_.Set.Ioo (0 : ℝ) b),
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
        (radialCurve (I := I) g p x t) 4
        (DifferentialGeometry.Geometry.Curvature.metricRm04At
          (I := I) (M := M) g (radialCurve (I := I) g p x t))) ≤ R) →
    (∀ t ∈ _root_.Set.Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x w) t) t) ∧
    (∀ t ∈ _root_.Set.Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g
            (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) s) t) t) ∧
    ∀ t ∈ _root_.Set.Ico (0 : ℝ) b,
      g.inner (radialCurve (I := I) g p x t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g
            (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) s) t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g
            (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) s) t) ≤
      K ^ 2 * g.inner (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x w t)
        (radialJacobiField (I := I) g p x w t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.Rm04DataAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.VolumeComparison.Rm04DataAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.Rm04DataAt ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.Rm04DataAt

omit [NeZero (Module.finrank ℝ E)] [T2Space M]
  [SigmaCompactSpace M] in
lemma jacobi_radius_le_c2
    (g : SmoothRiemannianMetric I M) (p : M) :
    jacobiVarRadius (I := I) g p ≤ expMapC2Radius (I := I) g p := by
  rw [jacobiVarRadius]
  have hpos := expMapC2Radius_pos (I := I) g p
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.jacobi_radius_le_c2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.VolumeComparison.jacobi_radius_le_c2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.jacobi_radius_le_c2 ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.jacobi_radius_le_c2

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] in
private lemma jacobiRadius_lt_exp
    (g : SmoothRiemannianMetric I M) (p : M) {x : E}
    (hx : ‖x‖ < jacobiVarRadius (I := I) g p) :
    ‖x‖ < expMapC2Radius (I := I) g p :=
  hx.trans_le (jacobi_radius_le_c2 (I := I) g p)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.jacobiRadius_lt_exp
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.jacobiRadius_lt_exp target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem rm04Data_jacobi
    (g : SmoothRiemannianMetric I M)
    (p : M) :
    Rm04DataAt (I := I) g p (jacobiVarRadius (I := I) g p) := by
  classical
  intro x w hx hw K R Vb b hK hVb hb hlaunch hKbound hRm
  have hdiff := jacobi_diff_of_lt (I := I) g p hx hw hb
  refine ⟨?_, ?_, ?_⟩
  · exact hdiff.1
  · exact hdiff.2
  · have hJacobian : ∀ t ∈ _root_.Set.Ioo (0 : ℝ) b,
        IsJacobiAt (I := I) g (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x w) t := by
      intro t ht
      have ht01 : t ∈ _root_.Set.Ioo (0 : ℝ) 1 :=
        ⟨ht.1, lt_of_lt_of_le ht.2 hb⟩
      exact radial_jacobi_of_lt (I := I) g p hx hw t ht01
    have hJacobian0 :
        IsJacobiAt (I := I) g (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x w) 0 := by
      exact jacobi_zero_of_lt (I := I) g p hx hw
    have hxrad : ‖x‖ < expMapC2Radius (I := I) g p :=
      jacobiRadius_lt_exp (I := I) g p hx
    have hbasis :
        ∀ t : ℝ, t ∈ _root_.Set.Ioo (0 : ℝ) b →
          ∃ basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ
              (TangentSpace I (radialCurve (I := I) g p x t)),
            ∀ i j,
              g.inner (radialCurve (I := I) g p x t)
                  (basis i) (basis j) =
                if i = j then (1 : ℝ) else 0 := by
      intro t _ht
      have hfin : Module.finrank ℝ
          (TangentSpace I (radialCurve (I := I) g p x t)) =
            Module.finrank ℝ E := rfl
      rw [← hfin]
      exact DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis
        (I := I) g (radialCurve (I := I) g p x t)
    choose basis hON using hbasis
    have hcurv : ∀ t ∈ _root_.Set.Ioo (0 : ℝ) b,
        g.inner (radialCurve (I := I) g p x t)
            ((DifferentialGeometry.Geometry.Curvature.riemannOp
              (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g)
                (radialCurve (I := I) g p x t))
              (radialJacobiField (I := I) g p x w t)
              (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
              (curveVelocity (I := I) (radialCurve (I := I) g p x) t))
            ((DifferentialGeometry.Geometry.Curvature.riemannOp
              (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g)
                (radialCurve (I := I) g p x t))
              (radialJacobiField (I := I) g p x w t)
              (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
              (curveVelocity (I := I) (radialCurve (I := I) g p x) t)) ≤
          K ^ 2 * g.inner (radialCurve (I := I) g p x t)
            (radialJacobiField (I := I) g p x w t)
            (radialJacobiField (I := I) g p x w t) := by
      refine curv_sq_of_rm04_velocity_Ioo (I := I) g p x w hK hVb basis
        (fun t ht i j => hON t ht i j)
        (radial_speed_le (I := I) g p x hxrad hb hlaunch) ?_
      intro t ht
      set C : ℝ :=
        Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : ℝ))
      set A : ℝ := Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
        (radialCurve (I := I) g p x t) 4
        (DifferentialGeometry.Geometry.Curvature.metricRm04At
          (I := I) (M := M) g (radialCurve (I := I) g p x t)))
      have hCnn : 0 ≤ C := Real.sqrt_nonneg _
      have hVsq : 0 ≤ Vb ^ 2 := sq_nonneg Vb
      have hA_le_R : A ≤ R := hRm t ht
      have hmul : C * A * Vb ^ 2 ≤ C * R * Vb ^ 2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hA_le_R hCnn) hVsq
      exact hmul.trans hKbound
    exact ode_Ico_of_Ioo_d2 (I := I) g p x w hJacobian hcurv
      (d2_zero_of_jacobian0 (I := I) g p x w hJacobian0)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.rm04Data_jacobi then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.VolumeComparison.rm04Data_jacobi"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.rm04Data_jacobi ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.rm04Data_jacobi

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem rm04_one_le
    (g : SmoothRiemannianMetric I M)
    (p : M) (x w : E)
    {a K R Vb b A B : ℝ}
    (ha : 0 < a) (hK : 0 ≤ K) (hVb : 0 ≤ Vb)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (h1b : (1 : ℝ) ≤ b)
    (hx : ‖x‖ < jacobiVarRadius (I := I) g p)
    (hw : ‖a • w‖ < jacobiVarRadius (I := I) g p)
    (hlaunch : Real.sqrt (g.inner p x x) ≤ Vb)
    (hKbound :
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : ℝ)) *
          R * Vb ^ 2 ≤ K)
    (hRm : ∀ t (_ht : t ∈ _root_.Set.Ioo (0 : ℝ) b),
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
        (radialCurve (I := I) g p x t) 4
        (DifferentialGeometry.Geometry.Curvature.metricRm04At
          (I := I) (M := M) g (radialCurve (I := I) g p x t))) ≤ R)
    (hγ : ∀ t ∈ _root_.Set.Icc (0 : ℝ) b,
      ContMDiffAt 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p x) t)
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hcard : ∀ t : ℝ,
      Fintype.card ι =
        Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t)))
    (F : ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p x t))
    (hpar : ∀ i, ∀ t ∈ _root_.Set.Icc (0 : ℝ) b,
      covDerivAlong (I := I) g (radialCurve (I := I) g p x) (F i) t = 0)
    (hON : ∀ t ∈ _root_.Set.Icc (0 : ℝ) b, ∀ i j,
      g.inner (radialCurve (I := I) g p x t) (F i t) (F j t) =
        if i = j then (1 : ℝ) else 0)
    (hFdiff : ∀ i, ∀ t ∈ _root_.Set.Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x) (F i) t) t)
    (hinit : Real.sqrt (g.inner p (a • w) (a • w)) ≤ A)
    (hmodel :
      A + gronwallBound 0 (_root_.Max.max K 1) (K * (b * A)) 1 ≤ a * B) :
    Real.sqrt (g.inner
      (expMap (I := I) g p (show TangentSpace I p from x))
      (radialJacobiField (I := I) g p x w 1)
      (radialJacobiField (I := I) g p x w 1)) ≤ B := by
  have hdata := rm04Data_jacobi (I := I) g p
  obtain ⟨hJdiff, hDJdiff, hODE⟩ :=
    hdata x (a • w) hx hw hK hVb hb1 hlaunch hKbound hRm
  have hderiv : ∀ y z : E,
      ‖y‖ < jacobiVarRadius (I := I) g p →
      ‖z‖ < jacobiVarRadius (I := I) g p →
      (covDerivAlong (I := I) g
        (fun v : ℝ => (expMap (I := I) g p
          (show TangentSpace I p from (v • y)) : M))
        (radialJacobiField (I := I) g p y z) 0 : E) = z := by
    intro y z hy hz
    exact radial_deriv_of_lt (I := I) g p hy hz
  exact radialJacobi_one_le_of_scaled_radius_at (I := I) g p x w
    ha hK hb0 h1b hγ hcard F hpar hON hFdiff hJdiff hDJdiff hODE
    hderiv hx hw hinit hmodel (jacobiRadius_lt_exp (I := I) g p hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.rm04_one_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.VolumeComparison.rm04_one_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.rm04_one_le ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.rm04_one_le

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem rm04_one_ge
    (g : SmoothRiemannianMetric I M)
    (p : M) (x w : E)
    {a K R Vb b B : ℝ}
    (ha : 0 < a) (hK : 0 ≤ K) (hVb : 0 ≤ Vb)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (h1b : (1 : ℝ) ≤ b)
    (hx : ‖x‖ < jacobiVarRadius (I := I) g p)
    (hw : ‖a • w‖ < jacobiVarRadius (I := I) g p)
    (hlaunch : Real.sqrt (g.inner p x x) ≤ Vb)
    (hKbound :
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : ℝ)) *
          R * Vb ^ 2 ≤ K)
    (hRm : ∀ t (_ht : t ∈ _root_.Set.Ioo (0 : ℝ) b),
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
        (radialCurve (I := I) g p x t) 4
        (DifferentialGeometry.Geometry.Curvature.metricRm04At
          (I := I) (M := M) g (radialCurve (I := I) g p x t))) ≤ R)
    (hγ : ∀ t ∈ _root_.Set.Icc (0 : ℝ) b,
      ContMDiffAt 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p x) t)
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hcard : ∀ t : ℝ,
      Fintype.card ι =
        Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t)))
    (F : ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p x t))
    (hpar : ∀ i, ∀ t ∈ _root_.Set.Icc (0 : ℝ) b,
      covDerivAlong (I := I) g (radialCurve (I := I) g p x) (F i) t = 0)
    (hON : ∀ t ∈ _root_.Set.Icc (0 : ℝ) b, ∀ i j,
      g.inner (radialCurve (I := I) g p x t) (F i t) (F j t) =
        if i = j then (1 : ℝ) else 0)
    (hFdiff : ∀ i, ∀ t ∈ _root_.Set.Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x) (F i) t) t)
    (hmodel :
      a * B ≤ Real.sqrt (g.inner p (a • w) (a • w)) -
        gronwallBound 0 (_root_.Max.max K 1)
          (K * (b * Real.sqrt (g.inner p (a • w) (a • w)))) 1) :
    B ≤ Real.sqrt (g.inner
      (expMap (I := I) g p (show TangentSpace I p from x))
      (radialJacobiField (I := I) g p x w 1)
      (radialJacobiField (I := I) g p x w 1)) := by
  have hdata := rm04Data_jacobi (I := I) g p
  obtain ⟨hJdiff, hDJdiff, hODE⟩ :=
    hdata x (a • w) hx hw hK hVb hb1 hlaunch hKbound hRm
  have hderiv : ∀ y z : E,
      ‖y‖ < jacobiVarRadius (I := I) g p →
      ‖z‖ < jacobiVarRadius (I := I) g p →
      (covDerivAlong (I := I) g
        (fun v : ℝ => (expMap (I := I) g p
          (show TangentSpace I p from (v • y)) : M))
        (radialJacobiField (I := I) g p y z) 0 : E) = z := by
    intro y z hy hz
    exact radial_deriv_of_lt (I := I) g p hy hz
  exact radialJacobi_one_ge_of_scaled_radius_at (I := I) g p x w
    ha hK hb0 h1b hγ hcard F hpar hON hFdiff hJdiff hDJdiff hODE
    hderiv hx hw hmodel (jacobiRadius_lt_exp (I := I) g p hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.rm04_one_ge then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.VolumeComparison.rm04_one_ge"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.rm04_one_ge ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.rm04_one_ge

end Radial

end VolumeComparison
end Riemannian
end Geometry
end DifferentialGeometry
