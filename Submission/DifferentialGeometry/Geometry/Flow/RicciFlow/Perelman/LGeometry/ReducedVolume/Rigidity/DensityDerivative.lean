import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Rigidity.Equation
import Submission.DifferentialGeometry.Geometry.Operator.LaplacianExponential

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.Submission.Topology

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [ConnectedSpace M] {D : RealTimeInterval}

theorem redDensity_hasDerivAt_of_redVolume_eq_one
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (hg : RiemannianMetricComplete (S.base.metric T)) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → _root_.Set.Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ _root_.Set.Icc (T - sigma) T, ∀ z : M,
        normSq0S (S.base.metric t) z 4 (S.base.rm04 t z) ≤ K)
    {tau s : ℝ} (hs : 0 < s) (hstau : s < tau)
    (hslab : _root_.Set.Icc (T - tau) T ⊆ D.regular)
    (hvol : redVolume S T x tau = 1) {Z : E}
    (hZ : Z ∈ lInjDomain S T x s) :
    HasDerivAt (fun r => redDensity S T x (lExp S T x Z s) r)
      (laplacian (LeviCivita (S.base.metric (T - s))) (S.base.metric (T - s))
          (fun y => redDensity S T x y s) (lExp S T x Z s) -
        S.scalar (T - s) (lExp S T x Z s) *
          redDensity S T x (lExp S T x Z s) s) s := by
  let y := lExp S T x Z s
  let g := S.base.metric (T - s)
  let f := fun z : M => redLength S T x z s
  let n : ℝ := Module.finrank ℝ E
  let c : ℝ := -(n / 2) * Real.log s - (n / 2) * Real.log (4 * Real.pi)
  let phi : M → ℝ := fun z => c - f z
  let q : ℝ := g.inner y (gradientFun g f y) (gradientFun g f y)
  obtain ⟨U, hU, hyU, hfU⟩ := redLength_smooth_of_rm S hS T hg x hRm hs hZ
  have hf : ContMDiffAt I 𝓘(ℝ) ∞ f y :=
    (hfU y hyU).contMDiffAt (hU.mem_nhds hyU)
  have hphi : ContMDiffAt I 𝓘(ℝ) ∞ phi y := contMDiffAt_const.sub hf
  have hphiLap : laplacian (LeviCivita g) g phi y =
      -laplacian (LeviCivita g) g f y := by
    have h := laplacian_sub_at_of_contMDiffAt (LeviCivita g) g
      (f := fun _ : M => c) contMDiffAt_const hf
    simpa only [laplacian_const, zero_sub, phi] using h
  have hphiGrad : gradientFun g phi y = -gradientFun g f y := by
    have h := gradientFun_sub g (f := fun _ : M => c)
      mdifferentiableAt_const (hf.mdifferentiableAt (by simp))
    simpa only [gradientFun_const, zero_sub, phi] using h
  have heq : (fun z : M => redDensity S T x z s) =
      (fun z : M => Real.exp (phi z)) := by
    funext z
    apply congrArg Real.exp
    dsimp only [redDensity, phi, c, f, n]
    ring
  have hlap : laplacian (LeviCivita g) g (fun z => redDensity S T x z s) y =
      redDensity S T x y s * (-laplacian (LeviCivita g) g f y + q) := by
    rw [heq, laplacian_exp (LeviCivita g) g
      (hphi.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))), hphiLap,
      hphiGrad]
    simp only [map_neg, neg_apply, neg_neg]
    rw [← congrFun heq y]
  have hpde := redLength_conjugateHeat_of_redVolume_eq_one
    S hS T hg x hRm hs hstau hslab hvol hZ
  change deriv (fun r => redLength S T x y r) s -
    laplacian (LeviCivita g) g f y + q - S.scalar (T - s) y +
    n / (2 * s) = 0 at hpde
  have ht := (redLength_hasDeriv_of_rm S hS T hg x hRm hs hZ).differentiableAt.hasDerivAt
  have hd := ((ht.neg.sub ((Real.hasDerivAt_log hs.ne').const_mul (n / 2))).sub_const
    ((n / 2) * Real.log (4 * Real.pi))).exp
  change HasDerivAt (fun r => redDensity S T x y r)
    (redDensity S T x y s *
      (-deriv (fun r => redLength S T x y r) s - n / 2 * s⁻¹)) s at hd
  have hfrac : n / 2 * s⁻¹ = n / (2 * s) := by
    rw [← div_eq_mul_inv, div_div]
  have hcoef : -deriv (fun r => redLength S T x y r) s - n / 2 * s⁻¹ =
      -laplacian (LeviCivita g) g f y + q - S.scalar (T - s) y := by
    rw [hfrac]
    linarith only [hpde]
  apply hd.congr_deriv
  rw [hcoef, hlap]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.redDensity_hasDerivAt_of_redVolume_eq_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.redDensity_hasDerivAt_of_redVolume_eq_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.redDensity_hasDerivAt_of_redVolume_eq_one ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.redDensity_hasDerivAt_of_redVolume_eq_one

end DifferentialGeometry.PDE.RicciFlow.Perelman
