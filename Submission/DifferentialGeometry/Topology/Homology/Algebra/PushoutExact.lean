import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
open _root_.CategoryTheory _root_.CategoryTheory.Limits
noncomputable section
namespace DifferentialGeometry.ShortComplex
variable {C : Type*} [Category* C] [Abelian C]
  {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {r : X ⟶ Z} {s : Y ⟶ Z}
  (sq : IsPushout f g r s)


abbrev pushoutShortComplex : _root_.CategoryTheory.ShortComplex C :=
  ShortComplex.mk (biprod.lift f (-g)) (biprod.desc r s) (by
    rw [biprod.lift_desc, Preadditive.neg_comp, sq.w, add_neg_cancel])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.ShortComplex.pushoutShortComplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.ShortComplex.pushoutShortComplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.ShortComplex.pushoutShortComplex ``Submission.DifferentialGeometry.ShortComplex.pushoutShortComplex


def pushoutSumIsCokernel :
    IsColimit (CokernelCofork.ofπ (pushoutShortComplex sq).g (pushoutShortComplex sq).zero) :=
  Cofork.IsColimit.mk _
    (fun c => sq.desc (biprod.inl ≫ Cofork.π c) (biprod.inr ≫ Cofork.π c) <|
      sub_eq_zero.1 <| by
        rw [← Category.assoc, ← Category.assoc, ← Preadditive.sub_comp,
          sub_eq_add_neg, ← Preadditive.neg_comp, ← biprod.lift_eq, Cofork.condition c,
          _root_.CategoryTheory.Limits.zero_comp])
    (fun c => by apply biprod.hom_ext' <;> simp [pushoutShortComplex, sq.inl_desc, sq.inr_desc])
    (fun c m hm => by
      apply sq.hom_ext
      · have h := congrArg (fun φ => biprod.inl ≫ φ) hm
        simpa [pushoutShortComplex, sq.inl_desc] using h
      · have h := congrArg (fun φ => biprod.inr ≫ φ) hm
        simpa [pushoutShortComplex, sq.inr_desc] using h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.ShortComplex.pushoutSumIsCokernel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.ShortComplex.pushoutSumIsCokernel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.ShortComplex.pushoutSumIsCokernel ``Submission.DifferentialGeometry.ShortComplex.pushoutSumIsCokernel

theorem pushoutShortExact [_root_.CategoryTheory.Mono f] : (pushoutShortComplex sq).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (pushoutSumIsCokernel sq)
  mono_f := by
    exact _root_.CategoryTheory.mono_of_mono_fac (show (pushoutShortComplex sq).f ≫ biprod.fst = f from biprod.lift_fst _ _)
  epi_g := _root_.CategoryTheory.Limits.epi_of_isColimit_cofork (pushoutSumIsCokernel sq)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.ShortComplex.pushoutShortExact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.ShortComplex.pushoutShortExact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.ShortComplex.pushoutShortExact ``Submission.DifferentialGeometry.ShortComplex.pushoutShortExact

end DifferentialGeometry.ShortComplex
