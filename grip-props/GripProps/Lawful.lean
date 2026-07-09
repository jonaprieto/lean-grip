/-
Copyright (c) 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Cubides
-/
import Grip
import GripProps.GradedMonad

/-!
# `GParser` is a lawful graded monad

The `grip` byte core is a concrete `Type 0` graded type with a `run` function, so the
graded-monad laws hold directly by function extensionality. The grade is a phantom
index of the `run` function's type (`run` ignores it), which trivialises the `≍`
(cross-grade) laws; the witness fields are `Prop`s, equal by proof irrelevance.
-/

open Grip

namespace Grip.Grade

/-- `Necessity` join is associative. -/
private theorem max_assoc (a b c : Necessity) : max (max a b) c = max a (max b c) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- `Grade` is a monoid under sequential composition (`mul` = componentwise join,
`one` = `⟨never, never⟩`). Reuses the core `Mul`/`One` instances. -/
instance : Monoid Grade where
  mul := Grade.mul
  one := Grade.one
  mul_assoc a b c := by
    cases a with | mk e1 c1
    cases b with | mk e2 c2
    cases c with | mk e3 c3
    show Grade.mul (Grade.mul ⟨e1, c1⟩ ⟨e2, c2⟩) ⟨e3, c3⟩
       = Grade.mul ⟨e1, c1⟩ (Grade.mul ⟨e2, c2⟩ ⟨e3, c3⟩)
    simp only [Grade.mul, Grade.mk.injEq]
    exact ⟨max_assoc _ _ _, max_assoc _ _ _⟩
  one_mul a := by
    cases a with | mk e c
    show Grade.mul Grade.one ⟨e, c⟩ = ⟨e, c⟩
    simp [Grade.mul, Grade.one]
  mul_one a := by
    cases a with | mk e c
    show Grade.mul ⟨e, c⟩ Grade.one = ⟨e, c⟩
    simp [Grade.mul, Grade.one]

end Grip.Grade

namespace Grip.GParser

variable {g : Grade} {α β : Type}

/-- Two parsers are equal when their `run` functions are (the witnesses are proof-
irrelevant `Prop`s). -/
@[ext] theorem ext {x y : GParser g α} (h : x.run = y.run) : x = y := by
  cases x; cases y; subst h; rfl

/-- Transport a `run`-equality across a grade equality (the grade is phantom). -/
theorem heq_of_run {i j : Grade} {x : GParser i α} {y : GParser j α}
    (hg : i = j) (h : x.run = y.run) : x ≍ y := by subst hg; exact heq_of_eq (ext h)

instance : GradedFunctor GParser where
  gmap := GParser.map

instance : GradedApplicative GParser where
  gpure := GParser.pure
  gseq f x := GParser.bind f (fun h => GParser.map h (x ()))

instance : GradedMonad GParser where
  gbind := GParser.bind

instance : LawfulGradedFunctor GParser where
  gmap_id x := by apply ext; funext arr p; simp only [gmap, GParser.map]; cases x.run arr p <;> rfl
  gmap_comp g h x := by
    apply ext; funext arr p; simp only [gmap, GParser.map, Function.comp]
    cases x.run arr p <;> rfl

instance : LawfulGradedApplicative GParser where
  gmap_gpure g x := by apply ext; funext arr p; simp [gmap, GParser.map, gpure, GParser.pure]
  gpure_gseq g x := by
    apply heq_of_run (one_mul _); funext arr p
    simp [gseq, gmap, GParser.bind, GParser.map, gpure, GParser.pure]
  gseq_gpure u x := by
    apply heq_of_run (mul_one _); funext arr p
    simp only [gseq, gmap, GParser.bind, GParser.map, gpure, GParser.pure]
  gseq_assoc u v w := by
    apply heq_of_run (mul_assoc _ _ _); funext arr p
    simp only [gseq, gmap, GParser.bind, GParser.map]
    cases u.run arr p <;> simp
    cases v.run arr _ <;> simp
    cases w.run arr _ <;> rfl

instance : LawfulGradedMonad GParser where
  gpure_gbind x f := by
    apply heq_of_run (one_mul _); funext arr p; simp [gbind, GParser.bind, gpure, GParser.pure]
  gbind_gpure x := by
    apply heq_of_run (mul_one _); funext arr p
    simp only [gbind, GParser.bind, gpure, GParser.pure]
    cases x.run arr p <;> rfl
  gbind_assoc x f g := by
    apply heq_of_run (mul_assoc _ _ _); funext arr p
    simp only [gbind, GParser.bind]
    cases x.run arr p <;> rfl

end Grip.GParser
