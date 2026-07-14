/-
Copyright (c) 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Cubides

Adapted from PrimParser/GradedMonad/Basic.lean in prim-parser by Jan Mas
Rovira (https://github.com/janmasrovira/prim-parser, commit 4fb271f,
2026-05-03): the GradedFunctor/GradedApplicative/GradedMonad and LawfulGraded*
class hierarchy, with its field names, operators, and law statements. grip
omits the graded-alternative classes it does not use.
-/
import Mathlib.Algebra.Group.Defs

/-!
# Graded monads

Type classes for functors, applicatives, and monads indexed by a monoidal grade;
composition multiplies grades via the monoid operation. These are the classes the
`grip` core does not need (it uses the combinators directly); `grip-props` uses them to
state and prove the graded-monad laws for `GParser`.
-/

variable {G : Type} [Monoid G]

/-- A type family indexed by a grade and a result type. -/
abbrev GradedType (G : Type) := G → Type → Type

/-- Graded functor. -/
class GradedFunctor (f : GradedType G) : Type 1 where
  /-- Map a function over a graded value, preserving the grade. -/
  gmap {i α β} (h : α → β) : f i α → f i β

/-- Graded applicative. -/
class GradedApplicative (f : GradedType G) extends GradedFunctor f where
  /-- Inject a value at the unit grade. -/
  gpure {α} : α → f 1 α
  /-- Graded application; grades multiply. -/
  gseq {i j α β} : f i (α → β) → (Unit → f j α) → f (i * j) β

/-- Graded monad. -/
class GradedMonad (m : GradedType G) extends GradedApplicative m where
  /-- Graded bind; grades multiply. -/
  gbind {i j α β} : m i α → (α → m j β) → m (i * j) β

export GradedFunctor (gmap)
export GradedApplicative (gpure gseq)
export GradedMonad (gbind)

/-- Cast a graded value across an equality of grades. -/
def gcast {f : GradedType G} {i j : G} {α} (h : i = j) (x : f i α) : f j α := h ▸ x

/-- Replace the result of a graded computation with a constant. -/
abbrev gconst {f : GradedType G} [GradedFunctor f] {i α β} (b : β) (x : f i α) : f i β :=
  gmap (fun _ => b) x

@[inherit_doc] infixr:100 " <$>ᵍ " => gmap
@[inherit_doc] infixr:100 " <$ᵍ "  => gconst
@[inherit_doc] infixl:60  " <*>ᵍ " => gseq
@[inherit_doc] infixl:55  " >>=ᵍ " => gbind

/-- Laws of a graded functor. -/
class LawfulGradedFunctor (f : GradedType G) [GradedFunctor f] : Prop where
  gmap_id {i α} (x : f i α) : id <$>ᵍ x = x
  gmap_comp {i α β γ} (g : β → γ) (h : α → β) (x : f i α)
    : (g ∘ h) <$>ᵍ x = g <$>ᵍ (h <$>ᵍ x)

/-- Laws of a graded applicative. -/
class LawfulGradedApplicative (f : GradedType G) [GradedApplicative f] : Prop
    extends LawfulGradedFunctor f where
  gmap_gpure {α β} (g : α → β) (x : α) : g <$>ᵍ (gpure x : f 1 α) = gpure (g x)
  gpure_gseq {i α β} (g : α → β) (x : f i α) : (gpure g <*>ᵍ fun () => x) ≍ (g <$>ᵍ x)
  gseq_gpure {i α β} (u : f i (α → β)) (x : α) : (u <*>ᵍ fun () => gpure x) ≍ ((· x) <$>ᵍ u)
  gseq_assoc {i j k α β γ} (u : f i (β → γ)) (v : f j (α → β)) (w : f k α)
    : ((Function.comp <$>ᵍ u <*>ᵍ fun () => v) <*>ᵍ fun () => w)
     ≍ (u <*>ᵍ fun () => (v <*>ᵍ fun () => w))

/-- Laws of a graded monad. -/
class LawfulGradedMonad (m : GradedType G) [GradedMonad m] : Prop
    extends LawfulGradedApplicative m where
  gpure_gbind {j α β} (x : α) (f : α → m j β) : (gpure x >>=ᵍ f) ≍ f x
  gbind_gpure {i α} (x : m i α) : (x >>=ᵍ gpure) ≍ x
  gbind_assoc {i j k α β γ} (x : m i α) (f : α → m j β) (g : β → m k γ)
    : (x >>=ᵍ f >>=ᵍ g) ≍ (x >>=ᵍ fun a => f a >>=ᵍ g)
