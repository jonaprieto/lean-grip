/-
Copyright (c) 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Cubides
-/
import GripProps.FixComplete
import GripProps.Json.Parse
import GripProps.Json.ScanStr

/-!
# Container round-trip lemmas

Infrastructure for the array and object cases of `parse_render`:
- `foldFwd_agree` – agreement of foldFwd under agreeing element parsers
- `value_body_guarded` – `Grip.Json.value_body` is `Guarded`
- `fixSelf_eq_value_of_gt` – `fixSelf value_body (arr.size - q)` at offsets `> q` agrees with `value`
- `value_run_at` – general embedding: `value` parses any occurrence of `render v` in a byte array
-/

open Grip Grip.Json Grip.Json.Json
open GripProps.Parse GripProps.ScanStr
open Grip.FixComplete

set_option maxHeartbeats 1600000

namespace GripProps.Container

-- ---------------------------------------------------------------------------
-- 1. foldFwd agreement
-- ---------------------------------------------------------------------------

/-- If two element parsers agree on every position reachable from `pos`, then
`foldFwd` gives the same result for both. -/
private theorem foldFwd_agree_bounded
    {ge : Modality} {α β : Type}
    (step : β → α → β) (p1 p2 : GParser ⟨ge, always⟩ α)
    (arr : ByteArray) :
    ∀ (n : Nat) (a : β) (pos : Nat),
      arr.size - pos ≤ n →
      (∀ r, pos ≤ r → AgreeOk (p1.run arr r) (p2.run arr r)) →
      foldFwd step p1 arr a pos = foldFwd step p2 arr a pos := by
  intro n
  induction n with
  | zero =>
    intro a pos hpos hagree
    unfold foldFwd
    cases hp1 : p1.run arr pos with
    | error e =>
      cases hp2 : p2.run arr pos with
      | error e2 => rfl
      | ok x2 q2 =>
        have := hagree pos le_rfl; simp only [AgreeOk, hp1, hp2] at this
    | ok x1 q1 =>
      cases hp2 : p2.run arr pos with
      | error e2 =>
        have := hagree pos le_rfl; simp only [AgreeOk, hp1, hp2] at this
      | ok x2 q2 =>
        have ha := hagree pos le_rfl
        simp only [AgreeOk, hp1, hp2] at ha
        obtain ⟨hx, hq⟩ := ha; subst hx; subst hq
        simp only [dif_neg (show ¬ (pos < q1 ∧ q1 ≤ arr.size) from by
          have := p1.cwit hp1; omega)]
  | succ n ih =>
    intro a pos hn hagree
    unfold foldFwd
    cases hp1 : p1.run arr pos with
    | error e =>
      cases hp2 : p2.run arr pos with
      | error e2 => rfl
      | ok x2 q2 =>
        have := hagree pos le_rfl; simp only [AgreeOk, hp1, hp2] at this
    | ok x1 q1 =>
      cases hp2 : p2.run arr pos with
      | error e2 =>
        have := hagree pos le_rfl; simp only [AgreeOk, hp1, hp2] at this
      | ok x2 q2 =>
        have ha := hagree pos le_rfl
        simp only [AgreeOk, hp1, hp2] at ha
        obtain ⟨hx, hq⟩ := ha; subst hx; subst hq
        by_cases hc : pos < q1 ∧ q1 ≤ arr.size
        · simp only [dif_pos hc]
          apply ih (step a x1) q1
          · have := p1.cwit hp1; omega
          · intro r hr; exact hagree r (le_trans (le_of_lt hc.1) hr)
        · simp only [dif_neg hc]

theorem foldFwd_agree
    {ge : Modality} {α β : Type}
    (step : β → α → β) (p1 p2 : GParser ⟨ge, always⟩ α)
    (arr : ByteArray) (a : β) (pos : Nat)
    (hagree : ∀ r, pos ≤ r → AgreeOk (p1.run arr r) (p2.run arr r)) :
    foldFwd step p1 arr a pos = foldFwd step p2 arr a pos :=
  foldFwd_agree_bounded step p1 p2 arr (arr.size - pos) a pos le_rfl hagree

-- ---------------------------------------------------------------------------
-- 2. Guarded value_body
-- ---------------------------------------------------------------------------

-- Helper: seqR comma s1 agrees with seqR comma s2 at r > q
private theorem seqR_comma_agree (s1 s2 : GParser conditional Json)
    (arr : ByteArray) (q r : Nat) (hr : q < r)
    (hpre : ∀ q', q < q' → AgreeOk (s1.run arr q') (s2.run arr q')) :
    AgreeOk ((GParser.seqR (Grip.Json.wsByte Ascii.comma) s1).run arr r)
            ((GParser.seqR (Grip.Json.wsByte Ascii.comma) s2).run arr r) := by
  simp only [GParser.seqR]
  rcases hcomma : (Grip.Json.wsByte Ascii.comma).run arr r with ⟨_, r'⟩ | _
  · exact hpre r' (lt_trans hr ((Grip.Json.wsByte Ascii.comma).cwit hcomma))
  · exact True.intro

-- Helper: arrayBody si at pos agrees
private theorem arrayBody_agree (s1 s2 : GParser conditional Json)
    (arr : ByteArray) (q : Nat)
    (hpre : ∀ q', q < q' → AgreeOk (s1.run arr q') (s2.run arr q'))
    (pos : Nat) (hpos : q < pos) :
    AgreeOk
      ((GParser.alt
          (GParser.bind s1 (fun x => GParser.foldMany (fun (a : Array Json) e => a.push e) #[x]
              (GParser.seqR (Grip.Json.wsByte Ascii.comma) s1)))
          (GParser.pure #[])).run arr pos)
      ((GParser.alt
          (GParser.bind s2 (fun x => GParser.foldMany (fun (a : Array Json) e => a.push e) #[x]
              (GParser.seqR (Grip.Json.wsByte Ascii.comma) s2)))
          (GParser.pure #[])).run arr pos) := by
  have hs := hpre pos hpos
  simp only [GParser.alt, GParser.bind, GParser.pure]
  rcases hs1 : s1.run arr pos with ⟨x1, q1⟩ | _ <;> rcases hs2 : s2.run arr pos with ⟨x2, q2⟩ | _
  · -- ok-ok
    rw [hs1, hs2] at hs; simp only [AgreeOk] at hs; obtain ⟨hx, hq⟩ := hs; subst hx; subst hq
    have hq1_gt : q < q1 := lt_trans hpos (s1.cwit hs1)
    simp only [GParser.foldMany]
    rw [foldFwd_agree (fun a e => a.push e)
        (GParser.seqR (Grip.Json.wsByte Ascii.comma) s1)
        (GParser.seqR (Grip.Json.wsByte Ascii.comma) s2)
        arr #[x1] q1
        (fun r hr_q1 => seqR_comma_agree s1 s2 arr q r (lt_of_lt_of_le hq1_gt hr_q1) hpre)]
    exact AgreeOk.refl _
  · -- ok-error: contradiction
    rw [hs1, hs2] at hs; simp [AgreeOk] at hs
  · -- error-ok: contradiction
    rw [hs1, hs2] at hs; simp [AgreeOk] at hs
  · -- error-error: both pure #[]
    exact AgreeOk.refl _

-- Helper: pair si at pos agrees
private theorem pair_agree (s1 s2 : GParser conditional Json)
    (arr : ByteArray) (q pos : Nat) (hpos : q < pos)
    (hpre : ∀ q', q < q' → AgreeOk (s1.run arr q') (s2.run arr q')) :
    AgreeOk
      ((GParser.map2 (fun k v => (k, v)) Grip.Json.jstr
          (GParser.seqR (Grip.Json.wsByte Ascii.colon) s1)).run arr pos)
      ((GParser.map2 (fun k v => (k, v)) Grip.Json.jstr
          (GParser.seqR (Grip.Json.wsByte Ascii.colon) s2)).run arr pos) := by
  simp only [GParser.map2, GParser.seqR]
  cases hjstr : Grip.Json.jstr.run arr pos with
  | error _ => exact AgreeOk.refl _
  | ok k qk =>
    dsimp only
    have hqk : pos < qk := Grip.Json.jstr.cwit hjstr
    cases hcolon : (Grip.Json.wsByte Ascii.colon).run arr qk with
    | error _ => exact AgreeOk.refl _
    | ok _ qc =>
      dsimp only
      have hqc_q : q < qc := lt_trans hpos (lt_trans hqk ((Grip.Json.wsByte Ascii.colon).cwit hcolon))
      have ha := hpre qc hqc_q
      cases hv1 : s1.run arr qc with
      | error e1 =>
        cases hv2 : s2.run arr qc with
        | error _ => dsimp only; trivial
        | ok v2 qv2 => rw [hv1, hv2] at ha; simp [AgreeOk] at ha
      | ok v1 qv1 =>
        cases hv2 : s2.run arr qc with
        | error _ => rw [hv1, hv2] at ha; simp [AgreeOk] at ha
        | ok v2 qv2 =>
          dsimp only
          rw [hv1, hv2] at ha; simp only [AgreeOk] at ha
          obtain ⟨hv, hq⟩ := ha; subst hv; subst hq
          exact AgreeOk.refl _

-- Helper: seqR comma (seqR ws (pair si)) at r ≥ qp1 > q agrees
private theorem seqR_comma_ws_pair_agree (s1 s2 : GParser conditional Json)
    (arr : ByteArray) (q qp1 r : Nat) (hqp1 : q < qp1) (hr : qp1 ≤ r)
    (hpre : ∀ q', q < q' → AgreeOk (s1.run arr q') (s2.run arr q')) :
    AgreeOk
      ((GParser.seqR (Grip.Json.wsByte Ascii.comma)
          (GParser.seqR GParser.ws
            (GParser.map2 (fun k v => (k, v)) Grip.Json.jstr
              (GParser.seqR (Grip.Json.wsByte Ascii.colon) s1)))).run arr r)
      ((GParser.seqR (Grip.Json.wsByte Ascii.comma)
          (GParser.seqR GParser.ws
            (GParser.map2 (fun k v => (k, v)) Grip.Json.jstr
              (GParser.seqR (Grip.Json.wsByte Ascii.colon) s2)))).run arr r) := by
  simp only [GParser.seqR, GParser.map2]
  cases hcomma : (Grip.Json.wsByte Ascii.comma).run arr r with
  | error _ => exact AgreeOk.refl _
  | ok _ rc =>
    dsimp only
    have hrc_q : q < rc := lt_trans (lt_of_lt_of_le hqp1 hr)
        ((Grip.Json.wsByte Ascii.comma).cwit hcomma)
    cases hws : GParser.ws.run arr rc with
    | error _ => exact AgreeOk.refl _
    | ok _ rw =>
      dsimp only
      have hrw_q : q < rw := lt_of_lt_of_le hrc_q (GParser.ws.cwit hws)
      exact pair_agree s1 s2 arr q rw hrw_q hpre

-- Helper: objectBody si at pos agrees
private theorem objectBody_agree (s1 s2 : GParser conditional Json)
    (arr : ByteArray) (q pos : Nat) (hpos : q < pos)
    (hpre : ∀ q', q < q' → AgreeOk (s1.run arr q') (s2.run arr q')) :
    AgreeOk
      ((GParser.alt
          (GParser.bind
            (GParser.map2 (fun k v => (k, v)) Grip.Json.jstr
                (GParser.seqR (Grip.Json.wsByte Ascii.colon) s1))
            (fun p => GParser.foldMany (fun (a : Array (String × Json)) x => a.push x) #[p]
              (GParser.seqR (Grip.Json.wsByte Ascii.comma)
                (GParser.seqR GParser.ws
                  (GParser.map2 (fun k v => (k, v)) Grip.Json.jstr
                    (GParser.seqR (Grip.Json.wsByte Ascii.colon) s1))))))
          (GParser.pure #[])).run arr pos)
      ((GParser.alt
          (GParser.bind
            (GParser.map2 (fun k v => (k, v)) Grip.Json.jstr
                (GParser.seqR (Grip.Json.wsByte Ascii.colon) s2))
            (fun p => GParser.foldMany (fun (a : Array (String × Json)) x => a.push x) #[p]
              (GParser.seqR (Grip.Json.wsByte Ascii.comma)
                (GParser.seqR GParser.ws
                  (GParser.map2 (fun k v => (k, v)) Grip.Json.jstr
                    (GParser.seqR (Grip.Json.wsByte Ascii.colon) s2))))))
          (GParser.pure #[])).run arr pos) := by
  have hp := pair_agree s1 s2 arr q pos hpos hpre
  simp only [GParser.alt, GParser.bind, GParser.pure, GParser.foldMany]
  rcases hp1 : (GParser.map2 (fun k v => (k, v)) Grip.Json.jstr
      (GParser.seqR (Grip.Json.wsByte Ascii.colon) s1)).run arr pos with ⟨kv1, qp1⟩ | _
    <;> rcases hp2 : (GParser.map2 (fun k v => (k, v)) Grip.Json.jstr
      (GParser.seqR (Grip.Json.wsByte Ascii.colon) s2)).run arr pos with ⟨kv2, qp2⟩ | _
  · -- ok-ok
    rw [hp1, hp2] at hp; simp only [AgreeOk] at hp; obtain ⟨hkv, hqp⟩ := hp; subst hkv; subst hqp
    have hqp1 : q < qp1 := lt_trans hpos
        ((GParser.map2 (fun k v => (k, v)) Grip.Json.jstr
          (GParser.seqR (Grip.Json.wsByte Ascii.colon) s1)).cwit hp1)
    dsimp only
    rw [foldFwd_agree (fun a x => a.push x)
        (GParser.seqR (Grip.Json.wsByte Ascii.comma)
          (GParser.seqR GParser.ws
            (GParser.map2 (fun k v => (k, v)) Grip.Json.jstr
              (GParser.seqR (Grip.Json.wsByte Ascii.colon) s1))))
        (GParser.seqR (Grip.Json.wsByte Ascii.comma)
          (GParser.seqR GParser.ws
            (GParser.map2 (fun k v => (k, v)) Grip.Json.jstr
              (GParser.seqR (Grip.Json.wsByte Ascii.colon) s2))))
        arr #[kv1] qp1
        (fun r hr => seqR_comma_ws_pair_agree s1 s2 arr q qp1 r hqp1 hr hpre)]
    exact AgreeOk.refl _
  · -- ok-error: contradiction
    rw [hp1, hp2] at hp; simp [AgreeOk] at hp
  · -- error-ok: contradiction
    rw [hp1, hp2] at hp; simp [AgreeOk] at hp
  · -- error-error: both pure #[]
    exact AgreeOk.refl _

/-- `value_body` is Guarded. -/
theorem value_body_guarded : Guarded Grip.Json.value_body := by
  intro s1 s2 arr q hpre
  simp only [Grip.Json.value_body, Grip.Json.wsDispatch]
  have hpq : q ≤ scanFwd arr Ascii.isWs q := scanFwd_ge arr Ascii.isWs q
  set p := scanFwd arr Ascii.isWs q
  by_cases hplt : p < arr.size
  · simp only [hplt]
    by_cases hbrace : arr[p] == Ascii.lbrace
    · simp only [hbrace, ↓reduceIte]
      -- Set ob1/ob2 before unfolding seqR/seqL/map so they stay opaque in the goal simp.
      set ob1 := GParser.alt
          (GParser.bind
            (GParser.map2 (fun k v => (k, v)) Grip.Json.jstr
              (GParser.seqR (Grip.Json.wsByte Ascii.colon) s1))
            (fun kp => GParser.foldMany (fun a x => a.push x) #[kp]
              (GParser.seqR (Grip.Json.wsByte Ascii.comma)
                (GParser.seqR GParser.ws
                  (GParser.map2 (fun k v => (k, v)) Grip.Json.jstr
                    (GParser.seqR (Grip.Json.wsByte Ascii.colon) s1))))))
          (GParser.pure #[])
      set ob2 := GParser.alt
          (GParser.bind
            (GParser.map2 (fun k v => (k, v)) Grip.Json.jstr
              (GParser.seqR (Grip.Json.wsByte Ascii.colon) s2))
            (fun kp => GParser.foldMany (fun a x => a.push x) #[kp]
              (GParser.seqR (Grip.Json.wsByte Ascii.comma)
                (GParser.seqR GParser.ws
                  (GParser.map2 (fun k v => (k, v)) Grip.Json.jstr
                    (GParser.seqR (Grip.Json.wsByte Ascii.colon) s2))))))
          (GParser.pure #[])
      simp only [GParser.seqR, GParser.seqL, GParser.map]
      cases hch : (GParser.ch '{').run arr p with
      | error _ => exact AgreeOk.refl _
      | ok _ p1 =>
        dsimp only
        have hp1 : p < p1 := (GParser.ch '{').cwit hch
        cases hws : GParser.ws.run arr p1 with
        | error _ => exact AgreeOk.refl _
        | ok _ p2 =>
          dsimp only
          have hp2 : p1 ≤ p2 := GParser.ws.cwit hws
          have hp2q : q < p2 := Nat.lt_of_le_of_lt hpq (Nat.lt_of_lt_of_le hp1 hp2)
          have hob := objectBody_agree s1 s2 arr q p2 hp2q hpre
          change AgreeOk (ob1.run arr p2) (ob2.run arr p2) at hob
          cases h1 : ob1.run arr p2 with
          | error e1 =>
            dsimp only
            cases h2 : ob2.run arr p2 with
            | error _ => dsimp only; trivial
            | ok xs2 q2 => rw [h1, h2] at hob; simp [AgreeOk] at hob
          | ok xs1 q1 =>
            dsimp only
            cases h2 : ob2.run arr p2 with
            | error _ => rw [h1, h2] at hob; simp [AgreeOk] at hob
            | ok xs2 q2 =>
              dsimp only
              rw [h1, h2] at hob; simp only [AgreeOk] at hob
              obtain ⟨hxs, hq⟩ := hob; subst hxs; subst hq
              exact AgreeOk.refl _
    · by_cases hbracket : arr[p] == Ascii.lbracket
      · simp only [hbrace, Bool.false_eq_true, ↓reduceIte, hbracket, ↓reduceIte]
        set ab1 := GParser.alt
            (GParser.bind s1 (fun x =>
              GParser.foldMany (fun (a : Array Json) e => a.push e) #[x]
                (GParser.seqR (Grip.Json.wsByte Ascii.comma) s1)))
            (GParser.pure #[])
        set ab2 := GParser.alt
            (GParser.bind s2 (fun x =>
              GParser.foldMany (fun (a : Array Json) e => a.push e) #[x]
                (GParser.seqR (Grip.Json.wsByte Ascii.comma) s2)))
            (GParser.pure #[])
        simp only [GParser.seqR, GParser.seqL, GParser.map]
        cases hch : (GParser.ch '[').run arr p with
        | error _ => exact AgreeOk.refl _
        | ok _ p1 =>
          dsimp only
          have hp1 : p < p1 := (GParser.ch '[').cwit hch
          have hp1q : q < p1 := Nat.lt_of_le_of_lt hpq hp1
          have hab := arrayBody_agree s1 s2 arr q hpre p1 hp1q
          change AgreeOk (ab1.run arr p1) (ab2.run arr p1) at hab
          cases h1 : ab1.run arr p1 with
          | error e1 =>
            dsimp only
            cases h2 : ab2.run arr p1 with
            | error _ => dsimp only; trivial
            | ok xs2 q2 => rw [h1, h2] at hab; simp [AgreeOk] at hab
          | ok xs1 q1 =>
            dsimp only
            cases h2 : ab2.run arr p1 with
            | error _ => rw [h1, h2] at hab; simp [AgreeOk] at hab
            | ok xs2 q2 =>
              dsimp only
              rw [h1, h2] at hab; simp only [AgreeOk] at hab
              obtain ⟨hxs, hq⟩ := hab; subst hxs; subst hq
              exact AgreeOk.refl _
      · simp only [hbrace, Bool.false_eq_true, ↓reduceIte, hbracket, Bool.false_eq_true, ↓reduceIte]
        exact AgreeOk.refl _
  · simp only [show ¬ p < arr.size from hplt]
    exact True.intro

-- ---------------------------------------------------------------------------
-- 3. fixSelf agrees with value at positions > q
-- ---------------------------------------------------------------------------

/-- At positions `q' > q`, `fixSelf value_body (arr.size - q)` agrees with `value`. -/
theorem fixSelf_eq_value_of_gt (arr : ByteArray) (q q' : Nat) (hqq' : q < q') :
    AgreeOk ((GParser.fixSelf Grip.Json.value_body (arr.size - q)).run arr q')
            (Grip.Json.value.run arr q') := by
  simp only [GParser.fixSelf_run, Grip.Json.value, GParser.fix]
  by_cases hq'le : q' ≤ arr.size
  · apply clamp_agree
    have hag := agree_add Grip.Json.value_body value_body_guarded arr q' (q' - q - 1)
    rwa [show arr.size - q' + 1 + (q' - q - 1) = arr.size - q from by omega] at hag
  · exact clamp_oob arr q' (by omega)

-- ---------------------------------------------------------------------------
-- 4. Structural byte facts for render (.str s)
-- ---------------------------------------------------------------------------

private theorem render_str_size (s : String) :
    (render (.str s)).toUTF8.size = 2 + (ebytes s.toList).length := by
  simp only [render, String.toUTF8_eq_toByteArray, String.toByteArray_append, ByteArray.size_append]
  have hqs : ("\"" : String).toByteArray.size = 1 := by decide
  have hes : (escape s).toByteArray.size = (ebytes s.toList).length := escape_toUTF8_size s
  omega

private theorem render_str_byte0 (s : String) :
    (render (.str s)).toUTF8[0]! = 34 := by
  simp only [render, String.toUTF8_eq_toByteArray, String.toByteArray_append]
  have hqs : ("\"" : String).toByteArray.size = 1 := by decide
  have hes : (escape s).toByteArray.size = (ebytes s.toList).length := escape_toUTF8_size s
  rw [ba_get!_append_left (by rw [ByteArray.size_append]; omega)]
  rw [ba_get!_append_left (by omega)]
  decide

private theorem render_str_byte_mid (s : String) (j : Nat)
    (hj : j < (ebytes s.toList).length) :
    (render (.str s)).toUTF8[1 + j]! = (ebytes s.toList)[j]! := by
  simp only [render, String.toUTF8_eq_toByteArray, String.toByteArray_append]
  have hqs : ("\"" : String).toByteArray.size = 1 := by decide
  have hes : (escape s).toByteArray.size = (ebytes s.toList).length := escape_toUTF8_size s
  rw [ba_get!_append_left (by rw [ByteArray.size_append]; omega)]
  rw [ba_get!_append_right (by omega) (by rw [ByteArray.size_append]; omega)]
  simp only [show 1 + j - ("\"" : String).toByteArray.size = j from by omega]
  exact escape_toUTF8_getElem! s j (hes ▸ hj)

private theorem render_str_byte_close (s : String) :
    (render (.str s)).toUTF8[1 + (ebytes s.toList).length]! = 34 := by
  simp only [render, String.toUTF8_eq_toByteArray, String.toByteArray_append]
  have hqs : ("\"" : String).toByteArray.size = 1 := by decide
  have hes : (escape s).toByteArray.size = (ebytes s.toList).length := escape_toUTF8_size s
  have hmid : ("\"" : String).toByteArray.size + (escape s).toByteArray.size =
      1 + (ebytes s.toList).length := by omega
  rw [ba_get!_append_right (by rw [ByteArray.size_append, hqs, hes])
    (by rw [ByteArray.size_append, ByteArray.size_append, hqs, hes]; omega)]
  simp only [ByteArray.size_append, hqs, hes, Nat.sub_self]
  decide

-- ---------------------------------------------------------------------------
-- 5. Helper byte-position lemmas for array/object round-trips
-- ---------------------------------------------------------------------------

private theorem str_app (s t : String) : (s ++ t).toUTF8 = s.toUTF8 ++ t.toUTF8 := by
  simp [String.toUTF8_eq_toByteArray, String.toByteArray_append]

private theorem lbracket_last_byte (body : String) :
    ("[" ++ body ++ "]").toUTF8[("[" ++ body ++ "]").toUTF8.size - 1]! = 93 := by
  have h1 : ("]" : String).toUTF8.size = 1 := by decide
  rw [str_app, ByteArray.size_append, h1,
      ba_get!_append_right (by omega) (by rw [ByteArray.size_append, h1]; omega)]
  simp only [show ("[" ++ body).toUTF8.size + 1 - 1 - ("[" ++ body).toUTF8.size = 0 from by omega]
  decide

private theorem lbrace_last_byte (body : String) :
    ("{" ++ body ++ "}").toUTF8[("{" ++ body ++ "}").toUTF8.size - 1]! = 125 := by
  have h1 : ("}" : String).toUTF8.size = 1 := by decide
  rw [str_app, ByteArray.size_append, h1,
      ba_get!_append_right (by omega) (by rw [ByteArray.size_append, h1]; omega)]
  simp only [show ("{" ++ body).toUTF8.size + 1 - 1 - ("{" ++ body).toUTF8.size = 0 from by omega]
  decide

-- First byte of "\""-prefixed string's UTF8 is 34
private theorem str_prepend_byte0 (s : String) : ("\"" ++ s).toUTF8[0]! = 34 := by
  rw [str_app, ba_get!_append_left (by decide)]
  decide

-- Byte 1+j of "o"++body++"c" equals body[j] when |o|=1
private theorem body_byte_j (open_b close_b : String) (ho : open_b.toUTF8.size = 1) (body : String)
    (j : Nat) (hj : j < body.toUTF8.size) :
    (open_b ++ body ++ close_b).toUTF8[1 + j]! = body.toUTF8[j]! := by
  rw [str_app, ba_get!_append_left (by rw [str_app, ByteArray.size_append, ho]; omega),
      str_app, ba_get!_append_right (by omega) (by rw [ByteArray.size_append]; omega)]
  simp only [show 1 + j - open_b.toUTF8.size = j from by omega]

-- Byte rv.size+1+j of (rv++","++rest) equals rest[j]
private theorem str_tail_byte (rv rest : String) (j : Nat) (hj : j < rest.toUTF8.size) :
    (rv ++ "," ++ rest).toUTF8[rv.toUTF8.size + 1 + j]! = rest.toUTF8[j]! := by
  have hcs : (",": String).toUTF8.size = 1 := by decide
  rw [String.append_assoc, str_app,
      ba_get!_append_right (by omega) (by
        rw [ByteArray.size_append, str_app, ByteArray.size_append, hcs]; omega)]
  simp only [show rv.toUTF8.size + 1 + j - rv.toUTF8.size = 1 + j from by omega]
  rw [str_app, ba_get!_append_right (by omega) (by rw [ByteArray.size_append, hcs]; omega)]
  simp only [show 1 + j - (",": String).toUTF8.size = j from by omega]

-- Byte j of joinWith "," (v::rest) equals (render v)[j] for j < render v size
private theorem jw_head_byte (v : Json) (rest : List Json) (j : Nat)
    (hj : j < (render v).toUTF8.size) :
    (joinWith "," ((v :: rest).map render)).toUTF8[j]! = (render v).toUTF8[j]! := by
  cases rest with
  | nil => simp [joinWith]
  | cons w more =>
    simp only [List.map_cons, joinWith]
    rw [String.append_assoc, str_app, ba_get!_append_left hj]

-- Byte render(v).size of joinWith "," (v::w::more) is comma (44)
private theorem jw_comma_byte (v w : Json) (more : List Json) :
    (joinWith "," ((v :: w :: more).map render)).toUTF8[(render v).toUTF8.size]! = 44 := by
  simp only [List.map_cons, joinWith]
  rw [String.append_assoc, str_app,
      ba_get!_append_right (by rfl) (by
        rw [ByteArray.size_append, str_app, ByteArray.size_append]
        have hcs : (",": String).toUTF8.size = 1 := by decide
        omega)]
  simp only [Nat.sub_self]
  rw [str_app, ba_get!_append_left (by decide)]
  decide

-- First byte of joinWith "," over kv entries is 34 ('"')
private theorem jw_kv_first_byte (k0 : String) (j0 : Json) (L : List (String × Json)) :
    (joinWith "," (((k0, j0) :: L).map (fun kj => "\"" ++ escape kj.1 ++ "\":" ++ render kj.2))).toUTF8[0]! = 34 := by
  simp only [List.map_cons]
  cases L with
  | nil =>
    simp only [List.map, joinWith]
    rw [String.append_assoc, String.append_assoc]
    exact str_prepend_byte0 _
  | cons p L' =>
    simp only [List.map_cons, joinWith]
    rw [String.append_assoc]
    have h_pos : 0 < ("\"" ++ escape k0 ++ "\":" ++ render j0).toUTF8.size := by
      simp only [str_app, ByteArray.size_append]
      have h1 : ("\"" : String).toUTF8.size = 1 := by decide
      omega
    rw [str_app, ba_get!_append_left h_pos, String.append_assoc, String.append_assoc]
    exact str_prepend_byte0 _

-- ---------------------------------------------------------------------------
-- 6. Comma-prefixed tail helper for array/object body round-trips
-- ---------------------------------------------------------------------------

-- "," ++ render x₀ ++ "," ++ render x₁ ++ ... for the tail elements
private def commaPrefix : List Json → String
  | []        => ""
  | x :: rest => "," ++ render x ++ commaPrefix rest

private theorem commaPrefix_cons_size (x : Json) (rest : List Json) :
    (commaPrefix (x :: rest)).toUTF8.size =
    1 + (render x).toUTF8.size + (commaPrefix rest).toUTF8.size := by
  simp only [commaPrefix, str_app, ByteArray.size_append]
  have h : (",":String).toUTF8.size = 1 := by decide
  omega

-- Byte 0 of commaPrefix (x :: rest) is ',' (44)
private theorem commaPrefix_byte_comma (x : Json) (rest : List Json) :
    (commaPrefix (x :: rest)).toUTF8[0]! = 44 := by
  simp only [commaPrefix, str_app]
  have hc : (",":String).toUTF8.size = 1 := by decide
  rw [ba_get!_append_left (by rw [ByteArray.size_append]; omega)]
  rw [ba_get!_append_left (by omega)]
  decide

-- Byte (1 + j) of commaPrefix (x :: rest) equals (render x)[j] for j < |render x|
private theorem commaPrefix_byte_x (x : Json) (rest : List Json) (j : Nat)
    (hj : j < (render x).toUTF8.size) :
    (commaPrefix (x :: rest)).toUTF8[1 + j]! = (render x).toUTF8[j]! := by
  simp only [commaPrefix, str_app]
  have hc : (",":String).toUTF8.size = 1 := by decide
  rw [ba_get!_append_left (by rw [ByteArray.size_append]; omega)]
  rw [ba_get!_append_right (by omega) (by rw [ByteArray.size_append]; omega)]
  simp only [show 1 + j - (",":String).toUTF8.size = j from by simp only [hc]; omega]

-- Byte (1 + |render x| + j) of commaPrefix (x :: rest) equals (commaPrefix rest)[j]
private theorem commaPrefix_byte_rest (x : Json) (rest : List Json) (j : Nat)
    (hj : j < (commaPrefix rest).toUTF8.size) :
    (commaPrefix (x :: rest)).toUTF8[1 + (render x).toUTF8.size + j]! = (commaPrefix rest).toUTF8[j]! := by
  simp only [commaPrefix, str_app]
  have hc : (",":String).toUTF8.size = 1 := by decide
  rw [ba_get!_append_right
      (by rw [ByteArray.size_append]; omega)
      (by rw [ByteArray.size_append, ByteArray.size_append]; omega)]
  simp only [show 1 + (render x).toUTF8.size + j - ((",":String).toUTF8 ++ (render x).toUTF8).size =
      j from by simp only [ByteArray.size_append, hc]; omega]

-- joinWith "," ((x :: rest).map render) = render x ++ commaPrefix rest
private theorem joinWith_map_render_eq (x : Json) (rest : List Json) :
    joinWith "," ((x :: rest).map render) = render x ++ commaPrefix rest := by
  induction rest generalizing x with
  | nil => simp [joinWith, commaPrefix]
  | cons y ys ih =>
    simp only [List.map, joinWith]
    cases ys with
    | nil => simp [joinWith, commaPrefix, String.append_assoc]
    | cons z zs =>
      rw [show joinWith "," (render y :: List.map render (z :: zs)) = render y ++ commaPrefix (z :: zs) from ih y]
      simp [commaPrefix, String.append_assoc]

-- ---------------------------------------------------------------------------
-- 6b. Key-value rendering and comma-prefixed tail for object body round-trips
-- ---------------------------------------------------------------------------

-- renderKV (k, v) = render (.str k) ++ ":" ++ render v
private def renderKV : String × Json → String
  | (k, v) => render (.str k) ++ ":" ++ render v

private def commaPrefixKV : List (String × Json) → String
  | []         => ""
  | kv :: rest => "," ++ renderKV kv ++ commaPrefixKV rest

private theorem renderKV_size (k : String) (v : Json) :
    (renderKV (k, v)).toUTF8.size =
    2 + (ebytes k.toList).length + 1 + (render v).toUTF8.size := by
  simp only [renderKV, str_app, ByteArray.size_append]
  rw [render_str_size k]
  have h : (":":String).toUTF8.size = 1 := by decide
  omega

private theorem renderKV_byte0 (kv : String × Json) :
    (renderKV kv).toUTF8[0]! = 34 := by
  simp only [renderKV, str_app]
  rw [ba_get!_append_left (by
    rw [ByteArray.size_append]
    have h := render_str_size kv.1
    have hc : (":":String).toUTF8.size = 1 := by decide
    omega)]
  rw [ba_get!_append_left (by
    have h := render_str_size kv.1; omega)]
  exact render_str_byte0 kv.1

private theorem renderKV_pos (kv : String × Json) : 0 < (renderKV kv).toUTF8.size := by
  simp only [renderKV, str_app, ByteArray.size_append]
  have h := render_str_size kv.1
  have hc : (":":String).toUTF8.size = 1 := by decide
  omega

private theorem commaPrefixKV_cons_size (kv : String × Json) (rest : List (String × Json)) :
    (commaPrefixKV (kv :: rest)).toUTF8.size =
    1 + (renderKV kv).toUTF8.size + (commaPrefixKV rest).toUTF8.size := by
  simp only [commaPrefixKV, str_app, ByteArray.size_append]
  have h : (",":String).toUTF8.size = 1 := by decide
  omega

private theorem commaPrefixKV_byte_comma (kv : String × Json) (rest : List (String × Json)) :
    (commaPrefixKV (kv :: rest)).toUTF8[0]! = 44 := by
  simp only [commaPrefixKV, str_app]
  have hc : (",":String).toUTF8.size = 1 := by decide
  rw [ba_get!_append_left (by rw [ByteArray.size_append]; omega)]
  rw [ba_get!_append_left (by omega)]
  decide

private theorem commaPrefixKV_byte_kv (kv : String × Json) (rest : List (String × Json))
    (j : Nat) (hj : j < (renderKV kv).toUTF8.size) :
    (commaPrefixKV (kv :: rest)).toUTF8[1 + j]! = (renderKV kv).toUTF8[j]! := by
  simp only [commaPrefixKV, str_app]
  have hc : (",":String).toUTF8.size = 1 := by decide
  rw [ba_get!_append_left (by rw [ByteArray.size_append]; omega)]
  rw [ba_get!_append_right (by omega) (by rw [ByteArray.size_append]; omega)]
  simp only [show 1 + j - (",":String).toUTF8.size = j from by simp only [hc]; omega]

private theorem commaPrefixKV_byte_rest (kv : String × Json) (rest : List (String × Json))
    (j : Nat) (hj : j < (commaPrefixKV rest).toUTF8.size) :
    (commaPrefixKV (kv :: rest)).toUTF8[1 + (renderKV kv).toUTF8.size + j]! =
    (commaPrefixKV rest).toUTF8[j]! := by
  simp only [commaPrefixKV, str_app]
  have hc : (",":String).toUTF8.size = 1 := by decide
  rw [ba_get!_append_right
      (by rw [ByteArray.size_append]; omega)
      (by rw [ByteArray.size_append, ByteArray.size_append]; omega)]
  simp only [show 1 + (renderKV kv).toUTF8.size + j -
      ((",":String).toUTF8 ++ (renderKV kv).toUTF8).size = j
      from by simp only [ByteArray.size_append, hc]; omega]

private theorem joinWith_map_renderKV_eq (kv : String × Json) (rest : List (String × Json)) :
    joinWith "," ((kv :: rest).map renderKV) = renderKV kv ++ commaPrefixKV rest := by
  induction rest generalizing kv with
  | nil => simp [joinWith, commaPrefixKV]
  | cons kv2 rest2 ih =>
    simp only [List.map, joinWith]
    cases rest2 with
    | nil => simp [joinWith, commaPrefixKV, String.append_assoc]
    | cons kv3 rest3 =>
      rw [show joinWith "," (renderKV kv2 :: List.map renderKV (kv3 :: rest3)) =
          renderKV kv2 ++ commaPrefixKV (kv3 :: rest3) from ih kv2]
      simp [commaPrefixKV, String.append_assoc]

/-- `foldFwd push (seqR comma (seqR ws kv_parser)) buf acc base` over a kv tail list. -/
private theorem foldFwd_comma_kv_run
    (kv_parser : GParser conditional (String × Json))
    (lst : List (String × Json)) (buf : ByteArray) (acc : Array (String × Json)) (base : Nat)
    (h_bound : base + (commaPrefixKV lst).toUTF8.size ≤ buf.size)
    (h_match : ∀ j, j < (commaPrefixKV lst).toUTF8.size →
        buf[base + j]! = (commaPrefixKV lst).toUTF8[j]!)
    (h_stop_cond : base + (commaPrefixKV lst).toUTF8.size = buf.size ∨
        (base + (commaPrefixKV lst).toUTF8.size < buf.size ∧
         Ascii.isDigit buf[base + (commaPrefixKV lst).toUTF8.size]! = false ∧
         buf[base + (commaPrefixKV lst).toUTF8.size]! ≠ 46 ∧
         Ascii.isExp buf[base + (commaPrefixKV lst).toUTF8.size]! = false))
    (h_term : ∀ u r, (Grip.Json.wsByte Ascii.comma).run buf
        (base + (commaPrefixKV lst).toUTF8.size) ≠ .ok u r)
    (h_kvp : ∀ kv ∈ lst, ∀ (p : Nat),
        p + (renderKV kv).toUTF8.size ≤ buf.size →
        (∀ j, j < (renderKV kv).toUTF8.size → buf[p + j]! = (renderKV kv).toUTF8[j]!) →
        (p + (renderKV kv).toUTF8.size = buf.size ∨
         (p + (renderKV kv).toUTF8.size < buf.size ∧
          Ascii.isDigit buf[p + (renderKV kv).toUTF8.size]! = false ∧
          buf[p + (renderKV kv).toUTF8.size]! ≠ 46 ∧
          Ascii.isExp buf[p + (renderKV kv).toUTF8.size]! = false)) →
        kv_parser.run buf p = .ok kv (p + (renderKV kv).toUTF8.size)) :
    foldFwd (fun a e => a.push e)
        (GParser.seqR (Grip.Json.wsByte Ascii.comma) (GParser.seqR GParser.ws kv_parser))
        buf acc base =
    (acc ++ lst.toArray, base + (commaPrefixKV lst).toUTF8.size) := by
  induction lst generalizing base acc with
  | nil =>
    have h_nil_size : (commaPrefixKV ([] : List (String × Json))).toUTF8.size = 0 := by
      simp [commaPrefixKV]
    have h_la_nil : ([] : List (String × Json)).toArray = #[] := rfl
    simp only [h_nil_size, Array.append_empty, Nat.add_zero] at h_term ⊢
    unfold foldFwd
    cases h_step : (GParser.seqR (Grip.Json.wsByte Ascii.comma)
        (GParser.seqR GParser.ws kv_parser)).run buf base with
    | ok v q' =>
      exfalso
      simp only [GParser.seqR] at h_step
      cases h_comma : (Grip.Json.wsByte Ascii.comma).run buf base with
      | ok u r => exact absurd h_comma (h_term u r)
      | error e => simp only [h_comma] at h_step; simp at h_step
    | error e => rfl
  | cons kv rest ih =>
    simp only [commaPrefixKV_cons_size] at h_bound h_match h_stop_cond h_term
    have hrkv_pos : 0 < (renderKV kv).toUTF8.size := renderKV_pos kv
    have hbase_lt : base < buf.size := by omega
    have hbase_byte! : buf[base]! = 44 := by
      have h0 := h_match 0 (by omega)
      simp only [Nat.add_zero] at h0
      rw [h0]; exact commaPrefixKV_byte_comma kv rest
    have hbase_byte : buf[base] = (44 : UInt8) := by rwa [← getElem!_pos buf base hbase_lt]
    have h_comma_ok : (Grip.Json.wsByte Ascii.comma).run buf base = .ok () (base + 1) :=
      wsByte_run_stop Ascii.comma buf base hbase_lt (by rw [hbase_byte]; decide)
        (by rw [hbase_byte]; decide)
    have hbase1_lt : base + 1 < buf.size := by omega
    have hrkv_byte0 : (renderKV kv).toUTF8[0]! = 34 := renderKV_byte0 kv
    have hbase1_byte! : buf[base + 1]! = 34 := by
      have h1 := h_match 1 (by omega)
      rw [h1, commaPrefixKV_byte_kv kv rest 0 hrkv_pos, hrkv_byte0]
    have hbase1_byte : buf[base + 1] = (34 : UInt8) := by
      rwa [← getElem!_pos buf _ hbase1_lt]
    have h_ws_ok : GParser.ws.run buf (base + 1) = .ok 0 (base + 1) :=
      ws_run_stop buf (base + 1) hbase1_lt (by rw [hbase1_byte]; decide)
    have hkv_bound : (base + 1) + (renderKV kv).toUTF8.size ≤ buf.size := by omega
    have hkv_match : ∀ j, j < (renderKV kv).toUTF8.size →
        buf[(base + 1) + j]! = (renderKV kv).toUTF8[j]! := by
      intro j hj
      have hmj := h_match (1 + j) (by omega)
      rw [show base + (1 + j) = (base + 1) + j from by ring] at hmj
      rw [hmj]; exact commaPrefixKV_byte_kv kv rest j hj
    -- Stop condition for kv at (base + 1) + |renderKV kv|
    have hkv_stop : (base + 1) + (renderKV kv).toUTF8.size = buf.size ∨
        ((base + 1) + (renderKV kv).toUTF8.size < buf.size ∧
         Ascii.isDigit buf[(base + 1) + (renderKV kv).toUTF8.size]! = false ∧
         buf[(base + 1) + (renderKV kv).toUTF8.size]! ≠ 46 ∧
         Ascii.isExp buf[(base + 1) + (renderKV kv).toUTF8.size]! = false) := by
      cases hrest : rest with
      | nil =>
        have h_cp_nil : (commaPrefixKV ([] : List (String × Json))).toUTF8.size = 0 := by
          simp [commaPrefixKV]
        rw [hrest, h_cp_nil, Nat.add_zero] at h_stop_cond
        rcases h_stop_cond with h | ⟨h1, h2, h3, h4⟩
        · left
          rw [show (base + 1) + (renderKV kv).toUTF8.size =
              base + (1 + (renderKV kv).toUTF8.size) from by ring]
          omega
        · right
          rw [show (base + 1) + (renderKV kv).toUTF8.size =
              base + (1 + (renderKV kv).toUTF8.size) from by ring]
          exact ⟨by omega, h2, h3, h4⟩
      | cons r rs =>
        right
        have hcp_pos : 0 < (commaPrefixKV rest).toUTF8.size := by
          rw [hrest, commaPrefixKV_cons_size]; omega
        have hbyte_comma : buf[(base + 1) + (renderKV kv).toUTF8.size]! = 44 := by
          have hmj := h_match (1 + (renderKV kv).toUTF8.size) (by omega)
          rw [show base + (1 + (renderKV kv).toUTF8.size) =
              (base + 1) + (renderKV kv).toUTF8.size from by ring] at hmj
          rw [hmj]
          have h_rest_byte := commaPrefixKV_byte_rest kv rest 0 hcp_pos
          rw [Nat.add_zero] at h_rest_byte
          rw [h_rest_byte, hrest]
          exact commaPrefixKV_byte_comma r rs
        exact ⟨by omega, by rw [hbyte_comma]; decide,
               by rw [hbyte_comma]; decide, by rw [hbyte_comma]; decide⟩
    have hkv_val := h_kvp kv List.mem_cons_self (base + 1) hkv_bound hkv_match hkv_stop
    have h_step : (GParser.seqR (Grip.Json.wsByte Ascii.comma)
        (GParser.seqR GParser.ws kv_parser)).run buf base =
        .ok kv (base + 1 + (renderKV kv).toUTF8.size) :=
      seqR_run _ _ _ _ () (base + 1) kv _ h_comma_ok
        (seqR_run _ _ _ _ 0 (base + 1) kv _ h_ws_ok hkv_val)
    have h_rest_bound :
        (base + 1 + (renderKV kv).toUTF8.size) + (commaPrefixKV rest).toUTF8.size ≤ buf.size :=
      by omega
    have h_rest_match : ∀ j, j < (commaPrefixKV rest).toUTF8.size →
        buf[(base + 1 + (renderKV kv).toUTF8.size) + j]! = (commaPrefixKV rest).toUTF8[j]! := by
      intro j hj
      have hmj := h_match (1 + (renderKV kv).toUTF8.size + j) (by omega)
      rw [show base + (1 + (renderKV kv).toUTF8.size + j) =
          (base + 1 + (renderKV kv).toUTF8.size) + j from by ring] at hmj
      rw [hmj]; exact commaPrefixKV_byte_rest kv rest j hj
    have h_rest_stop_cond : (base + 1 + (renderKV kv).toUTF8.size) + (commaPrefixKV rest).toUTF8.size = buf.size ∨
        ((base + 1 + (renderKV kv).toUTF8.size) + (commaPrefixKV rest).toUTF8.size < buf.size ∧
         Ascii.isDigit buf[(base + 1 + (renderKV kv).toUTF8.size) + (commaPrefixKV rest).toUTF8.size]! = false ∧
         buf[(base + 1 + (renderKV kv).toUTF8.size) + (commaPrefixKV rest).toUTF8.size]! ≠ 46 ∧
         Ascii.isExp buf[(base + 1 + (renderKV kv).toUTF8.size) + (commaPrefixKV rest).toUTF8.size]! = false) := by
      rw [show (base + 1 + (renderKV kv).toUTF8.size) + (commaPrefixKV rest).toUTF8.size =
          base + (1 + (renderKV kv).toUTF8.size + (commaPrefixKV rest).toUTF8.size) from by ring]
      exact h_stop_cond
    have h_rest_term : ∀ u r, (Grip.Json.wsByte Ascii.comma).run buf
        ((base + 1 + (renderKV kv).toUTF8.size) + (commaPrefixKV rest).toUTF8.size) ≠ .ok u r :=
      fun u r => by convert h_term u r using 2; ring
    have h_rest_kvp : ∀ kv2 ∈ rest, ∀ (p : Nat),
        p + (renderKV kv2).toUTF8.size ≤ buf.size →
        (∀ j, j < (renderKV kv2).toUTF8.size → buf[p + j]! = (renderKV kv2).toUTF8[j]!) →
        (p + (renderKV kv2).toUTF8.size = buf.size ∨
         (p + (renderKV kv2).toUTF8.size < buf.size ∧
          Ascii.isDigit buf[p + (renderKV kv2).toUTF8.size]! = false ∧
          buf[p + (renderKV kv2).toUTF8.size]! ≠ 46 ∧
          Ascii.isExp buf[p + (renderKV kv2).toUTF8.size]! = false)) →
        kv_parser.run buf p = .ok kv2 (p + (renderKV kv2).toUTF8.size) :=
      fun kv2 hkv2 => h_kvp kv2 (List.mem_cons.mpr (Or.inr hkv2))
    rw [foldFwd]
    simp only [h_step]
    have h_cond : base < base + 1 + (renderKV kv).toUTF8.size ∧
        base + 1 + (renderKV kv).toUTF8.size ≤ buf.size := ⟨by omega, by omega⟩
    rw [dif_pos h_cond,
        ih (acc.push kv) (base + 1 + (renderKV kv).toUTF8.size)
          h_rest_bound h_rest_match h_rest_stop_cond h_rest_term h_rest_kvp]
    simp only [Prod.mk.injEq]
    constructor
    · rw [Array.push_eq_append, List.toArray_cons]; simp
    · rw [commaPrefixKV_cons_size]; omega

/-- `foldFwd push (seqR comma value) buf acc base` processes a tail list with leading commas. -/
private theorem foldFwd_comma_value_run (lst : List Json) (buf : ByteArray) (acc : Array Json) (base : Nat)
    (h_bound : base + (commaPrefix lst).toUTF8.size ≤ buf.size)
    (h_match : ∀ j, j < (commaPrefix lst).toUTF8.size → buf[base + j]! = (commaPrefix lst).toUTF8[j]!)
    (h_stop_cond : base + (commaPrefix lst).toUTF8.size = buf.size ∨
        base + (commaPrefix lst).toUTF8.size < buf.size ∧
          Ascii.isDigit buf[base + (commaPrefix lst).toUTF8.size]! = false ∧
          buf[base + (commaPrefix lst).toUTF8.size]! ≠ 46 ∧
          Ascii.isExp buf[base + (commaPrefix lst).toUTF8.size]! = false)
    (h_term : ∀ u r, (Grip.Json.wsByte Ascii.comma).run buf
        (base + (commaPrefix lst).toUTF8.size) ≠ .ok u r)
    (h_vp : ∀ x ∈ lst, ∀ (p : Nat),
        p + (render x).toUTF8.size ≤ buf.size →
        (∀ j, j < (render x).toUTF8.size → buf[p + j]! = (render x).toUTF8[j]!) →
        (p + (render x).toUTF8.size = buf.size ∨
         p + (render x).toUTF8.size < buf.size ∧
           Ascii.isDigit buf[p + (render x).toUTF8.size]! = false ∧
           buf[p + (render x).toUTF8.size]! ≠ 46 ∧
           Ascii.isExp buf[p + (render x).toUTF8.size]! = false) →
        Grip.Json.value.run buf p = .ok x (p + (render x).toUTF8.size)) :
    foldFwd (fun a e => a.push e) (GParser.seqR (Grip.Json.wsByte Ascii.comma) Grip.Json.value)
        buf acc base =
    (acc ++ lst.toArray, base + (commaPrefix lst).toUTF8.size) := by
  induction lst generalizing base acc with
  | nil =>
    have h_cp_nil : (commaPrefix []).toUTF8.size = 0 := rfl
    have h_la_nil : ([] : List Json).toArray = #[] := rfl
    simp only [h_cp_nil, Array.append_empty, Nat.add_zero] at h_term ⊢
    unfold foldFwd
    cases h_seqR : (GParser.seqR (Grip.Json.wsByte Ascii.comma) Grip.Json.value).run buf base with
    | ok v q' =>
      exfalso
      simp only [GParser.seqR] at h_seqR
      cases h_wbc : (Grip.Json.wsByte Ascii.comma).run buf base with
      | ok u r => exact absurd h_wbc (h_term u r)
      | error e => simp only [h_wbc] at h_seqR; simp at h_seqR
    | error e => rfl
  | cons x rest ih =>
    simp only [commaPrefix_cons_size] at h_bound h_match h_stop_cond h_term
    -- wsByte comma succeeds at base (buf[base] = ',')
    have hbase_lt : base < buf.size := by omega
    have hbase_byte! : buf[base]! = 44 := by
      have h0 := h_match 0 (by omega)
      simp only [Nat.add_zero] at h0
      rw [h0]; exact commaPrefix_byte_comma x rest
    have hbase_byte : buf[base] = (44 : UInt8) := by rwa [← getElem!_pos buf base hbase_lt]
    have hws : Ascii.isWs buf[base] = false := by rw [hbase_byte]; decide
    have h_comma_ok : (Grip.Json.wsByte Ascii.comma).run buf base = .ok () (base + 1) :=
      wsByte_run_stop Ascii.comma buf base hbase_lt hws (by rw [hbase_byte]; decide)
    -- Bytes for render x at base+1
    have hx_bound : (base + 1) + (render x).toUTF8.size ≤ buf.size := by omega
    have hx_match : ∀ j, j < (render x).toUTF8.size → buf[(base + 1) + j]! = (render x).toUTF8[j]! := by
      intro j hj
      have hmj := h_match (1 + j) (by omega)
      rw [show base + (1 + j) = (base + 1) + j from by ring] at hmj
      rw [hmj]; exact commaPrefix_byte_x x rest j hj
    -- Stop condition for x (next byte is ',' or the terminal stop byte)
    have hx_stop : (base + 1) + (render x).toUTF8.size = buf.size ∨
        (base + 1) + (render x).toUTF8.size < buf.size ∧
          Ascii.isDigit buf[(base + 1) + (render x).toUTF8.size]! = false ∧
          buf[(base + 1) + (render x).toUTF8.size]! ≠ 46 ∧
          Ascii.isExp buf[(base + 1) + (render x).toUTF8.size]! = false := by
      cases hrest : rest with
      | nil =>
        -- rest empty: stop pos = base + 1 + |render x|, covered by h_stop_cond
        have h_cp_nil : (commaPrefix ([] : List Json)).toUTF8.size = 0 := rfl
        simp only [hrest, h_cp_nil, Nat.add_zero] at h_stop_cond
        rcases h_stop_cond with h | ⟨h1, h2, h3, h4⟩
        · left; omega
        · right
          rw [show (base + 1) + (render x).toUTF8.size =
              base + (1 + (render x).toUTF8.size) from by ring]
          exact ⟨by omega, h2, h3, h4⟩
      | cons r rs =>
        -- rest non-empty: next byte is ',' (44), not a number continuation
        right
        have hcr_pos : 0 < (commaPrefix rest).toUTF8.size := by
          rw [hrest]; simp only [commaPrefix_cons_size]; omega
        have h_byte_comma : buf[(base + 1) + (render x).toUTF8.size]! = 44 := by
          have hmj := h_match (1 + (render x).toUTF8.size) (by omega)
          rw [show base + (1 + (render x).toUTF8.size) = (base + 1) + (render x).toUTF8.size
              from by ring] at hmj
          rw [hmj]
          have hstep : (commaPrefix (x :: rest)).toUTF8[1 + (render x).toUTF8.size + 0]! =
              (commaPrefix rest).toUTF8[0]! := commaPrefix_byte_rest x rest 0 hcr_pos
          rw [Nat.add_zero] at hstep
          rw [hstep, hrest]
          exact commaPrefix_byte_comma r rs
        exact ⟨by omega, by rw [h_byte_comma]; decide, by rw [h_byte_comma]; decide,
               by rw [h_byte_comma]; decide⟩
    -- value parses x
    have hx_val := h_vp x List.mem_cons_self (base + 1) hx_bound hx_match hx_stop
    -- seqR comma value succeeds
    have h_seqR : (GParser.seqR (Grip.Json.wsByte Ascii.comma) Grip.Json.value).run buf base =
        .ok x (base + 1 + (render x).toUTF8.size) :=
      seqR_run _ _ _ _ () (base + 1) x _ h_comma_ok hx_val
    -- Prepare IH arguments for the rest
    have h_rest_bound : (base + 1 + (render x).toUTF8.size) + (commaPrefix rest).toUTF8.size ≤ buf.size :=
      by omega
    have h_rest_match : ∀ j, j < (commaPrefix rest).toUTF8.size →
        buf[(base + 1 + (render x).toUTF8.size) + j]! = (commaPrefix rest).toUTF8[j]! := by
      intro j hj
      have hmj := h_match (1 + (render x).toUTF8.size + j) (by omega)
      rw [show base + (1 + (render x).toUTF8.size + j) =
          (base + 1 + (render x).toUTF8.size) + j from by ring] at hmj
      rw [hmj]; exact commaPrefix_byte_rest x rest j hj
    have h_rest_stop : (base + 1 + (render x).toUTF8.size) + (commaPrefix rest).toUTF8.size = buf.size ∨
        (base + 1 + (render x).toUTF8.size) + (commaPrefix rest).toUTF8.size < buf.size ∧
          Ascii.isDigit buf[(base + 1 + (render x).toUTF8.size) + (commaPrefix rest).toUTF8.size]! = false ∧
          buf[(base + 1 + (render x).toUTF8.size) + (commaPrefix rest).toUTF8.size]! ≠ 46 ∧
          Ascii.isExp buf[(base + 1 + (render x).toUTF8.size) + (commaPrefix rest).toUTF8.size]! = false := by
      rw [show (base + 1 + (render x).toUTF8.size) + (commaPrefix rest).toUTF8.size =
          base + (1 + (render x).toUTF8.size + (commaPrefix rest).toUTF8.size) from by ring]
      exact h_stop_cond
    have h_rest_term : ∀ u r, (Grip.Json.wsByte Ascii.comma).run buf
        ((base + 1 + (render x).toUTF8.size) + (commaPrefix rest).toUTF8.size) ≠ .ok u r := by
      intro u r
      convert h_term u r using 2; ring
    have h_rest_vp : ∀ y ∈ rest, ∀ (p : Nat),
        p + (render y).toUTF8.size ≤ buf.size →
        (∀ j, j < (render y).toUTF8.size → buf[p + j]! = (render y).toUTF8[j]!) →
        (p + (render y).toUTF8.size = buf.size ∨
         p + (render y).toUTF8.size < buf.size ∧
           Ascii.isDigit buf[p + (render y).toUTF8.size]! = false ∧
           buf[p + (render y).toUTF8.size]! ≠ 46 ∧
           Ascii.isExp buf[p + (render y).toUTF8.size]! = false) →
        Grip.Json.value.run buf p = .ok y (p + (render y).toUTF8.size) :=
      fun y hy => h_vp y (List.mem_cons.mpr (Or.inr hy))
    -- Unfold foldFwd, apply seqR result, recurse via IH
    rw [foldFwd]
    simp only [h_seqR]
    have h_cond : base < base + 1 + (render x).toUTF8.size ∧
        base + 1 + (render x).toUTF8.size ≤ buf.size := ⟨by omega, by omega⟩
    rw [dif_pos h_cond,
        ih (acc.push x) (base + 1 + (render x).toUTF8.size)
          h_rest_bound h_rest_match h_rest_stop h_rest_term h_rest_vp]
    simp only [Prod.mk.injEq]
    constructor
    · rw [Array.push_eq_append, List.toArray_cons]; simp
    · rw [commaPrefix_cons_size]; omega

-- Note: the ByteArray parameter is named `buf` (not `arr`) throughout
-- because `Json.arr` is in scope and would shadow a bare `arr` in patterns.

/-- If bytes `buf[q..]` match `(render v).toUTF8`, then `value` parses `v` there.
The `hstop` hypothesis says the byte immediately after the rendered value is not a number
continuation (digit / `.` / `e`/`E`); it is needed only for the `.num` case but carried
uniformly to enable structural recursion for the `.arr` and `.obj` cases. -/
theorem value_run_at : ∀ (v : Json) (buf : ByteArray) (q : Nat),
    q + (render v).toUTF8.size ≤ buf.size →
    (∀ i, i < (render v).toUTF8.size → buf[q + i]! = (render v).toUTF8[i]!) →
    (q + (render v).toUTF8.size = buf.size ∨
     q + (render v).toUTF8.size < buf.size ∧
       Ascii.isDigit buf[q + (render v).toUTF8.size]! = false ∧
       buf[q + (render v).toUTF8.size]! ≠ 46 ∧
       Ascii.isExp buf[q + (render v).toUTF8.size]! = false) →
    Grip.Json.value.run buf q = .ok v (q + (render v).toUTF8.size)
  | .null, buf, q, hq, hmatch, _ => by
    have hrend : render Json.null = "null" := by simp [render]
    simp only [hrend, show ("null" : String).toUTF8.size = 4 from by decide] at hq hmatch ⊢
    exact value_run_null buf q hq hmatch
  | .bool true, buf, q, hq, hmatch, _ => by
    have hrend : render (Json.bool true) = "true" := by simp [render]
    simp only [hrend, show ("true" : String).toUTF8.size = 4 from by decide] at hq hmatch ⊢
    exact value_run_true buf q hq hmatch
  | .bool false, buf, q, hq, hmatch, _ => by
    have hrend : render (Json.bool false) = "false" := by simp [render]
    simp only [hrend, show ("false" : String).toUTF8.size = 5 from by decide] at hq hmatch ⊢
    exact value_run_false buf q hq hmatch
  | .str s, buf, q, hq, hmatch, _ => by
    have hsize : (render (.str s)).toUTF8.size = 2 + (ebytes s.toList).length :=
      render_str_size s
    rw [hsize] at hq ⊢
    rw [show q + (2 + (ebytes s.toList).length) = q + 1 + (ebytes s.toList).length + 1 from by ring]
    refine value_run_str buf q s (by omega) ?_ ?_ ?_
    · have h0 := hmatch 0 (by omega)
      simp only [Nat.add_zero] at h0
      rwa [render_str_byte0] at h0
    · intro j hj
      have hj' := hmatch (1 + j) (by omega)
      simp only [show q + (1 + j) = q + 1 + j from by ring] at hj'
      rwa [render_str_byte_mid s j hj] at hj'
    · have hn := hmatch (1 + (ebytes s.toList).length) (by omega)
      simp only [show q + (1 + (ebytes s.toList).length) = q + 1 + (ebytes s.toList).length
          from by ring] at hn
      rwa [render_str_byte_close] at hn
  | .num m e, buf, q, hq, hmatch, hstop => by
    have hrn : render (Json.num m e) = renderNumber m e := by simp [render]
    simp only [hrn] at hq hmatch hstop ⊢
    by_cases he : e > Decode.maxExp
    · have hlarge : renderNumber m e = renderNumScientific m e := by
        simp [renderNumber, he]
      rw [hlarge] at hq hmatch hstop ⊢
      exact value_run_num_scientific m e buf q he hq hmatch hstop
    · have hsmall : renderNumber m e = renderNum m e := by simp [renderNumber, he]
      rw [hsmall] at hq hmatch hstop ⊢
      exact value_run_num_at m e buf q hq hmatch hstop
  | .arr xs, buf, q, hq, hmatch, hstop => by
    have hrend : render (Json.arr xs) =
        "[" ++ joinWith "," (xs.attach.toList.map (fun x => render x.1)) ++ "]" := by
      simp [render]
    have hN2 : 2 ≤ (render (Json.arr xs)).toUTF8.size := by
      rw [hrend, str_app, ByteArray.size_append, str_app, ByteArray.size_append]
      have h1 : ("[" : String).toUTF8.size = 1 := by decide
      have h2 : ("]" : String).toUTF8.size = 1 := by decide
      omega
    have hqlt : q < buf.size := by omega
    have hbufq! : buf[q]! = 91 := by
      have h0 := hmatch 0 (by omega)
      simp only [Nat.add_zero] at h0
      rw [h0, hrend]
      simp only [str_app]
      have h1 : ("[" : String).toUTF8.size = 1 := by decide
      rw [ba_get!_append_left (by simp only [ByteArray.size_append]; omega)]
      rw [ba_get!_append_left (by decide)]
      decide
    have hbufq : buf[q] = 91 := by rwa [← getElem!_pos buf q hqlt]
    have hws_buf : Ascii.isWs buf[q] = false := by rw [hbufq]; decide
    -- last byte of render arr is ']' = 93; proved by byte position arithmetic
    have hbufN! : buf[q + (render (Json.arr xs)).toUTF8.size - 1]! = 93 := by
      have hNm := hmatch ((render (Json.arr xs)).toUTF8.size - 1) (by omega)
      rw [show q + ((render (Json.arr xs)).toUTF8.size - 1) =
          q + (render (Json.arr xs)).toUTF8.size - 1 from by omega] at hNm
      rw [hNm, hrend]; exact lbracket_last_byte _
    have hN1lt : q + (render (Json.arr xs)).toUTF8.size - 1 < buf.size := by omega
    have hbufN : buf[q + (render (Json.arr xs)).toUTF8.size - 1] = 93 := by
      rwa [← getElem!_pos buf _ hN1lt]
    have hch : (GParser.ch '[').run buf q = .ok () (q + 1) :=
      byte_run! 91 buf q hqlt hbufq!
    have hwsbr : (Grip.Json.wsByte Ascii.rbracket).run buf
        (q + (render (Json.arr xs)).toUTF8.size - 1) =
        .ok () (q + (render (Json.arr xs)).toUTF8.size) := by
      convert wsByte_run_stop Ascii.rbracket buf _ hN1lt (by rw [hbufN]; decide) (by rw [hbufN]; rfl) using 2
      omega
    -- arrayBody parses xs
    have harr_body : (GParser.alt
        (GParser.bind (GParser.fixSelf Grip.Json.value_body (buf.size - q))
          (fun x => GParser.foldMany (fun a e => a.push e) #[x]
            (GParser.seqR (Grip.Json.wsByte Ascii.comma)
              (GParser.fixSelf Grip.Json.value_body (buf.size - q)))))
        (GParser.pure #[])).run buf (q + 1) =
        .ok xs (q + (render (Json.arr xs)).toUTF8.size - 1) := by
      -- Transfer fixSelf → value via arrayBody_agree + fixSelf_eq_value_of_gt
      have h_agree := arrayBody_agree
          (GParser.fixSelf Grip.Json.value_body (buf.size - q)) Grip.Json.value buf q
          (fun q' hq' => fixSelf_eq_value_of_gt buf q q' hq') (q + 1) (by omega)
      suffices h_val : (GParser.alt
          (GParser.bind Grip.Json.value
            (fun xi => GParser.foldMany (fun a e => a.push e) #[xi]
              (GParser.seqR (Grip.Json.wsByte Ascii.comma) Grip.Json.value)))
          (GParser.pure #[])).run buf (q + 1) =
          .ok xs (q + (render (Json.arr xs)).toUTF8.size - 1) by
        rcases h_fix : (GParser.alt
            (GParser.bind (GParser.fixSelf Grip.Json.value_body (buf.size - q)) _)
            (GParser.pure #[])).run buf (q + 1) with ⟨xs', q'⟩ | e
        · rw [h_fix, h_val] at h_agree
          simp only [AgreeOk] at h_agree; obtain ⟨rfl, rfl⟩ := h_agree; rfl
        · rw [h_fix, h_val] at h_agree; exact absurd h_agree (by simp [AgreeOk])
      -- Establish body = joinWith "," (xs.toList.map render)
      have hatt_render : xs.attach.toList.map (fun x => render x.1) = xs.toList.map render := by
        have hcomp : (fun x : {x // x ∈ xs} => render x.1) = render ∘ (fun x => x.1) := by
          ext; rfl
        rw [hcomp, ← List.map_map]; congr 1; simp [Array.attach]
      set body := joinWith "," (xs.toList.map render) with h_body_def
      have hbody_eq : joinWith "," (xs.attach.toList.map (fun x => render x.1)) = body := by
        rw [hatt_render]
      have hbody_size : (render (Json.arr xs)).toUTF8.size = 1 + body.toUTF8.size + 1 := by
        rw [hrend, hbody_eq, str_app, ByteArray.size_append, str_app, ByteArray.size_append]
        simp only [show ("[":String).toUTF8.size = 1 from by decide,
                   show ("]":String).toUTF8.size = 1 from by decide]
      have hend : q + (render (Json.arr xs)).toUTF8.size - 1 = q + 1 + body.toUTF8.size := by
        omega
      rw [hend]
      -- Body bytes
      have hmatch_body : ∀ j, j < body.toUTF8.size → buf[q + 1 + j]! = body.toUTF8[j]! := by
        intro j hj
        have h := hmatch (1 + j) (by rw [hbody_size]; omega)
        rw [show q + (1 + j) = q + 1 + j from by ring] at h
        rw [h, hrend, hbody_eq]; exact body_byte_j "[" "]" (by decide) body j hj
      -- Byte after body = ']' = 93
      have hbyte_last : buf[q + 1 + body.toUTF8.size]! = 93 := by rw [← hend]; exact hbufN!
      have hq1body_lt : q + 1 + body.toUTF8.size < buf.size := by omega
      -- Case on xs.toList
      rcases hxl : xs.toList with _ | ⟨xi, rest_l⟩
      · -- Empty: xs = #[], body = "", value errors at q+1 (byte = ']' = 93)
        have hxs_empty : xs = #[] := by apply Array.ext'; simp [← hxl]
        have hbody_empty : body.toUTF8.size = 0 := by
          rw [h_body_def, hxl, List.map_nil, joinWith]; rfl
        subst hxs_empty
        simp only [hbody_empty, Nat.add_zero]
        have hq1lt : q + 1 < buf.size := by omega
        have hbuf1 : buf[q + 1] = (93 : UInt8) := by
          have h := hbyte_last
          rw [hbody_empty, Nat.add_zero] at h
          rw [← getElem!_pos buf _ hq1lt]; exact h
        have hws1 : Ascii.isWs buf[q + 1] = false := by rw [hbuf1]; decide
        obtain ⟨e, hval_err⟩ : ∃ e, Grip.Json.value.run buf (q + 1) = .error e := by
          rw [Grip.Json.value, fix_run_unroll]; simp only [Grip.Json.value_body]
          rw [wsDispatch_run_stop _ buf (q + 1) hq1lt hws1, hbuf1]
          simp only [Ascii.lbrace, Ascii.lbracket, Ascii.quote, Ascii.dash]
          norm_num [Ascii.isDigit]; simp [clampAdvance, GParser.map, GParser.satisfy]
        simp only [GParser.alt, GParser.bind, GParser.pure, hval_err]
      · -- Non-empty: xs.toList = xi :: rest_l
        -- body = render xi ++ commaPrefix rest_l
        have h_body_cons : body = render xi ++ commaPrefix rest_l := by
          rw [h_body_def, hxl]; exact joinWith_map_render_eq xi rest_l
        -- xs = (xi :: rest_l).toArray = #[xi] ++ rest_l.toArray
        have hxs_eq : xs = #[xi] ++ rest_l.toArray := by apply Array.ext'; simp [hxl]
        -- Match bytes for xi: buf[q+1+j]! = (render xi)[j]!
        have hmatch_xi : ∀ j, j < (render xi).toUTF8.size →
            buf[q + 1 + j]! = (render xi).toUTF8[j]! := by
          intro j hj
          rw [hmatch_body j (by rw [h_body_cons, str_app, ByteArray.size_append]; omega)]
          rw [h_body_cons, str_app, ba_get!_append_left hj]
        -- Stop condition for xi (next byte is ',' or ']', both pass)
        have hxi_bound : q + 1 + (render xi).toUTF8.size ≤ buf.size := by
          have h_sz : body.toUTF8.size = (render xi).toUTF8.size + (commaPrefix rest_l).toUTF8.size := by
            rw [h_body_cons, str_app, ByteArray.size_append]
          omega
        have hstop_xi : q + 1 + (render xi).toUTF8.size = buf.size ∨
            (q + 1 + (render xi).toUTF8.size < buf.size ∧
             Ascii.isDigit buf[q + 1 + (render xi).toUTF8.size]! = false ∧
             buf[q + 1 + (render xi).toUTF8.size]! ≠ 46 ∧
             Ascii.isExp buf[q + 1 + (render xi).toUTF8.size]! = false) := by
          have hcp_size : body.toUTF8.size = (render xi).toUTF8.size + (commaPrefix rest_l).toUTF8.size := by
            rw [h_body_cons, str_app, ByteArray.size_append]
          have hpos_lt : q + 1 + (render xi).toUTF8.size < buf.size := by omega
          -- Determine the byte at the stop position
          have hbyte : buf[q + 1 + (render xi).toUTF8.size]! = 44 ∨
                       buf[q + 1 + (render xi).toUTF8.size]! = 93 := by
            rcases hrl : rest_l with _ | ⟨w, ws⟩
            · -- rest_l = []: stop pos = q+1+body.size, byte is ']' = 93
              right
              have : q + 1 + (render xi).toUTF8.size = q + 1 + body.toUTF8.size := by
                have : (commaPrefix ([] : List Json)).toUTF8.size = 0 := rfl
                rw [hrl] at hcp_size; simp only [this, Nat.add_zero] at hcp_size; omega
              rw [this]; exact hbyte_last
            · -- rest_l = w :: ws: byte is ',' = 44
              left
              have hconspos : 0 < (commaPrefix (w :: ws)).toUTF8.size := by
                rw [commaPrefix_cons_size]; omega
              have hbound_xi : (render xi).toUTF8.size < body.toUTF8.size := by
                rw [hrl] at hcp_size; omega
              rw [hmatch_body (render xi).toUTF8.size hbound_xi,
                  h_body_cons, hrl, str_app,
                  ba_get!_append_right (le_refl _)
                    (by rw [ByteArray.size_append]; rw [hrl] at hcp_size; omega),
                  Nat.sub_self]
              exact commaPrefix_byte_comma w ws
          rcases hbyte with h | h
          · right; exact ⟨hpos_lt, by rw [h]; decide, by rw [h]; decide, by rw [h]; decide⟩
          · right; exact ⟨hpos_lt, by rw [h]; decide, by rw [h]; decide, by rw [h]; decide⟩
        -- value parses xi
        have hxi_val := value_run_at xi buf (q + 1) hxi_bound hmatch_xi hstop_xi
        -- commaPrefix rest_l bytes
        have hcp_size : (render xi).toUTF8.size + (commaPrefix rest_l).toUTF8.size =
            body.toUTF8.size := by
          rw [h_body_cons, str_app, ByteArray.size_append]
        have hrest_bound : q + 1 + (render xi).toUTF8.size + (commaPrefix rest_l).toUTF8.size ≤
            buf.size := by omega
        have hrest_match : ∀ j, j < (commaPrefix rest_l).toUTF8.size →
            buf[q + 1 + (render xi).toUTF8.size + j]! = (commaPrefix rest_l).toUTF8[j]! := by
          intro j hj
          have hm := hmatch_body ((render xi).toUTF8.size + j) (by omega)
          rw [show q + 1 + ((render xi).toUTF8.size + j) = q + 1 + (render xi).toUTF8.size + j
              from by ring] at hm
          rw [hm, h_body_cons, str_app,
              ba_get!_append_right (by omega) (by rw [ByteArray.size_append]; omega),
              Nat.add_sub_cancel_left]
        have hrest_stop : q + 1 + (render xi).toUTF8.size + (commaPrefix rest_l).toUTF8.size =
            buf.size ∨
            (q + 1 + (render xi).toUTF8.size + (commaPrefix rest_l).toUTF8.size < buf.size ∧
             Ascii.isDigit buf[q + 1 + (render xi).toUTF8.size + (commaPrefix rest_l).toUTF8.size]! = false ∧
             buf[q + 1 + (render xi).toUTF8.size + (commaPrefix rest_l).toUTF8.size]! ≠ 46 ∧
             Ascii.isExp buf[q + 1 + (render xi).toUTF8.size + (commaPrefix rest_l).toUTF8.size]! = false) := by
          right
          have hpos_eq : q + 1 + (render xi).toUTF8.size + (commaPrefix rest_l).toUTF8.size =
              q + 1 + body.toUTF8.size := by omega
          rw [hpos_eq]
          exact ⟨hq1body_lt, by rw [hbyte_last]; decide, by rw [hbyte_last]; decide,
                              by rw [hbyte_last]; decide⟩
        have hrest_term : ∀ u r, (Grip.Json.wsByte Ascii.comma).run buf
            (q + 1 + (render xi).toUTF8.size + (commaPrefix rest_l).toUTF8.size) ≠ .ok u r := by
          intro u r heq
          have hpos_eq : q + 1 + (render xi).toUTF8.size + (commaPrefix rest_l).toUTF8.size =
              q + 1 + body.toUTF8.size := by omega
          rw [hpos_eq] at heq
          have hb : buf[q + 1 + body.toUTF8.size] = (93 : UInt8) := by
            rwa [← getElem!_pos buf _ hq1body_lt]
          have hws93 : Ascii.isWs (93 : UInt8) = false := by decide
          have hs : scanFwd buf Ascii.isWs (q + 1 + body.toUTF8.size) =
              q + 1 + body.toUTF8.size := by
            rw [scanFwd, dif_pos hq1body_lt, if_neg (by rw [hb, hws93]; decide)]
          have h93 : ((93 : UInt8) == Ascii.comma) = false := by decide
          simp only [Grip.Json.wsByte, hs, dif_pos hq1body_lt, hb, h93] at heq
          simp at heq
        -- h_vp: for each y ∈ rest_l, value parses y
        have hrest_vp : ∀ y ∈ rest_l, ∀ (p : Nat),
            p + (render y).toUTF8.size ≤ buf.size →
            (∀ j, j < (render y).toUTF8.size → buf[p + j]! = (render y).toUTF8[j]!) →
            (p + (render y).toUTF8.size = buf.size ∨
             p + (render y).toUTF8.size < buf.size ∧
               Ascii.isDigit buf[p + (render y).toUTF8.size]! = false ∧
               buf[p + (render y).toUTF8.size]! ≠ 46 ∧
               Ascii.isExp buf[p + (render y).toUTF8.size]! = false) →
            Grip.Json.value.run buf p = .ok y (p + (render y).toUTF8.size) := by
          intro y hy p hp hm hsp
          exact value_run_at y buf p hp hm hsp
        -- Apply foldFwd_comma_value_run
        rw [show q + 1 + body.toUTF8.size =
            q + 1 + (render xi).toUTF8.size + (commaPrefix rest_l).toUTF8.size from by omega]
        simp only [GParser.alt, GParser.bind, GParser.pure, hxi_val]
        simp only [GParser.foldMany]
        rw [foldFwd_comma_value_run rest_l buf #[xi] (q + 1 + (render xi).toUTF8.size)
            hrest_bound hrest_match hrest_stop hrest_term hrest_vp]
        simp only [ParseResult.ok.injEq]
        exact ⟨hxs_eq.symm, trivial⟩
    have harr_map := map_run_ok Json.arr _ buf (q + 1) xs
        (q + (render (Json.arr xs)).toUTF8.size - 1) harr_body
    have hseqL := seqL_run (GParser.map Json.arr _) (Grip.Json.wsByte Ascii.rbracket)
        buf (q + 1) (Json.arr xs) (q + (render (Json.arr xs)).toUTF8.size - 1) ()
        (q + (render (Json.arr xs)).toUTF8.size) harr_map hwsbr
    rw [value, fix_run_unroll]
    simp only [value_body]
    rw [wsDispatch_run_stop _ buf q hqlt hws_buf]
    simp only [Ascii.lbrace, Ascii.lbracket]
    have h_notbrace : ¬ ((buf[q] == (123 : UInt8)) = true) := by rw [hbufq]; decide
    have h_bracket  :   ((buf[q] == (91  : UInt8)) = true) := by rw [hbufq]; decide
    rw [if_neg h_notbrace, if_pos h_bracket]
    rw [seqR_run _ _ buf q () (q + 1) (Json.arr xs) _ hch hseqL]
    exact clampAdvance_ok buf q (by omega) (by omega)
  | .obj kvs, buf, q, hq, hmatch, hstop => by
    have hrend : render (Json.obj kvs) =
        "{" ++ joinWith ","
          (kvs.attach.toList.map (fun ⟨(k, j), _h⟩ =>
            "\"" ++ escape k ++ "\":" ++ render j)) ++ "}" := by
      simp [render]
    have hN2 : 2 ≤ (render (Json.obj kvs)).toUTF8.size := by
      rw [hrend, str_app, ByteArray.size_append, str_app, ByteArray.size_append]
      have h1 : ("{" : String).toUTF8.size = 1 := by decide
      have h2 : ("}" : String).toUTF8.size = 1 := by decide
      omega
    have hqlt : q < buf.size := by omega
    have hbufq! : buf[q]! = 123 := by
      have h0 := hmatch 0 (by omega)
      simp only [Nat.add_zero] at h0
      rw [h0, hrend]
      simp only [str_app]
      have h1 : ("{" : String).toUTF8.size = 1 := by decide
      rw [ba_get!_append_left (by simp only [ByteArray.size_append]; omega)]
      rw [ba_get!_append_left (by decide)]
      decide
    have hbufq : buf[q] = 123 := by rwa [← getElem!_pos buf q hqlt]
    have hws_buf : Ascii.isWs buf[q] = false := by rw [hbufq]; decide
    -- last byte of render obj is '}' = 125
    have hbufN! : buf[q + (render (Json.obj kvs)).toUTF8.size - 1]! = 125 := by
      have hNm := hmatch ((render (Json.obj kvs)).toUTF8.size - 1) (by omega)
      rw [show q + ((render (Json.obj kvs)).toUTF8.size - 1) =
          q + (render (Json.obj kvs)).toUTF8.size - 1 from by omega] at hNm
      rw [hNm, hrend]; exact lbrace_last_byte _
    have hN1lt : q + (render (Json.obj kvs)).toUTF8.size - 1 < buf.size := by omega
    have hbufN : buf[q + (render (Json.obj kvs)).toUTF8.size - 1] = 125 := by
      rwa [← getElem!_pos buf _ hN1lt]
    have hch : (GParser.ch '{').run buf q = .ok () (q + 1) :=
      byte_run! 123 buf q hqlt hbufq!
    -- ws after '{': render has no whitespace, so ws consumes 0 bytes
    have hws_step : (GParser.ws).run buf (q + 1) = .ok 0 (q + 1) := by
      simp only [GParser.ws]
      apply takeWhile_run
      · intro i hi; omega
      · right; refine ⟨by omega, ?_⟩
        -- buf[q+1] is '"' (non-empty obj) or '}' (empty obj); neither is whitespace
        simp only [Nat.add_zero]
        rw [hmatch 1 (by omega), hrend]
        -- helper: first byte of joinWith "," (s :: tail) = first byte of s
        have hjw0 : ∀ (s : String) (tail : List String),
            0 < s.toUTF8.size →
            (joinWith "," (s :: tail)).toUTF8[0]! = s.toUTF8[0]! := by
          intro s tail hs
          cases tail with
          | nil => simp [joinWith]
          | cons t more =>
            simp only [joinWith]
            rw [String.append_assoc, str_app, ba_get!_append_left hs]
        rcases kvs.attach.toList with _ | ⟨⟨⟨k0, v0⟩, _⟩, rest⟩
        · simp only [List.map_nil, joinWith]; decide
        · simp only [List.map_cons]
          set e0 := "\"" ++ escape k0 ++ "\":" ++ render v0
          have he0_pos : 0 < e0.toUTF8.size := by
            simp only [e0, str_app, ByteArray.size_append]
            have : ("\"" : String).toUTF8.size = 1 := by decide
            omega
          have hbody_pos : 0 < (joinWith ","
              (e0 :: rest.map (fun ⟨(k, j), _h⟩ => "\"" ++ escape k ++ "\":" ++ render j))).toUTF8.size := by
            cases rest.map (fun ⟨(k, j), _h⟩ => "\"" ++ escape k ++ "\":" ++ render j) with
            | nil =>
              simp only [joinWith]
              have hc : (",":String).toUTF8.size = 1 := by decide
              have he : ("":String).toUTF8.size = 0 := by decide
              omega
            | cons e1 more => simp only [joinWith, str_app, ByteArray.size_append]; omega
          rw [body_byte_j "{" "}" (by decide) _ 0 hbody_pos,
              hjw0 e0 _ he0_pos]
          simp only [e0, String.append_assoc]
          rw [str_prepend_byte0]; decide
    have hwsbr : (Grip.Json.wsByte Ascii.rbrace).run buf
        (q + (render (Json.obj kvs)).toUTF8.size - 1) =
        .ok () (q + (render (Json.obj kvs)).toUTF8.size) := by
      convert wsByte_run_stop Ascii.rbrace buf _ hN1lt (by rw [hbufN]; decide) (by rw [hbufN]; rfl) using 2
      omega
    -- objectBody parses kvs
    have hobj_body : (GParser.alt
        (GParser.bind
          (GParser.map2 (fun k v => (k, v)) Grip.Json.jstr
            (GParser.seqR (Grip.Json.wsByte Ascii.colon)
              (GParser.fixSelf Grip.Json.value_body (buf.size - q))))
          (fun p => GParser.foldMany (fun a x => a.push x) #[p]
            (GParser.seqR (Grip.Json.wsByte Ascii.comma)
              (GParser.seqR GParser.ws
                (GParser.map2 (fun k v => (k, v)) Grip.Json.jstr
                  (GParser.seqR (Grip.Json.wsByte Ascii.colon)
                    (GParser.fixSelf Grip.Json.value_body (buf.size - q))))))))
        (GParser.pure #[])).run buf (q + 1) =
        .ok kvs (q + (render (Json.obj kvs)).toUTF8.size - 1) := by
      have h_agree := objectBody_agree
          (GParser.fixSelf Grip.Json.value_body (buf.size - q)) Grip.Json.value buf q (q + 1)
          (by omega) (fun q' hq' => fixSelf_eq_value_of_gt buf q q' hq')
      suffices h_val : (GParser.alt
          (GParser.bind
            (GParser.map2 (fun k v => (k, v)) Grip.Json.jstr
              (GParser.seqR (Grip.Json.wsByte Ascii.colon) Grip.Json.value))
            (fun p => GParser.foldMany (fun a x => a.push x) #[p]
              (GParser.seqR (Grip.Json.wsByte Ascii.comma)
                (GParser.seqR GParser.ws
                  (GParser.map2 (fun k v => (k, v)) Grip.Json.jstr
                    (GParser.seqR (Grip.Json.wsByte Ascii.colon) Grip.Json.value))))))
          (GParser.pure #[])).run buf (q + 1) =
          .ok kvs (q + (render (Json.obj kvs)).toUTF8.size - 1) by
        rcases h_fix : (GParser.alt
            (GParser.bind
              (GParser.map2 (fun k v => (k, v)) Grip.Json.jstr
                (GParser.seqR (Grip.Json.wsByte Ascii.colon)
                  (GParser.fixSelf Grip.Json.value_body (buf.size - q))))
              (fun p => GParser.foldMany (fun a x => a.push x) #[p]
                (GParser.seqR (Grip.Json.wsByte Ascii.comma)
                  (GParser.seqR GParser.ws
                    (GParser.map2 (fun k v => (k, v)) Grip.Json.jstr
                      (GParser.seqR (Grip.Json.wsByte Ascii.colon)
                        (GParser.fixSelf Grip.Json.value_body (buf.size - q))))))))
            (GParser.pure #[])).run buf (q + 1) with ⟨kvs', q'⟩ | e
        · rw [h_fix, h_val] at h_agree
          simp only [AgreeOk] at h_agree; obtain ⟨rfl, rfl⟩ := h_agree; rfl
        · rw [h_fix, h_val] at h_agree; exact absurd h_agree (by simp [AgreeOk])
      -- Simplify attach.toList.map to kvs.toList.map renderKV
      have hatt_renderKV : kvs.attach.toList.map (fun ⟨(k, j), _h⟩ => "\"" ++ escape k ++ "\":" ++ render j)
          = kvs.toList.map renderKV := by
        have hmap_eq : kvs.attach.toList.map (fun ⟨(k, j), _h⟩ => "\"" ++ escape k ++ "\":" ++ render j) =
            kvs.attach.toList.map (fun x : {x : String × Json // x ∈ kvs} => renderKV x) :=
          List.map_congr_left (fun ⟨⟨k, j⟩, _⟩ _ => by
            simp [renderKV, render, show ("\":" : String) = "\"" ++ ":" from by decide,
                  String.append_assoc])
        rw [hmap_eq, Array.toList_attach, List.attachWith_map_val]
      set body := joinWith "," (kvs.toList.map renderKV) with h_body_def
      have hbody_eq : joinWith "," (kvs.attach.toList.map (fun ⟨(k, j), _h⟩ =>
          "\"" ++ escape k ++ "\":" ++ render j)) = body := by rw [hatt_renderKV]
      have hbody_size : (render (Json.obj kvs)).toUTF8.size = 1 + body.toUTF8.size + 1 := by
        rw [hrend, hbody_eq, str_app, ByteArray.size_append, str_app, ByteArray.size_append]
        simp only [show ("{":String).toUTF8.size = 1 from by decide,
                   show ("}":String).toUTF8.size = 1 from by decide]
      have hend : q + (render (Json.obj kvs)).toUTF8.size - 1 = q + 1 + body.toUTF8.size := by omega
      rw [hend]
      have hmatch_body : ∀ j, j < body.toUTF8.size → buf[q + 1 + j]! = body.toUTF8[j]! := by
        intro j hj
        have h := hmatch (1 + j) (by rw [hbody_size]; omega)
        rw [show q + (1 + j) = q + 1 + j from by ring] at h
        rw [h, hrend, hbody_eq]; exact body_byte_j "{" "}" (by decide) body j hj
      have hbyte_last : buf[q + 1 + body.toUTF8.size]! = 125 := by rw [← hend]; exact hbufN!
      have hq1body_lt : q + 1 + body.toUTF8.size < buf.size := by omega
      -- Case on kvs.toList
      rcases hkvl : kvs.toList with _ | ⟨⟨k0, v0⟩, rest_kvs⟩
      · -- Empty kvs: pure #[] branch
        have hkvs_empty : kvs = #[] := by apply Array.ext'; simp [← hkvl]
        have hbody_empty : body.toUTF8.size = 0 := by
          rw [h_body_def, hkvl, List.map_nil, joinWith]; rfl
        subst hkvs_empty
        simp only [hbody_empty, Nat.add_zero]
        have hq1lt : q + 1 < buf.size := by omega
        have hbuf1 : buf[q + 1] = (125 : UInt8) := by
          have h := hbyte_last; rw [hbody_empty, Nat.add_zero] at h
          rw [← getElem!_pos buf _ hq1lt]; exact h
        obtain ⟨e, hjstr_err⟩ : ∃ e, Grip.Json.jstr.run buf (q + 1) = .error e := by
          simp only [Grip.Json.jstr]; rw [dif_pos hq1lt]
          have hne34 : ¬ (buf[q + 1] == (34 : UInt8)) = true := by rw [hbuf1]; decide
          rw [if_neg hne34]; exact ⟨_, rfl⟩
        simp only [GParser.alt, GParser.bind, GParser.pure, GParser.map2, GParser.seqR]
        simp only [hjstr_err]
      · -- Non-empty: kvs.toList = (k0, v0) :: rest_kvs
        have h_body_cons : body = renderKV (k0, v0) ++ commaPrefixKV rest_kvs := by
          rw [h_body_def, hkvl]; exact joinWith_map_renderKV_eq (k0, v0) rest_kvs
        have hkvs_eq : kvs = #[(k0, v0)] ++ rest_kvs.toArray := by
          apply Array.ext'; simp [hkvl]
        have hrkv_size : (renderKV (k0, v0)).toUTF8.size =
            2 + (ebytes k0.toList).length + 1 + (render v0).toUTF8.size :=
          renderKV_size k0 v0
        have hsk_size : (render (.str k0)).toUTF8.size = 2 + (ebytes k0.toList).length :=
          render_str_size k0
        have hbody_sz : body.toUTF8.size =
            (renderKV (k0, v0)).toUTF8.size + (commaPrefixKV rest_kvs).toUTF8.size := by
          rw [h_body_cons, str_app, ByteArray.size_append]
        -- Bytes of renderKV (k0, v0) at buf[q+1+j]
        have hmatch_kv : ∀ j, j < (renderKV (k0, v0)).toUTF8.size →
            buf[q + 1 + j]! = (renderKV (k0, v0)).toUTF8[j]! := by
          intro j hj
          rw [hmatch_body j (by omega), h_body_cons, str_app, ba_get!_append_left hj]
        have hkv_bound : q + 1 + (renderKV (k0, v0)).toUTF8.size ≤ buf.size := by omega
        -- buf[q+1]! = 34 (opening quote)
        have hq1_byte! : buf[q + 1]! = 34 := by
          rw [hmatch_kv 0 (by rw [hrkv_size]; omega)]; exact renderKV_byte0 (k0, v0)
        -- Key body bytes
        have hcontent_k : ∀ j, j < (ebytes k0.toList).length →
            buf[q + 1 + 1 + j]! = (ebytes k0.toList)[j]! := by
          intro j hj
          rw [show q + 1 + 1 + j = q + 1 + (1 + j) from by ring,
              hmatch_kv (1 + j) (by rw [hrkv_size]; omega)]
          simp only [renderKV, str_app]
          rw [ba_get!_append_left (by rw [ByteArray.size_append, hsk_size]; omega)]
          rw [ba_get!_append_left (by rw [hsk_size]; omega)]
          exact render_str_byte_mid k0 j hj
        -- Closing quote
        have hclose_k : buf[q + 1 + 1 + (ebytes k0.toList).length]! = 34 := by
          rw [show q + 1 + 1 + (ebytes k0.toList).length =
              q + 1 + (1 + (ebytes k0.toList).length) from by ring,
              hmatch_kv (1 + (ebytes k0.toList).length) (by rw [hrkv_size]; omega)]
          simp only [renderKV, str_app]
          rw [ba_get!_append_left (by rw [ByteArray.size_append, hsk_size]; omega)]
          rw [ba_get!_append_left (by rw [hsk_size]; omega)]
          exact render_str_byte_close k0
        -- jstr bound and parse
        have hjstr_bound : q + 1 + 1 + (ebytes k0.toList).length < buf.size := by
          rw [hrkv_size] at hkv_bound; omega
        have hjstr_ok : Grip.Json.jstr.run buf (q + 1) =
            .ok k0 (q + 1 + 1 + (ebytes k0.toList).length + 1) :=
          jstr_run buf (q + 1) k0 hjstr_bound hq1_byte! hcontent_k hclose_k
        -- Colon position: q + 1 + 2 + (ebytes k0.toList).length
        have hcolon_pos_lt : q + 1 + 2 + (ebytes k0.toList).length < buf.size := by
          rw [hrkv_size] at hkv_bound; omega
        have hcolon_byte! : buf[q + 1 + 2 + (ebytes k0.toList).length]! = 58 := by
          rw [show q + 1 + 2 + (ebytes k0.toList).length =
              q + 1 + (2 + (ebytes k0.toList).length) from by ring,
              hmatch_kv (2 + (ebytes k0.toList).length) (by rw [hrkv_size]; omega)]
          simp only [renderKV, str_app]
          have hc0 : (":":String).toUTF8.size = 1 := by decide
          rw [ba_get!_append_left (by rw [ByteArray.size_append, hsk_size, hc0]; omega)]
          rw [ba_get!_append_right (by omega) (by rw [ByteArray.size_append, hsk_size, hc0]; omega)]
          rw [hsk_size, Nat.sub_self]
          decide
        have hcolon_byte : buf[q + 1 + 2 + (ebytes k0.toList).length] = (58 : UInt8) := by
          rwa [← getElem!_pos buf _ hcolon_pos_lt]
        have hcolon_ws : Ascii.isWs buf[q + 1 + 2 + (ebytes k0.toList).length] = false := by
          rw [hcolon_byte]; decide
        -- wsByte colon succeeds
        have hwscolon : (Grip.Json.wsByte Ascii.colon).run buf (q + 1 + 2 + (ebytes k0.toList).length) =
            .ok () (q + 1 + 2 + (ebytes k0.toList).length + 1) :=
          wsByte_run_stop Ascii.colon buf _ hcolon_pos_lt hcolon_ws (by rw [hcolon_byte]; rfl)
        -- Value bytes at q + 1 + 3 + (ebytes k0.toList).length
        have hv0_start : q + 1 + 2 + (ebytes k0.toList).length + 1 =
            q + 1 + (2 + (ebytes k0.toList).length + 1) := by ring
        have hv0_bound : q + 1 + 2 + (ebytes k0.toList).length + 1 + (render v0).toUTF8.size ≤ buf.size := by
          rw [hrkv_size] at hkv_bound; omega
        have hmatch_v0 : ∀ j, j < (render v0).toUTF8.size →
            buf[q + 1 + 2 + (ebytes k0.toList).length + 1 + j]! = (render v0).toUTF8[j]! := by
          intro j hj
          rw [show q + 1 + 2 + (ebytes k0.toList).length + 1 + j =
              q + 1 + (2 + (ebytes k0.toList).length + 1 + j) from by ring,
              hmatch_kv (2 + (ebytes k0.toList).length + 1 + j) (by rw [hrkv_size]; omega)]
          simp only [renderKV, str_app]
          have hc0 : (":":String).toUTF8.size = 1 := by decide
          rw [ba_get!_append_right (by rw [ByteArray.size_append, hsk_size, hc0]; omega)
                                   (by rw [ByteArray.size_append, ByteArray.size_append, hsk_size, hc0]; omega)]
          congr 1
          rw [ByteArray.size_append, hsk_size, hc0]
          omega
        -- Stop condition for v0 (next byte is ',' or '}', not digit/dot/exp)
        have hstop_v0 : q + 1 + 2 + (ebytes k0.toList).length + 1 + (render v0).toUTF8.size =
            buf.size ∨
            (q + 1 + 2 + (ebytes k0.toList).length + 1 + (render v0).toUTF8.size < buf.size ∧
             Ascii.isDigit buf[q + 1 + 2 + (ebytes k0.toList).length + 1 + (render v0).toUTF8.size]! = false ∧
             buf[q + 1 + 2 + (ebytes k0.toList).length + 1 + (render v0).toUTF8.size]! ≠ 46 ∧
             Ascii.isExp buf[q + 1 + 2 + (ebytes k0.toList).length + 1 + (render v0).toUTF8.size]! = false) := by
          have hpos_eq : q + 1 + 2 + (ebytes k0.toList).length + 1 + (render v0).toUTF8.size =
              q + 1 + (renderKV (k0, v0)).toUTF8.size := by rw [hrkv_size]; ring
          have hpos_lt : q + 1 + 2 + (ebytes k0.toList).length + 1 + (render v0).toUTF8.size < buf.size := by
            omega
          have hbyte_after : buf[q + 1 + 2 + (ebytes k0.toList).length + 1 + (render v0).toUTF8.size]! =
              44 ∨ buf[q + 1 + 2 + (ebytes k0.toList).length + 1 + (render v0).toUTF8.size]! = 125 := by
            rcases hrest : rest_kvs with _ | ⟨kv2, rest2⟩
            · -- rest_kvs = []: byte is '}' (125)
              right; rw [hpos_eq]
              have : q + 1 + (renderKV (k0, v0)).toUTF8.size = q + 1 + body.toUTF8.size := by
                rw [hbody_sz, hrest, commaPrefixKV]; simp
              rw [this]; exact hbyte_last
            · -- rest_kvs non-empty: byte is ',' (44)
              left; rw [hpos_eq]
              have hcp_pos : 0 < (commaPrefixKV rest_kvs).toUTF8.size := by
                rw [hrest, commaPrefixKV_cons_size]; omega
              rw [hmatch_body (renderKV (k0, v0)).toUTF8.size (by rw [hbody_sz]; omega),
                  h_body_cons, str_app,
                  ba_get!_append_right (le_refl _) (by rw [ByteArray.size_append]; omega),
                  Nat.sub_self, hrest]
              exact commaPrefixKV_byte_comma kv2 rest2
          rcases hbyte_after with h | h
          · right; exact ⟨hpos_lt, by rw [h]; decide, by rw [h]; decide, by rw [h]; decide⟩
          · right; exact ⟨hpos_lt, by rw [h]; decide, by rw [h]; decide, by rw [h]; decide⟩
        -- value parses v0
        have hv0_val := value_run_at v0 buf (q + 1 + 2 + (ebytes k0.toList).length + 1)
            hv0_bound hmatch_v0 hstop_v0
        -- map2 jstr (seqR colon value) parses (k0, v0)
        have hkv0_val : (GParser.map2 (fun k v => (k, v)) Grip.Json.jstr
            (GParser.seqR (Grip.Json.wsByte Ascii.colon) Grip.Json.value)).run buf (q + 1) =
            .ok (k0, v0) (q + 1 + (renderKV (k0, v0)).toUTF8.size) := by
          have hq1_lt_buf : q + 1 + 1 + (ebytes k0.toList).length + 1 ≤ buf.size := by omega
          rw [show q + 1 + (renderKV (k0, v0)).toUTF8.size =
              q + 1 + 2 + (ebytes k0.toList).length + 1 + (render v0).toUTF8.size from by
            rw [hrkv_size]; ring]
          have h_seqR := seqR_run (Grip.Json.wsByte Ascii.colon) Grip.Json.value
              buf (q + 1 + 2 + (ebytes k0.toList).length)
              () (q + 1 + 2 + (ebytes k0.toList).length + 1)
              v0 _ hwscolon hv0_val
          exact map2_run (fun k v => (k, v)) Grip.Json.jstr
              (GParser.seqR (Grip.Json.wsByte Ascii.colon) Grip.Json.value)
              buf (q + 1) k0 (q + 1 + 2 + (ebytes k0.toList).length) v0 _
              (by convert hjstr_ok using 2; ring) h_seqR
        -- commaPrefixKV rest_kvs bytes
        have hcp_bound :
            (q + 1 + (renderKV (k0, v0)).toUTF8.size) + (commaPrefixKV rest_kvs).toUTF8.size ≤ buf.size :=
          by omega
        have hmatch_cp : ∀ j, j < (commaPrefixKV rest_kvs).toUTF8.size →
            buf[(q + 1 + (renderKV (k0, v0)).toUTF8.size) + j]! = (commaPrefixKV rest_kvs).toUTF8[j]! := by
          intro j hj
          rw [show (q + 1 + (renderKV (k0, v0)).toUTF8.size) + j = q + 1 + ((renderKV (k0, v0)).toUTF8.size + j) from by ring]
          rw [hmatch_body ((renderKV (k0, v0)).toUTF8.size + j) (by omega)]
          rw [h_body_cons, str_app,
              ba_get!_append_right (by omega) (by rw [ByteArray.size_append]; omega),
              Nat.add_sub_cancel_left]
        have hcp_term : ∀ u r, (Grip.Json.wsByte Ascii.comma).run buf
            ((q + 1 + (renderKV (k0, v0)).toUTF8.size) + (commaPrefixKV rest_kvs).toUTF8.size) ≠ .ok u r := by
          intro u r heq
          have hpos_eq : (q + 1 + (renderKV (k0, v0)).toUTF8.size) + (commaPrefixKV rest_kvs).toUTF8.size =
              q + 1 + body.toUTF8.size := by omega
          rw [hpos_eq] at heq
          have hb : buf[q + 1 + body.toUTF8.size] = (125 : UInt8) := by
            rwa [← getElem!_pos buf _ hq1body_lt]
          have hs : scanFwd buf Ascii.isWs (q + 1 + body.toUTF8.size) = q + 1 + body.toUTF8.size := by
            rw [scanFwd, dif_pos hq1body_lt, if_neg (by rw [hb]; decide)]
          have h125 : ((125 : UInt8) == Ascii.comma) = false := by decide
          simp only [Grip.Json.wsByte, hs, dif_pos hq1body_lt, hb, h125] at heq
          simp at heq
        -- h_kvp: for each kv2 ∈ rest_kvs, (map2 jstr (seqR colon value)) parses kv2
        have h_kvp : ∀ kv2 ∈ rest_kvs, ∀ (p : Nat),
            p + (renderKV kv2).toUTF8.size ≤ buf.size →
            (∀ j, j < (renderKV kv2).toUTF8.size → buf[p + j]! = (renderKV kv2).toUTF8[j]!) →
            (p + (renderKV kv2).toUTF8.size = buf.size ∨
             (p + (renderKV kv2).toUTF8.size < buf.size ∧
              Ascii.isDigit buf[p + (renderKV kv2).toUTF8.size]! = false ∧
              buf[p + (renderKV kv2).toUTF8.size]! ≠ 46 ∧
              Ascii.isExp buf[p + (renderKV kv2).toUTF8.size]! = false)) →
            (GParser.map2 (fun k v => (k, v)) Grip.Json.jstr
              (GParser.seqR (Grip.Json.wsByte Ascii.colon) Grip.Json.value)).run buf p =
              .ok kv2 (p + (renderKV kv2).toUTF8.size) := by
          intro ⟨k2, v2⟩ hkv2 p hp hmatch2 hstop_kv2
          have hrk2 : renderKV (k2, v2) = render (.str k2) ++ ":" ++ render v2 := rfl
          have hsk2 : (render (.str k2)).toUTF8.size = 2 + (ebytes k2.toList).length := render_str_size k2
          have hrk2_size : (renderKV (k2, v2)).toUTF8.size = 2 + (ebytes k2.toList).length + 1 + (render v2).toUTF8.size :=
            renderKV_size k2 v2
          have hq2! : p + (2 + (ebytes k2.toList).length + 1 + (render v2).toUTF8.size) ≤ buf.size := by
            rwa [← hrk2_size]
          have hbound2 : p + 1 + (ebytes k2.toList).length < buf.size := by omega
          have h34_2 : buf[p]! = 34 := by
            have h := hmatch2 0 (by rw [hrk2_size]; omega)
            simp only [Nat.add_zero] at h
            rw [h]; exact renderKV_byte0 (k2, v2)
          have hcont2 : ∀ j, j < (ebytes k2.toList).length → buf[p + 1 + j]! = (ebytes k2.toList)[j]! := by
            intro j hj
            rw [show p + 1 + j = p + (1 + j) from by ring,
                hmatch2 (1 + j) (by rw [hrk2_size]; omega)]
            simp only [renderKV, str_app]
            rw [ba_get!_append_left (by rw [ByteArray.size_append, hsk2]; omega)]
            rw [ba_get!_append_left (by rw [hsk2]; omega)]
            exact render_str_byte_mid k2 j hj
          have hclose2 : buf[p + 1 + (ebytes k2.toList).length]! = 34 := by
            rw [show p + 1 + (ebytes k2.toList).length = p + (1 + (ebytes k2.toList).length) from by ring,
                hmatch2 (1 + (ebytes k2.toList).length) (by rw [hrk2_size]; omega)]
            simp only [renderKV, str_app]
            rw [ba_get!_append_left (by rw [ByteArray.size_append, hsk2]; omega)]
            rw [ba_get!_append_left (by rw [hsk2]; omega)]
            exact render_str_byte_close k2
          have hjstr2 : Grip.Json.jstr.run buf p = .ok k2 (p + 1 + (ebytes k2.toList).length + 1) :=
            jstr_run buf p k2 hbound2 h34_2 hcont2 hclose2
          have hcolon2_lt : p + 2 + (ebytes k2.toList).length < buf.size := by omega
          have hcolon2! : buf[p + 2 + (ebytes k2.toList).length]! = 58 := by
            rw [show p + 2 + (ebytes k2.toList).length = p + (2 + (ebytes k2.toList).length) from by ring,
                hmatch2 (2 + (ebytes k2.toList).length) (by rw [hrk2_size]; omega)]
            simp only [renderKV, str_app]
            have hc2 : (":":String).toUTF8.size = 1 := by decide
            rw [ba_get!_append_left (by rw [ByteArray.size_append, hsk2, hc2]; omega)]
            rw [ba_get!_append_right (by omega) (by rw [ByteArray.size_append, hsk2, hc2]; omega)]
            rw [hsk2, Nat.sub_self]
            decide
          have hcolon2 : buf[p + 2 + (ebytes k2.toList).length] = (58 : UInt8) := by
            rwa [← getElem!_pos buf _ hcolon2_lt]
          have hwscolon2 : (Grip.Json.wsByte Ascii.colon).run buf (p + 2 + (ebytes k2.toList).length) =
              .ok () (p + 2 + (ebytes k2.toList).length + 1) :=
            wsByte_run_stop Ascii.colon buf _ hcolon2_lt (by rw [hcolon2]; decide) (by rw [hcolon2]; rfl)
          have hv2_bound : p + 2 + (ebytes k2.toList).length + 1 + (render v2).toUTF8.size ≤ buf.size := by
            omega
          have hmatch_v2 : ∀ j, j < (render v2).toUTF8.size →
              buf[p + 2 + (ebytes k2.toList).length + 1 + j]! = (render v2).toUTF8[j]! := by
            intro j hj
            rw [show p + 2 + (ebytes k2.toList).length + 1 + j =
                p + (2 + (ebytes k2.toList).length + 1 + j) from by ring,
                hmatch2 (2 + (ebytes k2.toList).length + 1 + j) (by rw [hrk2_size]; omega)]
            simp only [renderKV, str_app]
            have hc2 : (":":String).toUTF8.size = 1 := by decide
            rw [ba_get!_append_right (by rw [ByteArray.size_append, hsk2, hc2]; omega)
                                     (by rw [ByteArray.size_append, ByteArray.size_append, hsk2, hc2]; omega)]
            congr 1
            rw [ByteArray.size_append, hsk2, hc2]
            omega
          have hstop_v2 : p + 2 + (ebytes k2.toList).length + 1 + (render v2).toUTF8.size = buf.size ∨
              (p + 2 + (ebytes k2.toList).length + 1 + (render v2).toUTF8.size < buf.size ∧
               Ascii.isDigit buf[p + 2 + (ebytes k2.toList).length + 1 + (render v2).toUTF8.size]! = false ∧
               buf[p + 2 + (ebytes k2.toList).length + 1 + (render v2).toUTF8.size]! ≠ 46 ∧
               Ascii.isExp buf[p + 2 + (ebytes k2.toList).length + 1 + (render v2).toUTF8.size]! = false) := by
            rw [show p + 2 + (ebytes k2.toList).length + 1 + (render v2).toUTF8.size =
                p + (renderKV (k2, v2)).toUTF8.size from by rw [hrk2_size]; ring]
            exact hstop_kv2
          have hv2_val := value_run_at v2 buf (p + 2 + (ebytes k2.toList).length + 1)
              hv2_bound hmatch_v2 hstop_v2
          rw [show p + (renderKV (k2, v2)).toUTF8.size =
              p + 2 + (ebytes k2.toList).length + 1 + (render v2).toUTF8.size from by
            rw [hrk2_size]; ring]
          have h_seqR2 := seqR_run (Grip.Json.wsByte Ascii.colon) Grip.Json.value
              buf (p + 2 + (ebytes k2.toList).length)
              () (p + 2 + (ebytes k2.toList).length + 1)
              v2 _ hwscolon2 hv2_val
          exact map2_run (fun k v => (k, v)) Grip.Json.jstr
              (GParser.seqR (Grip.Json.wsByte Ascii.colon) Grip.Json.value)
              buf p k2 (p + 2 + (ebytes k2.toList).length) v2 _
              (by convert hjstr2 using 2; ring) h_seqR2
        -- Apply foldFwd_comma_kv_run
        rw [show q + 1 + body.toUTF8.size =
            (q + 1 + (renderKV (k0, v0)).toUTF8.size) + (commaPrefixKV rest_kvs).toUTF8.size from by omega]
        simp only [GParser.alt, GParser.bind, GParser.pure, hkv0_val]
        simp only [GParser.foldMany]
        -- h_stop_cond for foldFwd: byte after commaPrefixKV rest_kvs is '}' = 125
        have hfold_stop_cond : (q + 1 + (renderKV (k0, v0)).toUTF8.size) + (commaPrefixKV rest_kvs).toUTF8.size = buf.size ∨
            ((q + 1 + (renderKV (k0, v0)).toUTF8.size) + (commaPrefixKV rest_kvs).toUTF8.size < buf.size ∧
             Ascii.isDigit buf[(q + 1 + (renderKV (k0, v0)).toUTF8.size) + (commaPrefixKV rest_kvs).toUTF8.size]! = false ∧
             buf[(q + 1 + (renderKV (k0, v0)).toUTF8.size) + (commaPrefixKV rest_kvs).toUTF8.size]! ≠ 46 ∧
             Ascii.isExp buf[(q + 1 + (renderKV (k0, v0)).toUTF8.size) + (commaPrefixKV rest_kvs).toUTF8.size]! = false) :=
          Or.inr ⟨by omega,
            by rw [show (q + 1 + (renderKV (k0, v0)).toUTF8.size) + (commaPrefixKV rest_kvs).toUTF8.size =
                q + 1 + body.toUTF8.size from by omega, hbyte_last]; decide,
            by rw [show (q + 1 + (renderKV (k0, v0)).toUTF8.size) + (commaPrefixKV rest_kvs).toUTF8.size =
                q + 1 + body.toUTF8.size from by omega, hbyte_last]; decide,
            by rw [show (q + 1 + (renderKV (k0, v0)).toUTF8.size) + (commaPrefixKV rest_kvs).toUTF8.size =
                q + 1 + body.toUTF8.size from by omega, hbyte_last]; decide⟩
        rw [foldFwd_comma_kv_run
            (GParser.map2 (fun k v => (k, v)) Grip.Json.jstr
              (GParser.seqR (Grip.Json.wsByte Ascii.colon) Grip.Json.value))
            rest_kvs buf #[(k0, v0)] (q + 1 + (renderKV (k0, v0)).toUTF8.size)
            hcp_bound hmatch_cp hfold_stop_cond hcp_term h_kvp]
        simp only [ParseResult.ok.injEq]
        exact ⟨hkvs_eq.symm, trivial⟩
    have hobj_map := map_run_ok Json.obj _ buf (q + 1) kvs
        (q + (render (Json.obj kvs)).toUTF8.size - 1) hobj_body
    have hseqL_ob := seqL_run (GParser.map Json.obj _) (Grip.Json.wsByte Ascii.rbrace)
        buf (q + 1) (Json.obj kvs) (q + (render (Json.obj kvs)).toUTF8.size - 1) ()
        (q + (render (Json.obj kvs)).toUTF8.size) hobj_map hwsbr
    have hseqR_ws := seqR_run GParser.ws _ buf (q + 1) 0 (q + 1)
        (Json.obj kvs) (q + (render (Json.obj kvs)).toUTF8.size) hws_step hseqL_ob
    rw [value, fix_run_unroll]
    simp only [value_body]
    rw [wsDispatch_run_stop _ buf q hqlt hws_buf]
    simp only [Ascii.lbrace]
    have h_brace : ((buf[q] == (123 : UInt8)) = true) := by rw [hbufq]; decide
    rw [if_pos h_brace]
    rw [seqR_run _ _ buf q () (q + 1) (Json.obj kvs) _ hch hseqR_ws]
    exact clampAdvance_ok buf q (by omega) (by omega)
termination_by v => sizeOf v
decreasing_by
  · -- arr case xi: xi ∈ xs.toList, hence sizeOf xi < sizeOf (arr xs)
    have hxi_xs : xi ∈ xs := Array.mem_toList_iff.mp (hxl ▸ List.mem_cons.mpr (Or.inl rfl))
    have := Array.sizeOf_lt_of_mem hxi_xs; simp_wf; omega
  · -- arr case y: y ∈ rest_l ⊆ xs.toList, hence sizeOf y < sizeOf (arr xs)
    have hy_xs : y ∈ xs := Array.mem_toList_iff.mp (hxl ▸ List.mem_cons.mpr (Or.inr hy))
    have := Array.sizeOf_lt_of_mem hy_xs; simp_wf; omega
  · -- obj case v0: (k0, v0) is head of kvs.toList, so sizeOf v0 < sizeOf (obj kvs)
    have hkv0_kvs : (k0, v0) ∈ kvs :=
      Array.mem_toList_iff.mp (hkvl ▸ List.mem_cons.mpr (Or.inl rfl))
    have h1 := Array.sizeOf_lt_of_mem hkv0_kvs
    have h2 : sizeOf v0 < sizeOf (k0, v0) := by
      have := @Prod.mk.sizeOf_spec _ _ _ _ k0 v0; omega
    simp_wf; omega
  · -- obj case v2: (k2, v2) ∈ rest_kvs ⊆ kvs.toList, so sizeOf v2 < sizeOf (obj kvs)
    have hkv2_kvs : (k2, v2) ∈ kvs :=
      Array.mem_toList_iff.mp (hkvl ▸ List.mem_cons.mpr (Or.inr hkv2))
    have h1 := Array.sizeOf_lt_of_mem hkv2_kvs
    have h2 : sizeOf v2 < sizeOf (k2, v2) := by
      have := @Prod.mk.sizeOf_spec _ _ _ _ k2 v2; omega
    simp_wf; omega

-- ---------------------------------------------------------------------------
-- 6. parse_render: parse (render v) = ok v for all v
-- ---------------------------------------------------------------------------

/-- Round-trip: parsing the rendering of any JSON value returns that value. -/
theorem parse_render (v : Json) :
    Grip.Json.parse (render v).toUTF8 = .ok v := by
  simp only [Grip.Json.parse, Grip.Json.parser, GParser.parse]
  let arr := (render v).toUTF8
  have hval : Grip.Json.value.run arr 0 = .ok v arr.size := by
    have h := value_run_at v arr 0 (by simp [arr])
        (by intro i hi; simp only [arr, Nat.zero_add]) (Or.inl (by simp [arr]))
    simpa [arr] using h
  have hws : (GParser.ws).run arr arr.size = .ok 0 arr.size :=
    ws_run_end arr arr.size (le_refl _)
  have heof : (GParser.eof).run arr arr.size = .ok () arr.size :=
    eof_run_end arr arr.size (le_refl _)
  rw [seqL_run _ _ arr 0 v arr.size () arr.size hval
    (seqR_run _ _ arr arr.size 0 arr.size () arr.size hws heof)]

end GripProps.Container
