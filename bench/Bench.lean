/-
Copyright (c) 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides
-/
import Sexp
import Lambda
import Http
import Toml
import Yaml

/-! # grip core benchmark harness

This benchmark exercises the core byte parser through the non-JSON example grammars. The JSON
workload, including the core Grip validator row and DOM comparisons, lives in `lean-grip-json`.
-/

partial def repeatStr (s : String) (n : Nat) : String :=
  if n == 0 then ""
  else if n == 1 then s
  else
    let half := repeatStr s (n / 2)
    let doubled := half ++ half
    if n % 2 == 0 then doubled else doubled ++ s

@[noinline] def parseSexp (arr : ByteArray) : Nat :=
  match Grip.Examples.Sexp.parse arr with
  | some (.list xs) => xs.length
  | some _          => 1
  | none            => 0

@[noinline] def parseLambda (arr : ByteArray) : Nat :=
  match Grip.Examples.Lambda.parse arr with
  | some _ => 1
  | none   => 0

@[noinline] def parseHttp (arr : ByteArray) : Nat :=
  match Grip.Examples.Http.parse arr with
  | some r => r.headers.length
  | none   => 0

@[noinline] def parseToml (arr : ByteArray) : Nat :=
  match Grip.Examples.Toml.parse arr with
  | some d => d.tables.length
  | none   => 0

@[noinline] def parseYaml (arr : ByteArray) : Nat :=
  match Grip.Examples.Yaml.parse arr with
  | some (.seq xs) => xs.length
  | some _          => 1
  | none            => 0

structure Stats where
  min : Float
  median : Float

@[noinline] def barrier (_k : Nat) (src : ByteArray) : ByteArray := src

def sampleMs (reps : Nat) (act : Nat → Nat) : IO Stats := do
  let mut samples : Array Float := #[]
  for i in [0:reps] do
    let t0 ← IO.monoNanosNow
    if act i == 0 then IO.eprintln "bench: unexpected zero count"
    let t1 ← IO.monoNanosNow
    samples := samples.push (Float.ofNat (t1 - t0) / 1000000.0)
  let sorted := samples.qsort (· < ·)
  if sorted.isEmpty then return { min := 0.0, median := 0.0 }
  return { min := sorted[0]!, median := sorted[sorted.size / 2]! }

def benchOne (name : String) (src : ByteArray) (p : ByteArray → Nat) : IO Unit := do
  let count := p src
  let s ← sampleMs 20 (fun i => p (barrier i src))
  IO.println s!"{name} size={src.size} count={count} ms={s.min} med={s.median}"

def main : IO Unit := do
  benchOne "sexp" ("(" ++ repeatStr "sym " 50000 ++ ")").toUTF8 parseSexp
  benchOne "lambda" ("f" ++ repeatStr " x" 50000).toUTF8 parseLambda
  benchOne "http"
    ("GET / HTTP/1.1\r\n" ++ repeatStr "X-H: v\r\n" 10000 ++ "\r\n").toUTF8 parseHttp
  let tomlSrc ← IO.FS.readBinFile "bench/data/cargo.lock"
  benchOne "toml" tomlSrc parseToml
  benchOne "yaml" ("[" ++ repeatStr "x, " 30000 ++ "x]").toUTF8 parseYaml
