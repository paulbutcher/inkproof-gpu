/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

namespace Inkproof.Gpu

/-- Operand kinds. `words` is a length-prefixed array of 32-bit words. -/
inductive FieldTy where
  | u32
  | words
  deriving DecidableEq, Repr

inductive Arg where
  | u32 (n : UInt32)
  | words (ws : List UInt32)
  deriving DecidableEq, Repr

structure Spec where
  name : String
  op : UInt8
  fields : List FieldTy

/-- The command set. The encoder, the decoder and the generated JavaScript all read this table. -/
def specs : List Spec := [
  ⟨"createBuffer", 0, [.u32]⟩,
  ⟨"bufferData", 1, [.u32, .words]⟩,
  ⟨"deleteBuffer", 2, [.u32]⟩,
  ⟨"useProgram", 3, [.u32]⟩,
  ⟨"uniform", 4, [.u32, .words]⟩,
  ⟨"draw", 5, [.u32, .u32]⟩,
  ⟨"clear", 6, [.u32]⟩
]

def specOf (op : UInt8) : Option Spec := specs.find? (·.op == op)

structure Cmd where
  op : UInt8
  args : List Arg
  deriving DecidableEq, Repr

def Arg.Fits : Arg → FieldTy → Prop
  | .u32 _, .u32 => True
  | .words ws, .words => ws.length < UInt32.size
  | _, _ => False

def ArgsFit : List Arg → List FieldTy → Prop
  | [], [] => True
  | a :: as, t :: ts => a.Fits t ∧ ArgsFit as ts
  | _, _ => False

def Cmd.WellFormed (c : Cmd) : Prop :=
  ∃ s, specOf c.op = some s ∧ ArgsFit c.args s.fields

def le32 (n : UInt32) : List UInt8 :=
  [UInt8.ofNat n.toNat, UInt8.ofNat (n.toNat / 256), UInt8.ofNat (n.toNat / 65536),
    UInt8.ofNat (n.toNat / 16777216)]

def get32 : List UInt8 → Option (UInt32 × List UInt8)
  | a :: b :: c :: d :: r =>
    some (UInt32.ofNat (a.toNat + 256 * b.toNat + 65536 * c.toNat + 16777216 * d.toNat), r)
  | _ => none

def Arg.encode : Arg → List UInt8
  | .u32 n => le32 n
  | .words ws => le32 ws.length.toUInt32 ++ ws.flatMap le32

def encodeArgs (as : List Arg) : List UInt8 := as.flatMap Arg.encode

def Cmd.encode (c : Cmd) : List UInt8 := c.op :: encodeArgs c.args

/-- A command list as one buffer: command count, then each command. -/
def encode (cs : List Cmd) : List UInt8 :=
  le32 cs.length.toUInt32 ++ cs.flatMap Cmd.encode

def decodeWords : Nat → List UInt8 → Option (List UInt32 × List UInt8)
  | 0, bs => some ([], bs)
  | n + 1, bs => do
    let (w, r) ← get32 bs
    let (ws, r') ← decodeWords n r
    some (w :: ws, r')

def decodeArg : FieldTy → List UInt8 → Option (Arg × List UInt8)
  | .u32, bs => do
    let (n, r) ← get32 bs
    some (.u32 n, r)
  | .words, bs => do
    let (n, r) ← get32 bs
    let (ws, r') ← decodeWords n.toNat r
    some (.words ws, r')

def decodeArgs : List FieldTy → List UInt8 → Option (List Arg × List UInt8)
  | [], bs => some ([], bs)
  | t :: ts, bs => do
    let (a, r) ← decodeArg t bs
    let (as, r') ← decodeArgs ts r
    some (a :: as, r')

def decodeCmd : List UInt8 → Option (Cmd × List UInt8)
  | [] => none
  | op :: bs => do
    let s ← specOf op
    let (as, r) ← decodeArgs s.fields bs
    some (⟨op, as⟩, r)

def decodeCmds : Nat → List UInt8 → Option (List Cmd × List UInt8)
  | 0, bs => some ([], bs)
  | n + 1, bs => do
    let (c, r) ← decodeCmd bs
    let (cs, r') ← decodeCmds n r
    some (c :: cs, r')

def decode (bs : List UInt8) : Option (List Cmd) := do
  let (n, r) ← get32 bs
  let (cs, rest) ← decodeCmds n.toNat r
  if rest.isEmpty then some cs else none

theorem get32_le32 (n : UInt32) (r : List UInt8) : get32 (le32 n ++ r) = some (n, r) := by
  simp only [le32, List.cons_append, List.nil_append, get32]
  congr 2
  apply UInt32.toNat_inj.mp
  have := n.toNat_lt
  simp [UInt32.toNat_ofNat] at *
  omega

theorem decodeWords_flatMap (ws : List UInt32) (r : List UInt8) :
    decodeWords ws.length (ws.flatMap le32 ++ r) = some (ws, r) := by
  induction ws with
  | nil => simp [decodeWords]
  | cons w ws ih => simp [decodeWords, get32_le32, ih]

theorem decodeArg_encode {a : Arg} {t : FieldTy} (h : a.Fits t) (r : List UInt8) :
    decodeArg t (a.encode ++ r) = some (a, r) := by
  cases a <;> cases t <;> simp only [Arg.Fits] at h
  · simp [Arg.encode, decodeArg, get32_le32]
  · rename_i ws
    have hl : ws.length.toUInt32.toNat = ws.length := by
      simp [Nat.mod_eq_of_lt h]
    simp [Arg.encode, decodeArg, get32_le32, hl, decodeWords_flatMap]

theorem decodeArgs_encode {as : List Arg} {ts : List FieldTy} (h : ArgsFit as ts) (r : List UInt8) :
    decodeArgs ts (encodeArgs as ++ r) = some (as, r) := by
  induction as generalizing ts with
  | nil => cases ts <;> simp_all [ArgsFit, encodeArgs, decodeArgs]
  | cons a as ih =>
    cases ts with
    | nil => simp [ArgsFit] at h
    | cons t ts =>
      obtain ⟨h1, h2⟩ := h
      have := ih h2
      simp only [encodeArgs, List.flatMap_cons, List.append_assoc] at this ⊢
      simp [decodeArgs, decodeArg_encode h1, this]

theorem decodeCmd_encode {c : Cmd} (h : c.WellFormed) (r : List UInt8) :
    decodeCmd (c.encode ++ r) = some (c, r) := by
  obtain ⟨s, hs, ha⟩ := h
  simp [Cmd.encode, decodeCmd, hs, decodeArgs_encode ha]

theorem decodeCmds_encode {cs : List Cmd} (h : ∀ c ∈ cs, c.WellFormed) (r : List UInt8) :
    decodeCmds cs.length (cs.flatMap Cmd.encode ++ r) = some (cs, r) := by
  induction cs with
  | nil => simp [decodeCmds]
  | cons c cs ih =>
    have := ih (fun c' hc => h c' (List.mem_cons_of_mem _ hc))
    simp only [List.flatMap_cons, List.append_assoc] at this ⊢
    simp [decodeCmds, decodeCmd_encode (h c (List.mem_cons_self ..)), this]

/-- Decoding an encoded command list returns the original. -/
theorem decode_encode {cs : List Cmd} (h : ∀ c ∈ cs, c.WellFormed) (hl : cs.length < UInt32.size) :
    decode (encode cs) = some cs := by
  have hl' : cs.length.toUInt32.toNat = cs.length := by simp [Nat.mod_eq_of_lt hl]
  have := decodeCmds_encode h []
  simp only [List.append_nil] at this
  simp [decode, encode, get32_le32, hl', this]

end Inkproof.Gpu
