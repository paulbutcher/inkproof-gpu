/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Gpu.Wire
import Inkproof.Scene.PaintOrder

namespace Inkproof.Gpu

/-- A GPU operation with its handles as natural numbers; `Op.toCmd` gives the wire command. -/
inductive Op where
  | create (h : Nat)
  | upload (h : Nat) (ws : List UInt32)
  | delete (h : Nat)
  | uniform (ws : List UInt32)
  | draw (h : Nat) (n : Nat)
  deriving DecidableEq, Repr

/-- The wire command for an operation. Handles are taken modulo `2 ^ 32`. -/
def Op.toCmd : Op → Cmd
  | .create h => ⟨0, [.u32 h.toUInt32]⟩
  | .upload h ws => ⟨1, [.u32 h.toUInt32, .words ws]⟩
  | .delete h => ⟨2, [.u32 h.toUInt32]⟩
  | .uniform ws => ⟨4, [.u32 0, .words ws]⟩
  | .draw h n => ⟨5, [.u32 h.toUInt32, .u32 n.toUInt32]⟩

/-- One tile: the display list it covers, and the values of the transform uniform for the current view. -/
structure Tile where
  list : Scene.DisplayList
  uniform : List UInt32

/-- The vertex words of the commands of a tile, in the order they are painted. -/
def Tile.cmds (tess : Scene.Command → List UInt32) (t : Tile) : List (List UInt32) :=
  t.list.paintOrder.map tess

/-- Buffers `base`, `base + 1`, ... hold `words`, one buffer per command. -/
structure Entry where
  words : List (List UInt32)
  base : Nat

/-- The buffers resident on the GPU, and the first handle not yet used. -/
structure Cache where
  entries : List Entry := []
  next : Nat := 0

/-- A draw of one command: its buffer handle, vertex words and uniform. -/
structure Item where
  handle : Nat
  words : List UInt32
  uniform : List UInt32

def itemsOf (u : List UInt32) : Nat → List (List UInt32) → List Item
  | _, [] => []
  | h, w :: cs => ⟨h, w, u⟩ :: itemsOf u (h + 1) cs

def uploads : Nat → List (List UInt32) → List Op
  | _, [] => []
  | h, w :: ws => .create h :: .upload h w :: uploads (h + 1) ws

def deletes : Nat → Nat → List Op
  | _, 0 => []
  | h, n + 1 => .delete h :: deletes (h + 1) n

structure Stage where
  cache : Cache
  ops : List Op
  items : List Item

def stageTile (tess : Scene.Command → List UInt32) (s : Stage) (t : Tile) : Stage :=
  let cs := t.cmds tess
  match s.cache.entries.find? fun e => decide (e.words = cs) with
  | some e => { s with items := s.items ++ itemsOf t.uniform e.base cs }
  | none =>
    { cache := { entries := s.cache.entries ++ [⟨cs, s.cache.next⟩], next := s.cache.next + cs.length }
      ops := s.ops ++ uploads s.cache.next cs
      items := s.items ++ itemsOf t.uniform s.cache.next cs }

def Tile.Cached (tess : Scene.Command → List UInt32) (c : Cache) (t : Tile) : Prop :=
  ∃ e ∈ c.entries, e.words = t.cmds tess

instance (tess : Scene.Command → List UInt32) (c : Cache) (t : Tile) : Decidable (t.Cached tess c) :=
  inferInstanceAs (Decidable (∃ e ∈ c.entries, e.words = t.cmds tess))

/-- One frame: delete the buffers no tile uses, upload those of tiles not cached, then for each
command of each tile in paint order set the uniform and draw. -/
def compile (tess : Scene.Command → List UInt32) (c : Cache) (tiles : List Tile) : Cache × List Op :=
  let used (e : Entry) : Bool := tiles.any fun t => decide (e.words = t.cmds tess)
  let s := tiles.foldl (stageTile tess)
    ⟨{ c with entries := c.entries.filter used },
      (c.entries.filter (!used ·)).flatMap fun e => deletes e.base e.words.length, []⟩
  (s.cache, s.ops ++ s.items.flatMap fun i => [.uniform i.uniform, .draw i.handle (i.words.length / 2)])

/-- The wire form of a frame. -/
def compileCmds (tess : Scene.Command → List UInt32) (c : Cache) (tiles : List Tile) :
    Cache × List Cmd :=
  let r := compile tess c tiles
  (r.1, r.2.map Op.toCmd)

end Inkproof.Gpu
