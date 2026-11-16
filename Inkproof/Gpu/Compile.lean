/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Gpu.Wire
import Inkproof.Scene.Clip
import Inkproof.Scene.PaintOrder

namespace Inkproof.Gpu

/-- A GPU operation with its handles as natural numbers; `Op.toCmd` gives the wire command. -/
inductive Op where
  | create (h : Nat)
  | upload (h : Nat) (ws : List UInt32)
  | delete (h : Nat)
  | uniform (k : Nat) (ws : List UInt32)
  | scissor (ws : List UInt32)
  | draw (h : Nat) (n : Nat)
  deriving DecidableEq, Repr

/-- The wire command for an operation. Handles are taken modulo `2 ^ 32`. -/
def Op.toCmd : Op → Cmd
  | .create h => ⟨0, [.u32 h.toUInt32]⟩
  | .upload h ws => ⟨1, [.u32 h.toUInt32, .words ws]⟩
  | .delete h => ⟨2, [.u32 h.toUInt32]⟩
  | .uniform k ws => ⟨4, [.u32 k.toUInt32, .words ws]⟩
  | .scissor ws => ⟨8, [.words ws]⟩
  | .draw h n => ⟨5, [.u32 h.toUInt32, .u32 n.toUInt32]⟩

/-- What a draw reads besides its vertices: the uniforms `u_slope`, `u_offset` and `u_colour` (numbered 0 to 2), as Float32 words, and the scissor, which is four Int32 words (x, y, width, height) or none for no restriction. -/
structure State where
  slope : List UInt32
  offset : List UInt32
  colour : List UInt32
  scissor : List UInt32
  deriving DecidableEq

/-- The state with uniform `k` set to `ws`; a number that is no uniform of the renderer leaves it unchanged. -/
def State.set (s : State) (k : Nat) (ws : List UInt32) : State :=
  match k with
  | 0 => { s with slope := ws }
  | 1 => { s with offset := ws }
  | 2 => { s with colour := ws }
  | _ => s

/-- A colour as the Float32 words red, green, blue and alpha, each in 0 to 1. -/
def colourWords (c : Scene.Color) : List UInt32 :=
  [c.r, c.g, c.b, c.a].map fun v => (Float32.ofNat v.toNat / 255).toBits

/-- The rectangle that a shape is clipped to: `none` when it is not clipped, `some none` when its clips leave nothing, and otherwise the overlap of all of them. -/
def clipRect : Scene.Shape → Option (Option Scene.Rect)
  | .clipped r s =>
    match clipRect s with
    | none => some (some r)
    | some none => some none
    | some (some r') => some (r.meet r')
  | _ => none

/-- One tile: the display list it covers, the transform uniforms for the current view, and the scissor words for a rectangle in grid coordinates (four Int32 words, x, y, width and height in device pixels from the bottom left). -/
structure Tile where
  list : Scene.DisplayList
  slope : List UInt32
  offset : List UInt32
  scissor : Scene.Rect → List UInt32

/-- The state a command is drawn in. A command that is clipped to nothing gets an empty scissor, which draws nothing. -/
def Tile.stateOf (t : Tile) (c : Scene.Command) : State :=
  ⟨t.slope, t.offset, colourWords c.color,
    match clipRect c.shape with
    | none => []
    | some none => [0, 0, 0, 0]
    | some (some r) => t.scissor r⟩

/-- The vertex words of the commands of a tile, in the order they are painted. -/
def Tile.cmds (tess : Scene.Command → List UInt32) (t : Tile) : List (List UInt32) :=
  t.list.paintOrder.map tess

/-- The vertex words and draw state of each command of a tile, in the order they are painted. -/
def Tile.items (tess : Scene.Command → List UInt32) (t : Tile) : List (List UInt32 × State) :=
  t.list.paintOrder.map fun c => (tess c, t.stateOf c)

/-- Buffers `base`, `base + 1`, ... hold `words`, one buffer per command. -/
structure Entry where
  words : List (List UInt32)
  base : Nat

/-- The buffers resident on the GPU, and the first handle not yet used. -/
structure Cache where
  entries : List Entry := []
  next : Nat := 0

/-- A draw of one command: its buffer handle, vertex words and state. -/
structure Item where
  handle : Nat
  words : List UInt32
  state : State

/-- The operations of one draw: set the state, then draw. -/
def Item.ops (i : Item) : List Op :=
  [.uniform 0 i.state.slope, .uniform 1 i.state.offset, .uniform 2 i.state.colour,
    .scissor i.state.scissor, .draw i.handle (i.words.length / 2)]

def itemsOf : Nat → List (List UInt32 × State) → List Item
  | _, [] => []
  | h, (w, u) :: cs => ⟨h, w, u⟩ :: itemsOf (h + 1) cs

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
  | some e => { s with items := s.items ++ itemsOf e.base (t.items tess) }
  | none =>
    { cache := { entries := s.cache.entries ++ [⟨cs, s.cache.next⟩], next := s.cache.next + cs.length }
      ops := s.ops ++ uploads s.cache.next cs
      items := s.items ++ itemsOf s.cache.next (t.items tess) }

def Tile.Cached (tess : Scene.Command → List UInt32) (c : Cache) (t : Tile) : Prop :=
  ∃ e ∈ c.entries, e.words = t.cmds tess

instance (tess : Scene.Command → List UInt32) (c : Cache) (t : Tile) : Decidable (t.Cached tess c) :=
  inferInstanceAs (Decidable (∃ e ∈ c.entries, e.words = t.cmds tess))

/-- One frame: delete the buffers no tile uses, upload those of tiles not cached, then for each
command of each tile in paint order set the state and draw. -/
def compile (tess : Scene.Command → List UInt32) (c : Cache) (tiles : List Tile) : Cache × List Op :=
  let used (e : Entry) : Bool := tiles.any fun t => decide (e.words = t.cmds tess)
  let s := tiles.foldl (stageTile tess)
    ⟨{ c with entries := c.entries.filter used },
      (c.entries.filter (!used ·)).flatMap fun e => deletes e.base e.words.length, []⟩
  (s.cache, s.ops ++ s.items.flatMap Item.ops)

/-- The wire form of a frame. -/
def compileCmds (tess : Scene.Command → List UInt32) (c : Cache) (tiles : List Tile) :
    Cache × List Cmd :=
  let r := compile tess c tiles
  (r.1, r.2.map Op.toCmd)

end Inkproof.Gpu
