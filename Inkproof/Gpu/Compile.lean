/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Gpu.Gradient
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
  | draw (h : Nat) (n : Nat) (stride : Nat)
  deriving DecidableEq, Repr

/-- The wire command for an operation. Handles are taken modulo `2 ^ 32`. -/
def Op.toCmd : Op → Cmd
  | .create h => ⟨0, [.u32 h.toUInt32]⟩
  | .upload h ws => ⟨1, [.u32 h.toUInt32, .words ws]⟩
  | .delete h => ⟨2, [.u32 h.toUInt32]⟩
  | .uniform k ws => ⟨4, [.u32 k.toUInt32, .words ws]⟩
  | .scissor ws => ⟨8, [.words ws]⟩
  | .draw h n w => ⟨5, [.u32 h.toUInt32, .u32 n.toUInt32, .u32 w.toUInt32]⟩

/-- What a draw reads besides its vertices: the uniforms `u_slope`, `u_offset`, `u_size`, `u_view` and `u_colour` (numbered 0 to 4), as Float32 words, then the gradient uniforms (`u_axis`, `u_start`, `u_inv` and `u_delta0` to `u_delta3`, numbered 5 to 11), the stride in words of a vertex (two for a position alone, six for a position, a direction and a corner), and the scissor, which is four Int32 words (x, y, width, height) or none for no restriction. -/
structure State where
  slope : List UInt32
  offset : List UInt32
  size : List UInt32
  view : List UInt32
  colour : List UInt32
  stride : Nat
  scissor : List UInt32
  grad : Gradient := {}
  deriving DecidableEq

/-- The state with uniform `k` set to `ws`; a number that is no uniform of the renderer leaves it unchanged. -/
def State.set (s : State) (k : Nat) (ws : List UInt32) : State :=
  match k with
  | 0 => { s with slope := ws }
  | 1 => { s with offset := ws }
  | 2 => { s with size := ws }
  | 3 => { s with view := ws }
  | 4 => { s with colour := ws }
  | 5 => { s with grad := { s.grad with axis := ws } }
  | 6 => { s with grad := { s.grad with starts := ws } }
  | 7 => { s with grad := { s.grad with invs := ws } }
  | 8 => { s with grad := { s.grad with d0 := ws } }
  | 9 => { s with grad := { s.grad with d1 := ws } }
  | 10 => { s with grad := { s.grad with d2 := ws } }
  | 11 => { s with grad := { s.grad with d3 := ws } }
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

/-- One tile: the display list it covers, the transform uniforms for the current view, the view uniform of the target, the stride of its vertices, the stroke size of a shape in pixels (one Float32 word, which only strips and markers use), the scissor words for a rectangle in grid coordinates (four Int32 words, x, y, width and height in device pixels from the bottom left), and the origin of its vertices in grid coordinates, which gradient stops are taken relative to. -/
structure Tile where
  list : Scene.DisplayList
  slope : List UInt32
  offset : List UInt32
  view : List UInt32
  stride : Nat
  size : Scene.Shape → List UInt32
  scissor : Scene.Rect → List UInt32
  origin : Scene.Pt := ⟨0, 0⟩

/-- The state a command is drawn in. A command that is clipped to nothing, or whose shading the renderer cannot draw (`shadingState`), gets an empty scissor, which draws nothing. -/
def Tile.stateOf (t : Tile) (c : Scene.Command) : State :=
  match shadingState t.origin c.color with
  | none => ⟨t.slope, t.offset, t.size c.shape, t.view, colourWords ⟨0, 0, 0, 0⟩, t.stride, [0, 0, 0, 0], .flat⟩
  | some (k, g) =>
    ⟨t.slope, t.offset, t.size c.shape, t.view, colourWords k, t.stride,
      match clipRect c.shape with
      | none => []
      | some none => [0, 0, 0, 0]
      | some (some r) => t.scissor r, g⟩

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

/-- The operations that set the gradient uniforms to `g`, leaving out those whose words `prev`, the gradient the previous draw left in force, already holds; with no `prev`, all of them. -/
def Gradient.ops (prev : Option Gradient) (g : Gradient) : List Op :=
  let set (k : Nat) (f : Gradient → List UInt32) : List Op :=
    if prev.map f = some (f g) then [] else [.uniform k (f g)]
  set 5 (·.axis) ++ set 6 (·.starts) ++ set 7 (·.invs) ++ set 8 (·.d0) ++ set 9 (·.d1) ++
    set 10 (·.d2) ++ set 11 (·.d3)

/-- The operations of one draw: set the state, then draw. -/
def Item.ops (prev : Option Gradient) (i : Item) : List Op :=
  [.uniform 0 i.state.slope, .uniform 1 i.state.offset, .uniform 2 i.state.size,
    .uniform 3 i.state.view, .uniform 4 i.state.colour] ++ i.state.grad.ops prev ++
    [.scissor i.state.scissor, .draw i.handle (i.words.length / i.state.stride) i.state.stride]

/-- The operations of a run of draws, each leaving its gradient in force for the next. -/
def itemsOps : Option Gradient → List Item → List Op
  | _, [] => []
  | prev, i :: L => i.ops prev ++ itemsOps (some i.state.grad) L

def itemsOf : Nat → List (List UInt32 × State) → List Item
  | _, [] => []
  | h, (w, u) :: cs => ⟨h, w, u⟩ :: itemsOf (h + 1) cs

def uploads : Nat → List (List UInt32) → List Op
  | _, [] => []
  | h, w :: ws => .create h :: .upload h w :: uploads (h + 1) ws

def deletes : Nat → Nat → List Op
  | _, 0 => []
  | h, n + 1 => .delete h :: deletes (h + 1) n

private def itemsOfTR (h : Nat) (cs : List (List UInt32 × State)) : List Item :=
  (cs.foldl (fun (a : Nat × Array Item) (w, u) => (a.1 + 1, a.2.push ⟨a.1, w, u⟩)) (h, #[])).2.toList

private theorem itemsOfTR_go (cs : List (List UInt32 × State)) (h : Nat) (acc : Array Item) :
    (cs.foldl (fun (a : Nat × Array Item) (w, u) => (a.1 + 1, a.2.push ⟨a.1, w, u⟩)) (h, acc)).2.toList =
      acc.toList ++ itemsOf h cs := by
  induction cs generalizing h acc with
  | nil => simp [itemsOf]
  | cons c cs ih => simp [itemsOf, ih]

/-- Constant stack, which the browser needs for long display lists. -/
@[csimp] private theorem itemsOf_eq_itemsOfTR : @itemsOf = @itemsOfTR := by
  funext h cs
  simp [itemsOfTR, itemsOfTR_go]

private def itemsOpsTR (prev : Option Gradient) (L : List Item) : List Op :=
  (L.foldl (fun (a : Array Op × Option Gradient) i => (a.1 ++ (i.ops a.2).toArray, some i.state.grad))
    (#[], prev)).1.toList

private theorem itemsOpsTR_go (L : List Item) (prev : Option Gradient) (acc : Array Op) :
    (L.foldl (fun (a : Array Op × Option Gradient) i => (a.1 ++ (i.ops a.2).toArray, some i.state.grad))
      (acc, prev)).1.toList = acc.toList ++ itemsOps prev L := by
  induction L generalizing prev acc with
  | nil => simp [itemsOps]
  | cons i L ih => simp [itemsOps, ih]

/-- Constant stack, which the browser needs for long display lists. -/
@[csimp] private theorem itemsOps_eq_itemsOpsTR : @itemsOps = @itemsOpsTR := by
  funext prev L
  simp [itemsOpsTR, itemsOpsTR_go]

private def uploadsTR (h : Nat) (ws : List (List UInt32)) : List Op :=
  (ws.foldl (fun (a : Nat × Array Op) w => (a.1 + 1, (a.2.push (.create a.1)).push (.upload a.1 w)))
    (h, #[])).2.toList

private theorem uploadsTR_go (ws : List (List UInt32)) (h : Nat) (acc : Array Op) :
    (ws.foldl (fun (a : Nat × Array Op) w => (a.1 + 1, (a.2.push (.create a.1)).push (.upload a.1 w)))
      (h, acc)).2.toList = acc.toList ++ uploads h ws := by
  induction ws generalizing h acc with
  | nil => simp [uploads]
  | cons w ws ih => simp [uploads, ih]

@[csimp] private theorem uploads_eq_uploadsTR : @uploads = @uploadsTR := by
  funext h ws
  simp [uploadsTR, uploadsTR_go]

private def deletesTR (h n : Nat) : List Op :=
  (List.range n).map fun i => .delete (h + i)

private theorem deletesTR_eq (n h : Nat) : (List.range n).map (fun i => Op.delete (h + i)) = deletes h n := by
  induction n generalizing h with
  | zero => simp [deletes]
  | succ n ih =>
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [deletes]
    congr 1
    rw [← ih (h + 1)]
    apply List.map_congr_left
    intro i _
    simp [Function.comp, Nat.add_assoc, Nat.add_comm 1 i]

@[csimp] private theorem deletes_eq_deletesTR : @deletes = @deletesTR := by
  funext h n
  simp [deletesTR, deletesTR_eq]

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

/-- `Tile.items`, given the vertex words of the commands, which are those of `Tile.cmds`, so that they are built once. -/
private def Tile.itemsFrom (cs : List (List UInt32)) (t : Tile) : List (List UInt32 × State) :=
  (Array.zip cs.toArray (t.list.paintOrder.map t.stateOf).toArray).toList

private theorem zip_toArray {α β : Type} (a : List α) (b : List β) :
    (Array.zip a.toArray b.toArray).toList = List.zip a b := by
  simp only [Array.zip, Array.toList_zipWith]; rfl

private theorem Tile.items_eq_itemsFrom (tess : Scene.Command → List UInt32) (t : Tile) :
    t.items tess = t.itemsFrom (t.cmds tess) := by
  simp only [Tile.items, Tile.itemsFrom, Tile.cmds]
  rw [zip_toArray]
  induction t.list.paintOrder with
  | nil => rfl
  | cons c cs ih => simp [List.zip_cons_cons] at ih ⊢; simp [ih]

private def stageTileShared (tess : Scene.Command → List UInt32) (s : Stage) (t : Tile) : Stage :=
  let cs := t.cmds tess
  match s.cache.entries.find? fun e => decide (e.words = cs) with
  | some e => { s with items := s.items ++ itemsOf e.base (t.itemsFrom cs) }
  | none =>
    { cache := { entries := s.cache.entries ++ [⟨cs, s.cache.next⟩], next := s.cache.next + cs.length }
      ops := s.ops ++ uploads s.cache.next cs
      items := s.items ++ itemsOf s.cache.next (t.itemsFrom cs) }

/-- Builds the vertex words of a tile once, not twice, which matters for tiles of many commands in the browser. -/
@[csimp] private theorem stageTile_eq_stageTileShared : @stageTile = @stageTileShared := by
  funext tess s t
  simp only [stageTile, stageTileShared, Tile.items_eq_itemsFrom]

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
  (s.cache, s.ops ++ itemsOps none s.items)

/-- The wire form of a frame. -/
def compileCmds (tess : Scene.Command → List UInt32) (c : Cache) (tiles : List Tile) :
    Cache × List Cmd :=
  let r := compile tess c tiles
  (r.1, r.2.map Op.toCmd)

end Inkproof.Gpu
