/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Gpu.Frame

namespace Inkproof.Gpu

-- Stand-ins for instances Scene does not derive yet; delete them when it does, or they will clash.
deriving instance DecidableEq for Scene.Item
deriving instance DecidableEq for Scene.Shape
deriving instance DecidableEq for Scene.Shading
deriving instance DecidableEq for Scene.Command

/-- A run of commands as wire bytes: how many, and each in turn. -/
structure Piece where
  count : Nat
  body : ByteArray

def Piece.ofCmds (cs : List Cmd) : Piece :=
  ⟨cs.length, ⟨(cs.flatMap Cmd.encode).toArray⟩⟩

/-- The buffer of the pieces in order, as `encode` gives it for their commands. -/
def Piece.join (ps : List Piece) : ByteArray :=
  ⟨(le32 (ps.map Piece.count).sum.toUInt32).toArray⟩ ++ ps.foldl (fun b p => b ++ p.body) ByteArray.empty

theorem Piece.join_ofCmds (css : List (List Cmd)) :
    Piece.join (css.map Piece.ofCmds) = ⟨(encode css.flatten).toArray⟩ := by
  have key : ∀ (css : List (List Cmd)) (b : ByteArray),
      ((css.map Piece.ofCmds).foldl (fun b p => b ++ p.body) b).data =
        b.data ++ (css.flatten.flatMap Cmd.encode).toArray := by
    intro css
    induction css with
    | nil => intro b; simp
    | cons cs rest ih =>
      intro b
      simp [List.foldl_cons, ih, Piece.ofCmds, ByteArray.data_append, List.flatMap_append]
  have hc : ((css.map Piece.ofCmds).map (·.count)).sum = css.flatten.length := by
    induction css with
    | nil => simp
    | cons cs rest ih => simp_all [Piece.ofCmds]
  unfold Piece.join encode
  rw [List.map_map, show ((fun x => x.count) ∘ Piece.ofCmds) = List.length from rfl] at *
  apply ByteArray.ext
  rw [ByteArray.data_append, key]
  rw [hc]
  have : ByteArray.empty.data = #[] := rfl
  rw [this, Array.empty_append, List.append_toArray]

/-- The layer's tile under a view or on a pixel grid. -/
inductive TileKey where
  | pixel (w h : Nat)
  | view (w h : Nat) (v : View) (plot : Scene.Rect)
  deriving DecidableEq

def TileKey.tile : TileKey → Layer → Tile
  | .pixel w h, l => l.pixelTile w h
  | .view w h v plot, l => l.viewTile w h v plot

/-- Equality of layers, constant time when both are the same objects. -/
def Layer.same (a b : Layer) : Bool :=
  withPtrEq a.list b.list (fun _ => decide (a.list = b.list)) (by intro h; simp [h]) && wordsEq a.words b.words

theorem Layer.same_eq (a b : Layer) (h : a.same b = true) : a = b := by
  obtain ⟨l, w⟩ := a
  obtain ⟨l', w'⟩ := b
  simp only [Layer.same, Bool.and_eq_true] at h
  have h1 : decide (l = l') = true := h.1
  have h2 : decide (w = w') = true := h.2
  simp only [decide_eq_true_eq] at h1 h2
  rw [h1, h2]

/-- The draws of a layer whose buffers start at handle `b`, as bytes. -/
def layerPiece (key : TileKey) (l : Layer) (b : Nat) : Piece :=
  Piece.ofCmds ((tileDraws (fun _ => []) (key.tile l) b).map Op.toCmd)

/-- The draws of a layer in a tile, recorded once and replayed by every frame that draws the layer at the same handles. -/
structure Stream where
  key : TileKey
  layer : Layer
  base : Nat
  piece : Piece
  ok : piece = layerPiece key layer base

/-- The buffers a frame leaves on the GPU and the draws it recorded for its layers. -/
structure Retained where
  cache : Cache := {}
  streams : List Stream := []

def Stream.matches (key : TileKey) (l : Layer) (b : Nat) (s : Stream) : Bool :=
  decide (s.key = key) && s.base == b && s.layer.same l

def streamFor (r : Retained) (key : TileKey) (l : Layer) (b : Nat) : Stream :=
  match h : r.streams.find? (Stream.matches key l b) with
  | some s => ⟨key, l, b, s.piece, by
      have := List.find?_some h
      simp only [Stream.matches, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
      obtain ⟨⟨hk, hb⟩, hl⟩ := this
      obtain rfl := Layer.same_eq _ _ hl
      rw [← hk, ← hb]; exact s.ok⟩
  | none => ⟨key, l, b, layerPiece key l b, rfl⟩

/-- The stream of a layer's draws at `key` and `b`: the one `r` holds, or else one recorded now. -/
theorem streamFor_piece (r : Retained) (key : TileKey) (l : Layer) (b : Nat) :
    (streamFor r key l b).piece = layerPiece key l b := by
  unfold streamFor
  split
  · rename_i s h
    have := List.find?_some h
    simp only [Stream.matches, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    obtain ⟨⟨hk, hb⟩, hl⟩ := this
    obtain rfl := Layer.same_eq _ _ hl
    show s.piece = layerPiece key s.layer b
    subst hk hb
    exact s.ok
  · rfl

/-- The setup of a frame of `layers` and the tiles `extra`: the cache, the operations that upload and delete buffers, and the handle of each tile's first buffer. -/
def retainedSetup (tess : Scene.Command → List UInt32) (c : Cache) (layers held : List Layer)
    (extra : List Tile) : Cache × List Op × List Nat :=
  compileSetup c (held.map (·.words)) (layers.map (·.words) ++ extra.map (·.cmds tess))

/-- The tiles of a frame, in the order they are drawn. -/
def retainedTiles (key : TileKey) (layers : List Layer) (extra : List Tile) : List Tile :=
  layers.map key.tile ++ extra

/-- The operations of a frame of `layers` under `key` and the tiles `extra`, drawn in that order. -/
def retainedOps (tess : Scene.Command → List UInt32) (c : Cache) (key : TileKey) (layers held : List Layer)
    (extra : List Tile) : List Op :=
  let r := retainedSetup tess c layers held extra
  r.2.1 ++ ((retainedTiles key layers extra).zip r.2.2).flatMap fun p => tileDraws tess p.1 p.2

/-- A frame as wire bytes whose layers' draws are replayed from `r` when it holds them, so that the work is that of the layers drawn, not of their commands. `head` leads the frame. -/
def retainedFrame (tess : Scene.Command → List UInt32) (r : Retained) (key : TileKey)
    (layers held : List Layer) (extra : List Tile) (head : List Cmd) : Retained × ByteArray :=
  let s := retainedSetup tess r.cache layers held extra
  let used := (layers.zip (s.2.2.take layers.length)).map fun p => streamFor r key p.1 p.2
  let pieces := used.map (·.piece) ++
    ((extra.zip (s.2.2.drop layers.length)).map fun p => Piece.ofCmds ((tileDraws tess p.1 p.2).map Op.toCmd))
  let kept := r.streams.filter fun o =>
    s.1.entries.any (·.base == o.base) && !used.any fun n => n.base == o.base && n.layer.same o.layer
  (⟨s.1, used ++ kept⟩,
    Piece.join (Piece.ofCmds (head ++ s.2.1.map Op.toCmd) :: pieces))

/-- The wire bytes of one frame of `layers` in device pixels on a `w` by `h` target cleared to `bg`, as `strokeLayersFrame` draws them. A layer `r` holds the draws of is recognised by identity and replayed, so the frame costs time in the number of layers, not their commands, once a layer has been drawn under the same `w` and `h`. -/
def strokeLayersBytes (r : Retained) (fresh : Bool) (w h : Nat) (layers held : List Layer)
    (bg : Scene.Color) : Retained × ByteArray :=
  retainedFrame (fun _ => []) r (.pixel w h) layers held [] (frameSetup fresh bg)

/-- The wire bytes of one frame of `layers` in data coordinates under `v`, then `overlay` in device pixels, as `viewLayersFrame` draws them. A layer `r` holds the draws of is replayed as for `strokeLayersBytes`, under the same `w`, `h`, `v` and `plot`. -/
def viewLayersBytes (tess : Scene.Command → List UInt32) (r : Retained) (fresh : Bool) (w h : Nat)
    (v : View) (plot : Scene.Rect) (layers held : List Layer) (overlay : Scene.DisplayList)
    (bg : Scene.Color) : Retained × ByteArray :=
  retainedFrame tess r (.view w h v plot) layers held [pixelStrokeTile w h overlay] (frameSetup fresh bg)

end Inkproof.Gpu
