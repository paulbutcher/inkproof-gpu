/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Gpu.Proofs.Layers
import Inkproof.Gpu.Retained

namespace Inkproof.Gpu

theorem tileDraws_layer (tess : Scene.Command → List UInt32) (key : TileKey) (l : Layer) (b : Nat) :
    tileDraws tess (key.tile l) b = tileDraws (fun _ => []) (key.tile l) b := by
  cases key <;> rfl

@[simp] theorem retainedTiles_eq (key : TileKey) (layers : List Layer) (extra : List Tile) :
    retainedTiles key layers extra = layers.map key.tile ++ extra := rfl

theorem Layer.same_self (l : Layer) : l.same l = true := by
  simp [Layer.same, withPtrEq]

/-- A stream matches exactly the layer, tile and handle it records. -/
theorem Stream.matches_iff (key : TileKey) (l : Layer) (b : Nat) (s : Stream) :
    s.matches key l b = true ↔ s.key = key ∧ s.base = b ∧ s.layer = l := by
  constructor
  · intro h
    simp only [Stream.matches, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    exact ⟨h.1.1, h.1.2, Layer.same_eq _ _ h.2⟩
  · rintro ⟨hk, hb, hl⟩
    subst hk hb hl
    simp [Stream.matches, Layer.same_self]

theorem retainedSetup_length (tess : Scene.Command → List UInt32) (c : Cache) (layers held : List Layer)
    (extra : List Tile) :
    (retainedSetup tess c layers held extra).2.2.length = layers.length + extra.length := by
  simp [retainedSetup, compileSetup, stageAll_length]

private theorem zip_split {α β : Type} (A B : List α) (bs : List β) (h : bs.length = A.length + B.length) :
    (A ++ B).zip bs = A.zip (bs.take A.length) ++ B.zip (bs.drop A.length) := by
  have e : (A ++ B).zip bs = (A ++ B).zip (bs.take A.length ++ bs.drop A.length) := by
    rw [List.take_append_drop]
  rw [e, List.zip_append]
  simp only [List.length_take]
  omega

/-- A frame's bytes are the encoding of its operations, whichever of its layers' draws were replayed. -/
theorem retainedFrame_bytes (tess : Scene.Command → List UInt32) (r : Retained) (key : TileKey)
    (layers held : List Layer) (extra : List Tile) (head : List Cmd) :
    (retainedFrame tess r key layers held extra head).2 =
      ⟨(encode (head ++ (retainedOps tess r.cache key layers held extra).map Op.toCmd)).toArray⟩ := by
  have hlen := retainedSetup_length tess r.cache layers held extra
  unfold retainedFrame retainedOps
  simp only []
  generalize retainedSetup tess r.cache layers held extra = s at hlen ⊢
  have hz := zip_split (layers.map key.tile) extra s.2.2 (by simpa using hlen)
  have hpieces : (layers.zip (s.2.2.take layers.length)).map (fun p => (streamFor r key p.1 p.2).piece) =
      ((layers.zip (s.2.2.take layers.length)).map fun p =>
        Piece.ofCmds ((tileDraws tess (key.tile p.1) p.2).map Op.toCmd)) := by
    refine List.map_congr_left fun p _ => ?_
    rw [streamFor_piece, layerPiece, tileDraws_layer tess]
  have := Piece.join_ofCmds ((head ++ s.2.1.map Op.toCmd) ::
    ((layers.zip (s.2.2.take layers.length)).map (fun p => (tileDraws tess (key.tile p.1) p.2).map Op.toCmd) ++
      (extra.zip (s.2.2.drop layers.length)).map fun p => (tileDraws tess p.1 p.2).map Op.toCmd))
  simp only [List.map_cons, List.map_append, List.map_map, Function.comp_def] at this ⊢
  rw [retainedTiles, hz]
  simp only [List.flatMap_append, List.flatten_cons, List.map_append] at *
  rw [hpieces, this, List.length_map]
  congr 3
  simp [List.flatMap_def, List.map_flatten, List.map_map, Function.comp_def, List.zip_map_left,
    List.append_assoc]

theorem TileKey.tile_cmds (tess : Scene.Command → List UInt32) (key : TileKey) (l : Layer) :
    (key.tile l).cmds tess = l.words := by
  cases key <;> rfl

theorem retainedSetup_eq (tess : Scene.Command → List UInt32) (c : Cache) (key : TileKey)
    (layers held : List Layer) (extra : List Tile) :
    retainedSetup tess c layers held extra =
      compileSetup c (held.map (·.words)) ((retainedTiles key layers extra).map (·.cmds tess)) := by
  simp [retainedSetup, retainedTiles, List.map_map, Function.comp_def, TileKey.tile_cmds]

/-- A frame's cache is the one `compileKeeping` leaves for the same tiles. -/
theorem retainedSetup_cache (tess : Scene.Command → List UInt32) (c : Cache) (key : TileKey)
    (layers held : List Layer) (extra : List Tile) :
    (retainedSetup tess c layers held extra).1 =
      (compileKeeping tess c (held.map (·.words)) (retainedTiles key layers extra)).1 := by
  rw [retainedSetup_eq tess c key, compileSetup_cache]

/-- A frame of retained layers draws what `compileKeeping` does for their tiles, in order. -/
theorem retainedOps_draws (tess : Scene.Command → List UInt32) (c : Cache) (key : TileKey)
    (layers held : List Layer) (extra : List Tile) (g : Gpu)
    (hs : ∀ t ∈ retainedTiles key layers extra, t.Sound tess) (hv : c.Valid g) :
    (g.run (retainedOps tess c key layers held extra)).log =
        g.log ++ frameDraws tess (retainedTiles key layers extra) ∧
      (retainedSetup tess c layers held extra).1.Valid (g.run (retainedOps tess c key layers held extra)) := by
  have := compileSetup_log tess c (held.map (·.words)) (retainedTiles key layers extra) g hs hv
  rw [← retainedSetup_eq tess c key] at this
  exact this

/-- Layers drawn in pixels from a frame that replays them draw what one `pixelStrokeTile` of the concatenation of their lists draws. -/
theorem strokeLayersOps_draws (tess : Scene.Command → List UInt32) (c : Cache) (w h : Nat)
    (layers held : List Layer) (g : Gpu) (hsound : ∀ l ∈ layers, l.Sound tess)
    (hst : DisplayList.Stacked (layers.map (·.list))) (hv : c.Valid g) :
    (g.run (retainedOps tess c (.pixel w h) layers held [])).log =
      g.log ++ frameDraws tess [pixelStrokeTile w h (DisplayList.concat (layers.map (·.list)))] := by
  have := (retainedOps_draws tess c (.pixel w h) layers held [] g (fun t ht => by
    simp only [retainedTiles, List.append_nil, List.mem_map] at ht
    obtain ⟨l, hl, rfl⟩ := ht
    exact Layer.pixelTile_sound tess w h l (hsound l hl)) hv).1
  rw [this, retainedTiles, List.append_nil]
  exact congrArg _ (strokeLayers_draws tess w h layers hst)

/-- Layers drawn under a view from a frame that replays them, then the overlay, draw what one `viewTile` of the concatenation of their lists and the overlay's tile draw. -/
theorem viewLayersOps_draws (tess : Scene.Command → List UInt32)
    (htess : ∀ (c : Scene.Command) (r : Scene.Rect), tess { c with shape := .clipped r c.shape } = tess c)
    (c : Cache) (w h : Nat) (v : View) (plot : Scene.Rect) (layers held : List Layer)
    (overlay : Scene.DisplayList) (g : Gpu) (hsound : ∀ l ∈ layers, l.Sound tess)
    (hst : DisplayList.Stacked (layers.map (·.list))) (hv : c.Valid g) :
    (g.run (retainedOps tess c (.view w h v plot) layers held [pixelStrokeTile w h overlay])).log =
      g.log ++ frameDraws tess [viewTile w h v plot (DisplayList.concat (layers.map (·.list)))] ++
        frameDraws tess [pixelStrokeTile w h overlay] := by
  have := (retainedOps_draws tess c (.view w h v plot) layers held [pixelStrokeTile w h overlay] g
    (fun t ht => by
      simp only [retainedTiles, List.mem_append, List.mem_map, List.mem_singleton] at ht
      rcases ht with ⟨l, hl, rfl⟩ | rfl
      · exact Layer.viewTile_sound tess htess w h v plot l (hsound l hl)
      · exact Tile.sound_of_words_none tess _ rfl) hv).1
  rw [this, retainedTiles]
  have e : frameDraws tess (layers.map (TileKey.tile (.view w h v plot)) ++ [pixelStrokeTile w h overlay]) =
      frameDraws tess (layers.map (Layer.viewTile w h v plot)) ++ frameDraws tess [pixelStrokeTile w h overlay] := by
    simp only [frameDraws, List.flatMap_append]
    rfl
  rw [e, viewLayers_draws tess w h v plot layers hst, List.append_assoc]

theorem strokeLayersBytes_eq (r : Retained) (fresh : Bool) (w h : Nat) (layers held : List Layer)
    (bg : Scene.Color) :
    (strokeLayersBytes r fresh w h layers held bg).2 =
      ⟨(encode (frameSetup fresh bg ++
        (retainedOps (fun _ => []) r.cache (.pixel w h) layers held []).map Op.toCmd)).toArray⟩ :=
  retainedFrame_bytes _ r _ layers held [] _

theorem viewLayersBytes_eq (tess : Scene.Command → List UInt32) (r : Retained) (fresh : Bool) (w h : Nat)
    (v : View) (plot : Scene.Rect) (layers held : List Layer) (overlay : Scene.DisplayList)
    (bg : Scene.Color) :
    (viewLayersBytes tess r fresh w h v plot layers held overlay bg).2 =
      ⟨(encode (frameSetup fresh bg ++
        (retainedOps tess r.cache (.view w h v plot) layers held [pixelStrokeTile w h overlay]).map
          Op.toCmd)).toArray⟩ :=
  retainedFrame_bytes tess r _ layers held _ _

/-- The buffers a frame leaves are those `strokeLayersFrame` leaves. -/
theorem strokeLayersBytes_cache (tess : Scene.Command → List UInt32) (r : Retained) (fresh : Bool)
    (w h : Nat) (layers held : List Layer) (bg : Scene.Color) :
    (strokeLayersBytes r fresh w h layers held bg).1.cache =
      (strokeLayersFrame tess r.cache fresh w h layers held bg).1 := by
  have := retainedSetup_cache tess r.cache (.pixel w h) layers held []
  have e : retainedSetup (fun _ => []) r.cache layers held [] =
      retainedSetup tess r.cache layers held [] := rfl
  simp only [strokeLayersBytes, retainedFrame, e]
  rw [retainedTiles, List.append_nil] at this
  exact this

/-- The buffers a frame leaves are those `viewLayersFrame` leaves. -/
theorem viewLayersBytes_cache (tess : Scene.Command → List UInt32) (r : Retained) (fresh : Bool)
    (w h : Nat) (v : View) (plot : Scene.Rect) (layers held : List Layer) (overlay : Scene.DisplayList)
    (bg : Scene.Color) :
    (viewLayersBytes tess r fresh w h v plot layers held overlay bg).1.cache =
      (viewLayersFrame tess r.cache fresh w h v plot layers held overlay bg).1 := by
  have := retainedSetup_cache tess r.cache (.view w h v plot) layers held [pixelStrokeTile w h overlay]
  exact this

end Inkproof.Gpu
