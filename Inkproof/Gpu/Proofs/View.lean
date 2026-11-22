/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Gpu.Proofs.Frame
import Inkproof.Scale.Proofs.Affine
import Inkproof.Scale.Proofs.Linear

namespace Inkproof.Gpu

theorem viewX_apply (v : View) (plot : Scene.Rect) (x : Rat) :
    (viewX v plot).apply x = plot.x0 + (x - v.x0) * ((plot.x1 - plot.x0) / (v.x1 - v.x0)) := by
  unfold viewX
  rw [Scale.Linear.toAffine_eq]
  unfold Scale.Affine.apply
  dsimp only
  grind

theorem viewY_apply (v : View) (plot : Scene.Rect) (y : Rat) :
    (viewY v plot).apply y = plot.y1 + (y - v.y0) * ((plot.y0 - plot.y1) / (v.y1 - v.y0)) := by
  unfold viewY
  rw [Scale.Linear.toAffine_eq]
  unfold Scale.Affine.apply
  dsimp only
  grind

/-- The view's horizontal range fills the plot's. -/
theorem viewX_ends (v : View) (plot : Scene.Rect) (h : v.x0 ≠ v.x1) :
    (viewX v plot).apply v.x0 = plot.x0 ∧ (viewX v plot).apply v.x1 = plot.x1 := by
  have : v.x1 - v.x0 ≠ 0 := fun e => h (by grind)
  rw [viewX_apply, viewX_apply]
  constructor
  · grind
  · have : (v.x1 - v.x0) * ((plot.x1 - plot.x0) / (v.x1 - v.x0)) = plot.x1 - plot.x0 := by
      rw [Rat.div_def, Rat.mul_comm _ (_ * _), Rat.mul_assoc, Rat.inv_mul_cancel _ this, Rat.mul_one]
    grind

/-- The view's vertical range fills the plot's, `y0` at the bottom. -/
theorem viewY_ends (v : View) (plot : Scene.Rect) (h : v.y0 ≠ v.y1) :
    (viewY v plot).apply v.y0 = plot.y1 ∧ (viewY v plot).apply v.y1 = plot.y0 := by
  have : v.y1 - v.y0 ≠ 0 := fun e => h (by grind)
  rw [viewY_apply, viewY_apply]
  constructor
  · grind
  · have : (v.y1 - v.y0) * ((plot.y0 - plot.y1) / (v.y1 - v.y0)) = plot.y0 - plot.y1 := by
      rw [Rat.div_def, Rat.mul_comm _ (_ * _), Rat.mul_assoc, Rat.inv_mul_cancel _ this, Rat.mul_one]
    grind

/-- A data point's clip position under the view tile's map is that of its pixel position under the pixel map, exactly, before the uniforms are rounded to Float32. -/
theorem viewClip_x (w : Nat) (v : View) (plot : Scene.Rect) (x : Rat) :
    ((pixelX w).comp (viewX v plot)).apply x = (pixelX w).apply ((viewX v plot).apply x) :=
  Scale.Affine.comp_apply _ _ _

theorem viewClip_y (h : Nat) (v : View) (plot : Scene.Rect) (y : Rat) :
    ((pixelY h).comp (viewY v plot)).apply y = (pixelY h).apply ((viewY v plot).apply y) :=
  Scale.Affine.comp_apply _ _ _

theorem viewTile_slope (w h : Nat) (v : View) (plot : Scene.Rect) (l : Scene.DisplayList) :
    (viewTile w h v plot l).slope =
      [(ratToFloat32 ((pixelX w).comp (viewX v plot)).slope).toBits,
        (ratToFloat32 ((pixelY h).comp (viewY v plot)).slope).toBits] := rfl

theorem viewTile_offset (w h : Nat) (v : View) (plot : Scene.Rect) (l : Scene.DisplayList) :
    (viewTile w h v plot l).offset =
      [(ratToFloat32 ((pixelX w).comp (viewX v plot)).offset).toBits,
        (ratToFloat32 ((pixelY h).comp (viewY v plot)).offset).toBits] := rfl

theorem viewTile_list (w h : Nat) (v : View) (plot : Scene.Rect) (l : Scene.DisplayList) :
    (viewTile w h v plot l).list = v.clip l := rfl

/-- The scissor of a data rectangle is the pixel scissor of its image, corners in ascending order. -/
theorem viewScissor_eq (w h : Nat) (v : View) (plot r : Scene.Rect) :
    viewScissor w h v plot r =
      pixelScissor w h ⟨min ((viewX v plot).apply r.x0) ((viewX v plot).apply r.x1),
        min ((viewY v plot).apply r.y0) ((viewY v plot).apply r.y1),
        max ((viewX v plot).apply r.x0) ((viewX v plot).apply r.x1),
        max ((viewY v plot).apply r.y0) ((viewY v plot).apply r.y1)⟩ := rfl

theorem viewTile_scissor (w h : Nat) (v : View) (plot : Scene.Rect) (l : Scene.DisplayList) :
    (viewTile w h v plot l).scissor = viewScissor w h v plot := rfl

/-- Clipping to the view keeps each command's layer and shading and wraps its shape. -/
theorem View.clip_eq (v : View) (l : Scene.DisplayList) :
    v.clip l = l.map fun c => { c with shape := .clipped ⟨v.x0, v.y0, v.x1, v.y1⟩ c.shape } := rfl

/-- A clipped shape has the triangles of what it clips. -/
theorem tessellate_clipped (origin : Scene.Pt) (c : Scene.Command) (r : Scene.Rect) :
    tessellate origin { c with shape := .clipped r c.shape } = tessellate origin c := by
  simp [tessellate, triangles]

/-- A clipped shape has the stroke vertices of what it clips. -/
theorem tessellateStroke_clipped (origin : Scene.Pt) (c : Scene.Command) (r : Scene.Rect) :
    tessellateStroke origin { c with shape := .clipped r c.shape } = tessellateStroke origin c := by
  simp [tessellateStroke, strokeVertices]

theorem viewTile_view (w h : Nat) (v : View) (plot : Scene.Rect) (l : Scene.DisplayList) :
    (viewTile w h v plot l).view = viewWords w h := rfl

theorem viewTile_stride (w h : Nat) (v : View) (plot : Scene.Rect) (l : Scene.DisplayList) :
    (viewTile w h v plot l).stride = 6 := rfl

theorem viewTile_size (w h : Nat) (v : View) (plot : Scene.Rect) (l : Scene.DisplayList) :
    (viewTile w h v plot l).size = strokeSizeWords := rfl

/-- Clipping to a view reorders nothing, so a tessellator that ignores clips sees the same commands in the same order whatever the view. -/
theorem viewTile_cmds (tess : Scene.Command → List UInt32)
    (htess : ∀ (c : Scene.Command) (r : Scene.Rect), tess { c with shape := .clipped r c.shape } = tess c)
    (w h : Nat) (v : View) (plot : Scene.Rect) (l : Scene.DisplayList) :
    (viewTile w h v plot l).cmds tess = l.paintOrder.map tess := by
  simp only [Tile.cmds, viewTile, View.clip, Scene.DisplayList.paintOrder, Array.toList_map]
  rw [← List.map_mergeSort (f := fun c : Scene.Command =>
    ({ c with shape := .clipped ⟨v.x0, v.y0, v.x1, v.y1⟩ c.shape } : Scene.Command))
    (r := fun a b => decide (a.layer ≤ b.layer)) (by intro a _ b _; rfl)]
  simp [List.map_map, Function.comp_def, htess]

/-- A frame under one view is the setup followed by the wire commands of `compile` for the view's tile. -/
theorem viewFrame_eq (tess : Scene.Command → List UInt32) (c : Cache) (fresh : Bool) (w h : Nat)
    (v : View) (plot : Scene.Rect) (list : Scene.DisplayList) (bg : Scene.Color) :
    viewFrame tess c fresh w h v plot list bg =
      ((compile tess c [viewTile w h v plot list]).1,
        frameSetup fresh bg ++ (compile tess c [viewTile w h v plot list]).2.map Op.toCmd) := rfl

/-- A stroke frame is the setup followed by the wire commands of `compile` for the one pixel tile of strokes. -/
theorem strokeFrame_eq (tess : Scene.Command → List UInt32) (c : Cache) (fresh : Bool) (w h : Nat)
    (list : Scene.DisplayList) (bg : Scene.Color) :
    strokeFrame tess c fresh w h list bg =
      ((compile tess c [pixelStrokeTile w h list]).1,
        frameSetup fresh bg ++ (compile tess c [pixelStrokeTile w h list]).2.map Op.toCmd) := rfl

/-- `strokeFrameBytes` is the encoding of a fresh stroke frame, tessellated at the origin with an empty cache. -/
theorem strokeFrameBytes_eq (w h : Nat) (list : Scene.DisplayList) (bg : Scene.Color) :
    strokeFrameBytes w h list bg =
      ⟨(encode (strokeFrame (tessellateStroke ⟨0, 0⟩) {} true w h list bg).2).toArray⟩ := rfl

theorem viewFrameBytes_eq (w h : Nat) (v : View) (plot : Scene.Rect) (list : Scene.DisplayList)
    (bg : Scene.Color) :
    viewFrameBytes w h v plot list bg =
      ⟨(encode (viewFrame (tessellateStroke ⟨0, 0⟩) {} true w h v plot list bg).2).toArray⟩ := rfl

/-- After a frame of a list under one view, a frame of the same list under any other view creates and uploads nothing, whatever the targets and plots: it only sets uniforms, draws and deletes buffers it does not need. -/
theorem viewFrame_cached (tess : Scene.Command → List UInt32)
    (htess : ∀ (c : Scene.Command) (r : Scene.Rect), tess { c with shape := .clipped r c.shape } = tess c)
    (c : Cache) (w h : Nat) (v : View) (plot : Scene.Rect) (list : Scene.DisplayList)
    (w' h' : Nat) (v' : View) (plot' : Scene.Rect) :
    ∀ o ∈ (compile tess (compile tess c [viewTile w h v plot list]).1
      [viewTile w' h' v' plot' list]).2, ¬ o.IsUpload := by
  refine compile_cached tess _ _ fun t ht => ?_
  obtain rfl := List.mem_singleton.mp ht
  have := compile_cache_cached tess c [viewTile w h v plot list] _ (List.mem_singleton.mpr rfl)
  rw [Tile.Cached, viewTile_cmds tess htess, ← viewTile_cmds tess htess w h v plot list]
  exact this

/-- A frame of strips and markers sized in pixels, under another view, uploads nothing: their vertices are the same whatever the view, and only the transform and the view uniform change. -/
theorem viewFrame_stroke_cached (c : Cache) (w h : Nat) (v : View) (plot : Scene.Rect)
    (list : Scene.DisplayList) (w' h' : Nat) (v' : View) (plot' : Scene.Rect) :
    ∀ o ∈ (compile (tessellateStroke ⟨0, 0⟩)
      (compile (tessellateStroke ⟨0, 0⟩) c [viewTile w h v plot list]).1
      [viewTile w' h' v' plot' list]).2, ¬ o.IsUpload :=
  viewFrame_cached _ (tessellateStroke_clipped _) c w h v plot list w' h' v' plot'

theorem viewOverlayFrame_eq (tess : Scene.Command → List UInt32) (c : Cache) (fresh : Bool) (w h : Nat)
    (v : View) (plot : Scene.Rect) (list overlay : Scene.DisplayList) (bg : Scene.Color) :
    viewOverlayFrame tess c fresh w h v plot list overlay bg =
      ((compile tess c [viewTile w h v plot list, pixelStrokeTile w h overlay]).1,
        frameSetup fresh bg ++
          (compile tess c [viewTile w h v plot list, pixelStrokeTile w h overlay]).2.map Op.toCmd) := rfl

theorem viewOverlayFrameBytes_eq (w h : Nat) (v : View) (plot : Scene.Rect)
    (list overlay : Scene.DisplayList) (bg : Scene.Color) :
    viewOverlayFrameBytes w h v plot list overlay bg =
      ⟨(encode (viewOverlayFrame (tessellateStroke ⟨0, 0⟩) {} true w h v plot list overlay bg).2).toArray⟩ := rfl

theorem pixelStrokeTile_stride (w h : Nat) (l : Scene.DisplayList) :
    (pixelStrokeTile w h l).stride = 6 := rfl

theorem pixelStrokeTile_size (w h : Nat) (l : Scene.DisplayList) :
    (pixelStrokeTile w h l).size = strokeSizeWords := rfl

/-- The overlay tile is the pixel tile of its list with stroke vertices: only the stride and the size differ. -/
theorem pixelStrokeTile_eq (w h : Nat) (l : Scene.DisplayList) :
    pixelStrokeTile w h l = { pixelTile w h l with stride := 6, size := strokeSizeWords } := rfl

theorem pixelStrokeTile_cmds (tess : Scene.Command → List UInt32) (w h : Nat)
    (l : Scene.DisplayList) : (pixelStrokeTile w h l).cmds tess = l.paintOrder.map tess := rfl

private theorem overlay_data_cached (tess : Scene.Command → List UInt32)
    (htess : ∀ (c : Scene.Command) (r : Scene.Rect), tess { c with shape := .clipped r c.shape } = tess c)
    (c : Cache) (w h : Nat) (v : View) (plot : Scene.Rect) (list overlay : Scene.DisplayList)
    (w' h' : Nat) (v' : View) (plot' : Scene.Rect) :
    (viewTile w' h' v' plot' list).Cached tess
      (compile tess c [viewTile w h v plot list, pixelStrokeTile w h overlay]).1 := by
  have := compile_cache_cached tess c [viewTile w h v plot list, pixelStrokeTile w h overlay]
    (viewTile w h v plot list) (by simp)
  rw [Tile.Cached, viewTile_cmds tess htess, ← viewTile_cmds tess htess w h v plot list]
  exact this

/-- After a frame of a list and an overlay, a frame of the same list and overlay under any other view creates and uploads nothing. -/
theorem viewOverlayFrame_cached (tess : Scene.Command → List UInt32)
    (htess : ∀ (c : Scene.Command) (r : Scene.Rect), tess { c with shape := .clipped r c.shape } = tess c)
    (c : Cache) (w h : Nat) (v : View) (plot : Scene.Rect) (list overlay : Scene.DisplayList)
    (w' h' : Nat) (v' : View) (plot' : Scene.Rect) :
    ∀ o ∈ (compile tess (compile tess c [viewTile w h v plot list, pixelStrokeTile w h overlay]).1
      [viewTile w' h' v' plot' list, pixelStrokeTile w' h' overlay]).2, ¬ o.IsUpload := by
  refine compile_cached tess _ _ fun t ht => ?_
  rcases List.mem_cons.mp ht with rfl | ht
  · exact overlay_data_cached tess htess c w h v plot list overlay _ _ _ _
  · obtain rfl := List.mem_singleton.mp ht
    have := compile_cache_cached tess c [viewTile w h v plot list, pixelStrokeTile w h overlay]
      (pixelStrokeTile w h overlay) (by simp)
    simpa [Tile.Cached, pixelStrokeTile_cmds] using this

private theorem deletes_not_upload (b n : Nat) : ∀ o ∈ deletes b n, ¬ o.IsUpload := by
  induction n generalizing b with
  | zero => simp [deletes]
  | succ n ih =>
    intro o ho
    simp only [deletes, List.mem_cons] at ho
    rcases ho with rfl | ho
    · simp [Op.IsUpload]
    · exact ih _ o ho

private theorem compile_cached_head (tess : Scene.Command → List UInt32) (c' : Cache) (d a : Tile)
    (hd : d.Cached tess c') :
    ∀ o ∈ (compile tess c' [d, a]).2, o.IsUpload → ∃ b, o ∈ uploads b (a.cmds tess) := by
  obtain ⟨e, he, hw⟩ := hd
  intro o ho hu
  let s0 : Stage := ⟨{ c' with entries := c'.entries.filter (fun e =>
      [d, a].any (fun t => decide (e.words = t.cmds tess))) },
    (c'.entries.filter (fun e => !([d, a].any (fun t => decide (e.words = t.cmds tess))))).flatMap
      (fun e => deletes e.base e.words.length), []⟩
  have hs0 : s0 = ⟨{ c' with entries := c'.entries.filter (fun e =>
      [d, a].any (fun t => decide (e.words = t.cmds tess))) },
    (c'.entries.filter (fun e => !([d, a].any (fun t => decide (e.words = t.cmds tess))))).flatMap
      (fun e => deletes e.base e.words.length), []⟩ := rfl
  have hfind : ∃ e', s0.cache.entries.find? (fun e => decide (e.words = d.cmds tess)) = some e' := by
    have : (s0.cache.entries.find? fun e => decide (e.words = d.cmds tess)).isSome := by
      rw [List.find?_isSome]
      exact ⟨e, by simp [hs0, he, hw], by simpa using hw⟩
    exact Option.isSome_iff_exists.mp this
  obtain ⟨e', he'⟩ := hfind
  have h1 : stageTile tess s0 d = { s0 with items := s0.items ++ itemsOf e'.base (d.items tess) } := by
    simp [stageTile, he']
  have hops : ∀ o ∈ s0.ops, ¬ o.IsUpload := by
    intro o ho
    simp only [hs0, List.mem_flatMap] at ho
    obtain ⟨e, _, ho⟩ := ho
    exact deletes_not_upload _ _ o ho
  have h2 : ∀ x ∈ (stageTile tess (stageTile tess s0 d) a).ops, x.IsUpload → ∃ b, x ∈ uploads b (a.cmds tess) := by
    intro x hx hxu
    rw [h1] at hx
    unfold stageTile at hx
    dsimp only at hx
    split at hx
    · exact absurd hxu (hops x hx)
    · simp only [List.mem_append] at hx
      rcases hx with hx | hx
      · exact absurd hxu (hops x hx)
      · exact ⟨_, hx⟩
  simp only [compile, List.foldl_cons, List.foldl_nil, List.mem_append] at ho
  rcases ho with ho | ho
  · exact h2 o ho hu
  · obtain ⟨i, _, ho⟩ := mem_itemsOps _ _ _ ho
    simp only [Item.ops_none, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Op.IsUpload] at hu


/-- A frame of the same list under another view, with any overlay, uploads only buffers of the overlay's vertices: the list's are not uploaded again. -/
theorem viewOverlayFrame_data_cached (tess : Scene.Command → List UInt32)
    (htess : ∀ (c : Scene.Command) (r : Scene.Rect), tess { c with shape := .clipped r c.shape } = tess c)
    (c : Cache) (w h : Nat) (v : View) (plot : Scene.Rect) (list overlay : Scene.DisplayList)
    (w' h' : Nat) (v' : View) (plot' : Scene.Rect) (overlay' : Scene.DisplayList) :
    ∀ o ∈ (compile tess (compile tess c [viewTile w h v plot list, pixelStrokeTile w h overlay]).1
      [viewTile w' h' v' plot' list, pixelStrokeTile w' h' overlay']).2,
      o.IsUpload → ∃ b, o ∈ uploads b (overlay'.paintOrder.map tess) :=
  compile_cached_head tess _ _ _ (overlay_data_cached tess htess c w h v plot list overlay w' h' v' plot')

end Inkproof.Gpu
