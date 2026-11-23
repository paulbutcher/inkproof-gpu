/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Gpu.Proofs.View

namespace Inkproof.Gpu

/-- The words of a layer are those of its commands under `tess`. -/
def Layer.Sound (tess : Scene.Command → List UInt32) (l : Layer) : Prop :=
  l.words = l.list.paintOrder.map tess

theorem Layer.build_sound (tess : Scene.Command → List UInt32) (list : Scene.DisplayList) :
    (Layer.build tess list).Sound tess := rfl

theorem Layer.stroke_sound (list : Scene.DisplayList) :
    (Layer.stroke list).Sound (tessellateStroke ⟨0, 0⟩) := rfl

theorem Layer.stroke_eq (list : Scene.DisplayList) :
    Layer.stroke list = Layer.build (tessellateStroke ⟨0, 0⟩) list := rfl

theorem Layer.build_words (tess : Scene.Command → List UInt32) (list : Scene.DisplayList) :
    (Layer.build tess list).words = list.paintOrder.map tess := rfl

theorem Layer.pixelTile_cmds (tess : Scene.Command → List UInt32) (w h : Nat) (l : Layer) :
    (l.pixelTile w h).cmds tess = l.words := rfl

theorem Layer.viewTile_cmds (tess : Scene.Command → List UInt32) (w h : Nat) (v : View)
    (plot : Scene.Rect) (l : Layer) : (l.viewTile w h v plot).cmds tess = l.words := rfl

/-- A tile of a sound layer is sound. -/
theorem Layer.pixelTile_sound (tess : Scene.Command → List UInt32) (w h : Nat) (l : Layer)
    (hl : l.Sound tess) : (l.pixelTile w h).Sound tess := hl

/-- A tile of a sound layer under a view is sound, for a tessellator that ignores clips. -/
theorem Layer.viewTile_sound (tess : Scene.Command → List UInt32)
    (htess : ∀ (c : Scene.Command) (r : Scene.Rect), tess { c with shape := .clipped r c.shape } = tess c)
    (w h : Nat) (v : View) (plot : Scene.Rect) (l : Layer) (hl : l.Sound tess) :
    (l.viewTile w h v plot).Sound tess := by
  have := Inkproof.Gpu.viewTile_cmds tess htess w h v plot l.list
  unfold Tile.Sound
  rw [Layer.viewTile_cmds, hl]
  exact this.symm.trans rfl

theorem strokeLayersFrame_eq (tess : Scene.Command → List UInt32) (c : Cache) (fresh : Bool) (w h : Nat)
    (layers held : List Layer) (bg : Scene.Color) :
    strokeLayersFrame tess c fresh w h layers held bg =
      ((compileKeeping tess c (held.map (·.words)) (layers.map (Layer.pixelTile w h))).1,
        frameSetup fresh bg ++
          (compileKeeping tess c (held.map (·.words)) (layers.map (Layer.pixelTile w h))).2.map Op.toCmd) := rfl

theorem viewLayersFrame_eq (tess : Scene.Command → List UInt32) (c : Cache) (fresh : Bool) (w h : Nat)
    (v : View) (plot : Scene.Rect) (layers held : List Layer) (overlay : Scene.DisplayList)
    (bg : Scene.Color) :
    viewLayersFrame tess c fresh w h v plot layers held overlay bg =
      ((compileKeeping tess c (held.map (·.words))
          (layers.map (Layer.viewTile w h v plot) ++ [pixelStrokeTile w h overlay])).1,
        frameSetup fresh bg ++
          (compileKeeping tess c (held.map (·.words))
            (layers.map (Layer.viewTile w h v plot) ++ [pixelStrokeTile w h overlay])).2.map Op.toCmd) := rfl

/-- After a frame that draws `layers` and keeps `held`, a frame under any other view, of the same overlay and of any layers that were drawn or were kept while already in the cache, creates and uploads nothing: it tessellates no layer, and it only sets uniforms, draws and deletes buffers it does not need. -/
theorem viewLayersFrame_cached (tess : Scene.Command → List UInt32) (c : Cache) (w h : Nat) (v : View)
    (plot : Scene.Rect) (layers held : List Layer) (overlay : Scene.DisplayList)
    (w' h' : Nat) (v' : View) (plot' : Scene.Rect) (layers' held' : List Layer)
    (hl : ∀ l ∈ layers', l ∈ layers ∨ (l ∈ held ∧ ∃ e ∈ c.entries, e.words = l.words)) :
    ∀ o ∈ (compileKeeping tess
      (compileKeeping tess c (held.map (·.words))
        (layers.map (Layer.viewTile w h v plot) ++ [pixelStrokeTile w h overlay])).1
      (held'.map (·.words))
      (layers'.map (Layer.viewTile w' h' v' plot') ++ [pixelStrokeTile w' h' overlay])).2,
      ¬ o.IsUpload := by
  refine compileKeeping_cached tess _ _ _ fun t ht => ?_
  rcases List.mem_append.mp ht with ht | ht
  · obtain ⟨l, hl', rfl⟩ := List.mem_map.mp ht
    rcases hl l hl' with hd | ⟨hh, e, he, hw⟩
    · have := compileKeeping_cache_cached tess c (held.map (·.words))
        (layers.map (Layer.viewTile w h v plot) ++ [pixelStrokeTile w h overlay])
        (l.viewTile w h v plot) (List.mem_append_left _ (List.mem_map_of_mem hd))
      simpa [Tile.Cached, Layer.viewTile_cmds] using this
    · refine ⟨e, compileKeeping_kept tess c _ _ e he ?_, by simpa [Layer.viewTile_cmds] using hw⟩
      exact List.mem_map.mpr ⟨l, hh, hw.symm⟩
  · obtain rfl := List.mem_singleton.mp ht
    have := compileKeeping_cache_cached tess c (held.map (·.words))
      (layers.map (Layer.viewTile w h v plot) ++ [pixelStrokeTile w h overlay])
      (pixelStrokeTile w h overlay) (by simp)
    simpa [Tile.Cached, pixelStrokeTile_cmds] using this

private theorem eq_of_sorted_filter :
    ∀ (X Y : List Scene.Command), X.Pairwise (fun a b => a.layer ≤ b.layer) →
      Y.Pairwise (fun a b => a.layer ≤ b.layer) →
      (∀ k, X.filter (fun c => c.layer == k) = Y.filter (fun c => c.layer == k)) → X = Y := by
  intro X
  induction X with
  | nil =>
    intro Y _ hY h
    cases Y with
    | nil => rfl
    | cons y ys =>
      have := h y.layer
      simp at this
  | cons x xs ih =>
    intro Y hX hY h
    cases Y with
    | nil =>
      have := h x.layer
      simp at this
    | cons y ys =>
      have hxy : x.layer = y.layer := by
        have h1 : y.layer ≤ x.layer := by
          have := h x.layer
          have hne : (y :: ys).filter (fun c => c.layer == x.layer) ≠ [] := by
            rw [← this]; simp
          obtain ⟨z, hz⟩ := List.exists_mem_of_ne_nil _ hne
          obtain ⟨hz1, hz2⟩ := List.mem_filter.mp hz
          rcases List.mem_cons.mp hz1 with rfl | hz1
          · simp at hz2; omega
          · have := (List.pairwise_cons.mp hY).1 z hz1
            simp at hz2; omega
        have h2 : x.layer ≤ y.layer := by
          have := h y.layer
          have hne : (x :: xs).filter (fun c => c.layer == y.layer) ≠ [] := by
            rw [this]; simp
          obtain ⟨z, hz⟩ := List.exists_mem_of_ne_nil _ hne
          obtain ⟨hz1, hz2⟩ := List.mem_filter.mp hz
          rcases List.mem_cons.mp hz1 with rfl | hz1
          · simp at hz2; omega
          · have := (List.pairwise_cons.mp hX).1 z hz1
            simp at hz2; omega
        omega
      have hk := h x.layer
      rw [List.filter_cons_of_pos (by simp), List.filter_cons_of_pos (by simp [hxy])] at hk
      obtain ⟨rfl, hrest⟩ := List.cons.inj hk
      refine congrArg (x :: ·) (ih ys (List.pairwise_cons.mp hX).2 (List.pairwise_cons.mp hY).2 fun k => ?_)
      by_cases hkx : k = x.layer
      · subst hkx; exact hrest
      · have := h k
        simpa [List.filter_cons, Ne.symm hkx] using this

/-- Painting two display lists one after the other, the first never above the second, is painting their concatenation. -/
theorem paintOrder_append (a b : Scene.DisplayList) (h : ∀ x ∈ a, ∀ y ∈ b, x.layer ≤ y.layer) :
    (a ++ b).paintOrder = a.paintOrder ++ b.paintOrder := by
  refine eq_of_sorted_filter _ _ (a ++ b).paintOrder_sorted ?_ fun k => ?_
  · rw [List.pairwise_append]
    refine ⟨a.paintOrder_sorted, b.paintOrder_sorted, fun x hx y hy => h x ?_ y ?_⟩
    · exact Array.mem_def.mpr (a.paintOrder_perm.mem_iff.mp hx)
    · exact Array.mem_def.mpr (b.paintOrder_perm.mem_iff.mp hy)
  · rw [(a ++ b).paintOrder_layer, List.filter_append, a.paintOrder_layer, b.paintOrder_layer]
    simp [Array.toList_append, List.filter_append]

/-- The commands of display lists one after the other. -/
def DisplayList.concat (ls : List Scene.DisplayList) : Scene.DisplayList :=
  (ls.flatMap Array.toList).toArray

theorem DisplayList.concat_toList (ls : List Scene.DisplayList) :
    (DisplayList.concat ls).toList = ls.flatMap Array.toList := rfl

/-- Display lists none of which paints above a later one: each command of an earlier list is on a layer no higher than each of a later list. -/
def DisplayList.Stacked (ls : List Scene.DisplayList) : Prop :=
  ls.Pairwise fun a b => ∀ x ∈ a, ∀ y ∈ b, x.layer ≤ y.layer

/-- Painting stacked display lists one after the other is painting their concatenation. -/
theorem paintOrder_concat (ls : List Scene.DisplayList) (h : DisplayList.Stacked ls) :
    (DisplayList.concat ls).paintOrder = ls.flatMap Scene.DisplayList.paintOrder := by
  induction ls with
  | nil => simp [DisplayList.concat, Scene.DisplayList.paintOrder]
  | cons a rest ih =>
    obtain ⟨hab, hrest⟩ := List.pairwise_cons.mp h
    have hc : DisplayList.concat (a :: rest) = a ++ DisplayList.concat rest := by
      apply Array.toList_inj.mp
      simp [DisplayList.concat]
    rw [hc, List.flatMap_cons, ← ih hrest]
    refine paintOrder_append _ _ fun x hx y hy => ?_
    simp only [DisplayList.concat, Array.mem_def, List.mem_flatMap] at hy
    obtain ⟨b, hb, hyb⟩ := hy
    exact hab b hb x hx y (Array.mem_def.mpr hyb)

/-- Tiles of `as`, each with the commands `lst` gives and the state of `base`, drawn in the order given, draw what one tile of the concatenated commands draws. -/
theorem frameDraws_concat {α : Type} (tess : Scene.Command → List UInt32) (base : Tile)
    (as : List α) (lst : α → Scene.DisplayList) (mk : α → Tile)
    (hl : ∀ a, (mk a).list = lst a) (hst : ∀ a, (mk a).stateOf = base.stateOf)
    (h : DisplayList.Stacked (as.map lst)) :
    frameDraws tess (as.map mk) =
      frameDraws tess [{ base with list := DisplayList.concat (as.map lst), words := none }] := by
  have hd : ∀ L : Scene.DisplayList, frameDraws tess [{ base with list := L, words := none }] =
      L.paintOrder.map fun c => Draw.mk (tess c) ((tess c).length / (base.stateOf c).stride) (base.stateOf c) :=
    fun L => by
      simp only [frameDraws, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      exact List.map_congr_left fun c _ => rfl
  have e : frameDraws tess (as.map mk) =
      as.flatMap fun a => (lst a).paintOrder.map fun c =>
        Draw.mk (tess c) ((tess c).length / (base.stateOf c).stride) (base.stateOf c) := by
    simp only [frameDraws, List.flatMap_map, hl, hst]
  rw [e, hd, paintOrder_concat _ h, List.map_flatMap, List.flatMap_map]

/-- Layers drawn in pixels, in the order given, draw what one `pixelStrokeTile` of the concatenation of their lists draws, which is what `strokeFrame` draws for it. -/
theorem strokeLayers_draws (tess : Scene.Command → List UInt32) (w h : Nat) (layers : List Layer)
    (hs : DisplayList.Stacked (layers.map (·.list))) :
    frameDraws tess (layers.map (Layer.pixelTile w h)) =
      frameDraws tess [pixelStrokeTile w h (DisplayList.concat (layers.map (·.list)))] :=
  frameDraws_concat tess (pixelStrokeTile w h #[]) layers (·.list) (Layer.pixelTile w h)
    (fun _ => rfl) (fun _ => rfl) hs

/-- Layers drawn under a view, in the order given, draw what one `viewTile` of the concatenation of their lists draws, which is what `viewFrame` draws for it. -/
theorem viewLayers_draws (tess : Scene.Command → List UInt32) (w h : Nat) (v : View)
    (plot : Scene.Rect) (layers : List Layer)
    (hs : DisplayList.Stacked (layers.map (·.list))) :
    frameDraws tess (layers.map (Layer.viewTile w h v plot)) =
      frameDraws tess [viewTile w h v plot (DisplayList.concat (layers.map (·.list)))] := by
  have hc : v.clip (DisplayList.concat (layers.map (·.list))) =
      DisplayList.concat (layers.map fun l => v.clip l.list) := by
    apply Array.toList_inj.mp
    simp [View.clip, DisplayList.concat, List.map_flatMap, List.flatMap_map]
  have hs' : DisplayList.Stacked (layers.map fun l => v.clip l.list) := by
    simp only [DisplayList.Stacked, List.pairwise_map] at hs ⊢
    refine hs.imp fun {a b} hab x hx y hy => ?_
    obtain ⟨x', hx', rfl⟩ := Array.mem_map.mp hx
    obtain ⟨y', hy', rfl⟩ := Array.mem_map.mp hy
    exact hab x' hx' y' hy'
  have := frameDraws_concat tess (Inkproof.Gpu.viewTile w h v plot #[]) layers (fun l => v.clip l.list)
    (Layer.viewTile w h v plot) (fun _ => rfl) (fun _ => rfl) (by simpa [List.map_map, Function.comp_def] using hs')
  rw [this, ← hc]
  rfl

end Inkproof.Gpu
