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

theorem Layer.strokeCut_eq (list : Scene.DisplayList) :
    Layer.strokeCut list = Layer.cut (tessellateStroke ⟨0, 0⟩) list := rfl

theorem layerRunsStep_nil (c : Scene.Command) : layerRunsStep c [] = [[c]] := rfl

theorem layerRunsStep_cons (c : Scene.Command) (g : List Scene.Command) (gs : List (List Scene.Command)) :
    layerRunsStep c (g :: gs) =
      if g.head?.map (·.layer) == some c.layer then (c :: g) :: gs else [c] :: g :: gs := rfl

/-- The runs of `cs` hold its commands in order, each of one layer number. -/
theorem layerRuns_spec (cs : List Scene.Command) : (layerRuns cs).flatten = cs ∧
    ∀ g ∈ layerRuns cs, ∀ x ∈ g, ∀ y ∈ g, x.layer = y.layer := by
  induction cs with
  | nil => simp [layerRuns]
  | cons c cs ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hr : layerRuns (c :: cs) = layerRunsStep c (layerRuns cs) := rfl
    rw [hr]
    generalize layerRuns cs = L at ih1 ih2
    match L, ih1, ih2 with
    | [], ih1, _ => simp [layerRunsStep, ← ih1]
    | g :: gs, ih1, ih2 =>
      by_cases hc : (g.head?.map (·.layer)) == some c.layer
      · obtain ⟨a, g', rfl⟩ : ∃ a g', g = a :: g' := by
          cases g with
          | nil => simp at hc
          | cons a g' => exact ⟨a, g', rfl⟩
        have ha : a.layer = c.layer := by simpa using hc
        simp only [layerRunsStep, hc, ite_true]
        refine ⟨by simpa using ih1, fun g'' hg'' x hx y hy => ?_⟩
        have hsame := ih2 (a :: g') List.mem_cons_self
        rcases List.mem_cons.mp hg'' with rfl | hg''
        · have hl : ∀ z ∈ c :: a :: g', z.layer = c.layer := fun z hz => by
            rcases List.mem_cons.mp hz with rfl | hz
            · rfl
            · rw [← ha]; exact hsame z hz a List.mem_cons_self
          rw [hl x hx, hl y hy]
        · exact ih2 g'' (List.mem_cons_of_mem _ hg'') x hx y hy
      · simp only [layerRunsStep, hc]
        simp only [Bool.false_eq_true, ite_false]
        refine ⟨by simpa using ih1, fun g'' hg'' x hx y hy => ?_⟩
        rcases List.mem_cons.mp hg'' with rfl | hg''
        · simp at hx hy; rw [hx, hy]
        · exact ih2 g'' hg'' x hx y hy

/-- The lists of the pieces of a cut are its runs of equal layer in paint order. -/
theorem Layer.cut_lists (tess : Scene.Command → List UInt32) (list : Scene.DisplayList) :
    (Layer.cut tess list).map (·.list) = (layerRuns list.paintOrder).map List.toArray := by
  simp [Layer.cut, Layer.build, List.map_map, Function.comp_def]

/-- Each piece of a cut holds the commands of one layer number, and its words are `tess`'s. -/
theorem Layer.cut_sound (tess : Scene.Command → List UInt32) (list : Scene.DisplayList) :
    ∀ l ∈ Layer.cut tess list, l.Sound tess ∧ ∀ x ∈ l.list, ∀ y ∈ l.list, x.layer = y.layer := by
  intro l hl
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hl
  exact ⟨rfl, fun x hx y hy => (layerRuns_spec _).2 g hg x (Array.mem_def.mp hx) y (Array.mem_def.mp hy)⟩

/-- The pieces of a cut are stacked, lowest layer first. -/
theorem Layer.cut_stacked (tess : Scene.Command → List UInt32) (list : Scene.DisplayList) :
    DisplayList.Stacked ((Layer.cut tess list).map (·.list)) := by
  rw [Layer.cut_lists]
  have h := list.paintOrder_sorted
  rw [← (layerRuns_spec list.paintOrder).1, List.pairwise_flatten] at h
  simp only [DisplayList.Stacked, List.pairwise_map]
  exact h.2.imp fun {a b} hab x hx y hy => hab x (Array.mem_def.mp hx) y (Array.mem_def.mp hy)

/-- The concatenation of the pieces of a cut paints in the order `list` does. -/
theorem Layer.cut_paintOrder (tess : Scene.Command → List UInt32) (list : Scene.DisplayList) :
    (DisplayList.concat ((Layer.cut tess list).map (·.list))).paintOrder = list.paintOrder := by
  rw [paintOrder_concat _ (Layer.cut_stacked tess list), Layer.cut_lists]
  have hp : ∀ g ∈ layerRuns list.paintOrder, Scene.DisplayList.paintOrder g.toArray = g := by
    intro g hg
    refine List.mergeSort_of_pairwise ?_
    refine List.pairwise_of_forall_mem_list fun x hx y hy => ?_
    simpa using Nat.le_of_eq ((layerRuns_spec _).2 g hg x hx y hy)
  rw [List.flatMap_map]
  have hm : (layerRuns list.paintOrder).map (fun g => Scene.DisplayList.paintOrder g.toArray) =
      layerRuns list.paintOrder := (List.map_congr_left hp).trans (List.map_id _)
  rw [List.flatMap, hm]
  exact (layerRuns_spec list.paintOrder).1

/-- Drawing the pieces of a cut in pixels, in order, draws what one `pixelStrokeTile` of `list` draws, which is what `strokeFrame` draws for it. -/
theorem Layer.cut_draws (tess : Scene.Command → List UInt32) (w h : Nat) (list : Scene.DisplayList) :
    frameDraws tess ((Layer.cut tess list).map (Layer.pixelTile w h)) =
      frameDraws tess [pixelStrokeTile w h list] := by
  rw [strokeLayers_draws tess w h _ (Layer.cut_stacked tess list)]
  have hst : ∀ L c, (pixelStrokeTile w h L).stateOf c = (pixelStrokeTile w h list).stateOf c :=
    fun _ _ => rfl
  simp only [frameDraws, List.flatMap_cons, List.flatMap_nil, List.append_nil, hst]
  change List.map _ (DisplayList.concat _).paintOrder = List.map _ list.paintOrder
  rw [Layer.cut_paintOrder]

/-- Clipping to a view keeps the paint order. -/
theorem View.clip_paintOrder (v : View) (list : Scene.DisplayList) :
    (v.clip list).paintOrder = list.paintOrder.map fun c => { c with shape := .clipped ⟨v.x0, v.y0, v.x1, v.y1⟩ c.shape } := by
  simp only [Scene.DisplayList.paintOrder, View.clip, Array.toList_map]
  symm
  exact List.map_mergeSort (f := fun c : Scene.Command => { c with shape := .clipped ⟨v.x0, v.y0, v.x1, v.y1⟩ c.shape })
    (s := fun a b => decide (a.layer ≤ b.layer)) fun a _ b _ => rfl

/-- Drawing the pieces of a cut under a view, in order, draws what one `viewTile` of `list` draws, which is what `viewFrame` draws for it. -/
theorem Layer.cut_viewDraws (tess : Scene.Command → List UInt32) (w h : Nat) (v : View)
    (plot : Scene.Rect) (list : Scene.DisplayList) :
    frameDraws tess ((Layer.cut tess list).map (Layer.viewTile w h v plot)) =
      frameDraws tess [Inkproof.Gpu.viewTile w h v plot list] := by
  rw [viewLayers_draws tess w h v plot _ (Layer.cut_stacked tess list)]
  have hst : ∀ L c, (Inkproof.Gpu.viewTile w h v plot L).stateOf c = (Inkproof.Gpu.viewTile w h v plot list).stateOf c :=
    fun _ _ => rfl
  simp only [frameDraws, List.flatMap_cons, List.flatMap_nil, List.append_nil, hst]
  change List.map _ (v.clip _).paintOrder = List.map _ (v.clip list).paintOrder
  rw [View.clip_paintOrder, View.clip_paintOrder, Layer.cut_paintOrder]

theorem insertKey_mem (a k : Nat) (ks : List Nat) : k ∈ insertKey a ks ↔ k = a ∨ k ∈ ks := by
  induction ks with
  | nil => simp [insertKey]
  | cons b ks ih =>
    unfold insertKey
    by_cases h1 : a < b
    · simp [h1]
    · by_cases h2 : a = b
      · subst h2; simp
      · simp only [h1, h2, ↓reduceIte, List.mem_cons, ih]
        exact or_left_comm

theorem insertKey_sorted (a : Nat) (ks : List Nat) (h : ks.Pairwise (· < ·)) :
    (insertKey a ks).Pairwise (· < ·) := by
  induction ks with
  | nil => simp [insertKey]
  | cons b ks ih =>
    obtain ⟨hb, hks⟩ := List.pairwise_cons.mp h
    unfold insertKey
    by_cases h1 : a < b
    · simp only [h1, ↓reduceIte]
      exact List.pairwise_cons.mpr ⟨by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact h1
        · exact Nat.lt_trans h1 (hb x hx), h⟩
    · simp only [h1, ↓reduceIte]
      by_cases h2 : a = b
      · simp only [h2, ↓reduceIte]; exact h
      · simp only [h2, ↓reduceIte]
        refine List.pairwise_cons.mpr ⟨fun x hx => ?_, ih hks⟩
        rcases (insertKey_mem a x ks).mp hx with rfl | hx
        · omega
        · exact hb x hx

theorem layerKeys_mem (ns : List Nat) (k : Nat) : k ∈ layerKeys ns ↔ k ∈ ns := by
  induction ns with
  | nil => simp [layerKeys]
  | cons a ns ih =>
    have : layerKeys (a :: ns) = insertKey a (layerKeys ns) := rfl
    rw [this, insertKey_mem, ih]; simp

theorem layerKeys_sorted (ns : List Nat) : (layerKeys ns).Pairwise (· < ·) := by
  induction ns with
  | nil => simp [layerKeys]
  | cons a ns ih => exact insertKey_sorted a _ ih

/-- The commands of `list` on layer number `k`, as `Layer.cutMany` takes them. -/
private abbrev onLayer (k : Nat) (list : Scene.DisplayList) : Scene.DisplayList :=
  list.filter fun c => c.layer == k

private theorem onLayer_layer (k : Nat) (list : Scene.DisplayList) :
    ∀ x ∈ onLayer k list, x.layer = k := fun x hx => by
  have := (Array.mem_filter.mp hx).2
  simpa using this

private theorem onLayer_paintOrder (k : Nat) (list : Scene.DisplayList) :
    (onLayer k list).paintOrder = list.toList.filter fun c => c.layer == k := by
  have h : (onLayer k list).paintOrder = (onLayer k list).toList := by
    refine List.mergeSort_of_pairwise ?_
    refine List.pairwise_of_forall_mem_list fun x hx y hy => ?_
    have := onLayer_layer k list x (Array.mem_def.mpr hx)
    have := onLayer_layer k list y (Array.mem_def.mpr hy)
    simpa using Nat.le_of_eq (by omega)
  rw [h]
  simp [onLayer]

theorem Layer.cutMany_eq (tess : Scene.Command → List UInt32) (lists : List Scene.DisplayList) :
    Layer.cutMany tess lists =
      (layerKeys (lists.flatMap fun l => l.toList.map (·.layer))).map fun k =>
        lists.map fun l => Layer.build tess (onLayer k l) := rfl

theorem Layer.strokeCutMany_eq (lists : List Scene.DisplayList) :
    Layer.strokeCutMany lists = Layer.cutMany (tessellateStroke ⟨0, 0⟩) lists := rfl

/-- Every group has one layer per input list. -/
theorem Layer.cutMany_length (tess : Scene.Command → List UInt32) (lists : List Scene.DisplayList) :
    ∀ g ∈ Layer.cutMany tess lists, g.length = lists.length := by
  intro g hg
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hg
  simp

/-- Layer `j` of the group for number `k` is list `j` restricted to `k`, so lists with no command on `k` give an empty layer; and every number on a command of any list has a group, ascending. -/
theorem Layer.cutMany_list (tess : Scene.Command → List UInt32) (lists : List Scene.DisplayList)
    (g : List Layer) (hg : g ∈ Layer.cutMany tess lists) :
    ∃ k, (∃ l ∈ lists, ∃ c ∈ l, c.layer = k) ∧ g.map (·.list) = lists.map fun l => l.filter fun c => c.layer == k := by
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hg
  refine ⟨k, ?_, by simp [Layer.build]⟩
  obtain ⟨l, hl, hm⟩ := List.mem_flatMap.mp ((layerKeys_mem _ k).mp hk)
  obtain ⟨c, hc, he⟩ := List.mem_map.mp hm
  exact ⟨l, hl, c, Array.mem_def.mpr hc, he⟩

/-- The pieces are sound, each of one layer number. -/
theorem Layer.cutMany_sound (tess : Scene.Command → List UInt32) (lists : List Scene.DisplayList) :
    ∀ g ∈ Layer.cutMany tess lists, ∀ l ∈ g, l.Sound tess ∧ ∀ x ∈ l.list, ∀ y ∈ l.list, x.layer = y.layer := by
  intro g hg l hl
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hg
  obtain ⟨d, _, rfl⟩ := List.mem_map.mp hl
  exact ⟨rfl, fun x hx y hy => (onLayer_layer k d x hx).trans (onLayer_layer k d y hy).symm⟩

private theorem flatMap_ite_single {α : Type} (K : List Nat) (hnd : K.Nodup) (k : Nat) (X : List α) :
    (K.flatMap fun k' => if k' = k then X else []) = if k ∈ K then X else [] := by
  induction K with
  | nil => simp
  | cons a K ih =>
    obtain ⟨ha, hK⟩ := List.nodup_cons.mp hnd
    rw [List.flatMap_cons, ih hK]
    by_cases hak : a = k
    · subst hak; simp [ha]
    · simp [hak, Ne.symm hak]

/-- The layers of all the groups, flattened, are stacked. -/
theorem Layer.cutMany_stacked (tess : Scene.Command → List UInt32) (lists : List Scene.DisplayList) :
    DisplayList.Stacked ((Layer.cutMany tess lists).flatten.map (·.list)) := by
  have e : (Layer.cutMany tess lists).flatten.map (·.list) =
      (layerKeys (lists.flatMap fun l => l.toList.map (·.layer))).flatMap fun k => lists.map (onLayer k) := by
    simp [Layer.cutMany_eq, List.flatMap, List.map_flatten, List.map_map, Layer.build, Function.comp_def]
  rw [e, DisplayList.Stacked, List.pairwise_flatMap]
  refine ⟨fun k _ => ?_, ?_⟩
  · rw [List.pairwise_map]
    refine List.pairwise_of_forall_mem_list fun a _ b _ x hx y hy => ?_
    rw [onLayer_layer k a x hx, onLayer_layer k b y hy]; exact Nat.le_refl _
  · refine (layerKeys_sorted _).imp fun {a b} hab X hX Y hY x hx y hy => ?_
    obtain ⟨d, _, rfl⟩ := List.mem_map.mp hX
    obtain ⟨d', _, rfl⟩ := List.mem_map.mp hY
    rw [onLayer_layer a d x hx, onLayer_layer b d' y hy]
    exact Nat.le_of_lt hab

private theorem cutMany_flat (tess : Scene.Command → List UInt32) (lists : List Scene.DisplayList) :
    (Layer.cutMany tess lists).flatten.map (·.list) =
      (layerKeys (lists.flatMap fun l => l.toList.map (·.layer))).flatMap fun k => lists.map (onLayer k) := by
  simp [Layer.cutMany_eq, List.flatMap, List.map_flatten, List.map_map, Layer.build, Function.comp_def]

/-- The layers of all the groups, flattened, paint in the order of the concatenation of the lists: by layer number, and within one, list by list. -/
theorem Layer.cutMany_paintOrder (tess : Scene.Command → List UInt32) (lists : List Scene.DisplayList) :
    (DisplayList.concat ((Layer.cutMany tess lists).flatten.map (·.list))).paintOrder =
      (DisplayList.concat lists).paintOrder := by
  refine eq_of_sorted_filter _ _ (Scene.DisplayList.paintOrder_sorted _) (Scene.DisplayList.paintOrder_sorted _) fun k => ?_
  rw [Scene.DisplayList.paintOrder_layer, Scene.DisplayList.paintOrder_layer, DisplayList.concat_toList,
    DisplayList.concat_toList, cutMany_flat, List.filter_flatMap]
  have hin : ∀ k', (lists.map (onLayer k')).flatMap (fun a => a.toList.filter fun c => c.layer == k) =
      if k' = k then lists.flatMap (fun d => d.toList.filter fun c => c.layer == k) else [] := by
    intro k'
    rw [List.flatMap_map]
    by_cases h : k' = k
    · subst h
      simp [onLayer, List.filter_filter]
    · simp only [h, ite_false]
      refine List.flatMap_eq_nil_iff.mpr fun d _ => ?_
      simp [onLayer, List.filter_filter]
      intro c _ hc1 hc2
      exact h (hc1.symm.trans hc2).symm
  rw [List.flatMap_assoc, List.filter_flatMap]
  simp only [hin]
  rw [flatMap_ite_single _ ((layerKeys_sorted _).imp Nat.ne_of_lt)]
  by_cases hk : k ∈ layerKeys (lists.flatMap fun l => l.toList.map (·.layer))
  · simp [hk]
  · simp only [hk, ite_false]
    symm
    refine List.flatMap_eq_nil_iff.mpr fun d hd => ?_
    refine List.filter_eq_nil_iff.mpr fun c hc => ?_
    intro hck
    exact hk ((layerKeys_mem _ k).mpr (List.mem_flatMap.mpr ⟨d, hd, List.mem_map.mpr ⟨c, hc, by simpa using hck⟩⟩))

private theorem layerKeys_head (r : Scene.Command) (rs : List Scene.Command)
    (hs : (r :: rs).Pairwise fun a b => a.layer ≤ b.layer) :
    ∃ t, layerKeys ((r :: rs).map (·.layer)) = r.layer :: t := by
  have hmem : ∀ k, k ∈ layerKeys ((r :: rs).map (·.layer)) ↔ k ∈ (r :: rs).map (·.layer) := layerKeys_mem _
  have hsort := layerKeys_sorted ((r :: rs).map (·.layer))
  generalize layerKeys ((r :: rs).map (·.layer)) = K at hmem hsort
  have hr : r.layer ∈ K := (hmem _).mpr (by simp)
  cases K with
  | nil => simp at hr
  | cons h t =>
    refine ⟨t, ?_⟩
    have hle : r.layer ≤ h := by
      obtain ⟨y, hy, hyh⟩ := List.mem_map.mp ((hmem h).mp List.mem_cons_self)
      rcases List.mem_cons.mp hy with rfl | hy
      · omega
      · have := (List.pairwise_cons.mp hs).1 y hy; omega
    rcases List.mem_cons.mp hr with e | ht
    · rw [e]
    · have := (List.pairwise_cons.mp hsort).1 _ ht; omega

/-- The runs of a list sorted by layer number are its commands on each number present, ascending. -/
theorem layerRuns_sorted (cs : List Scene.Command) (hs : cs.Pairwise fun a b => a.layer ≤ b.layer) :
    layerRuns cs = (layerKeys (cs.map (·.layer))).map fun k => cs.filter fun c => c.layer == k := by
  induction cs with
  | nil => simp [layerRuns, layerKeys]
  | cons c rest ih =>
    obtain ⟨hc, hrest⟩ := List.pairwise_cons.mp hs
    have hr : layerRuns (c :: rest) = layerRunsStep c (layerRuns rest) := rfl
    have hk : layerKeys ((c :: rest).map (·.layer)) = insertKey c.layer (layerKeys (rest.map (·.layer))) := rfl
    rw [hr, hk]
    cases rest with
    | nil => simp [layerRuns, layerKeys, insertKey, layerRunsStep]
    | cons r rs =>
      obtain ⟨t, ht⟩ := layerKeys_head r rs hrest
      have hsort := layerKeys_sorted ((r :: rs).map (·.layer))
      rw [ht] at hsort
      have htgt := (List.pairwise_cons.mp hsort).1
      have htmem : ∀ k ∈ t, ∃ y ∈ r :: rs, y.layer = k := fun k hk' =>
        List.mem_map.mp ((layerKeys_mem _ k).mp (by rw [ht]; exact List.mem_cons_of_mem _ hk'))
      rw [ih hrest, ht]
      have hhead : (List.filter (fun c => c.layer == r.layer) (r :: rs)).head?.map (·.layer) = some r.layer := by
        simp
      simp only [List.map_cons, layerRunsStep, hhead]
      have hcr : c.layer ≤ r.layer := hc r List.mem_cons_self
      by_cases hcl : c.layer = r.layer
      · have e : insertKey c.layer (r.layer :: t) = r.layer :: t := by simp [insertKey, hcl]
        rw [e]
        simp only [hcl, beq_self_eq_true, ite_true, List.map_cons]
        refine List.cons_eq_cons.mpr ⟨?_, List.map_congr_left fun k hk' => ?_⟩
        · simp [hcl]
        · have : ¬ (c.layer == k) = true := by
            have := htgt k hk'; simp; omega
          exact (List.filter_cons_of_neg (p := fun x : Scene.Command => x.layer == k) this).symm
      · have hlt : c.layer < r.layer := by omega
        have e : insertKey c.layer (r.layer :: t) = c.layer :: r.layer :: t := by simp [insertKey, hlt]
        rw [e]
        have hne : (some r.layer == some c.layer) = false := by simp; omega
        simp only [hne, Bool.false_eq_true, ite_false, List.map_cons]
        have hrs : ∀ k, r.layer ≤ k → ¬ (c.layer == k) = true := fun k hk' => by simp; omega
        refine List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, List.map_congr_left fun k hk' => ?_⟩⟩
        · rw [List.filter_cons_of_pos (by simp)]
          congr 1
          rw [List.filter_eq_nil_iff.mpr]
          intro y hy
          have : r.layer ≤ y.layer := by
            rcases List.mem_cons.mp hy with rfl | hy
            · exact Nat.le_refl _
            · exact (List.pairwise_cons.mp hrest).1 y hy
          simp; omega
        · exact (List.filter_cons_of_neg (p := fun x : Scene.Command => x.layer == r.layer) (hrs _ (Nat.le_refl _))).symm
        · exact (List.filter_cons_of_neg (p := fun x : Scene.Command => x.layer == k) (hrs k (Nat.le_of_lt (htgt k hk')))).symm

theorem layerKeys_perm (ns ms : List Nat) (h : ns.Perm ms) : layerKeys ns = layerKeys ms := by
  have hnd : ∀ ns : List Nat, (layerKeys ns).Nodup := fun ns => (layerKeys_sorted ns).imp Nat.ne_of_lt
  refine List.Perm.eq_of_pairwise (le := (· < ·)) (fun a b _ _ h1 h2 => by omega)
    (layerKeys_sorted ns) (layerKeys_sorted ms) ?_
  exact (List.perm_ext_iff_of_nodup (hnd ns) (hnd ms)).mpr fun k => by
    rw [layerKeys_mem, layerKeys_mem]; exact h.mem_iff

/-- For one list, the groups are the layers of `Layer.cut`, one each. -/
theorem Layer.cutMany_single (tess : Scene.Command → List UInt32) (list : Scene.DisplayList) :
    Layer.cutMany tess [list] = (Layer.cut tess list).map fun l => [l] := by
  have hP := list.paintOrder_sorted
  have hkeys : layerKeys (list.paintOrder.map (·.layer)) =
      layerKeys ([list].flatMap fun l => l.toList.map (·.layer)) := by
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact layerKeys_perm _ _ ((Scene.DisplayList.paintOrder_perm list).map _)
  rw [Layer.cutMany_eq, Layer.cut, layerRuns_sorted _ hP, hkeys, List.map_map, List.map_map]
  refine List.map_congr_left fun k _ => ?_
  simp only [Function.comp_apply, List.map_cons, List.map_nil]
  have : (list.paintOrder.filter fun c => c.layer == k).toArray = onLayer k list := by
    apply Array.toList_inj.mp
    rw [Scene.DisplayList.paintOrder_layer]
    simp [onLayer]
  rw [this]

/-- Drawing the layers of all groups in pixels, in order, draws what one `pixelStrokeTile` of the lists one after the other draws. -/
theorem Layer.cutMany_draws (tess : Scene.Command → List UInt32) (w h : Nat) (lists : List Scene.DisplayList) :
    frameDraws tess ((Layer.cutMany tess lists).flatten.map (Layer.pixelTile w h)) =
      frameDraws tess [pixelStrokeTile w h (DisplayList.concat lists)] := by
  rw [strokeLayers_draws tess w h _ (Layer.cutMany_stacked tess lists)]
  have hst : ∀ L c, (pixelStrokeTile w h L).stateOf c = (pixelStrokeTile w h (DisplayList.concat lists)).stateOf c :=
    fun _ _ => rfl
  simp only [frameDraws, List.flatMap_cons, List.flatMap_nil, List.append_nil, hst]
  change List.map _ (DisplayList.concat _).paintOrder = List.map _ (DisplayList.concat lists).paintOrder
  rw [Layer.cutMany_paintOrder]

/-- Drawing the layers of all groups under a view, in order, draws what one `viewTile` of the lists one after the other draws. -/
theorem Layer.cutMany_viewDraws (tess : Scene.Command → List UInt32) (w h : Nat) (v : View)
    (plot : Scene.Rect) (lists : List Scene.DisplayList) :
    frameDraws tess ((Layer.cutMany tess lists).flatten.map (Layer.viewTile w h v plot)) =
      frameDraws tess [Inkproof.Gpu.viewTile w h v plot (DisplayList.concat lists)] := by
  rw [viewLayers_draws tess w h v plot _ (Layer.cutMany_stacked tess lists)]
  have hst : ∀ L c, (Inkproof.Gpu.viewTile w h v plot L).stateOf c =
      (Inkproof.Gpu.viewTile w h v plot (DisplayList.concat lists)).stateOf c := fun _ _ => rfl
  simp only [frameDraws, List.flatMap_cons, List.flatMap_nil, List.append_nil, hst]
  change List.map _ (v.clip _).paintOrder = List.map _ (v.clip (DisplayList.concat lists)).paintOrder
  rw [View.clip_paintOrder, View.clip_paintOrder, Layer.cutMany_paintOrder]

end Inkproof.Gpu
