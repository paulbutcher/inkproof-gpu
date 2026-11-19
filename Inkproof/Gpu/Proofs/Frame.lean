/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Gpu.Frame
import Inkproof.Gpu.Proofs.Compile

namespace Inkproof.Gpu

/-- The column map sends pixel `x` to clip `2x/w - 1`. -/
theorem pixelX_apply (w : Nat) (x : Rat) : (pixelX w).apply x = 2 * x / w - 1 := by
  unfold Scale.Affine.apply
  simp only [pixelX, Rat.div_def, Rat.sub_eq_add_neg]
  grind

/-- The row map sends pixel row `y` from the top to clip `1 - 2y/h`. -/
theorem pixelY_apply (h : Nat) (y : Rat) : (pixelY h).apply y = 1 - 2 * y / h := by
  unfold Scale.Affine.apply
  simp only [pixelY, Rat.div_def, Rat.sub_eq_add_neg]
  grind

theorem pixelTile_slope (w h : Nat) (l : Scene.DisplayList) :
    (pixelTile w h l).slope =
      [(ratToFloat32 (pixelX w).slope).toBits, (ratToFloat32 (pixelY h).slope).toBits] := rfl

theorem pixelTile_offset (w h : Nat) (l : Scene.DisplayList) :
    (pixelTile w h l).offset =
      [(ratToFloat32 (pixelX w).offset).toBits, (ratToFloat32 (pixelY h).offset).toBits] := rfl

theorem pixelScissor_eq (w h : Nat) (r : Scene.Rect) :
    pixelScissor w h r =
      [(pixelBox w h r).1.toUInt32, (pixelBox w h r).2.1.toUInt32,
        (pixelBox w h r).2.2.1.toUInt32, (pixelBox w h r).2.2.2.toUInt32] := rfl

/-- The scissor box covers every pixel of the target whose cell meets the rectangle, the row of pixel `j` from the top being row `h - 1 - j` from the bottom. -/
theorem pixelBox_covers (w h : Nat) (r : Scene.Rect) (i j : Nat) (hi : i < w) (hj : j < h)
    (hx1 : (i : Rat) < r.x1) (hx0 : r.x0 < i + 1) (hy1 : (j : Rat) < r.y1) (hy0 : r.y0 < j + 1) :
    (pixelBox w h r).1 ≤ i ∧ i < (pixelBox w h r).1 + (pixelBox w h r).2.2.1 ∧
    (pixelBox w h r).2.1 ≤ h - 1 - j ∧ h - 1 - j < (pixelBox w h r).2.1 + (pixelBox w h r).2.2.2 := by
  have a1 : r.x0.floor ≤ (i : Int) := by
    refine Int.not_lt.mp fun hc => ?_
    have : ((i : Int) + 1 : Int) ≤ r.x0.floor := by omega
    have := Rat.le_floor_iff.mp this
    push_cast at this
    grind
  have a2 : (i : Int) < r.x1.ceil := by
    exact Rat.lt_ceil_iff.mpr (by exact_mod_cast hx1)
  have a3 : r.y0.floor ≤ (j : Int) := by
    refine Int.not_lt.mp fun hc => ?_
    have : ((j : Int) + 1 : Int) ≤ r.y0.floor := by omega
    have := Rat.le_floor_iff.mp this
    push_cast at this
    grind
  have a4 : (j : Int) < r.y1.ceil := by
    exact Rat.lt_ceil_iff.mpr (by exact_mod_cast hy1)
  simp only [pixelBox]
  omega

/-- The word is red, green, blue and alpha as the bytes of a 32-bit number, red most significant. -/
theorem clearWord_toNat (c : Scene.Color) :
    (clearWord c).toNat =
      c.r.toNat * 2 ^ 24 + c.g.toNat * 2 ^ 16 + c.b.toNat * 2 ^ 8 + c.a.toNat := by
  have := c.r.toNat_lt; have := c.g.toNat_lt; have := c.b.toNat_lt; have := c.a.toNat_lt
  simp only [clearWord, UInt32.toNat_add, UInt32.toNat_mul, UInt8.toNat_toUInt32]
  simp
  omega

theorem frameSetup_fresh (bg : Scene.Color) :
    frameSetup true bg = [⟨7, [.u32 programHandle]⟩] ++ frameSetup false bg := rfl

theorem frameSetup_stale (bg : Scene.Color) :
    frameSetup false bg =
      [⟨3, [.u32 programHandle]⟩, ⟨8, [.words []]⟩, ⟨6, [.u32 (clearWord bg)]⟩] := rfl

/-- A frame is the setup followed by the wire commands of `compile` for the one pixel tile. -/
theorem frame_eq (tess : Scene.Command → List UInt32) (c : Cache) (fresh : Bool) (w h : Nat)
    (list : Scene.DisplayList) (bg : Scene.Color) :
    frame tess c fresh w h list bg =
      ((compile tess c [pixelTile w h list]).1,
        frameSetup fresh bg ++ (compile tess c [pixelTile w h list]).2.map Op.toCmd) := rfl

/-- `frameBytes` is the encoding of a fresh frame, tessellated at the origin with an empty cache. -/
theorem frameBytes_eq (w h : Nat) (list : Scene.DisplayList) (bg : Scene.Color) :
    frameBytes w h list bg =
      ⟨(encode (frame (tessellate ⟨0, 0⟩) {} true w h list bg).2).toArray⟩ := rfl

theorem programHandle_eq : programHandle = 0 := rfl

/-- The operation's word lists fit the wire's 32-bit length. -/
def Op.Fits : Op → Prop
  | .upload _ ws | .uniform _ ws | .scissor ws => ws.length < UInt32.size
  | _ => True

private theorem Op.Fits.wellFormed {o : Op} (h : o.Fits) : o.toCmd.WellFormed := by
  cases o <;> simp_all [Op.Fits, Op.toCmd, Cmd.WellFormed, specOf, specs, ArgsFit, Arg.Fits]

private def Item.Fits (i : Item) : Prop :=
  i.state.slope.length < UInt32.size ∧ i.state.offset.length < UInt32.size ∧
    i.state.colour.length < UInt32.size ∧ i.state.scissor.length < UInt32.size

private theorem itemsOf_fits (tess : Scene.Command → List UInt32) (t : Tile)
    (hs : t.slope.length < UInt32.size) (ho : t.offset.length < UInt32.size)
    (hc : ∀ r, (t.scissor r).length < UInt32.size) :
    ∀ (b : Nat) (ps : List (List UInt32 × State)), (∀ p ∈ ps, ∃ c ∈ t.list.paintOrder, p = (tess c, t.stateOf c)) →
      ∀ i ∈ itemsOf b ps, i.Fits := by
  intro b ps
  induction ps generalizing b with
  | nil => simp [itemsOf]
  | cons p ps ih =>
    intro hp i hi
    obtain ⟨w, u⟩ := p
    simp only [itemsOf, List.mem_cons] at hi
    rcases hi with rfl | hi
    · obtain ⟨c, _, he⟩ := hp (w, u) (List.mem_cons_self ..)
      obtain ⟨-, rfl⟩ := Prod.mk.inj he
      refine ⟨hs, ho, by simp [Tile.stateOf, colourWords, UInt32.size], ?_⟩
      simp only [Tile.stateOf]
      split
      · simp [UInt32.size]
      · simp [UInt32.size]
      · exact hc _
    · exact ih (b + 1) (fun q hq => hp q (List.mem_cons_of_mem _ hq)) i hi

/-- Every operation of a frame fits the wire when the vertex words of every command and the words of every tile do. -/
theorem compile_fits (tess : Scene.Command → List UInt32) (c : Cache) (tiles : List Tile)
    (htess : ∀ x, (tess x).length < UInt32.size)
    (ht : ∀ t ∈ tiles, t.slope.length < UInt32.size ∧ t.offset.length < UInt32.size ∧
      ∀ r, (t.scissor r).length < UInt32.size) :
    ∀ o ∈ (compile tess c tiles).2, o.Fits := by
  have hup : ∀ (b : Nat) (ws : List (List UInt32)), (∀ w ∈ ws, w.length < UInt32.size) →
      ∀ o ∈ uploads b ws, o.Fits := by
    intro b ws
    induction ws generalizing b with
    | nil => simp [uploads]
    | cons w ws ih =>
      intro h o ho
      simp only [uploads, List.mem_cons] at ho
      rcases ho with rfl | rfl | ho
      · trivial
      · exact h w (List.mem_cons_self ..)
      · exact ih _ (fun x hx => h x (List.mem_cons_of_mem _ hx)) o ho
  have hdel : ∀ (b n : Nat), ∀ o ∈ deletes b n, o.Fits := by
    intro b n
    induction n generalizing b with
    | zero => simp [deletes]
    | succ n ih =>
      intro o ho
      simp only [deletes, List.mem_cons] at ho
      rcases ho with rfl | ho
      · trivial
      · exact ih _ o ho
  have key : ∀ (ts : List Tile), (∀ t ∈ ts, t ∈ tiles) → ∀ (s : Stage), (∀ o ∈ s.ops, o.Fits) →
      (∀ i ∈ s.items, i.Fits) →
      (∀ o ∈ (ts.foldl (stageTile tess) s).ops, o.Fits) ∧
      ∀ i ∈ (ts.foldl (stageTile tess) s).items, i.Fits := by
    intro ts
    induction ts with
    | nil => intro _ s h1 h2; exact ⟨h1, h2⟩
    | cons t ts ih =>
      intro hts s h1 h2
      obtain ⟨hs, ho, hc⟩ := ht t (hts t (List.mem_cons_self ..))
      have hps : ∀ p ∈ t.items tess, ∃ c ∈ t.list.paintOrder, p = (tess c, t.stateOf c) := by
        intro p hp
        simp only [Tile.items, List.mem_map] at hp
        obtain ⟨c, hc, rfl⟩ := hp
        exact ⟨c, hc, rfl⟩
      have hcm : ∀ w ∈ t.cmds tess, w.length < UInt32.size := by
        intro w hw
        simp only [Tile.cmds, List.mem_map] at hw
        obtain ⟨x, _, rfl⟩ := hw
        exact htess x
      simp only [List.foldl_cons]
      refine ih (fun t' h' => hts t' (List.mem_cons_of_mem _ h')) _ ?_ ?_
      · unfold stageTile
        dsimp only
        split
        · exact h1
        · intro o ho'
          simp only [List.mem_append] at ho'
          rcases ho' with ho' | ho'
          · exact h1 o ho'
          · exact hup _ _ hcm o ho'
      · unfold stageTile
        dsimp only
        split
        · intro i hi
          simp only [List.mem_append] at hi
          rcases hi with hi | hi
          · exact h2 i hi
          · exact itemsOf_fits tess t hs ho hc _ _ hps i hi
        · intro i hi
          simp only [List.mem_append] at hi
          rcases hi with hi | hi
          · exact h2 i hi
          · exact itemsOf_fits tess t hs ho hc _ _ hps i hi
  unfold compile
  dsimp only
  have hset : ∀ o ∈ ((c.entries.filter fun e =>
      !(tiles.any fun t => decide (e.words = t.cmds tess))).flatMap
        fun e => deletes e.base e.words.length), o.Fits := by
    intro o ho
    simp only [List.mem_flatMap] at ho
    obtain ⟨e, _, ho⟩ := ho
    exact hdel _ _ o ho
  have hk := key tiles (fun _ h => h)
    ⟨{ c with entries := c.entries.filter fun e => tiles.any fun t => decide (e.words = t.cmds tess) },
      (c.entries.filter fun e => !(tiles.any fun t => decide (e.words = t.cmds tess))).flatMap
        fun e => deletes e.base e.words.length, []⟩ hset (fun i hi => nomatch hi)
  intro o ho
  simp only [List.mem_append, List.mem_flatMap] at ho
  rcases ho with ho | ⟨i, hi, ho⟩
  · exact hk.1 o ho
  · obtain ⟨a, b, c', d⟩ := hk.2 i hi
    simp only [Item.ops, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl <;> first | trivial | assumption

/-- A frame decodes to itself once encoded, whatever the display list, provided the vertex words of a command fit the wire and the frame has fewer than `2 ^ 32` commands. -/
theorem frame_roundtrip (tess : Scene.Command → List UInt32) (c : Cache) (fresh : Bool) (w h : Nat)
    (list : Scene.DisplayList) (bg : Scene.Color)
    (htess : ∀ x, (tess x).length < UInt32.size)
    (hl : (frame tess c fresh w h list bg).2.length < UInt32.size) :
    decode (encode (frame tess c fresh w h list bg).2) = some (frame tess c fresh w h list bg).2 := by
  refine decode_encode ?_ hl
  intro x hx
  simp only [frame, compileCmds, List.mem_append, List.mem_map] at hx
  rcases hx with hx | ⟨o, ho, rfl⟩
  · simp only [frameSetup, List.mem_append] at hx
    rcases hx with hx | hx
    · split at hx <;> simp_all [Cmd.WellFormed, specOf, specs, ArgsFit, Arg.Fits]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;>
        simp [Cmd.WellFormed, specOf, specs, ArgsFit, Arg.Fits, UInt32.size]
  · exact (compile_fits tess c [pixelTile w h list] htess (by
      intro t ht
      obtain rfl := List.mem_singleton.mp ht
      simp [pixelTile, UInt32.size, pixelScissor])  o ho).wellFormed

end Inkproof.Gpu
