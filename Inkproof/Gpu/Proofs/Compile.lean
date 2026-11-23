/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Gpu.Compile
import Inkproof.Scene.Clip

namespace Inkproof.Gpu

/-- One draw as the GPU performs it: the buffer's contents, the vertex count and the state in force. -/
structure Draw where
  words : List UInt32
  count : Nat
  state : State

/-- An abstract GPU: buffer contents by handle, the uniforms and scissor in force, and the draws so far. -/
structure Gpu where
  buffers : Nat → Option (List UInt32)
  state : State
  log : List Draw

def Gpu.empty : Gpu := ⟨fun _ => none, ⟨[], [], [], [], [], 0, [], {}⟩, []⟩

def Gpu.set (g : Gpu) (h : Nat) (v : Option (List UInt32)) : Gpu :=
  { g with buffers := fun k => if k = h then v else g.buffers k }

/-- Drawing, or uploading to, a buffer that does not exist does nothing. -/
def Gpu.step (g : Gpu) : Op → Gpu
  | .create h => g.set h (some [])
  | .upload h ws => if (g.buffers h).isSome then g.set h (some ws) else g
  | .delete h => g.set h none
  | .uniform k ws => { g with state := g.state.set k ws }
  | .scissor ws => { g with state := { g.state with scissor := ws } }
  | .draw h n s =>
    match g.buffers h with
    | some w => { g with state := { g.state with stride := s }, log := g.log ++ [⟨w, n, { g.state with stride := s }⟩] }
    | none => g

def Gpu.run (g : Gpu) (ops : List Op) : Gpu := ops.foldl Gpu.step g

@[simp] private theorem Gpu.run_nil (g : Gpu) : g.run [] = g := rfl

@[simp] private theorem Gpu.run_cons (g : Gpu) (o : Op) (os : List Op) : g.run (o :: os) = (g.step o).run os := rfl

private theorem Gpu.run_append (g : Gpu) (a b : List Op) : g.run (a ++ b) = (g.run a).run b := by
  simp [Gpu.run, List.foldl_append]

def Op.IsSetup : Op → Prop
  | .create _ | .upload _ _ | .delete _ => True
  | _ => False

def Op.IsUpload : Op → Prop
  | .create _ | .upload _ _ => True
  | _ => False

private theorem Gpu.run_setup (g : Gpu) (ops : List Op) (h : ∀ o ∈ ops, o.IsSetup) :
    (g.run ops).log = g.log ∧ (g.run ops).state = g.state := by
  induction ops generalizing g with
  | nil => simp [Gpu.run]
  | cons o os ih =>
    have ho := h o (List.mem_cons_self ..)
    have := ih (g.step o) (fun p hp => h p (List.mem_cons_of_mem _ hp))
    simp only [Gpu.run, List.foldl_cons] at this ⊢
    refine ⟨this.1.trans ?_, this.2.trans ?_⟩ <;>
    cases o <;> simp_all [Op.IsSetup, Gpu.step, Gpu.set] <;> split <;> rfl

private theorem uploads_setup (b : Nat) (ws : List (List UInt32)) : ∀ o ∈ uploads b ws, o.IsSetup := by
  induction ws generalizing b with
  | nil => simp [uploads]
  | cons w ws ih =>
    intro o ho
    simp only [uploads, List.mem_cons] at ho
    rcases ho with rfl | rfl | ho
    · trivial
    · trivial
    · exact ih _ o ho

private theorem deletes_setup (b n : Nat) : ∀ o ∈ deletes b n, o.IsSetup := by
  induction n generalizing b with
  | zero => simp [deletes]
  | succ n ih =>
    intro o ho
    simp only [deletes, List.mem_cons] at ho
    rcases ho with rfl | ho
    · trivial
    · exact ih _ o ho

private theorem uploads_not_upload_free (b n : Nat) : ∀ o ∈ deletes b n, ¬ o.IsUpload := by
  induction n generalizing b with
  | zero => simp [deletes]
  | succ n ih =>
    intro o ho
    simp only [deletes, List.mem_cons] at ho
    rcases ho with rfl | ho
    · simp [Op.IsUpload]
    · exact ih _ o ho

private theorem run_uploads_out (g : Gpu) (b : Nat) (ws : List (List UInt32)) (k : Nat)
    (hk : k < b ∨ b + ws.length ≤ k) : (g.run (uploads b ws)).buffers k = g.buffers k := by
  induction ws generalizing b g with
  | nil => simp [uploads]
  | cons w ws ih =>
    simp only [uploads, Gpu.run_cons] at ih ⊢
    simp only [List.length_cons] at hk
    rw [ih _ (b + 1) (by omega)]
    have : k ≠ b := by omega
    simp [Gpu.step, Gpu.set, this]

private theorem run_uploads_in (g : Gpu) (b : Nat) (ws : List (List UInt32)) (i : Nat)
    (hi : i < ws.length) : (g.run (uploads b ws)).buffers (b + i) = ws[i]? := by
  induction ws generalizing b g i with
  | nil => simp at hi
  | cons w ws ih =>
    simp only [uploads, Gpu.run_cons] at ih ⊢
    cases i with
    | zero =>
      have := run_uploads_out ((g.step (Op.create b)).step (Op.upload b w)) (b + 1) ws b (by omega)
      simp only [Nat.add_zero]
      rw [this]
      simp [Gpu.step, Gpu.set]
    | succ i =>
      have := ih ((g.step (Op.create b)).step (Op.upload b w)) (b + 1) i (by simpa using hi)
      rw [show b + (i + 1) = b + 1 + i by omega, this]
      simp

private theorem run_deletes_out (g : Gpu) (b n k : Nat) (hk : k < b ∨ b + n ≤ k) :
    (g.run (deletes b n)).buffers k = g.buffers k := by
  induction n generalizing b g with
  | zero => simp [deletes]
  | succ n ih =>
    simp only [deletes, Gpu.run_cons] at ih ⊢
    rw [ih _ (b + 1) (by omega)]
    have : k ≠ b := by omega
    simp [Gpu.step, Gpu.set, this]

private theorem run_deletes_flatMap_out (g : Gpu) (l : List Entry) (k : Nat)
    (hk : ∀ f ∈ l, k < f.base ∨ f.base + f.words.length ≤ k) :
    (g.run (l.flatMap fun e => deletes e.base e.words.length)).buffers k = g.buffers k := by
  induction l generalizing g with
  | nil => simp
  | cons f l ih =>
    rw [List.flatMap_cons, Gpu.run_append, ih _ (fun e he => hk e (List.mem_cons_of_mem _ he)),
      run_deletes_out _ _ _ _ (hk f (List.mem_cons_self ..))]

def Item.toDraw (i : Item) : Draw := Draw.mk i.words (i.words.length / i.state.stride) i.state

private theorem itemsOf_map (h : Nat) (ps : List (List UInt32 × State)) :
    (itemsOf h ps).map Item.toDraw = ps.map fun p => Draw.mk p.1 (p.1.length / p.2.stride) p.2 := by
  induction ps generalizing h with
  | nil => simp [itemsOf]
  | cons c cs ih => obtain ⟨w, u⟩ := c; simp [itemsOf, ih, Item.toDraw]

theorem Tile.items_eq (tess : Scene.Command → List UInt32) (t : Tile) (hs : t.Sound tess) :
    t.items tess = t.list.paintOrder.map fun c => (tess c, t.stateOf c) := by
  unfold Tile.Sound at hs
  simp only [Tile.items, hs]
  generalize t.list.paintOrder = l
  induction l with
  | nil => rfl
  | cons c cs ih => simp [List.zip_cons_cons, ih]

private theorem items_cmds (tess : Scene.Command → List UInt32) (t : Tile) (hs : t.Sound tess) :
    (t.items tess).map Prod.fst = t.cmds tess := by
  rw [Tile.items_eq tess t hs]
  unfold Tile.Sound at hs
  rw [hs]
  simp [List.map_map, Function.comp_def]

/-- The draws of a frame: each tile's commands in the display list's paint order, each with the
tile's transform, its colour and its clip. -/
def frameDraws (tess : Scene.Command → List UInt32) (tiles : List Tile) : List Draw :=
  tiles.flatMap fun t => t.list.paintOrder.map fun c =>
    Draw.mk (tess c) ((tess c).length / (t.stateOf c).stride) (t.stateOf c)

/-- The buffers the cache claims are resident hold what it says, and its handles are disjoint and
below `next`. -/
def Cache.Valid (c : Cache) (g : Gpu) : Prop :=
  (∀ e ∈ c.entries, e.base + e.words.length ≤ c.next ∧
    ∀ i, i < e.words.length → g.buffers (e.base + i) = e.words[i]?) ∧
  c.entries.Pairwise fun e f => e.base + e.words.length ≤ f.base ∨ f.base + f.words.length ≤ e.base

theorem Cache.valid_empty (g : Gpu) : (({} : Cache)).Valid g := by
  simp [Cache.Valid]

private theorem Cache.Valid.congr {c : Cache} {g g' : Gpu} (h : c.Valid g) (hb : g'.buffers = g.buffers) :
    c.Valid g' := by
  simp only [Cache.Valid, hb] at h ⊢
  exact h

/-- A stage is consistent with the GPU `g` it starts from. -/
def Stage.Inv (s : Stage) (g : Gpu) : Prop :=
  s.cache.Valid (g.run s.ops) ∧
  (∀ i ∈ s.items, i.handle < s.cache.next ∧ (g.run s.ops).buffers i.handle = some i.words) ∧
  ∀ o ∈ s.ops, o.IsSetup

private theorem itemsOf_ok (g : Gpu) (ps : List (List UInt32 × State)) (h : Nat)
    (hg : ∀ j, j < ps.length → g.buffers (h + j) = (ps.map Prod.fst)[j]?) :
    ∀ i ∈ itemsOf h ps, ∃ j, j < ps.length ∧ i.handle = h + j ∧ g.buffers i.handle = some i.words := by
  induction ps generalizing h with
  | nil => simp [itemsOf]
  | cons c cs ih =>
    obtain ⟨w, u⟩ := c
    intro i hi
    simp only [itemsOf, List.mem_cons] at hi
    rcases hi with rfl | hi
    · exact ⟨0, by simp, by simp, by simpa using hg 0 (by simp)⟩
    · obtain ⟨j, hj, h1, h2⟩ := ih (h + 1) (fun j hj => by
        have := hg (j + 1) (by simpa using hj)
        rw [show h + (j + 1) = h + 1 + j by omega] at this
        simpa using this) i hi
      exact ⟨j + 1, by simpa using hj, by omega, h2⟩

private theorem stageTile_inv (tess : Scene.Command → List UInt32) (s : Stage) (g : Gpu) (t : Tile)
    (hsound : t.Sound tess) (hs : s.Inv g) :
    (stageTile tess s t).Inv g ∧
    (stageTile tess s t).items.map Item.toDraw =
      s.items.map Item.toDraw ++ (t.items tess).map fun p => Draw.mk p.1 (p.1.length / p.2.stride) p.2 := by
  obtain ⟨hv, hi, hset⟩ := hs
  have hmap := fun h ps => itemsOf_map h ps
  unfold stageTile
  dsimp only
  split
  · rename_i e he
    have hmem := List.mem_of_find?_eq_some he
    have hw : e.words = (t.cmds tess) := by simpa using List.find?_some he
    obtain ⟨hb, hbuf⟩ := hv.1 e hmem
    have hok := itemsOf_ok (g.run s.ops) (t.items tess) e.base (fun j hj => by
      rw [items_cmds tess t hsound, ← hw]; exact hbuf j (by rw [hw, ← items_cmds tess t hsound, List.length_map]; exact hj))
    refine ⟨⟨hv, ?_, hset⟩, ?_⟩
    · intro i hi'
      simp only [List.mem_append] at hi'
      rcases hi' with hi' | hi'
      · exact hi i hi'
      · obtain ⟨j, hj, h1, h2⟩ := hok i hi'
        refine ⟨?_, h2⟩
        have : j < e.words.length := by rw [hw, ← items_cmds tess t hsound, List.length_map]; exact hj
        dsimp only
        omega
    · rw [List.map_append, hmap]
  · rename_i hnone
    generalize hws : t.cmds tess = ws at hnone ⊢
    obtain ⟨hv1, hv2⟩ := hv
    generalize hn : s.cache.next = n at hv1 hi ⊢
    have hrun : (g.run (s.ops ++ uploads n ws)) = (g.run s.ops).run (uploads n ws) := Gpu.run_append ..
    have hnew : ∀ j, j < ws.length →
        ((g.run s.ops).run (uploads n ws)).buffers (n + j) = ws[j]? := fun j hj =>
      run_uploads_in _ _ _ _ (by omega)
    have hfst : (t.items tess).map Prod.fst = ws := by rw [items_cmds tess t hsound, hws]
    have hlen : (t.items tess).length = ws.length := by
      rw [← hfst, List.length_map]
    have hold : ∀ k, k < n → ((g.run s.ops).run (uploads n ws)).buffers k = (g.run s.ops).buffers k :=
      fun k hk => run_uploads_out _ _ _ _ (Or.inl hk)
    have hok := itemsOf_ok ((g.run s.ops).run (uploads n ws)) (t.items tess) n (fun j hj => by
      rw [hfst]
      exact hnew j (by omega))
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · rw [hrun]
      refine ⟨?_, ?_⟩
      · intro e he
        simp only [List.mem_append, List.mem_singleton] at he
        rcases he with he | rfl
        · obtain ⟨hb, hbuf⟩ := hv1 e he
          refine ⟨by simp only; omega, fun i hi' => ?_⟩
          rw [hold _ (by omega)]
          exact hbuf i hi'
        · exact ⟨by simp only; omega, fun i hi' => hnew i (by simp only at hi'; omega)⟩
      · simp only [List.pairwise_append, List.pairwise_singleton, List.mem_singleton,
          forall_eq]
        refine ⟨hv2, trivial, fun a ha => Or.inl (hv1 a ha).1⟩
    · intro i hi'
      simp only [List.mem_append] at hi'
      rw [hrun]
      rcases hi' with hi' | hi'
      · obtain ⟨h1, h2⟩ := hi i hi'
        exact ⟨by simp only; omega, by rw [hold _ h1]; exact h2⟩
      · obtain ⟨j, hj, h1, h2⟩ := hok i hi'
        exact ⟨by simp only; omega, h2⟩
    · intro o ho
      simp only [List.mem_append] at ho
      rcases ho with ho | ho
      · exact hset o ho
      · exact uploads_setup _ _ o ho
    · rw [List.map_append, hmap]

private theorem foldl_stage (tess : Scene.Command → List UInt32) (g : Gpu) :
    ∀ (tiles : List Tile) (s : Stage), (∀ t ∈ tiles, t.Sound tess) → s.Inv g →
      (tiles.foldl (stageTile tess) s).Inv g ∧
      (tiles.foldl (stageTile tess) s).items.map Item.toDraw =
        s.items.map Item.toDraw ++ frameDraws tess tiles := by
  intro tiles
  induction tiles with
  | nil => intro s _ hs; simp [frameDraws, hs]
  | cons t ts ih =>
    intro s hsound hs
    obtain ⟨h1, h2⟩ := stageTile_inv tess s g t (hsound t (List.mem_cons_self ..)) hs
    obtain ⟨h3, h4⟩ := ih _ (fun t' ht' => hsound t' (List.mem_cons_of_mem _ ht')) h1
    refine ⟨h3, ?_⟩
    simp only [List.foldl_cons, h4, h2, frameDraws, List.flatMap_cons, List.append_assoc]
    rw [Tile.items_eq tess t (hsound t (List.mem_cons_self ..))]
    simp [List.map_map, Function.comp_def]

theorem Gradient.ops_sub (prev : Option Gradient) (g : Gradient) (o : Op) (h : o ∈ g.ops prev) :
    o ∈ g.ops none := by
  simp only [Gradient.ops, List.mem_append] at h ⊢
  simp only [Option.map_none, reduceCtorEq, ite_false]
  repeat' split at h
  all_goals grind

/-- With no gradient known to be in force, all seven gradient uniforms are set. -/
theorem Gradient.ops_none (g : Gradient) :
    g.ops none = [.uniform 5 g.axis, .uniform 6 g.starts, .uniform 7 g.invs, .uniform 8 g.d0,
      .uniform 9 g.d1, .uniform 10 g.d2, .uniform 11 g.d3] := by
  simp [Gradient.ops]

/-- A gradient already in force is not set again. -/
theorem Gradient.ops_self (g : Gradient) : g.ops (some g) = [] := by
  simp [Gradient.ops]

theorem itemsOps_nil (prev : Option Gradient) : itemsOps prev [] = [] := rfl

theorem itemsOps_cons (prev : Option Gradient) (i : Item) (L : List Item) :
    itemsOps prev (i :: L) = i.ops prev ++ itemsOps (some i.state.grad) L := rfl

theorem Item.ops_sub (prev : Option Gradient) (i : Item) (o : Op) (h : o ∈ i.ops prev) :
    o ∈ i.ops none := by
  simp only [Item.ops, List.mem_append] at h ⊢
  rcases h with (h | h) | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr (Gradient.ops_sub _ _ _ h))
  · exact Or.inr h

theorem Item.ops_none (i : Item) :
    i.ops none = [.uniform 0 i.state.slope, .uniform 1 i.state.offset, .uniform 2 i.state.size,
      .uniform 3 i.state.view, .uniform 4 i.state.colour, .uniform 5 i.state.grad.axis,
      .uniform 6 i.state.grad.starts, .uniform 7 i.state.grad.invs, .uniform 8 i.state.grad.d0,
      .uniform 9 i.state.grad.d1, .uniform 10 i.state.grad.d2, .uniform 11 i.state.grad.d3,
      .scissor i.state.scissor, .draw i.handle (i.words.length / i.state.stride) i.state.stride] := by
  simp [Item.ops, Gradient.ops]

theorem mem_itemsOps (prev : Option Gradient) (L : List Item) (o : Op) (h : o ∈ itemsOps prev L) :
    ∃ i ∈ L, o ∈ i.ops none := by
  induction L generalizing prev with
  | nil => simp [itemsOps] at h
  | cons i L ih =>
    simp only [itemsOps, List.mem_append] at h
    rcases h with h | h
    · exact ⟨i, List.mem_cons_self .., Item.ops_sub _ _ _ h⟩
    · obtain ⟨j, hj, hj'⟩ := ih _ h
      exact ⟨j, List.mem_cons_of_mem _ hj, hj'⟩

private theorem run_gradient (g : Gpu) (prev : Option Gradient) (gr : Gradient)
    (hp : ∀ p, prev = some p → g.state.grad = p) :
    g.run (gr.ops prev) = { g with state := { g.state with grad := gr } } := by
  obtain ⟨ax, st, iv, a0, a1, a2, a3⟩ := gr
  obtain ⟨b, ⟨sl, of, sz, vw, co, sd, sc, pg⟩, lg⟩ := g
  cases prev with
  | none => simp [Gradient.ops, Gpu.run, Gpu.step, State.set]
  | some p =>
    have h := hp p rfl
    obtain ⟨pa, ps, pi, p0, p1, p2, p3⟩ := p
    simp only at h
    subst h
    simp only [Gradient.ops, Gpu.run, List.foldl_append, Option.map_some, Option.some.injEq]
    repeat' split
    all_goals simp_all [Gpu.step, State.set]

private theorem run_draws (g : Gpu) (prev : Option Gradient) (L : List Item)
    (hp : ∀ p, prev = some p → g.state.grad = p)
    (h : ∀ i ∈ L, g.buffers i.handle = some i.words) :
    (g.run (itemsOps prev L)).log = g.log ++ L.map Item.toDraw ∧
    (g.run (itemsOps prev L)).buffers = g.buffers := by
  induction L generalizing g prev with
  | nil => simp [Gpu.run, itemsOps]
  | cons i L ih =>
    have hi := h i (List.mem_cons_self ..)
    have hs : g.run (i.ops prev) =
        ⟨g.buffers, i.state, g.log ++ [Draw.mk i.words (i.words.length / i.state.stride) i.state]⟩ := by
      have h1 := run_gradient (g.run [.uniform 0 i.state.slope, .uniform 1 i.state.offset,
        .uniform 2 i.state.size, .uniform 3 i.state.view, .uniform 4 i.state.colour]) prev i.state.grad
        (by simpa [Gpu.run, Gpu.step, State.set] using hp)
      simp only [Item.ops, Gpu.run_append, h1]
      simp [Gpu.run, Gpu.step, State.set, hi]
    have := ih (g.run (i.ops prev)) (some i.state.grad) (by intro p hp; rw [hs]; exact Option.some.inj hp)
      (fun j hj => by rw [hs]; simpa using h j (List.mem_cons_of_mem _ hj))
    rw [itemsOps, Gpu.run_append]
    rw [hs] at this ⊢
    refine ⟨by rw [this.1]; simp [Item.toDraw], this.2⟩

private theorem compile_eq (tess : Scene.Command → List UInt32) (c : Cache)
    (keep : List (List (List UInt32))) (tiles : List Tile) :
    ∃ s : Stage, s = tiles.foldl (stageTile tess)
      ⟨{ c with entries := c.entries.filter fun e =>
          keep.any (fun ws => decide (e.words = ws)) || tiles.any fun t => decide (e.words = t.cmds tess) },
        (c.entries.filter fun e =>
          !(keep.any (fun ws => decide (e.words = ws)) || tiles.any fun t => decide (e.words = t.cmds tess))).flatMap
          fun e => deletes e.base e.words.length, []⟩ ∧
      compileKeeping tess c keep tiles = (s.cache, s.ops ++ itemsOps none s.items) :=
  ⟨_, rfl, rfl⟩

/-- A frame deletes the buffers neither a tile nor `keep` uses, stages each tile in order, and draws what the stages collected. -/
theorem compileKeeping_eq (tess : Scene.Command → List UInt32) (c : Cache)
    (keep : List (List (List UInt32))) (tiles : List Tile) :
    compileKeeping tess c keep tiles =
      let used (e : Entry) : Bool :=
        keep.any (fun ws => decide (e.words = ws)) || tiles.any fun t => decide (e.words = t.cmds tess)
      let s := tiles.foldl (stageTile tess)
        ⟨{ c with entries := c.entries.filter used },
          (c.entries.filter (!used ·)).flatMap fun e => deletes e.base e.words.length, []⟩
      (s.cache, s.ops ++ itemsOps none s.items) :=
  rfl

private theorem initial_inv (tess : Scene.Command → List UInt32) (c : Cache)
    (keep : List (List (List UInt32))) (tiles : List Tile) (g : Gpu)
    (hv : c.Valid g) :
    (Stage.mk
      { c with entries := c.entries.filter fun e =>
          keep.any (fun ws => decide (e.words = ws)) || tiles.any fun t => decide (e.words = t.cmds tess) }
      ((c.entries.filter fun e =>
          !(keep.any (fun ws => decide (e.words = ws)) || tiles.any fun t => decide (e.words = t.cmds tess))).flatMap
          fun e => deletes e.base e.words.length) []).Inv g := by
  have hperm := List.filter_append_perm
    (fun e : Entry => keep.any (fun ws => decide (e.words = ws)) || tiles.any fun t => decide (e.words = t.cmds tess)) c.entries
  have hpw := (hperm.pairwise_iff (fun h => by omega)).mpr hv.2
  rw [List.pairwise_append] at hpw
  refine ⟨⟨fun e he => ?_, hpw.1⟩, by simp, fun o ho => ?_⟩
  · have he' := (List.mem_filter.mp he).1
    obtain ⟨hb, hbuf⟩ := hv.1 e he'
    refine ⟨hb, fun i hi => ?_⟩
    refine (run_deletes_flatMap_out g _ (e.base + i) ?_).trans (hbuf i hi)
    · intro f hf
      have hf' := List.mem_filter.mp hf
      have hne := hpw.2.2 e he f (by simpa using hf)
      have := hpw.2.2 e he f (by simpa using hf)
      rcases this with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
  · simp only [List.mem_flatMap] at ho
    obtain ⟨e, _, ho⟩ := ho
    exact deletes_setup _ _ o ho

/-- Running a frame from any GPU the cache is valid for performs the draws of the display lists
in paint order, and leaves the cache valid for the GPU it produces. Buffers in `keep` stay resident. -/
theorem compileKeeping_log (tess : Scene.Command → List UInt32) (c : Cache)
    (keep : List (List (List UInt32))) (tiles : List Tile) (g : Gpu)
    (hsound : ∀ t ∈ tiles, t.Sound tess) (hv : c.Valid g) :
    (g.run (compileKeeping tess c keep tiles).2).log = g.log ++ frameDraws tess tiles ∧
    (compileKeeping tess c keep tiles).1.Valid (g.run (compileKeeping tess c keep tiles).2) := by
  obtain ⟨s, hs, hc⟩ := compile_eq tess c keep tiles
  rw [hc]
  obtain ⟨hinv, hmap⟩ := foldl_stage tess g tiles _ hsound (initial_inv tess c keep tiles g hv)
  rw [← hs] at hinv hmap
  obtain ⟨hvalid, hitems, hset⟩ := hinv
  rw [Gpu.run_append]
  obtain ⟨hlog, hbuf⟩ := run_draws (g.run s.ops) none s.items (by simp) (fun i hi => (hitems i hi).2)
  refine ⟨?_, hvalid.congr hbuf⟩
  rw [hlog, (Gpu.run_setup g s.ops hset).1]
  simp only [List.nil_append, List.map_nil] at hmap
  rw [← hmap]

theorem compile_log (tess : Scene.Command → List UInt32) (c : Cache) (tiles : List Tile) (g : Gpu)
    (hsound : ∀ t ∈ tiles, t.Sound tess) (hv : c.Valid g) :
    (g.run (compile tess c tiles).2).log = g.log ++ frameDraws tess tiles ∧
    (compile tess c tiles).1.Valid (g.run (compile tess c tiles).2) :=
  compileKeeping_log tess c [] tiles g hsound hv

theorem compile_valid (tess : Scene.Command → List UInt32) (c : Cache) (tiles : List Tile) (g : Gpu)
    (hsound : ∀ t ∈ tiles, t.Sound tess) (hv : c.Valid g) :
    (compile tess c tiles).1.Valid (g.run (compile tess c tiles).2) :=
  (compile_log tess c tiles g hsound hv).2

private theorem stageTile_entries (tess : Scene.Command → List UInt32) (s : Stage) (t : Tile) :
    (∀ e ∈ s.cache.entries, e ∈ (stageTile tess s t).cache.entries) ∧
    t.Cached tess (stageTile tess s t).cache := by
  unfold stageTile Tile.Cached
  dsimp only
  split
  · rename_i e he
    exact ⟨fun e' h => h, e, List.mem_of_find?_eq_some he, by simpa using List.find?_some he⟩
  · exact ⟨fun e h => by simp [h], ⟨⟨t.cmds tess, s.cache.next⟩, by simp, rfl⟩⟩

private theorem foldl_entries (tess : Scene.Command → List UInt32) :
    ∀ (ts : List Tile) (s : Stage),
      (∀ e ∈ s.cache.entries, e ∈ (ts.foldl (stageTile tess) s).cache.entries) ∧
      ∀ t ∈ ts, t.Cached tess (ts.foldl (stageTile tess) s).cache := by
  intro ts
  induction ts with
  | nil => intro s; exact ⟨fun e h => h, fun t ht => nomatch ht⟩
  | cons t ts ih =>
    intro s
    obtain ⟨h1, h2⟩ := ih (stageTile tess s t)
    obtain ⟨h3, h4⟩ := stageTile_entries tess s t
    refine ⟨fun e he => h1 e (h3 e he), fun t' ht' => ?_⟩
    rcases List.mem_cons.mp ht' with rfl | ht'
    · obtain ⟨e, he, hw⟩ := h4
      exact ⟨e, h1 e he, hw⟩
    · exact h2 t' ht'

/-- After a frame, every tile of it is cached. -/
theorem compileKeeping_cache_cached (tess : Scene.Command → List UInt32) (c : Cache)
    (keep : List (List (List UInt32))) (tiles : List Tile) :
    ∀ t ∈ tiles, t.Cached tess (compileKeeping tess c keep tiles).1 := by
  obtain ⟨s, hs, hc⟩ := compile_eq tess c keep tiles
  rw [hc]
  subst hs
  exact (foldl_entries tess tiles _).2

/-- A buffer of the cache whose words are in `keep` survives a frame whatever its tiles. -/
theorem compileKeeping_kept (tess : Scene.Command → List UInt32) (c : Cache)
    (keep : List (List (List UInt32))) (tiles : List Tile) (e : Entry) (he : e ∈ c.entries)
    (hk : e.words ∈ keep) : e ∈ (compileKeeping tess c keep tiles).1.entries := by
  obtain ⟨s, hs, hc⟩ := compile_eq tess c keep tiles
  rw [hc]
  subst hs
  refine (foldl_entries tess tiles _).1 e ?_
  simp only [List.mem_filter, Bool.or_eq_true, List.any_eq_true]
  exact ⟨he, Or.inl ⟨e.words, hk, by simp⟩⟩

theorem compile_cache_cached (tess : Scene.Command → List UInt32) (c : Cache) (tiles : List Tile) :
    ∀ t ∈ tiles, t.Cached tess (compile tess c tiles).1 :=
  compileKeeping_cache_cached tess c [] tiles

/-- Reusing cached buffers draws what uploading afresh would. -/
theorem cached_eq_fresh (tess : Scene.Command → List UInt32) (c : Cache) (tiles : List Tile) (g : Gpu)
    (hsound : ∀ t ∈ tiles, t.Sound tess) (hv : c.Valid g) :
    (g.run (compile tess c tiles).2).log = g.log ++ frameDraws tess tiles ∧
    (Gpu.empty.run (compile tess {} tiles).2).log = frameDraws tess tiles := by
  refine ⟨(compile_log tess c tiles g hsound hv).1, ?_⟩
  simpa [Gpu.empty] using (compile_log tess {} tiles Gpu.empty hsound (Cache.valid_empty _)).1

/-- When every tile is cached, a frame creates and uploads nothing: it is uniform updates, draws and
deletions of buffers no tile needs. -/
theorem compileKeeping_cached (tess : Scene.Command → List UInt32) (c : Cache)
    (keep : List (List (List UInt32))) (tiles : List Tile)
    (h : ∀ t ∈ tiles, t.Cached tess c) : ∀ o ∈ (compileKeeping tess c keep tiles).2, ¬ o.IsUpload := by
  obtain ⟨s, hs, hc⟩ := compile_eq tess c keep tiles
  rw [hc]
  subst hs
  have key : ∀ (ts : List Tile) (s : Stage), (∀ o ∈ s.ops, ¬ o.IsUpload) →
      (∀ t ∈ ts, t.Cached tess s.cache) →
      ∀ o ∈ (ts.foldl (stageTile tess) s).ops, ¬ o.IsUpload := by
    intro ts
    induction ts with
    | nil => intro s h1 _; simpa using h1
    | cons t ts ih =>
      intro s h1 h2
      obtain ⟨e, he, hw⟩ := h2 t (List.mem_cons_self ..)
      have hsome : (s.cache.entries.find? fun e => decide (e.words = t.cmds tess)).isSome := by
        rw [List.find?_isSome]
        exact ⟨e, he, by simpa using hw⟩
      simp only [List.foldl_cons]
      apply ih
      · unfold stageTile
        dsimp only
        split
        · exact h1
        · rename_i hn
          rw [hn] at hsome
          simp at hsome
      · intro t' ht'
        unfold stageTile
        dsimp only
        split
        · exact h2 t' (List.mem_cons_of_mem _ ht')
        · rename_i hn
          rw [hn] at hsome
          simp at hsome
  intro o ho
  simp only [List.mem_append] at ho
  rcases ho with ho | ho
  · refine key tiles _ ?_ ?_ o ho
    · intro o ho
      simp only [List.mem_flatMap] at ho
      obtain ⟨e, _, ho⟩ := ho
      exact uploads_not_upload_free _ _ o ho
    · intro t ht
      obtain ⟨e, he, hw⟩ := h t ht
      refine ⟨e, ?_, hw⟩
      simp only [List.mem_filter, List.any_eq_true, Bool.or_eq_true]
      exact ⟨he, Or.inr ⟨t, ht, by simpa using hw⟩⟩
  · obtain ⟨i, _, ho⟩ := mem_itemsOps _ _ _ ho
    simp only [Item.ops_none, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Op.IsUpload]

theorem compile_cached (tess : Scene.Command → List UInt32) (c : Cache) (tiles : List Tile)
    (h : ∀ t ∈ tiles, t.Cached tess c) : ∀ o ∈ (compile tess c tiles).2, ¬ o.IsUpload :=
  compileKeeping_cached tess c [] tiles h

theorem Op.toCmd_wellFormed (o : Op)
    (h : (∀ h ws, o = .upload h ws → ws.length < UInt32.size) ∧
      (∀ k ws, o = .uniform k ws → ws.length < UInt32.size) ∧
      ∀ ws, o = .scissor ws → ws.length < UInt32.size) : o.toCmd.WellFormed := by
  cases o <;> simp_all [Op.toCmd, Cmd.WellFormed, specOf, specs, ArgsFit, Arg.Fits]

theorem compileCmds_eq (tess : Scene.Command → List UInt32) (c : Cache) (tiles : List Tile) :
    compileCmds tess c tiles = ((compile tess c tiles).1, (compile tess c tiles).2.map Op.toCmd) := rfl

@[simp] theorem Op.toCmd_create (h : Nat) : (Op.create h).toCmd = ⟨0, [.u32 h.toUInt32]⟩ := rfl

@[simp] theorem Op.toCmd_upload (h : Nat) (ws : List UInt32) :
    (Op.upload h ws).toCmd = ⟨1, [.u32 h.toUInt32, .words ws]⟩ := rfl

@[simp] theorem Op.toCmd_delete (h : Nat) : (Op.delete h).toCmd = ⟨2, [.u32 h.toUInt32]⟩ := rfl

@[simp] theorem Op.toCmd_uniform (k : Nat) (ws : List UInt32) :
    (Op.uniform k ws).toCmd = ⟨4, [.u32 k.toUInt32, .words ws]⟩ := rfl

@[simp] theorem Op.toCmd_scissor (ws : List UInt32) : (Op.scissor ws).toCmd = ⟨8, [.words ws]⟩ := rfl

@[simp] theorem Op.toCmd_draw (h n w : Nat) :
    (Op.draw h n w).toCmd = ⟨5, [.u32 h.toUInt32, .u32 n.toUInt32, .u32 w.toUInt32]⟩ := rfl

theorem Tile.cmds_eq (tess : Scene.Command → List UInt32) (t : Tile) (h : t.words = none) :
    t.cmds tess = t.list.paintOrder.map tess := by simp [Tile.cmds, h]

/-- A tile that holds no words is sound. -/
theorem Tile.sound_of_words_none (tess : Scene.Command → List UInt32) (t : Tile) (h : t.words = none) :
    t.Sound tess := Tile.cmds_eq tess t h

theorem specOf_eq_find (op : UInt8) : specOf op = specs.find? (·.op == op) := rfl

/-- Scissoring to the clip rectangle loses nothing of the shape: every point of the shape lies in it, and a shape clipped to nothing has no points. -/
theorem clipRect_region (s : Scene.Shape) (p : Scene.Pt) (h : s.region p) :
    match clipRect s with
    | none => True
    | some none => False
    | some (some r) => r.Holds p := by
  induction s with
  | clipped r s ih =>
    have h' : r.Holds p ∧ s.region p := h
    have := ih h'.2
    rcases hc : clipRect s with _ | _ | r'
    · simpa [clipRect, hc] using h'.1
    · rw [hc] at this; exact this.elim
    · rw [hc] at this
      obtain ⟨m, hm, hh⟩ := (Scene.Rect.meet_holds r r' p).mpr ⟨h'.1, this⟩
      simp only [clipRect, hc, hm]
      exact hh
  | _ => simp [clipRect]

theorem shadingState_flat (o : Scene.Pt) (k : Scene.Color) : shadingState o (.flat k) = some (k, .flat) := rfl

/-- A gradient that the renderer can draw has the first stop's colour as its base. -/
theorem shadingState_gradient (o : Scene.Pt) (a : Scene.GradientAxis) (s : Scene.Stop) (rest : List Scene.Stop)
    (hn : rest.length ≤ gradientSegments) (hs : stopsAscend (s :: rest) = true) :
    shadingState o (.gradient a s rest) = some (s.color, .ofStops o a s rest) := by
  simp [shadingState, hn, hs]

/-- A gradient with more than `gradientSegments` segments, or with stops that descend, is not drawn. -/
theorem shadingState_unsupported (o : Scene.Pt) (a : Scene.GradientAxis) (s : Scene.Stop) (rest : List Scene.Stop)
    (h : ¬ (rest.length ≤ gradientSegments ∧ stopsAscend (s :: rest) = true)) :
    shadingState o (.gradient a s rest) = none := by
  simp [shadingState, h]

/-- Every uniform of a gradient has at most four words. -/
def Gradient.Short (g : Gradient) : Prop :=
  g.axis.length ≤ 4 ∧ g.starts.length ≤ 4 ∧ g.invs.length ≤ 4 ∧ g.d0.length ≤ 4 ∧ g.d1.length ≤ 4 ∧
    g.d2.length ≤ 4 ∧ g.d3.length ≤ 4

theorem Gradient.flat_short : Gradient.flat.Short := by simp [Gradient.flat, Gradient.Short]

theorem deltaWords_length (a b : Scene.Color) : (deltaWords a b).length = 4 := rfl

theorem Gradient.ofStops_short (o : Scene.Pt) (a : Scene.GradientAxis) (s : Scene.Stop) (rest : List Scene.Stop)
    (h : rest.length ≤ gradientSegments) : (Gradient.ofStops o a s rest).Short := by
  have hz : ∀ i : Nat, (((((s :: rest).zip rest)[i]?).map fun (p : Scene.Stop × Scene.Stop) =>
      deltaWords p.1.color p.2.color).getD [0, 0, 0, 0]).length = 4 := by
    intro i
    cases hg : ((s :: rest).zip rest)[i]? <;> simp [deltaWords]
  have hl : ((s :: rest).zip rest).length = rest.length := by simp
  simp only [Gradient.ofStops, Gradient.Short]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases a <;> simp
  · simp only [List.length_rightpad, List.length_map, hl]
    have : gradientSegments = 4 := rfl
    omega
  · simp only [List.length_rightpad, List.length_map, hl]
    have : gradientSegments = 4 := rfl
    omega
  all_goals simp only [hz]; omega

theorem Gradient.ofSteps_short (o : Scene.Pt) (a : Scene.GradientAxis) (s : Scene.Stop) (rest : List Scene.Stop)
    (h : rest.length ≤ gradientSegments) : (Gradient.ofSteps o a s rest).Short := by
  have hz : ∀ i : Nat, (((((s :: rest).zip rest)[i]?).map fun (p : Scene.Stop × Scene.Stop) =>
      deltaWords p.1.color p.2.color).getD [0, 0, 0, 0]).length = 4 := by
    intro i
    cases hg : ((s :: rest).zip rest)[i]? <;> simp [deltaWords]
  have hl : ((s :: rest).zip rest).length = rest.length := by simp
  simp only [Gradient.ofSteps, Gradient.Short]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases a <;> simp
  · simp only [List.length_rightpad, List.length_map, hl]
    have : gradientSegments = 4 := rfl
    omega
  · simp only [List.length_rightpad, List.length_map, hl]
    have : gradientSegments = 4 := rfl
    omega
  all_goals simp only [hz]; omega

/-- Steps that the renderer can draw have the first stop's colour as their base. -/
theorem shadingState_steps (o : Scene.Pt) (a : Scene.GradientAxis) (s : Scene.Stop) (rest : List Scene.Stop)
    (hn : rest.length ≤ gradientSegments) (hs : stopsAscend (s :: rest) = true) :
    shadingState o (.steps a s rest) = some (s.color, .ofSteps o a s rest) := by
  simp [shadingState, hn, hs]

/-- Steps with more than `gradientSegments` changes, or with stops that descend, are not drawn. -/
theorem shadingState_steps_unsupported (o : Scene.Pt) (a : Scene.GradientAxis) (s : Scene.Stop) (rest : List Scene.Stop)
    (h : ¬ (rest.length ≤ gradientSegments ∧ stopsAscend (s :: rest) = true)) :
    shadingState o (.steps a s rest) = none := by
  simp [shadingState, h]

theorem shadingState_short (o : Scene.Pt) (sh : Scene.Shading) (k : Scene.Color) (g : Gradient)
    (h : shadingState o sh = some (k, g)) : g.Short := by
  cases sh with
  | flat c => simp [shadingState] at h; rw [← h.2]; exact Gradient.flat_short
  | gradient a s rest =>
    by_cases hc : rest.length ≤ gradientSegments ∧ stopsAscend (s :: rest) = true
    · simp [shadingState, hc] at h; rw [← h.2]; exact Gradient.ofStops_short o a s rest hc.1
    · simp [shadingState, hc] at h
  | steps a s rest =>
    by_cases hc : rest.length ≤ gradientSegments ∧ stopsAscend (s :: rest) = true
    · simp [shadingState, hc] at h; rw [← h.2]; exact Gradient.ofSteps_short o a s rest hc.1
    · simp [shadingState, hc] at h

/-- A flat shading is drawn in its colour with a gradient that changes nothing. -/
theorem Tile.stateOf_colour (t : Tile) (c : Scene.Command) (k : Scene.Color) (h : c.color = .flat k) :
    (t.stateOf c).colour = colourWords k ∧ (t.stateOf c).grad = .flat := by
  simp [Tile.stateOf, shadingState, h]

/-- A gradient that the renderer can draw takes its first stop's colour and the gradient of its stops. -/
theorem Tile.stateOf_gradient (t : Tile) (c : Scene.Command) (a s rest) (h : c.color = .gradient a s rest)
    (hn : rest.length ≤ gradientSegments) (hs : stopsAscend (s :: rest) = true) :
    (t.stateOf c).colour = colourWords s.color ∧ (t.stateOf c).grad = .ofStops t.origin a s rest := by
  simp [Tile.stateOf, shadingState, h, hn, hs]

/-- A gradient that cannot be drawn gets an empty scissor, so it draws nothing. -/
theorem Tile.stateOf_unsupported (t : Tile) (c : Scene.Command) (a s rest) (h : c.color = .gradient a s rest)
    (hu : ¬ (rest.length ≤ gradientSegments ∧ stopsAscend (s :: rest) = true)) :
    (t.stateOf c).scissor = [0, 0, 0, 0] := by
  simp [Tile.stateOf, shadingState, h, hu]

theorem Tile.stateOf_transform (t : Tile) (c : Scene.Command) :
    (t.stateOf c).slope = t.slope ∧ (t.stateOf c).offset = t.offset := by
  unfold Tile.stateOf; split <;> exact ⟨rfl, rfl⟩

theorem Tile.stateOf_scissor (t : Tile) (c : Scene.Command) (k : Scene.Color) (h : c.color = .flat k) :
    (t.stateOf c).scissor = match clipRect c.shape with
      | none => []
      | some none => [0, 0, 0, 0]
      | some (some r) => t.scissor r := by
  unfold Tile.stateOf; rw [h]; rfl

theorem colourWords_length (c : Scene.Color) : (colourWords c).length = 4 := rfl

theorem colourWords_eq (c : Scene.Color) :
    colourWords c = [c.r, c.g, c.b, c.a].map fun v => (Float32.ofNat v.toNat / 255).toBits := rfl

theorem State.set_slope (s : State) (ws : List UInt32) : (s.set 0 ws) = { s with slope := ws } := rfl

theorem State.set_offset (s : State) (ws : List UInt32) : (s.set 1 ws) = { s with offset := ws } := rfl

theorem State.set_size (s : State) (ws : List UInt32) : (s.set 2 ws) = { s with size := ws } := rfl

theorem State.set_view (s : State) (ws : List UInt32) : (s.set 3 ws) = { s with view := ws } := rfl

theorem State.set_colour (s : State) (ws : List UInt32) : (s.set 4 ws) = { s with colour := ws } := rfl

theorem State.set_axis (s : State) (ws : List UInt32) :
    s.set 5 ws = { s with grad := { s.grad with axis := ws } } := rfl

theorem State.set_starts (s : State) (ws : List UInt32) :
    s.set 6 ws = { s with grad := { s.grad with starts := ws } } := rfl

theorem State.set_invs (s : State) (ws : List UInt32) :
    s.set 7 ws = { s with grad := { s.grad with invs := ws } } := rfl

theorem State.set_d0 (s : State) (ws : List UInt32) :
    s.set 8 ws = { s with grad := { s.grad with d0 := ws } } := rfl

theorem State.set_d1 (s : State) (ws : List UInt32) :
    s.set 9 ws = { s with grad := { s.grad with d1 := ws } } := rfl

theorem State.set_d2 (s : State) (ws : List UInt32) :
    s.set 10 ws = { s with grad := { s.grad with d2 := ws } } := rfl

theorem State.set_d3 (s : State) (ws : List UInt32) :
    s.set 11 ws = { s with grad := { s.grad with d3 := ws } } := rfl

theorem State.set_other (s : State) (k : Nat) (ws : List UInt32) (h : 12 ≤ k) : s.set k ws = s := by
  match k, h with
  | k + 12, _ => rfl

theorem Item.ops_eq (prev : Option Gradient) (i : Item) :
    i.ops prev = [.uniform 0 i.state.slope, .uniform 1 i.state.offset, .uniform 2 i.state.size,
      .uniform 3 i.state.view, .uniform 4 i.state.colour] ++ i.state.grad.ops prev ++
      [.scissor i.state.scissor, .draw i.handle (i.words.length / i.state.stride) i.state.stride] := rfl

end Inkproof.Gpu
