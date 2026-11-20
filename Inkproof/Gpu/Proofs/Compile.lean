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

def Gpu.empty : Gpu := ⟨fun _ => none, ⟨[], [], [], [], [], 0, []⟩, []⟩

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

private theorem items_cmds (tess : Scene.Command → List UInt32) (t : Tile) :
    (t.items tess).map Prod.fst = t.cmds tess := by
  simp [Tile.items, Tile.cmds, List.map_map, Function.comp_def]

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
    (hs : s.Inv g) :
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
      rw [items_cmds, ← hw]; exact hbuf j (by rw [hw, ← items_cmds, List.length_map]; exact hj))
    refine ⟨⟨hv, ?_, hset⟩, ?_⟩
    · intro i hi'
      simp only [List.mem_append] at hi'
      rcases hi' with hi' | hi'
      · exact hi i hi'
      · obtain ⟨j, hj, h1, h2⟩ := hok i hi'
        refine ⟨?_, h2⟩
        have : j < e.words.length := by rw [hw, ← items_cmds, List.length_map]; exact hj
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
    have hfst : (t.items tess).map Prod.fst = ws := by rw [items_cmds, hws]
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
    ∀ (tiles : List Tile) (s : Stage), s.Inv g →
      (tiles.foldl (stageTile tess) s).Inv g ∧
      (tiles.foldl (stageTile tess) s).items.map Item.toDraw =
        s.items.map Item.toDraw ++ frameDraws tess tiles := by
  intro tiles
  induction tiles with
  | nil => intro s hs; simp [frameDraws, hs]
  | cons t ts ih =>
    intro s hs
    obtain ⟨h1, h2⟩ := stageTile_inv tess s g t hs
    obtain ⟨h3, h4⟩ := ih _ h1
    refine ⟨h3, ?_⟩
    simp only [List.foldl_cons, h4, h2, frameDraws, List.flatMap_cons, List.append_assoc]
    simp [Tile.items, List.map_map, Function.comp_def]

private theorem run_draws (g : Gpu) (L : List Item)
    (h : ∀ i ∈ L, g.buffers i.handle = some i.words) :
    (g.run (L.flatMap Item.ops)).log = g.log ++ L.map Item.toDraw ∧
    (g.run (L.flatMap Item.ops)).buffers = g.buffers := by
  induction L generalizing g with
  | nil => simp [Gpu.run]
  | cons i L ih =>
    have hi := h i (List.mem_cons_self ..)
    have hs : g.run i.ops =
        ⟨g.buffers, i.state, g.log ++ [Draw.mk i.words (i.words.length / i.state.stride) i.state]⟩ := by
      simp [Item.ops, Gpu.run, Gpu.step, State.set, hi]
    have := ih (g.run i.ops) (fun j hj => by
      rw [hs]; simpa using h j (List.mem_cons_of_mem _ hj))
    rw [List.flatMap_cons, Gpu.run_append]
    rw [hs] at this ⊢
    refine ⟨by rw [this.1]; simp [Item.toDraw], this.2⟩

private theorem compile_eq (tess : Scene.Command → List UInt32) (c : Cache) (tiles : List Tile) :
    ∃ s : Stage, s = tiles.foldl (stageTile tess)
      ⟨{ c with entries := c.entries.filter fun e => tiles.any fun t => decide (e.words = t.cmds tess) },
        (c.entries.filter fun e => !(tiles.any fun t => decide (e.words = t.cmds tess))).flatMap
          fun e => deletes e.base e.words.length, []⟩ ∧
      compile tess c tiles = (s.cache, s.ops ++ s.items.flatMap Item.ops) :=
  ⟨_, rfl, rfl⟩

private theorem initial_inv (tess : Scene.Command → List UInt32) (c : Cache) (tiles : List Tile) (g : Gpu)
    (hv : c.Valid g) :
    (Stage.mk
      { c with entries := c.entries.filter fun e => tiles.any fun t => decide (e.words = t.cmds tess) }
      ((c.entries.filter fun e => !(tiles.any fun t => decide (e.words = t.cmds tess))).flatMap
          fun e => deletes e.base e.words.length) []).Inv g := by
  have hperm := List.filter_append_perm
    (fun e : Entry => tiles.any fun t => decide (e.words = t.cmds tess)) c.entries
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
in paint order, and leaves the cache valid for the GPU it produces. -/
theorem compile_log (tess : Scene.Command → List UInt32) (c : Cache) (tiles : List Tile) (g : Gpu)
    (hv : c.Valid g) :
    (g.run (compile tess c tiles).2).log = g.log ++ frameDraws tess tiles ∧
    (compile tess c tiles).1.Valid (g.run (compile tess c tiles).2) := by
  obtain ⟨s, hs, hc⟩ := compile_eq tess c tiles
  rw [hc]
  obtain ⟨hinv, hmap⟩ := foldl_stage tess g tiles _ (initial_inv tess c tiles g hv)
  rw [← hs] at hinv hmap
  obtain ⟨hvalid, hitems, hset⟩ := hinv
  rw [Gpu.run_append]
  obtain ⟨hlog, hbuf⟩ := run_draws (g.run s.ops) s.items (fun i hi => (hitems i hi).2)
  refine ⟨?_, hvalid.congr hbuf⟩
  rw [hlog, (Gpu.run_setup g s.ops hset).1]
  simp only [List.nil_append, List.map_nil] at hmap
  rw [← hmap]

theorem compile_valid (tess : Scene.Command → List UInt32) (c : Cache) (tiles : List Tile) (g : Gpu)
    (hv : c.Valid g) : (compile tess c tiles).1.Valid (g.run (compile tess c tiles).2) :=
  (compile_log tess c tiles g hv).2

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
theorem compile_cache_cached (tess : Scene.Command → List UInt32) (c : Cache) (tiles : List Tile) :
    ∀ t ∈ tiles, t.Cached tess (compile tess c tiles).1 := by
  obtain ⟨s, hs, hc⟩ := compile_eq tess c tiles
  rw [hc]
  subst hs
  exact (foldl_entries tess tiles _).2

/-- Reusing cached buffers draws what uploading afresh would. -/
theorem cached_eq_fresh (tess : Scene.Command → List UInt32) (c : Cache) (tiles : List Tile) (g : Gpu)
    (hv : c.Valid g) :
    (g.run (compile tess c tiles).2).log = g.log ++ frameDraws tess tiles ∧
    (Gpu.empty.run (compile tess {} tiles).2).log = frameDraws tess tiles := by
  refine ⟨(compile_log tess c tiles g hv).1, ?_⟩
  simpa [Gpu.empty] using (compile_log tess {} tiles Gpu.empty (Cache.valid_empty _)).1

/-- When every tile is cached, a frame creates and uploads nothing: it is uniform updates, draws and
deletions of buffers no tile needs. -/
theorem compile_cached (tess : Scene.Command → List UInt32) (c : Cache) (tiles : List Tile)
    (h : ∀ t ∈ tiles, t.Cached tess c) : ∀ o ∈ (compile tess c tiles).2, ¬ o.IsUpload := by
  obtain ⟨s, hs, hc⟩ := compile_eq tess c tiles
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
  simp only [List.mem_append, List.mem_flatMap] at ho
  rcases ho with ho | ⟨i, _, ho⟩
  · refine key tiles _ ?_ ?_ o ho
    · intro o ho
      simp only [List.mem_flatMap] at ho
      obtain ⟨e, _, ho⟩ := ho
      exact uploads_not_upload_free _ _ o ho
    · intro t ht
      obtain ⟨e, he, hw⟩ := h t ht
      refine ⟨e, ?_, hw⟩
      simp only [List.mem_filter, List.any_eq_true]
      exact ⟨he, t, ht, by simpa using hw⟩
  · simp only [Item.ops, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Op.IsUpload]

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

theorem Tile.cmds_eq (tess : Scene.Command → List UInt32) (t : Tile) :
    t.cmds tess = t.list.paintOrder.map tess := rfl

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

theorem shadingColour_flat (k : Scene.Color) : shadingColour (.flat k) = some k := rfl

theorem shadingColour_gradient (a s rest) : shadingColour (.gradient a s rest) = none := rfl

theorem Tile.stateOf_colour (t : Tile) (c : Scene.Command) (k : Scene.Color) (h : c.color = .flat k) :
    (t.stateOf c).colour = colourWords k := by
  simp [Tile.stateOf, shadingColour, h]

/-- A gradient command is not drawn: its scissor is empty. -/
theorem Tile.stateOf_gradient (t : Tile) (c : Scene.Command) (a s rest) (h : c.color = .gradient a s rest) :
    (t.stateOf c).scissor = [0, 0, 0, 0] := by
  simp [Tile.stateOf, shadingColour, h]

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

theorem State.set_other (s : State) (k : Nat) (ws : List UInt32) (h : 5 ≤ k) : s.set k ws = s := by
  match k, h with
  | k + 5, _ => rfl

theorem Item.ops_eq (i : Item) :
    i.ops = [.uniform 0 i.state.slope, .uniform 1 i.state.offset, .uniform 2 i.state.size,
      .uniform 3 i.state.view, .uniform 4 i.state.colour, .scissor i.state.scissor,
      .draw i.handle (i.words.length / i.state.stride) i.state.stride] := rfl

theorem Tile.items_eq (tess : Scene.Command → List UInt32) (t : Tile) :
    t.items tess = t.list.paintOrder.map fun c => (tess c, t.stateOf c) := rfl

end Inkproof.Gpu
