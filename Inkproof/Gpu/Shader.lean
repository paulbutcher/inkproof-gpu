/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

namespace Inkproof.Gpu.Shader

inductive Op where
  | add
  | sub
  | mul
  deriving DecidableEq, Repr

/-- Float32 expressions over scalars and vectors; a vector is its list of components. Operators are componentwise, and a scalar operand is broadcast. `rsqrt` is the reciprocal square root of a scalar. Nothing here names a graphics API. -/
inductive Expr where
  | var (name : String)
  | lit (n : Nat)
  | bin (op : Op) (a b : Expr)
  | vec2 (a b : Expr)
  | vec4 (a b c d : Expr)
  | comp (i : Fin 4) (e : Expr)
  | rsqrt (e : Expr)
  deriving Repr

def Op.apply : Op → Float32 → Float32 → Float32
  | .add => (· + ·)
  | .sub => (· - ·)
  | .mul => (· * ·)

def Op.lift (op : Op) : List Float32 → List Float32 → Option (List Float32)
  | [x], ys => some (ys.map (op.apply x))
  | xs, [y] => some (xs.map (op.apply · y))
  | xs, ys => if xs.length = ys.length then some (List.zipWith op.apply xs ys) else none

/-- Components of a scalar expression, `none` if it is not one. -/
def scalar : List Float32 → Option Float32
  | [x] => some x
  | _ => none

/-- Values are Float32 under the model of inkproof-float; no fused multiply-add is assumed. -/
def Expr.eval (env : String → Option (List Float32)) : Expr → Option (List Float32)
  | .var n => env n
  | .lit n => some [OfNat.ofNat n]
  | .bin op a b => do op.lift (← a.eval env) (← b.eval env)
  | .vec2 a b => do
    let x ← scalar (← a.eval env)
    let y ← scalar (← b.eval env)
    some [x, y]
  | .vec4 a b c d => do
    let x ← scalar (← a.eval env)
    let y ← scalar (← b.eval env)
    let z ← scalar (← c.eval env)
    let w ← scalar (← d.eval env)
    some [x, y, z, w]
  | .comp i e => do
    let v ← e.eval env
    match v[i.val]? with
    | some x => some [x]
    | none => none
  | .rsqrt e => do
    let x ← scalar (← e.eval env)
    some [1 / x.sqrt]

def broadcastDim (m n : Nat) : Option Nat :=
  if m = 1 then some n else if n = 1 then some m else if m = n then some m else none

/-- The dimension (1, 2, 3 or 4) of an expression given the dimensions of its variables. -/
def Expr.dim (env : String → Option Nat) : Expr → Option Nat
  | .var n => env n
  | .lit _ => some 1
  | .bin _ a b => do broadcastDim (← a.dim env) (← b.dim env)
  | .vec2 a b => do
    if (← a.dim env) = 1 ∧ (← b.dim env) = 1 then some 2 else none
  | .vec4 a b c d => do
    if (← a.dim env) = 1 ∧ (← b.dim env) = 1 ∧ (← c.dim env) = 1 ∧ (← d.dim env) = 1
    then some 4 else none
  | .comp i e => do
    if i.val < (← e.dim env) then some 1 else none
  | .rsqrt e => do
    if (← e.dim env) = 1 then some 1 else none

def Op.glsl : Op → String
  | .add => "+"
  | .sub => "-"
  | .mul => "*"

def componentName : Fin 4 → String
  | 0 => "x"
  | 1 => "y"
  | 2 => "z"
  | 3 => "w"

/-- GLSL text of an expression; operators are fully parenthesised so no precedence is relied on. -/
def Expr.glsl : Expr → String
  | .var n => n
  | .lit n => s!"{n}.0"
  | .bin op a b => s!"({a.glsl} {op.glsl} {b.glsl})"
  | .vec2 a b => s!"vec2({a.glsl}, {b.glsl})"
  | .vec4 a b c d => s!"vec4({a.glsl}, {b.glsl}, {c.glsl}, {d.glsl})"
  | .comp i e => s!"{e.glsl}.{componentName i}"
  | .rsqrt e => s!"inversesqrt({e.glsl})"

theorem Expr.glsl_var (n : String) : (Expr.var n).glsl = n := rfl

theorem Expr.glsl_lit (n : Nat) : (Expr.lit n).glsl = s!"{n}.0" := rfl

theorem Expr.glsl_bin (op : Op) (a b : Expr) :
    (Expr.bin op a b).glsl = s!"({a.glsl} {op.glsl} {b.glsl})" := rfl

theorem Expr.glsl_vec2 (a b : Expr) :
    (Expr.vec2 a b).glsl = s!"vec2({a.glsl}, {b.glsl})" := rfl

theorem Expr.glsl_vec4 (a b c d : Expr) :
    (Expr.vec4 a b c d).glsl = s!"vec4({a.glsl}, {b.glsl}, {c.glsl}, {d.glsl})" := rfl

theorem Expr.glsl_comp (i : Fin 4) (e : Expr) :
    (Expr.comp i e).glsl = s!"{e.glsl}.{componentName i}" := rfl

theorem Expr.glsl_rsqrt (e : Expr) : (Expr.rsqrt e).glsl = s!"inversesqrt({e.glsl})" := rfl

theorem Op.glsl_add : Op.add.glsl = "+" := rfl

theorem Op.glsl_sub : Op.sub.glsl = "-" := rfl

theorem Op.glsl_mul : Op.mul.glsl = "*" := rfl

theorem Expr.eval_var (env : String → Option (List Float32)) (n : String) :
    (Expr.var n).eval env = env n := rfl

theorem Expr.eval_lit (env : String → Option (List Float32)) (n : Nat) :
    (Expr.lit n).eval env = some [OfNat.ofNat n] := rfl

theorem Expr.eval_bin (env : String → Option (List Float32)) (op : Op) (a b : Expr) :
    (Expr.bin op a b).eval env = (do op.lift (← a.eval env) (← b.eval env)) := rfl

theorem Expr.eval_vec2 (env : String → Option (List Float32)) (a b : Expr) :
    (Expr.vec2 a b).eval env = (do
      let x ← scalar (← a.eval env)
      let y ← scalar (← b.eval env)
      some [x, y]) := rfl

theorem Expr.eval_vec4 (env : String → Option (List Float32)) (a b c d : Expr) :
    (Expr.vec4 a b c d).eval env = (do
      let x ← scalar (← a.eval env)
      let y ← scalar (← b.eval env)
      let z ← scalar (← c.eval env)
      let w ← scalar (← d.eval env)
      some [x, y, z, w]) := rfl

theorem Expr.eval_comp (env : String → Option (List Float32)) (i : Fin 4) (e : Expr) :
    (Expr.comp i e).eval env = (do
      let v ← e.eval env
      match v[i.val]? with
      | some x => some [x]
      | none => none) := rfl

theorem Expr.eval_rsqrt (env : String → Option (List Float32)) (e : Expr) :
    (Expr.rsqrt e).eval env = (do
      let x ← scalar (← e.eval env)
      some [1 / x.sqrt]) := rfl

theorem Op.lift_scalar_left (op : Op) (x : Float32) (ys : List Float32) :
    op.lift [x] ys = some (ys.map (op.apply x)) := by
  simp [Op.lift]

theorem Op.lift_scalar_right (op : Op) (x : Float32) (xs : List Float32) (h : xs.length ≠ 1) :
    op.lift xs [x] = some (xs.map (op.apply · x)) := by
  match xs, h with
  | [], _ | _ :: _ :: _, _ => simp [Op.lift]
  | [_], h => exact absurd rfl h

theorem Op.lift_zipWith (op : Op) (xs ys : List Float32) (hx : xs.length ≠ 1) (hy : ys.length ≠ 1)
    (h : xs.length = ys.length) : op.lift xs ys = some (List.zipWith op.apply xs ys) := by
  match xs, ys, hx, hy with
  | [], [], _, _ => simp [Op.lift]
  | [], _ :: _ :: _, _, _ => simp [Op.lift, h]
  | _ :: _ :: _, [], _, _ => simp [Op.lift, h]
  | _ :: _ :: _, _ :: _ :: _, _, _ => simp [Op.lift, h]
  | [_], _, hx, _ => exact absurd rfl hx
  | _, [_], _, hy => exact absurd rfl hy

theorem Expr.dim_var (env : String → Option Nat) (n : String) : (Expr.var n).dim env = env n := rfl

theorem Expr.dim_lit (env : String → Option Nat) (n : Nat) : (Expr.lit n).dim env = some 1 := rfl

theorem Expr.dim_bin (env : String → Option Nat) (op : Op) (a b : Expr) :
    (Expr.bin op a b).dim env = (do broadcastDim (← a.dim env) (← b.dim env)) := rfl

theorem Expr.dim_vec2 (env : String → Option Nat) (a b : Expr) :
    (Expr.vec2 a b).dim env = (do
      if (← a.dim env) = 1 ∧ (← b.dim env) = 1 then some 2 else none) := rfl

theorem Expr.dim_vec4 (env : String → Option Nat) (a b c d : Expr) :
    (Expr.vec4 a b c d).dim env = (do
      if (← a.dim env) = 1 ∧ (← b.dim env) = 1 ∧ (← c.dim env) = 1 ∧ (← d.dim env) = 1
      then some 4 else none) := rfl

theorem Expr.dim_rsqrt (env : String → Option Nat) (e : Expr) :
    (Expr.rsqrt e).dim env = (do
      if (← e.dim env) = 1 then some 1 else none) := rfl

theorem Expr.dim_comp (env : String → Option Nat) (i : Fin 4) (e : Expr) :
    (Expr.comp i e).dim env = (do
      if i.val < (← e.dim env) then some 1 else none) := rfl

def tyGlsl : Nat → String
  | 1 => "float"
  | n => s!"vec{n}"

/-- A named, typed shader variable. -/
structure Var where
  name : String
  dim : Nat

structure Decl where
  name : String
  dim : Nat
  init : Expr

/-- A shader stage: inputs and uniforms are given by the caller, `decls` are local definitions in order, and each assignment writes an output, either declared in `outs` or a built-in. -/
structure Shader where
  ins : List Var
  uniforms : List Var
  outs : List Var
  decls : List Decl
  assigns : List (String × Expr)

def Shader.env (s : Shader) : String → Option Nat := fun n =>
  ((s.ins ++ s.uniforms ++ s.decls.map fun (d : Decl) => (⟨d.name, d.dim⟩ : Var)).find? (·.name == n)).map (·.dim)

/-- Every declaration has the dimension it claims. Built-in outputs are checked by the caller. -/
def Shader.WellTyped (s : Shader) : Prop :=
  ∀ d ∈ s.decls, d.init.dim s.env = some d.dim

instance (s : Shader) : Decidable s.WellTyped := by
  unfold Shader.WellTyped; infer_instance

def Var.glsl (qualifier : String) (v : Var) : String :=
  s!"{qualifier} {tyGlsl v.dim} {v.name};"

/-- `#version` must be the first line: WebGL2 rejects anything before it, comments included. -/
def glslHeader : List String :=
  ["#version 300 es",
   "// Copyright (c) 2026 Paul Butcher. All rights reserved.",
   "// Released under Apache 2.0 license as described in the file LICENSE.",
   "// Generated from Inkproof.Gpu.Shader. Do not edit.",
   "precision highp float;"]

/-- GLSL ES 3.00 source. -/
def Shader.glsl (s : Shader) : String :=
  let header := glslHeader
  let vars := s.ins.map (·.glsl "in") ++ s.uniforms.map (·.glsl "uniform") ++ s.outs.map (·.glsl "out")
  let decls := s.decls.map fun d => s!"  {tyGlsl d.dim} {d.name} = {d.init.glsl};"
  let assigns := s.assigns.map fun (n, e) => s!"  {n} = {e.glsl};"
  "\n".intercalate (header ++ vars ++ ["void main() {"] ++ decls ++ assigns ++ ["}"]) ++ "\n"

/-- Runs the stage: the result lists each assigned output. -/
def Shader.run (s : Shader) (inputs : String → Option (List Float32)) :
    Option (List (String × List Float32)) := do
  let env ← s.decls.foldlM (init := inputs) fun env d => do
    let v ← d.init.eval env
    some fun n => if n == d.name then some v else env n
  s.assigns.mapM fun (n, e) => do some (n, ← e.eval env)

theorem Shader.glsl_eq (s : Shader) :
    s.glsl = "\n".intercalate (glslHeader ++ (s.ins.map (·.glsl "in") ++
      s.uniforms.map (·.glsl "uniform") ++ s.outs.map (·.glsl "out")) ++ ["void main() {"] ++
      s.decls.map (fun d => s!"  {tyGlsl d.dim} {d.name} = {d.init.glsl};") ++
      s.assigns.map (fun (n, e) => s!"  {n} = {e.glsl};") ++ ["}"]) ++ "\n" := rfl

theorem Shader.run_eq (s : Shader) (inputs : String → Option (List Float32)) :
    s.run inputs = (do
      let env ← s.decls.foldlM (init := inputs) fun env d => do
        let v ← d.init.eval env
        some fun n => if n == d.name then some v else env n
      s.assigns.mapM fun (n, e) => do some (n, ← e.eval env)) := rfl

theorem Shader.run_no_decls (s : Shader) (h : s.decls = []) (inputs : String → Option (List Float32)) :
    s.run inputs = (s.assigns.mapM fun (n, e) => do some (n, ← e.eval inputs)) := by
  simp [Shader.run, h]

end Inkproof.Gpu.Shader
