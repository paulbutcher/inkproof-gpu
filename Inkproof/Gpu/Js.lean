/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Gpu.Wire
import Inkproof.Gpu.Shaders

namespace Inkproof.Gpu

def FieldTy.jsRead : FieldTy → String
  | .u32 => "r.u32()"
  | .words => "r.words()"

theorem FieldTy.jsRead_u32 : FieldTy.u32.jsRead = "r.u32()" := rfl

theorem FieldTy.jsRead_words : FieldTy.words.jsRead = "r.words()" := rfl

/-- The uniforms of the renderer's program, in the order `uniform` numbers them: those of the vertex shader, then those of the fragment shader. -/
def uniformNames : List String :=
  (vertexShader.uniforms ++ fragmentShader.uniforms).map (·.name)

theorem uniformNames_eq : uniformNames = ["u_slope", "u_offset", "u_colour"] := rfl

/-- The WebGL2 realisation of each command, over `gl`, the context, and `s`, the interpreter state. `createProgram` builds the renderer's program, and `uniform` takes the number of a uniform of that program; `draw` reads each vertex as two floats bound to attribute 0. -/
def webglBody : String → List String
  | "createBuffer" => ["s.buffers.set(a[0], gl.createBuffer());"]
  | "bufferData" => ["gl.bindBuffer(gl.ARRAY_BUFFER, s.buffers.get(a[0]));",
      "gl.bufferData(gl.ARRAY_BUFFER, a[1], gl.STATIC_DRAW);"]
  | "deleteBuffer" => ["gl.deleteBuffer(s.buffers.get(a[0]));", "s.buffers.delete(a[0]);"]
  | "useProgram" => ["s.current = s.programs.get(a[0]);", "gl.useProgram(s.current.program);"]
  | "uniform" => ["const w = new Float32Array(a[1].buffer);",
      "gl[\"uniform\" + w.length + \"fv\"](s.current.uniforms[a[0]], w);"]
  | "draw" => ["gl.bindBuffer(gl.ARRAY_BUFFER, s.buffers.get(a[0]));",
      "gl.enableVertexAttribArray(0);", "gl.vertexAttribPointer(0, 2, gl.FLOAT, false, 0, 0);",
      "gl.drawArrays(gl.TRIANGLES, 0, a[1]);"]
  | "clear" => ["gl.clearColor((a[0] >>> 24) / 255, ((a[0] >>> 16) & 255) / 255,",
      "  ((a[0] >>> 8) & 255) / 255, (a[0] & 255) / 255);", "gl.clear(gl.COLOR_BUFFER_BIT);"]
  | "createProgram" => ["s.programs.set(a[0], buildProgram(gl));"]
  | _ => []

theorem webglBody_createBuffer :
    webglBody "createBuffer" = ["s.buffers.set(a[0], gl.createBuffer());"] := rfl

theorem webglBody_useProgram :
    webglBody "useProgram" = ["s.current = s.programs.get(a[0]);", "gl.useProgram(s.current.program);"] := rfl

theorem webglBody_createProgram :
    webglBody "createProgram" = ["s.programs.set(a[0], buildProgram(gl));"] := rfl

theorem webglBody_unknown (n : String) (h : n ∉ ["createBuffer", "bufferData", "deleteBuffer",
    "useProgram", "uniform", "draw", "clear", "createProgram"]) : webglBody n = [] := by
  unfold webglBody
  split <;> simp_all

def jsSpecCase (s : Spec) : String :=
  let reads := ", ".intercalate (s.fields.map FieldTy.jsRead)
  s!"    case {s.op}: return \{ op: {s.op}, name: \"{s.name}\", args: [{reads}] };"

theorem jsSpecCase_eq (s : Spec) :
    jsSpecCase s = s!"    case {s.op}: return \{ op: {s.op}, name: \"{s.name}\", args: [{", ".intercalate (s.fields.map FieldTy.jsRead)}] };" := rfl

def jsRunCase (s : Spec) : String :=
  let body := "\n".intercalate ((webglBody s.name).map ("      " ++ ·))
  s!"    case {s.op}: \{\n{body}\n      break;\n    }"

theorem jsRunCase_eq (s : Spec) :
    jsRunCase s = s!"    case {s.op}: \{\n{"\n".intercalate ((webglBody s.name).map ("      " ++ ·))}\n      break;\n    }" := rfl

/-- The generated decoder and interpreter. -/
def js : String :=
  let decode := "\n".intercalate (specs.map jsSpecCase)
  let run := "\n".intercalate (specs.map jsRunCase)
  "// Copyright (c) 2026 Paul Butcher. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.
// Generated from Inkproof.Gpu.specs. Do not edit.

class Reader {
  constructor(bytes) {
    this.v = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
    this.p = 0;
  }
  u8() { return this.v.getUint8(this.p++); }
  u32() { const n = this.v.getUint32(this.p, true); this.p += 4; return n; }
  words() {
    const n = this.u32();
    const w = new Uint32Array(n);
    for (let i = 0; i < n; i++) w[i] = this.u32();
    return w;
  }
  done() { return this.p === this.v.byteLength; }
}

const VERTEX_SOURCE = " ++ vertexShader.glsl.quote ++ ";
const FRAGMENT_SOURCE = " ++ fragmentShader.glsl.quote ++ ";
const UNIFORM_NAMES = [" ++ ", ".intercalate (uniformNames.map String.quote) ++ "];

function compile(gl, type, source) {
  const shader = gl.createShader(type);
  gl.shaderSource(shader, source);
  gl.compileShader(shader);
  if (!gl.getShaderParameter(shader, gl.COMPILE_STATUS)) throw new Error(gl.getShaderInfoLog(shader));
  return shader;
}

function buildProgram(gl) {
  const program = gl.createProgram();
  gl.attachShader(program, compile(gl, gl.VERTEX_SHADER, VERTEX_SOURCE));
  gl.attachShader(program, compile(gl, gl.FRAGMENT_SHADER, FRAGMENT_SOURCE));
  gl.bindAttribLocation(program, 0, \"a_position\");
  gl.linkProgram(program);
  if (!gl.getProgramParameter(program, gl.LINK_STATUS)) throw new Error(gl.getProgramInfoLog(program));
  return { program, uniforms: UNIFORM_NAMES.map(n => gl.getUniformLocation(program, n)) };
}

function decodeCommand(r) {
  switch (r.u8()) {
" ++ decode ++ "
    default: throw new Error(\"unknown command\");
  }
}

export function decode(bytes) {
  const r = new Reader(bytes);
  const n = r.u32();
  const cmds = [];
  for (let i = 0; i < n; i++) cmds.push(decodeCommand(r));
  if (!r.done()) throw new Error(\"trailing bytes\");
  return cmds;
}

export function newState() {
  return { buffers: new Map(), programs: new Map(), current: null };
}

export function run(gl, s, bytes) {
  for (const { op, args: a } of decode(bytes)) {
    switch (op) {
" ++ run ++ "
    }
  }
}
"

end Inkproof.Gpu
