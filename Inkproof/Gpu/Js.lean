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

theorem uniformNames_eq :
    uniformNames = ["u_slope", "u_offset", "u_size", "u_view", "u_colour", "u_axis", "u_start", "u_inv",
      "u_delta0", "u_delta1", "u_delta2", "u_delta3"] := rfl

/-- The value each attribute of the vertex shader after the first takes when a vertex has no words for it. -/
def attributeDefaults : List (Nat × Nat) := [(1, 0), (0, 0)]

theorem attributeDefaults_eq : attributeDefaults = [(1, 0), (0, 0)] := rfl

/-- The lines that bind a vertex buffer to the attributes of the vertex shader. A vertex's words are two floats for each attribute in order, as many as its stride in words says, and the rest take their defaults. -/
def attributeLines : List String :=
  ["const n = a[2] / 2;", "for (let i = 0; i < n; i++) {", "  gl.enableVertexAttribArray(i);",
   "  gl.vertexAttribPointer(i, 2, gl.FLOAT, false, 4 * a[2], 8 * i);", "}"] ++
  (attributeDefaults.mapIdx fun i d =>
    s!"if (n <= {i + 1}) \{ gl.disableVertexAttribArray({i + 1}); gl.vertexAttrib2f({i + 1}, {d.1}, {d.2}); }")

/-- The WebGL2 realisation of each command, over `gl`, the context, and `s`, the interpreter state. `createProgram` builds the renderer's program, and `uniform` takes the number of a uniform of that program; `draw` reads each vertex as the number of words its third operand gives, two floats for each attribute of the vertex shader in order, with the defaults of `attributeDefaults` for any it has no words for, and `useProgram` also enables source-over blending of premultiplied colours, and `clear` premultiplies its colour; `scissor` takes four 32-bit integers (x, y, width, height from the bottom left) or none to draw unrestricted. -/
def webglBody : String → List String
  | "createBuffer" => ["s.buffers.set(a[0], gl.createBuffer());"]
  | "bufferData" => ["gl.bindBuffer(gl.ARRAY_BUFFER, s.buffers.get(a[0]));",
      "gl.bufferData(gl.ARRAY_BUFFER, a[1], gl.STATIC_DRAW);"]
  | "deleteBuffer" => ["gl.deleteBuffer(s.buffers.get(a[0]));", "s.buffers.delete(a[0]);"]
  | "useProgram" => ["s.current = s.programs.get(a[0]);", "gl.useProgram(s.current.program);",
      "gl.enable(gl.BLEND);", "gl.blendFunc(gl.ONE, gl.ONE_MINUS_SRC_ALPHA);"]
  | "uniform" => ["const w = new Float32Array(a[1].buffer);",
      "gl[\"uniform\" + w.length + \"fv\"](s.current.uniforms[a[0]], w);"]
  | "draw" => ["gl.bindBuffer(gl.ARRAY_BUFFER, s.buffers.get(a[0]));"] ++ attributeLines ++
      ["gl.drawArrays(gl.TRIANGLES, 0, a[1]);"]
  | "clear" => ["const ca = (a[0] & 255) / 255;",
      "gl.clearColor((a[0] >>> 24) / 255 * ca, ((a[0] >>> 16) & 255) / 255 * ca,",
      "  ((a[0] >>> 8) & 255) / 255 * ca, ca);", "gl.clear(gl.COLOR_BUFFER_BIT);"]
  | "createProgram" => ["s.programs.set(a[0], buildProgram(gl));"]
  | "scissor" => ["const w = new Int32Array(a[0].buffer);",
      "if (w.length === 4) { gl.enable(gl.SCISSOR_TEST); gl.scissor(w[0], w[1], w[2], w[3]); }",
      "else { gl.disable(gl.SCISSOR_TEST); }"]
  | _ => []

theorem webglBody_createBuffer :
    webglBody "createBuffer" = ["s.buffers.set(a[0], gl.createBuffer());"] := rfl

theorem webglBody_useProgram :
    webglBody "useProgram" = ["s.current = s.programs.get(a[0]);", "gl.useProgram(s.current.program);",
      "gl.enable(gl.BLEND);", "gl.blendFunc(gl.ONE, gl.ONE_MINUS_SRC_ALPHA);"] := rfl

theorem webglBody_createProgram :
    webglBody "createProgram" = ["s.programs.set(a[0], buildProgram(gl));"] := rfl

theorem webglBody_unknown (n : String) (h : n ∉ ["createBuffer", "bufferData", "deleteBuffer",
    "useProgram", "uniform", "draw", "clear", "createProgram", "scissor"]) : webglBody n = [] := by
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

/-- The lines of `buildProgram` that give each attribute of the vertex shader its location, its position in `ins`. -/
def bindLines : String :=
  "\n".intercalate ((vertexShader.ins.mapIdx fun i v =>
    s!"  gl.bindAttribLocation(program, {i}, {v.name.quote});"))

theorem attributeLines_eq :
    attributeLines =
      ["const n = a[2] / 2;", "for (let i = 0; i < n; i++) {", "  gl.enableVertexAttribArray(i);",
       "  gl.vertexAttribPointer(i, 2, gl.FLOAT, false, 4 * a[2], 8 * i);", "}",
       "if (n <= 1) { gl.disableVertexAttribArray(1); gl.vertexAttrib2f(1, 1, 0); }",
       "if (n <= 2) { gl.disableVertexAttribArray(2); gl.vertexAttrib2f(2, 0, 0); }"] := by decide +kernel

theorem bindLines_eq :
    bindLines = "\n".intercalate
      ((["a_position", "a_dir", "a_corner"] : List String).mapIdx fun i n =>
        s!"  gl.bindAttribLocation(program, {i}, {n.quote});") := by
  simp [bindLines, vertexShader, List.mapIdx_eq_zipIdx_map]

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
  const shaders = [compile(gl, gl.VERTEX_SHADER, VERTEX_SOURCE), compile(gl, gl.FRAGMENT_SHADER, FRAGMENT_SOURCE)];
  for (const shader of shaders) gl.attachShader(program, shader);
" ++ bindLines ++ "
  gl.linkProgram(program);
  const linked = gl.getProgramParameter(program, gl.LINK_STATUS);
  for (const shader of shaders) gl.deleteShader(shader);
  if (!linked) {
    const log = gl.getProgramInfoLog(program);
    gl.deleteProgram(program);
    throw new Error(log);
  }
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

export function releaseState(gl, s) {
  if (s.current) gl.useProgram(null);
  for (const b of s.buffers.values()) gl.deleteBuffer(b);
  for (const p of s.programs.values()) gl.deleteProgram(p.program);
  s.buffers.clear();
  s.programs.clear();
  s.current = null;
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
