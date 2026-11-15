/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Gpu

open Inkproof.Gpu

def sample : List Cmd := [
  ⟨0, [.u32 7]⟩,
  ⟨1, [.u32 7, .words [1, 2, 0xFFFFFFFF]]⟩,
  ⟨4, [.u32 0, .words []]⟩,
  ⟨5, [.u32 7, .u32 3]⟩,
  ⟨6, [.u32 0x11223344]⟩
]

def fail (msg : String) : IO UInt32 := do
  IO.eprintln s!"FAIL: {msg}"
  return 1

/-- The generated decoder, run under node, must agree with the Lean decoder. -/
def jsDecodes (dir : System.FilePath) (cs : List Cmd) : IO Bool := do
  let mod := dir / "gpu.mjs"
  IO.FS.writeFile mod js
  let bytes := ", ".intercalate ((encode cs).map (toString ·.toNat))
  let script := s!"import \{ decode } from \"{mod}\";
const cmds = decode(new Uint8Array([{bytes}]));
console.log(JSON.stringify(cmds.map(c => [c.op, c.args.map(a => typeof a === \"number\" ? a : Array.from(a))])));"
  IO.FS.writeFile (dir / "run.mjs") script
  let out ← IO.Process.output { cmd := "node", args := #[(dir / "run.mjs").toString] }
  let arg : Arg → String
    | .u32 n => toString n
    | .words ws => "[" ++ ",".intercalate (ws.map toString) ++ "]"
  let expected := "[" ++ ",".intercalate (cs.map fun c =>
    s!"[{c.op},[" ++ ",".intercalate (c.args.map arg) ++ "]]") ++ "]"
  return out.exitCode == 0 && out.stdout.trimAscii.toString == expected

def main : IO UInt32 := do
  let dir : System.FilePath := "/tmp/inkproof-gpu-test"
  IO.FS.createDirAll dir
  if !(← jsDecodes dir sample) then return ← fail "generated JavaScript decoder"
  for (name, text) in [("gpu.js", js), ("vertex.glsl", vertexShader.glsl),
      ("fragment.glsl", fragmentShader.glsl)] do
    if (← IO.FS.readFile s!"../generated/{name}") != text then
      return ← fail s!"generated/{name} is stale; run lake exe gen generated"
  IO.println "ok"
  return 0
