/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Gpu.Shader

namespace Inkproof.Gpu.Shader

theorem broadcastDim_eq (m n : Nat) : broadcastDim m n =
    if m = 1 then some n else if n = 1 then some m else if m = n then some m else none := rfl

theorem env_eq (s : Shader) (n : String) : s.env n =
    ((s.ins ++ s.uniforms ++ s.decls.map fun (d : Decl) => (⟨d.name, d.dim⟩ : Var)).find?
      (·.name == n)).map (·.dim) := rfl

theorem tyGlsl_one : tyGlsl 1 = "float" := rfl

theorem tyGlsl_of_ne_one (n : Nat) (h : n ≠ 1) : tyGlsl n = s!"vec{n}" := by
  unfold tyGlsl; split <;> simp_all

theorem Var.glsl_eq (q : String) (v : Var) : v.glsl q = s!"{q} {tyGlsl v.dim} {v.name};" := rfl

theorem componentName_eq (i : Fin 4) : componentName i =
    (match i with | 0 => "x" | 1 => "y" | 2 => "z" | 3 => "w") := by
  match i with
  | 0 | 1 | 2 | 3 => rfl

end Inkproof.Gpu.Shader
