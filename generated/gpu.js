// Copyright (c) 2026 Paul Butcher. All rights reserved.
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

function decodeCommand(r) {
  switch (r.u8()) {
    case 0: return { op: 0, name: "createBuffer", args: [r.u32()] };
    case 1: return { op: 1, name: "bufferData", args: [r.u32(), r.words()] };
    case 2: return { op: 2, name: "deleteBuffer", args: [r.u32()] };
    case 3: return { op: 3, name: "useProgram", args: [r.u32()] };
    case 4: return { op: 4, name: "uniform", args: [r.u32(), r.words()] };
    case 5: return { op: 5, name: "draw", args: [r.u32(), r.u32()] };
    case 6: return { op: 6, name: "clear", args: [r.u32()] };
    default: throw new Error("unknown command");
  }
}

export function decode(bytes) {
  const r = new Reader(bytes);
  const n = r.u32();
  const cmds = [];
  for (let i = 0; i < n; i++) cmds.push(decodeCommand(r));
  if (!r.done()) throw new Error("trailing bytes");
  return cmds;
}

export function newState() {
  return { buffers: new Map(), programs: new Map(), uniforms: new Map() };
}

export function run(gl, s, bytes) {
  for (const { op, args: a } of decode(bytes)) {
    switch (op) {
    case 0: {
      s.buffers.set(a[0], gl.createBuffer());
      break;
    }
    case 1: {
      gl.bindBuffer(gl.ARRAY_BUFFER, s.buffers.get(a[0]));
      gl.bufferData(gl.ARRAY_BUFFER, a[1], gl.STATIC_DRAW);
      break;
    }
    case 2: {
      gl.deleteBuffer(s.buffers.get(a[0]));
      s.buffers.delete(a[0]);
      break;
    }
    case 3: {
      gl.useProgram(s.programs.get(a[0]));
      break;
    }
    case 4: {
      gl.uniform4fv(s.uniforms.get(a[0]), new Float32Array(a[1].buffer));
      break;
    }
    case 5: {
      gl.bindBuffer(gl.ARRAY_BUFFER, s.buffers.get(a[0]));
      gl.drawArrays(gl.TRIANGLES, 0, a[1]);
      break;
    }
    case 6: {
      gl.clearColor((a[0] >>> 24) / 255, ((a[0] >>> 16) & 255) / 255,
        ((a[0] >>> 8) & 255) / 255, (a[0] & 255) / 255);
      gl.clear(gl.COLOR_BUFFER_BIT);
      break;
    }
    }
  }
}
