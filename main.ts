// Tiny stack VM for make.fun's tiny-stack-vm-01 ISA (ISA.md / vm.mjs).
// Runs every program in $MAKEFUN_INPUT_DIR/<id>/ and writes
// $MAKEFUN_OUTPUT_DIR/<id>/{stdout.bin,exit.txt}.
// Semantics: 32-bit wrapping ints, 256-value data stack, 64-deep call
// stack, 256 words of memory, 10 traps with their own exit codes,
// 1,000,000 step limit, 65,536 output limit. Plain JS in a .ts file so
// Node 22 runs it as-is.
//
// 0 HALT, 1 PUSH8 (imm8 sign-extended), 2 PUSH32 (imm32 LE), 3 DROP,
// 4 DUP, 5 SWAP, 6 OVER, 7 ROT, 16 ADD, 17 SUB, 18 MUL, 19 DIV, 20 MOD,
// 21 DIVU, 22 MODU, 23 NEG, 24 AND, 25 OR, 26 XOR, 27 NOT, 28 SHL,
// 29 SHR, 30 SHRU (counts & 31), 32 EQ, 33 LT, 34 LTU (push 1/0;
// DIV/MOD truncate; INT_MIN/-1 wraps; x%-1=0; U=unsigned), 48 JMP,
// 49 JZ, 50 JNZ (imm16 signed rel. to instr. end; pop value), 51 CALL
// (imm16 absolute), 52 RET, 64 LOAD, 65 STORE (pops address then
// value; memory zeroed), 80 PRINT (decimal), 81 PUTC (byte), 82 IN
// (byte; -1 at end of input), 83 EXIT (low byte). Traps (code; prior output
// kept): 2 underflow, 3 overflow, 4 div by zero, 5 unknown opcode,
// 6 bad address, 7 call stack full, 8 empty RET, 9 pc out of
// bounds/truncated imm, 10 step limit, 11 output limit (crossing
// write dropped). I/O: per <id> in MAKEFUN_INPUT_DIR: program.bin +
// input.bin (IN); stdout.bin + exit.txt (code + newline) to
// MAKEFUN_OUTPUT_DIR/<id>/. Unreadable: empty output, exit 0.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Per opcode: [byte, immediate bytes, pops, pushes].
const OPS = [
  [0, 0, 0, 0], [1, 1, 0, 1], [2, 4, 0, 1], [3, 0, 1, 0], [4, 0, 1, 2],
  [5, 0, 2, 2], [6, 0, 2, 3], [7, 0, 3, 3], [16, 0, 2, 1], [17, 0, 2, 1],
  [18, 0, 2, 1], [19, 0, 2, 1], [20, 0, 2, 1], [21, 0, 2, 1], [22, 0, 2, 1],
  [23, 0, 1, 1], [24, 0, 2, 1], [25, 0, 2, 1], [26, 0, 2, 1], [27, 0, 1, 1],
  [28, 0, 2, 1], [29, 0, 2, 1], [30, 0, 2, 1], [32, 0, 2, 1], [33, 0, 2, 1],
  [34, 0, 2, 1], [48, 2, 0, 0], [49, 2, 1, 0], [50, 2, 1, 0], [51, 2, 0, 0],
  [52, 0, 0, 0], [64, 0, 1, 1], [65, 0, 2, 0], [80, 0, 1, 0], [81, 0, 1, 0],
  [82, 0, 0, 1], [83, 0, 1, 0],
];
const BY = new Map(OPS.map((o) => [o[0], o]));

function run(p, inp) {
  const n = p.length;
  const D = new Int32Array(256);
  const C = new Int32Array(64);
  const M = new Int32Array(256);
  const out = new Uint8Array(65536);
  let sp = 0, cp = 0, pc = 0, ip = 0, ol = 0, st = 0;
  const end = (c) => ({ o: out.slice(0, ol), c });
  for (;;) {
    if (st === 1e6) return end(10);
    if (pc < 0 || pc >= n) return end(9);
    const op = p[pc];
    const e = BY.get(op);
    if (!e) return end(5);
    const im = e[1];
    if (pc + im >= n) return end(9);
    st++;
    const nx = pc + 1 + im;
    if (sp < e[2]) return end(2);
    if (sp - e[2] + e[3] > 256) return end(3);
    pc = nx;
    switch (op) {
      case 0:
        return end(0);
      case 1:
        D[sp++] = (p[nx - 1] << 24) >> 24;
        break;
      case 2:
        D[sp++] = p[nx - 4] | (p[nx - 3] << 8) | (p[nx - 2] << 16) | (p[nx - 1] << 24);
        break;
      case 3:
        sp--;
        break;
      case 4:
        D[sp] = D[sp - 1];
        sp++;
        break;
      case 5: {
        const t = D[sp - 1];
        D[sp - 1] = D[sp - 2];
        D[sp - 2] = t;
        break;
      }
      case 6:
        D[sp] = D[sp - 2];
        sp++;
        break;
      case 7: {
        const a = D[sp - 3];
        D[sp - 3] = D[sp - 2];
        D[sp - 2] = D[sp - 1];
        D[sp - 1] = a;
        break;
      }
      case 23:
        D[sp - 1] = -D[sp - 1] | 0;
        break;
      case 27:
        D[sp - 1] = ~D[sp - 1];
        break;
      case 16: case 17: case 18: case 19: case 20: case 21: case 22:
      case 24: case 25: case 26: case 28: case 29: case 30:
      case 32: case 33: case 34: {
        const b = D[sp - 1];
        const a = D[sp - 2];
        let r;
        if (op === 16) r = (a + b) | 0;
        else if (op === 17) r = (a - b) | 0;
        else if (op === 18) r = Math.imul(a, b);
        else if (op === 19) {
          if (b === 0) return end(4);
          r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
        } else if (op === 20) {
          if (b === 0) return end(4);
          r = b === -1 ? 0 : (a % b) | 0;
        } else if (op === 21) {
          if (b === 0) return end(4);
          r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
        } else if (op === 22) {
          if (b === 0) return end(4);
          r = ((a >>> 0) % (b >>> 0)) | 0;
        } else if (op === 24) r = a & b;
        else if (op === 25) r = a | b;
        else if (op === 26) r = a ^ b;
        else if (op === 28) r = a << (b & 31);
        else if (op === 29) r = a >> (b & 31);
        else if (op === 30) r = (a >>> (b & 31)) | 0;
        else if (op === 32) r = a === b ? 1 : 0;
        else if (op === 33) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
        sp -= 2;
        D[sp++] = r;
        break;
      }
      case 48: case 49: case 50: {
        const rel = ((p[nx - 2] | (p[nx - 1] << 8)) << 16) >> 16;
        if (op === 48 || (op === 49 ? D[--sp] === 0 : D[--sp] !== 0)) pc = nx + rel;
        break;
      }
      case 51:
        if (cp === 64) return end(7);
        C[cp++] = nx;
        pc = p[nx - 2] | (p[nx - 1] << 8);
        break;
      case 52:
        if (cp === 0) return end(8);
        pc = C[--cp];
        break;
      case 64: {
        const a = D[sp - 1];
        if (a < 0 || a >= 256) return end(6);
        D[sp - 1] = M[a];
        break;
      }
      case 65: {
        const a = D[sp - 1];
        const v = D[sp - 2];
        if (a < 0 || a >= 256) return end(6);
        sp -= 2;
        M[a] = v;
        break;
      }
      case 80: {
        const s = String(D[sp - 1]);
        if (ol + s.length > 65536) return end(11);
        sp--;
        for (let i = 0; i < s.length; i++) out[ol++] = s.charCodeAt(i);
        break;
      }
      case 81:
        if (ol + 1 > 65536) return end(11);
        out[ol++] = D[--sp] & 255;
        break;
      case 82:
        D[sp++] = ip < inp.length ? inp[ip++] : -1;
        break;
      case 83:
        return end(D[--sp] & 255);
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  let r;
  try {
    r = run(
      new Uint8Array(readFileSync(join(I, id, 'program.bin'))),
      new Uint8Array(readFileSync(join(I, id, 'input.bin'))),
    );
  } catch {
    r = { o: new Uint8Array(0), c: 0 };
  }
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.o);
  writeFileSync(join(O, id, 'exit.txt'), r.c + '\n');
}
