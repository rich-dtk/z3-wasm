
const { instance, module } = await WebAssembly.instantiateStreaming(
    fetch("https://raw.githubusercontent.com/dtk/dtk-cli/test-z32/z3-built.wasm"),
  );
const _foo = 1
  /*
const wasmModule = new WebAssembly.Module(wasmCode);
const wasmInstance = new WebAssembly.Instance(wasmModule);
const main = wasmInstance.exports.main as CallableFunction;
console.log(main().toString());
*/
export { };
/*
import { init } from "npm:z3-solver";
const { Context } = await init();
const { Solver, Int, And } = new Context("main");

const x = Int.const("x");

const solver = new Solver();
solver.add(And(x.ge(0), x.le(9)));
console.log(await solver.check()); // line that fail
*/
