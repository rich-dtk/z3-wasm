




import init from "./z3-solver/build/node.d.ts"

export async function loadWasm() {
  await init()
  const bytes = await Deno.readFile("z3-built.wasm");
  const wasmModule = new WebAssembly.Module(bytes);
  const imports = {}; 
  //const wasmInstance = new WebAssembly.Instance(wasmModule, imports);
  const _foo = 1
}
await loadWasm()
/*
const module = await WebAssembly.compileStreaming(
  fetch(path),
);

/* do some more stuff */
/*
const instance = await WebAssembly.instantiate(module);
instance.exports.increment as (input: number) => number;
const _foo2 = 1
*/
/*
const fetchWrapper =  fetch()
const { instance, module } = await WebAssembly.instantiateStreaming(fetchWrapper)
const _foo = 1

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
