import { start, compile_and_update_all, default as init } from './pkg/rolandc_wasm.js';

window.initApp = async function initApp() {
   await init('./pkg/rolandc_wasm_bg.wasm');
   start();
   document.getElementById('compile_button').disabled = false;
}

window.addEventListener('DOMContentLoaded', (event) => {
   initApp();
});

window.compileUpdateAll = async function compileUpdateAll() {
   let output_frame = document.getElementById("out_frame");
   output_frame.textContent = "Compiling...";
   let wasm_bytes = compile_and_update_all();
   if (wasm_bytes != null) {
      output_frame.textContent = "Executing...";
      let response = new Response(wasm_bytes.buffer);
      let exec_result = await WebAssembly.instantiateStreaming(response);
   }
};
