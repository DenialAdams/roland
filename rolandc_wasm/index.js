import { start, compile_and_update_all, default as init } from './pkg/rolandc_wasm.js';

let instance = null;

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
      let headers = new Headers({
         'Content-Type': 'application/wasm'
      });
      let response = new Response(wasm_bytes, { "headers": headers });
      let wasi_polyfill = { fd_write: fd_write_polyfill };
      let result = await WebAssembly.instantiateStreaming(response, { wasi_unstable: wasi_polyfill });
      instance = result.instance;
      output_frame.textContent = '';
      instance.exports._start();
   }
};

function fd_write_polyfill(fd, iovs, iovsLen, nwritten) {

   var view = new DataView(instance.exports.memory.buffer);

   let sum = 0;

   var buffers = Array.from({ length: iovsLen }, function (_, i) {
      var ptr = iovs + i * 8;
      var buf = view.getUint32(ptr, !0);
      var bufLen = view.getUint32(ptr + 4, !0);

      sum += bufLen;

      return new Uint8Array(instance.exports.memory.buffer, buf, bufLen);
   });

   let bufferBytes = new Uint8Array(sum);
   let i = 0;
   buffers.forEach(buffer => {
      for (let j = 0; j < buffer.length; j++) {
         bufferBytes[i++] = buffer[j++];
      }
   });

   document.getElementById("out_frame").textContent += new TextDecoder("utf-8").decode(bufferBytes);

   view.setUint32(nwritten, 0, !0);

   return 0;
}
