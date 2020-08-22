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
      output_frame.textContent = "Executing...";
      let headers = new Headers({
         'Content-Type': 'application/wasm'
      });
      let response = new Response(wasm_bytes, { "headers": headers });
      let wasi_polyfill = { fd_write: fd_write_polyfill };
      let result = await WebAssembly.instantiateStreaming(response, { wasi_unstable: wasi_polyfill });
      instance = result.instance;
      instance.exports._start();
   }
};

function fd_write_polyfill(fd, iovs, iovsLen, nwritten) {

   var view = new DataView(instance.exports.memory.buffer);

   var written = 0;
   var bufferBytes = [];

   function getiovs(iovs, iovsLen) {
       // iovs* -> [iov, iov, ...]
       // __wasi_ciovec_t {
       //   void* buf,
       //   size_t buf_len,
       // }
       var buffers = Array.from({ length: iovsLen }, function (_, i) {
              var ptr = iovs + i * 8;
              var buf = view.getUint32(ptr, !0);
              var bufLen = view.getUint32(ptr + 4, !0);

              return new Uint8Array(instance.exports.memory.buffer, buf, bufLen);
           });

       return buffers;
   }

   var buffers = getiovs(iovs, iovsLen);
   function writev(iov) {

       for (var b = 0; b < iov.byteLength; b++) {

          bufferBytes.push(iov[b]);
       }

       written += b;
   }

   buffers.forEach(writev);

   if (fd === WASI_STDOUT_FILENO) console.log(String.fromCharCode.apply(null, bufferBytes));

   view.setUint32(nwritten, written, !0);

   return WASI_ESUCCESS;
}
