import { createEditorState, createEditorView } from './cm6.bundle.js';
//import { start, compile_and_update_all, default as init } from './pkg/rolandc_wasm.js';

const FIB =
`proc main() {
   let x = fib(9);
   println(int_to_string(x));
}

proc fib(n: u64) -> u64 {
   if n == 0 {
      return 0;
   } else if n == 1 {
      return 1;
   }
   return fib(n - 1) + fib(n - 2);
}
`;

const HELLO_WORLD =
`proc main() {
   println("Hello, world!");
}
`;

let instance = null;
let code_editor = null;
let disasm_viewer = null;

window.setHelloWorld = function setHelloWorld() {
   code_editor.getDoc().setValue(HELLO_WORLD);
};

window.setFib = function setFib() {
   code_editor.getDoc().setValue(FIB);
};

window.initApp = async function initApp() {
   await init('./pkg/rolandc_web_bg.wasm');
   start();
   document.getElementById('compile_button').disabled = false;
};

window.addEventListener('DOMContentLoaded', (event) => {
   code_editor = createEditorView(createEditorState(HELLO_WORLD, false)),
   document.getElementById('buttons').insertAdjacentElement('beforebegin', code_editor.dom);
   disasm_viewer = createEditorView(createEditorState("", true)),
   document.getElementById('disassembly_div').insertAdjacentElement('beforeend', disasm_viewer.dom);
   initApp();
});

window.compileUpdateAll = async function compileUpdateAll() {
   let output_frame = document.getElementById("out_frame");
   output_frame.textContent = "Compiling...";
   disasm_viewer.getDoc().setValue('');
   let compilation_output = compile_and_update_all(code_editor.getDoc().getValue());
   if (compilation_output != null) {
      disasm_viewer.getDoc().setValue(compilation_output.disasm);
      let headers = new Headers({
         'Content-Type': 'application/wasm'
      });
      let response = new Response(compilation_output.bytes, { "headers": headers });
      let wasi_polyfill = { fd_write: fd_write_polyfill };
      let result;
      try {
         result = await WebAssembly.instantiateStreaming(response, { wasi_unstable: wasi_polyfill });
      } catch (err) {
         if (err instanceof WebAssembly.LinkError) {
            output_frame.textContent = err.message;
            output_frame.textContent += "\n---\n";
            output_frame.textContent += "Note: External procedures in the Roland playground can't successfully link."
            return;
         } else if (err instanceof WebAssembly.CompileError) {
            output_frame.textContent = err.message;
            output_frame.textContent += "\n---\n";
            output_frame.textContent += "Note: This is a bug in the roland compiler! Please file a github issue with the code that caused this."
            return;
         }
         throw err;
      };
      instance = result.instance;
      output_frame.textContent = '';
      try {
         instance.exports._start();
      } catch(e) {
         output_frame.textContent += "!!! Runtime panic:\n";
         output_frame.textContent += e.toString();
      }
   }
};

window.toggleDisassembly = async function toggleDisassembly() {
   if (document.getElementById('disassembly_div').hasAttribute('hidden')) {
      document.getElementById('out_frame').setAttribute('hidden', '');
      document.getElementById('disassembly_div').removeAttribute('hidden');
   } else {
      document.getElementById('disassembly_div').setAttribute('hidden', '');
      document.getElementById('out_frame').removeAttribute('hidden');
   }
   disasm_viewer.refresh();
}

function fd_write_polyfill(fd, iovs, iovsLen, nwritten) {

   let view = new DataView(instance.exports.memory.buffer);

   let sum = 0;

   let buffers = Array.from({ length: iovsLen }, function (_, i) {
      let ptr = iovs + i * 8;
      let buf = view.getUint32(ptr, true);
      let bufLen = view.getUint32(ptr + 4, true);

      sum += bufLen;

      return new Uint8Array(instance.exports.memory.buffer, buf, bufLen);
   });

   let bufferBytes = new Uint8Array(sum);
   let i = 0;
   buffers.forEach(buffer => {
      for (let j = 0; j < buffer.length; j++) {
         bufferBytes[i++] = buffer[j];
      }
   });

   document.getElementById("out_frame").textContent += new TextDecoder("utf-8").decode(bufferBytes);

   view.setUint32(nwritten, sum, true);

   return 0;
}
