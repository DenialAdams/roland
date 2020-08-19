import { start, compile_and_update_all, default as init } from './pkg/rolandc_wasm.js';

window.initApp = async function initApp() {
   await init('./pkg/cedict_bg.wasm');
   start();
   document.getElementById('compile_button').disabled = false;
}

window.addEventListener('DOMContentLoaded', (event) => {
   initApp();
});

window.compileUpdateAll = function compileUpdateAll() {
   compile_and_update_all();
};
