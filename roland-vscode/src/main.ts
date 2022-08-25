import * as lc from 'vscode-languageclient/node';
import * as vscode from 'vscode';
import * as os from "os";
import { inspect } from "util";
import { existsSync, watch } from 'fs';

let client: lc.LanguageClient;

function getLocalPath(): string {
   let path = os.homedir() + "/roland/target/release/rolandc_lsp";
   if (process.platform == "win32") {
      path += ".exe";
   }
   if (existsSync(path)) {
      return path;
   }
   return "";
}

async function startServer(path: string) {
   const run: lc.Executable = {
      command: path,
      transport: lc.TransportKind.stdio,
   };
   const serverOptions: lc.ServerOptions = {
      run,
      debug: run,
   };
   const clientOptions: lc.LanguageClientOptions = {
      documentSelector: [{ scheme: 'file', language: 'roland' }],
   }

   client = new lc.LanguageClient('roland', 'Roland Language Server', serverOptions, clientOptions);

   await client.start();
}

export async function activate(context: vscode.ExtensionContext) {
   log.info("Starting language client...");

   let local_path = getLocalPath();
   if (local_path != "") {
      log.info("Launching local copy of rolandc...");
      watch(local_path, {persistent: false}, async function(event, _filename) {
         if (event == "change") {
            log.info("Detected change to language server, restarting..");
            await deactivate();
            await startServer(local_path)
            log.info("Finished restarting language server");
         }
      });
      await deactivate(); // just in case the watcher triggered before we got here? seems reasonable
      await startServer(local_path);
   } else {
      log.info("Launching embedded rolandc...");
      let extension_path = context.asAbsolutePath("rolandc_lsp");
      if (process.platform == "win32") {
         extension_path += ".exe";
      }
      await startServer(extension_path);
   }

   log.info("Finished starting language client");
}

export async function deactivate(): Promise<void> {
   if (!client) {
      return;
   }
   return client.stop();
}

const log = new class {
   private readonly output = vscode.window.createOutputChannel("Roland Client");

   // Hint: the type [T, ...T[]] means a non-empty array
   debug(...msg: [unknown, ...unknown[]]): void {
      log.write("DEBUG", ...msg);
   }

   info(...msg: [unknown, ...unknown[]]): void {
      log.write("INFO", ...msg);
   }

   warn(...msg: [unknown, ...unknown[]]): void {
      debugger;
      log.write("WARN", ...msg);
   }

   error(...msg: [unknown, ...unknown[]]): void {
      debugger;
      log.write("ERROR", ...msg);
      log.output.show(true);
   }

   private write(label: string, ...messageParts: unknown[]): void {
      const message = messageParts.map(log.stringify).join(" ");
      const dateTime = new Date().toLocaleString();
      log.output.appendLine(`${label} [${dateTime}]: ${message}`);
   }

   private stringify(val: unknown): string {
      if (typeof val === "string") return val;
      return inspect(val, {
            colors: false,
            depth: 6, // heuristic
      });
   }
};
