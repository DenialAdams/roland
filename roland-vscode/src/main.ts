import * as lc from 'vscode-languageclient/node';
import * as vscode from 'vscode';
import * as os from "os";
import { inspect } from "util";
import { existsSync } from 'fs';

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

export async function activate(context: vscode.ExtensionContext) {
   let extension_path = context.asAbsolutePath("rolandc_lsp");
   if (process.platform == "win32") {
      extension_path += ".exe";
   }
   let local_path = getLocalPath();
   let final_path = extension_path;
   if (local_path != "") {
      final_path = local_path;
   }
   const run: lc.Executable = {
      command: final_path,
      transport: lc.TransportKind.stdio,
   };
   const serverOptions: lc.ServerOptions = {
      run,
      debug: run,
   };

   const clientOptions: lc.LanguageClientOptions = {
      documentSelector: [{ scheme: 'file', language: 'roland' }],
   }

   log.info("Starting language client...");
   client = new lc.LanguageClient('roland', 'Roland Language Server', serverOptions, clientOptions);
   client.start();
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
