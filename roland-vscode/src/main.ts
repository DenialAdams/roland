import * as lc from 'vscode-languageclient/node';
import * as vscode from 'vscode';
import * as os from "os";
import { inspect } from "util";
import { existsSync, watchFile } from 'fs';
import { Mutex } from 'async-mutex';

let client: lc.LanguageClient | undefined;
const serverMutex = new Mutex();

async function stopServer(): Promise<void> {
   if (client) {
      await client.stop();
      client = undefined;
   }
}

function getLocalPath(): string {
   let path = os.homedir() + "/roland/target/release/rolandc-lsp";
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
   await serverMutex.runExclusive(async () => {
      log.info("Starting language client...");
      const local_path = getLocalPath();
      let server_path = local_path;
      if (local_path != "") {
         log.info("Launching local copy of rolandc...");
         watchFile(local_path, { persistent: false }, current => {
            if (!current.isFile()) return;
            void serverMutex.runExclusive(async () => {
               log.info("Detected change to language server, restarting..");
               await stopServer();
               await startServer(local_path);
               log.info("Finished restarting language server");
            }).catch(error => log.error("Failed to restart language server", error));
         });
      } else {
         log.info("Launching embedded rolandc...");
         server_path = context.asAbsolutePath("rolandc-lsp");
         if (process.platform == "win32") {
            server_path += ".exe";
         }
      }
      await stopServer();
      await startServer(server_path);
      log.info("Finished starting language client");
   });
}

export async function deactivate(): Promise<void> {
   return serverMutex.runExclusive(stopServer);
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
