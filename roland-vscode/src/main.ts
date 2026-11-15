import * as lc from 'vscode-languageclient/node';
import * as vscode from 'vscode';
import * as os from "os";
import { inspect } from "util";
import { existsSync, unwatchFile, watchFile, type Stats } from 'fs';
import { Mutex } from 'async-mutex';

let client: lc.LanguageClient | undefined;
let watcher: vscode.Disposable | undefined;
const serverMutex = new Mutex();

async function stopServer(): Promise<void> {
   watcher?.dispose();
   watcher = undefined;
   const stoppingClient = client;
   client = undefined;
   await stoppingClient?.dispose();
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

function createClient(path: string): lc.LanguageClient {
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

   return new lc.LanguageClient('roland', 'Roland Language Server', serverOptions, clientOptions);
}

export async function activate(context: vscode.ExtensionContext) {
   await serverMutex.runExclusive(async () => {
      log.info("Starting language client...");
      const local_path = getLocalPath();
      let server_path = local_path;
      if (local_path != "") {
         log.info("Launching local copy of rolandc...");
      } else {
         log.info("Launching embedded rolandc...");
         server_path = context.asAbsolutePath("rolandc-lsp");
         if (process.platform == "win32") {
            server_path += ".exe";
         }
      }
      await stopServer();
      const currentClient = createClient(server_path);
      client = currentClient;
      if (local_path != "") {
         const onChange = (current: Stats) => {
            if (!current.isFile()) return;
            void serverMutex.runExclusive(async () => {
               if (client !== currentClient) return;
               log.info("Detected change to language server, restarting..");
               await currentClient.restart();
               log.info("Finished restarting language server");
            }).catch(error => log.error("Failed to restart language server", error));
         };
         watchFile(local_path, { persistent: false }, onChange);
         watcher = new vscode.Disposable(() => unwatchFile(local_path, onChange));
         context.subscriptions.push(watcher);
      }
      await currentClient.start();
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
