pipeline {
   agent any

   stages {
      stage('Clean') {
         steps {
            sh 'cargo clean'
         }
      }

      stage('Wasm Build') {
         steps {
            dir('rolandc_wasm') {
               sh 'cargo build --release --target wasm32-unknown-unknown'
               sh 'wasm-bindgen --target web ../target/wasm32-unknown-unknown/release/rolandc_wasm.wasm --out-dir ./pkg'
            }
         }
      }

      stage('Build CLI') {
         steps {
            dir('rolandc_cli') {
               sh 'cargo build --release --target=x86_64-unknown-linux-musl'
               sh 'cargo build --release --target x86_64-pc-windows-gnu'
            }
         }
      }

      stage('Build LSP') {
         steps {
            dir('rolandc_lsp') {
               sh 'cargo build --release --target=x86_64-unknown-linux-musl'
               sh 'cargo build --release --target x86_64-pc-windows-gnu'
            }
         }
      }

      stage('Publish LSP') {
         when {
            expression { env.BRANCH_NAME == "master" }
         }
         steps {
            dir('roland-vscode') {
               sh 'npm install'
               sh 'cp ../target/x86_64-pc-windows-gnu/release/rolandc_cli.exe ./rolandc.exe'
               sh 'cp ../target/x86_64-unknown-linux-musl/release/rolandc_lsp .'
               sh 'vsce publish'
            }
         }
      }

      stage('Deploy Site') {
         when {
            expression { env.BRANCH_NAME == "master" }
         }
         steps {
            dir('publish') {
               dir('pkg') {
                  sh 'cp ../../rolandc_wasm/pkg/rolandc_wasm.js .'
                  sh 'cp ../../rolandc_wasm/pkg/rolandc_wasm_bg.wasm .'
               }
               sh 'cp -r ../rolandc_wasm/lib .'
               sh 'cp ../rolandc_wasm/index.html .'
               sh 'cp ../rolandc_wasm/index.js .'
               sh 'cp ../rolandc_wasm/stylesheet.css .'
               sh 'cp ../target/x86_64-pc-windows-gnu/release/rolandc_cli.exe ./rolandc.exe'
               sh 'cp ../target/x86_64-unknown-linux-musl/release/rolandc_cli ./rolandc'
               sshagent (credentials: ['jenkins-ssh-nfs']) {
                  sh 'rsync -avr -e "ssh -l flandoo_brickcodes -o StrictHostKeyChecking=no" --exclude ".git" --exclude "pkg@tmp" . ssh.phx.nearlyfreespeech.net:/home/public/roland'
               }
            }
         }
      }
   }
}
