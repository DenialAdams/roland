pipeline {
   agent any

   environment {
      CARGO_INCREMENTAL = "0"
   }

   stages {
      stage('Wasm Build') {
         steps {
            dir('rolandc_web') {
               sh 'cargo build --release --target wasm32-unknown-unknown'
               sh 'wasm-bindgen --target web ../target/wasm32-unknown-unknown/release/rolandc_web.wasm --out-dir ./pkg'
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

      stage('Build site bundle') {
         steps {
            dir('roland_site') {
               sh 'npm install'
               sh 'npx rollup editor.js -o cm6.bundle.js -p @rollup/plugin-node-resolve -p @rollup/plugin-terser --output.name cm6'
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
                  sh 'cp ../../rolandc_web/pkg/rolandc_web.js .'
                  sh 'cp ../../rolandc_web/pkg/rolandc_web_bg.wasm .'
               }
               sh 'cp ../roland_site/cm6.bundle.js .'
               sh 'cp ../roland_site/index.html .'
               sh 'cp ../roland_site/index.js .'
               sh 'cp ../roland_site/stylesheet.css .'
               sh 'cp ../target/x86_64-pc-windows-gnu/release/rolandc_cli.exe ./rolandc.exe'
               sh 'cp ../target/x86_64-unknown-linux-musl/release/rolandc_cli ./rolandc'
               sshagent (credentials: ['jenkins-ssh-nfs']) {
                  sh 'rsync -avr -e "ssh -l flandoo_brickcodes -o StrictHostKeyChecking=no" --exclude ".git" --exclude "pkg@tmp" . ssh.nyc1.nearlyfreespeech.net:/home/public/roland'
               }
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
               sh 'cp ../target/x86_64-pc-windows-gnu/release/rolandc_lsp.exe .'
               sh 'cp ../target/x86_64-unknown-linux-musl/release/rolandc_lsp .'
               withCredentials([string(credentialsId: 'vsce', variable: 'VSCE_PAT')]) {
                  sh 'vsce publish || true'
               }
            }
         }
      }

      stage('Publish NPM') {
         when {
            expression { env.BRANCH_NAME == "master" }
         }
         steps {
            dir('rolandc_web') {
               dir('pkg') {
                  sh 'npm pack'
                  sh 'npm publish || true'
               }
            }
         }
      }
   }
}
