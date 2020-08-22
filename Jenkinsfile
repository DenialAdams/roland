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

      stage('Deploy') {
         when {
            expression { env.BRANCH_NAME == "master" }
         }
         steps {
            dir('publish') {
               dir('pkg') {
                  sh 'cp ../../rolandc_wasm/pkg/rolandc_wasm.js .'
                  sh 'cp ../../rolandc_wasm/pkg/rolandc_wasm_bg.wasm .'
               }
               sh 'cp ../rolandc_wasm/lib .'
               sh 'cp ../ast.css .'
               sh 'cp ../rolandc_wasm/index.html .'
               sh 'cp ../rolandc_wasm/index.js .'
               sh 'cp ../rolandc_wasm/stylesheet.css .'
               sshagent (credentials: ['jenkins-ssh-nfs']) {
                  sh 'rsync -avr -e "ssh -l flandoo_brickcodes -o StrictHostKeyChecking=no" --exclude ".git" --exclude "pkg@tmp" . ssh.phx.nearlyfreespeech.net:/home/public/roland'
               }
            }
         }
      }
   }
}
