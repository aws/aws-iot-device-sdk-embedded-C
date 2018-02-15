node {
  stage 'Checkout'
    checkout scm
  
  stage 'Cloning dependencies...'
    dir('external_libs/mbedTLS')
    {
      sh 'ls -all'
      sh 'rm -rf *'
      sh 'git clone https://github.com/ARMmbed/mbedtls .'
    }
    echo 'Done.'
  
  stage 'Build'
    echo 'Building shadow sample...'
    dir('samples/linux/shadow_sample')
    {
      sh 'make -j8'
    }
    echo 'Done.'
}
