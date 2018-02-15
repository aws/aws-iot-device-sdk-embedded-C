node {
  stage 'Checkout'
    checkout scm
  
  stage 'Cloning dependencies...'
    dir('external_libs/mbedTLS')
    {
      sh 'rm README.txt'
      sh 'ls'
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
