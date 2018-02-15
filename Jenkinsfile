node {
  stage 'Checkout'
    checkout scm
  
  stage 'Build'
    echo 'Building shadow sample...'
    dir('external_libs/mbedTLS')
    {
      sh 'rm README.txt'
      sh 'git clone https://github.com/ARMmbed/mbedtls'
    }
    dir('samples/linux/shadow_sample')
    {
      sh 'make -j8'
    }
    echo 'Done.'
}
