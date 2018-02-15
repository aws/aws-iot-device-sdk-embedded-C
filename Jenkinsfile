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
    echo 'Building samples'
    dir('samples/linux/shadow_sample')
    {
      sh 'make -j8'
    }
    dir('samples/linux/shadow_sample_console_echo')
    {
      sh 'make -j8'
    }
    dir('samples/linux/subscribe_publish_cpp_sample')
    {
      sh 'make -j8'
    }
    dir('samples/linux/subscribe_publish_library_sample')
    {
      sh 'make -j8'
    }
    dir('samples/linux/subscribe_publish_sample')
    {
      sh 'make -j8'
    }
    echo 'Done.'
}
