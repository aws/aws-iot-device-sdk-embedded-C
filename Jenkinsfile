node {
  stage 'Checkout'
    checkout scm
  
  stage 'Get dependencies'
    sh 'rm -rf external_libs/mbedTLS'
    sh 'git clone https://github.com/ARMmbed/mbedtls external_libs/mbedTLS'
    sh 'rm -rf external_libs/CppUTest'
    sh 'wget https://github.com/cpputest/cpputest/archive/v3.6.zip -O cpputest.zip'
    sh 'unzip cpputest.zip -d external_libs/CppUTest'
    echo 'Done.'
  
  stage 'Build samples'
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
  
    stage 'Run unit tests'
      sh 'make run-unit-tests -j8'
}
