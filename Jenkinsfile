node {
  stage 'Checkout'
    checkout scm
  
  stage 'Get dependencies'
    sh 'rm -rf external_libs/mbedTLS'
    sh 'git clone https://github.com/ARMmbed/mbedtls external_libs/mbedTLS'
    sh 'rm -rf external_libs/CppUTest'
    sh 'wget https://github.com/cpputest/cpputest/archive/v3.6.zip -O cpputest.zip'
    sh 'unzip cpputest.zip -d external_libs/'
    sh 'mv external_libs/cpputest-3.6/ external_libs/CppUTest'
    
  stage 'Build samples'
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
    dir('samples/linux/jobs_sample')
    {
      sh 'make -j8'
    }
    echo 'Done.'
  
    stage 'Run unit tests'
      sh 'make run-unit-tests'

    stage 'Run integration tests'
      sh 'cp /home/jenkins/certs/* certs/'
      sh 'rm tests/integration/include/aws_iot_config.h'
      sh 'cp /home/jenkins/aws_iot_config.h tests/integration/include/'
      dir('tests/integration')
      {
        sh 'make'
      }
}
