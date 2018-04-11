node {
  stage 'Checkout'
    echo "Script v1.0"
    checkout scm
  
  stage 'Get dependencies'
    sh 'rm -rf external_libs/mbedTLS'
    sh 'git clone https://github.com/ARMmbed/mbedtls external_libs/mbedTLS'
    sh 'rm -rf external_libs/CppUTest'
    sh 'wget https://github.com/cpputest/cpputest/archive/v3.6.zip -O cpputest.zip'
    sh 'echo "A" | unzip cpputest.zip -d external_libs/'
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

    stage 'Run Tests'
      sh '''
      timeLimit=$(( $(date +%s) + 259200 )) #run for 3 days
      cp /home/jenkins/certs/* certs/
      rm tests/integration/include/aws_iot_config.h
      cp /home/jenkins/aws_iot_config.h tests/integration/include/
      cd ./tests/integration/
      make app
      cd ../../
      
      while [ $(date +%s) -lt "$timeLimit" ]; do 
      #make run-unit-tests 
      cd ./tests/integration/
      make tests
      cd ../../
      done 
      
      cd ./tests/integration/
      make clean
      cd ../../
      '''
}
