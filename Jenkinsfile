node {
  stage 'Checkout'
    checkout scm
    
  stage 'Build'
    echo 'Building shadow sample...'
    cd 'samples/linux/shadow_sample'
    sh 'make'
    echo 'Done.'
}
