node {
  stage 'Checkout'
    checkout scm
    
  stage 'Build'
    echo 'Building shadow sample...'
    dir 'samples/linux/shadow_sample'
    sh 'make'
    echo 'Done.'
}
