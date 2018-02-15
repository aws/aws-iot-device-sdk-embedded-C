node {
  stage 'Checkout'
    checkout scm
    
  stage 'Build'
    echo 'Building shadow sample...'
    sh 'cd samples/linux/shadow_sample'
    sh 'make'
    echo 'Done.'
}
