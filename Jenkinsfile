node {
  stage 'Checkout'
    checkout scm
    
  stage 'Build'
    echo 'Building shadow sample...'
    sh 'make'
    echo 'Done.'
}
