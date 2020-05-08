#!/usr/bin/env bash

set -eux -o pipefail

main() {
  cargo check --target $TARGET

  if [[ $TARGET = x86_64-unknown-linux-gnu ]]; then
    cargo test --target $TARGET
  fi
}

if [ -z ${TRAVIS_BRANCH-} ]; then
  TRAVIS_BRANCH=auto
fi

if [ -z ${TARGET-} ]; then
  TARGET=$(rustc -Vv | grep host | cut -d ' ' -f2)
fi

if [ $TRAVIS_BRANCH != master ]; then
  main
fi
