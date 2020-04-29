#!/bin/sh

set -e
if [ -z $1 ]; then
  echo "You must specify the version to install."
else
  git checkout -q $1
  echo "Copying the standard library into" ~/.local/share/neut/$1/library
  mkdir -p ~/.local/share/neut/$1/library
  cp -r ./core ~/.local/share/neut/$1/library
  echo "Compiling and testing Neut $1"
  stack test
  stack install
  git checkout -q master
fi
