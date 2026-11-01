#!/bin/sh
set -e
dir="$(dirname "$0")/../data/mnist"
mkdir -p "$dir"
base="https://storage.googleapis.com/cvdf-datasets/mnist"
for name in train-images-idx3-ubyte train-labels-idx1-ubyte t10k-images-idx3-ubyte t10k-labels-idx1-ubyte; do
  [ -f "$dir/$name" ] && continue
  curl -fsSL "$base/$name.gz" | gunzip > "$dir/$name"
done
echo "MNIST ready in $dir"
