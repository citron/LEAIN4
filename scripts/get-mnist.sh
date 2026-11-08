#!/bin/sh
# Download MNIST (idx binaries) into data/mnist, then verify SHA-256 against the
# pinned manifest scripts/mnist-sha256.txt (hashes of the uncompressed idx files,
# computed from this same cvdf-datasets source). Downloading from an unverified
# mirror without updating the manifest is a deliberate act, not an accident.
set -e
root="$(cd "$(dirname "$0")/.." && pwd)"
dir="$root/data/mnist"
mkdir -p "$dir"
base="https://storage.googleapis.com/cvdf-datasets/mnist"
for name in train-images-idx3-ubyte train-labels-idx1-ubyte t10k-images-idx3-ubyte t10k-labels-idx1-ubyte; do
  [ -f "$dir/$name" ] && continue
  curl -fsSL "$base/$name.gz" | gunzip > "$dir/$name"
done
if [ -f "$root/scripts/mnist-sha256.txt" ]; then
  (cd "$dir" && sha256sum -c "$root/scripts/mnist-sha256.txt")
else
  echo "warning: scripts/mnist-sha256.txt missing; integrity check skipped" >&2
fi
echo "MNIST ready in $dir"
