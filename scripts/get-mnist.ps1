$ErrorActionPreference = 'Stop'
$dir = Join-Path $PSScriptRoot '..\data\mnist'
New-Item -ItemType Directory -Force $dir | Out-Null
$base = 'https://storage.googleapis.com/cvdf-datasets/mnist'
foreach ($name in 'train-images-idx3-ubyte', 'train-labels-idx1-ubyte', 't10k-images-idx3-ubyte', 't10k-labels-idx1-ubyte') {
    $out = Join-Path $dir $name
    if (Test-Path $out) { continue }
    $gz = "$out.gz"
    Invoke-WebRequest -Uri "$base/$name.gz" -OutFile $gz
    $src = [IO.File]::OpenRead($gz)
    $dst = [IO.File]::Create($out)
    $gzip = New-Object IO.Compression.GzipStream($src, [IO.Compression.CompressionMode]::Decompress)
    $gzip.CopyTo($dst)
    $gzip.Dispose(); $dst.Dispose(); $src.Dispose()
    Remove-Item $gz
}
Write-Host "MNIST ready in $dir"
