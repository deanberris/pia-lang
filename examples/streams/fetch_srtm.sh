#!/bin/sh
# Downloads the SRTM 1" tile N46E008 (the Swiss Alps) from the Terrain
# Tiles dataset on AWS, checks its sha256, and unpacks it into the given
# directory (the current one by default). The tile is not checked in; see
# examples/streams/testdata/README.md for its source and attribution.
#
#   examples/streams/fetch_srtm.sh [dir]
#   bazel run //examples/streams:srtm -- dir/N46E008.hgt out.png
set -eu
dir="${1:-.}"
url=https://elevation-tiles-prod.s3.amazonaws.com/skadi/N46/N46E008.hgt.gz
gz_sha=79b5b5e78f7e0edb7aca4e1f74f235c18ba6bd82557b92ab1ec42d8e37600c86
hgt_sha=dc98088f2eb13b9713edff1d8f3f8e858b2f8f29d515b2d185ad1efcca72bd40
mkdir -p "$dir"
cd "$dir"
if [ ! -f N46E008.hgt.gz ]; then
  curl -sSfL --retry 3 -o N46E008.hgt.gz.part "$url"
  mv N46E008.hgt.gz.part N46E008.hgt.gz
fi
echo "$gz_sha  N46E008.hgt.gz" | shasum -a 256 -c -
gunzip -kf N46E008.hgt.gz
echo "$hgt_sha  N46E008.hgt" | shasum -a 256 -c -
echo "$(pwd)/N46E008.hgt"
