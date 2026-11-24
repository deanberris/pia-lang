# Test data for the stream demo

## `N46E008_crop256.hgt`

A 256 × 256 crop of the SRTM 1″ tile N46E008 (46–47°N, 8–9°E, in the
Swiss Alps), around the Eiger in the Bernese Oberland, in the tile's own
format: big-endian `i16` metres, row by row from the north-west
corner. Heights range from 1121 to 4030 m, and there are no voids.

| | |
| --- | --- |
| Source | <https://elevation-tiles-prod.s3.amazonaws.com/skadi/N46/N46E008.hgt.gz> |
| Tile sha256 (`.hgt.gz`) | `79b5b5e78f7e0edb7aca4e1f74f235c18ba6bd82557b92ab1ec42d8e37600c86` |
| Tile sha256 (`.hgt`) | `dc98088f2eb13b9713edff1d8f3f8e858b2f8f29d515b2d185ad1efcca72bd40` |
| Crop window | rows 1400–1655 and columns 0–255 of the 3601 × 3601 tile, about 46.61–46.54°N, 8.00–8.07°E |
| Crop sha256 | `41b2f797dbd0a9c37dfc7f1e46b61a4b47b93190f82ff32fb58dbde2b216bf8f` |

The crop is the first 256 cells of each of rows 1400 to 1655, two bytes a
cell, with nothing changed.

### Attribution

The tile comes from the [Terrain Tiles](https://registry.opendata.aws/terrain-tiles/)
dataset on the Registry of Open Data on AWS. Its `skadi` tiles are
derived from SRTM.

SRTM data: courtesy of the U.S. Geological Survey, and NASA's Shuttle
Radar Topography Mission. SRTM is in the public domain.

The whole tile is not checked in. `examples/streams/fetch_srtm.sh`
downloads it and checks its sha256.
