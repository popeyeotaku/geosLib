### geosLib

MODIFIED TO SUPPORT PYTHON 3 (in progress)

geosLib is a Python library to convert [GEOS](https://www.c64-wiki.de/index.php/GEOS) geoPaint, geoWrite, Photo Album and Photo Scrap files to modern formats.

Image files can be converted to PNG.

Text formats can be converted to RTFD, HTML and TXT.

GEOS font files are rendered as PNG for each size.


### Inspiration, Code Template and "broken CVT logic"

[geowrite2rtf](https://github.com/mist64/geowrite2rtf) by [Michael Steil](http://www.pagetable.com/).  If you haven't seen his  [c64talk](https://www.youtube.com/watch?v=ZsRRCnque2E), go watch it.


### Requirements

+ [pillow](https://github.com/python-pillow/Pillow)

### Usage:


```shell
# for geoPaint, Photo Album, Photo Scrap, geoWrite, Text Album and Text Scrap in CBM Convert files format (CVT):

python convertCVTFiles.py *.cvt


# for geos font files in any format (d64, d81, zipped, gzipped, cvt):
# the PNG files are written to a directory "./geosFonts"

python geosCollectAllFonts.py  files or folders


# to collect everything in directories "./geosExports" and "./geosFonts"

python geosConvertAll.py files or folders

```

### To do:

+ Text Album files

+ Some differences between "Write Image V2.0" and "Write Image V2.1"

+ geoPublish format? If someone has a pointer please write up an issue.


### Summary

+ Send CBM-CVT files to CBMConvertFile and  cbm disk image files (.d64, .d81) to DiskImage. Look at geosFiletypeScanner's usage of geosLib.getCompressedFile() on how to handle gzip and zip files.

+ IOW: get your geos file into a VLIRFile structure. The name is misleading since SEQ files go there too. That's what any of the conversion functions in geosLib expect.

### Update

+ Welcome the new addition 'macpaintLib.py'. For the start it will be kept in it's own file but will be integrated after maturing. It uses a lot of common code and is very beta.
+ Currently it converts all but one from all the macpaint files I could find on the net with a speed of ca. 15docs/sec.
  + sources so far:
    + [http://cd.textfiles.com/carousel344/PIC](http://cd.textfiles.com/carousel344/PIC)
    + [http://cd.textfiles.com/vgaspectrum/mac/mac1](http://cd.textfiles.com/vgaspectrum/mac/mac1)
    + [http://cd.textfiles.com/vgaspectrum/mac/mac2](http://cd.textfiles.com/vgaspectrum/mac/mac2)
  + If you find more macpaint files, please create an issue

+ Usage

```

python macpaintLib.py /Path/To/Folder/with/MacPaint/Files/

```

this will create a folder macpaintExports at the same location from where the script is started.