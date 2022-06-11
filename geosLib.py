#!/usr/bin/env python
# -*- coding: utf-8 -*-

from __future__ import annotations
from dataclasses import dataclass, field
from fileinput import filename

import time
import pdb
import sys
import os

import datetime
import struct
import typing

import zipfile
import gzip

import PIL
import PIL.Image
import PIL.ImageDraw
from PIL.Image import Image as ImgType

import pprint
pp = pprint.pprint

kwdbg = 0
kwlog = 1


#
# constants
#

# unused and incomplete (yet)
# intention is to use it with rtf & html conversion
#
# for IDs look here https://www.lyonlabs.org/commodore/onrequest/geos/geoFont.pdf
#
# mappings by github user gitjeff2
fontmapping = {
    # geosfontid -> (geos font name, real world font name ;-)
    0: ('BSW', 'Geneva'),
    1: ('University', ''),
    2: ('California', 'Helvetica'),
    3: ('Roma', 'Times'),
    4: ('Dwinelle', 'Old English'),
    5: ('Cory', 'Data 70'),
    6: ('Tolman', 'Comic Sans'),
    7: ('Bubble', ''),
    8: ('Fontknox', ''),
    9: ('Harmon', 'Courier'),
    10: ('Mykonos', ''),
    11: ('Boalt', ''),
    12: ('Stadium', ''),
    14: ('Evans', ''),
    13: ('Tilden', ''),
    15: ('Durant', ''),
    16: ('Telegraph', ''),
    17: ('Superb', 'Broadway'),
    18: ('Bowditch', 'Palatino'),
    19: ('Ormond', 'Microgramma Extended'),
    20: ('Elmwood', ''),
    21: ('Hearst', ''),
    # 21: ('Brennens (BUG)', ''),
    23: ('Channing', ''),
    24: ('Putnam', ''),
    25: ('LeConte', 'Chicago'),
    52: ('Callaghan', 'Stencil'),
    866: ('Lewis', 'Playbill'),
    0x1e: ('Barrows', 'Courier'),
    0xdf: ('Birge', 'Mistral'),
    0xd6: ('Lewis', 'Playbill'),
    0x86: ('Oxford', 'Monotype Tektura'),
}

# Probably could double check the accuracy of this pallete
c64colors = {
    0: (0, 0, 0),
    1: (255, 255, 255),
    2: (0x88, 0, 0),
    3: (0xaa, 0xff, 0xee),
    4: (0xcc, 0x44, 0xcc),
    5: (0x00, 0xcc, 0x55),
    6: (0x00, 0x00, 0xaa),
    7: (0xee, 0xee, 0x77),
    8: (0xdd, 0x88, 0x55),
    9: (0x66, 0x44, 0x00),
    10: (0xff, 0x77, 0x77),
    11: (0x33, 0x33, 0x33),
    12: (0x77, 0x77, 0x77),
    13: (0xaa, 0xff, 0x66),
    14: (0x00, 0x88, 0xff),
    15: (0xbb, 0xbb, 0xbb)}

geosFileTypes = {
    0: 'Non-GEOS file',
    1: 'BASIC Program',
    2: 'Assembly program',
    3: 'Data file',
    4: 'System file',
    5: 'Desk Accessory',
    6: 'Application',
    7: 'Application Data',
    8: 'Font file',
    9: 'Printer driver',
    10: 'Input driver',
    11: 'Disk Device',
    12: 'System Boot file',
    13: 'Temporary',
    14: 'Auto Executing',
    15: 'Input 128'}

filetypesWithAuthor = (
    1, 2, 4, 5, 6, 9, 10, 14, 15)

programTypes = (
    1, 2, 4, 5, 6, 9, 10, 11, 12, 14, 15)

dosFileTypes = {
    0: 'DEL',
    1: 'SEQ',
    2: 'PRG',
    3: 'USR',
    4: 'REL',
    5: 'CBM'}

fourtyEightyFlags = {
    0:    "GEOS 64/128 40 columns",
    64:   "GEOS 64/128 40/80 columns",
    128:  "GEOS 64 40 columns",
    192:  "GEOS 128 80 columns"}

# a lot of names are surrounded by this
stripchars = b'\x00\xa0'


#
# disk image constants
#


# drive geometries
sectorTables = {
    '.d64': (
            (0,  0,  0),
            (1, 17, 21),
            (18, 24, 19),
            (25, 30, 18),
            (31, 35, 17)),

    '.d71': (
            (0,  0,  0),
        # side 1
            (1, 17, 21),
            (18, 24, 19),
            (25, 30, 18),
            (31, 35, 17),
        # side 2
            (36, 52, 21),
            (53, 59, 19),
            (60, 65, 18),
            (66, 70, 17)),

    '.d81': (
            (0,  0,  0),
        # side 1
            (1, 40, 40),
        # side 2
            (41, 80, 40))
}  # type:dict[str, tuple[tuple[int, int, int], ...]]

minMaxTrack = {
    '.d81': (1, 80),
    '.d71': (1, 70),
    '.d64': (1, 35)}  # type:dict[str, tuple[int, int]]

extToImagesize = {
    # ext, filesize, sector count
    '.d64': ((174848,  683),),
    '.d81': ((819200, 3200),),
    '.d71': ((349696, 1366),
             (349696+1366, 1366))}  # type:dict[str, tuple[tuple[int, int], ...]]

imagesizeToExt = {
    # filesize, ext, sector count
    174848: ('.d64',  683),
    175531: ('.d64',  683),
    819200: ('.d81', 3200),
    349696: ('.d71', 1366),
    351062: ('.d71', 1366)}  # type:dict[int, tuple[str, int]]

dirSectorsForDrives = {
    '.d64': (18, 0),
    '.d71': (18, 0),
    '.d81': (40, 0)}  # type:dict[str, tuple[int, int]]

# TO DO: .D71
dirSectorStructures = {
    # the first entry is the struct unpack string
    # the second entry are names to be attached in a dict

    # CONVERT TO UNSIGNED?
    '.d64': ("<b b  c      c    140s 16s 2x 2s x   2s 4x b     b     11s       5s 67x",
             "tr sc format dosv1 bam dnam   diskid dosv2 dsktr dsksc geoformat geoversion"),
    '.d81': ("<b b  cx  16s 2x 2s x 2s 2x 3x 96s 16x 16s 2x 9x b b 11s 5s 3x 64x",
             "tr sc fmt dnam   dskid dosv power64 geoname dsktr dsksc geoformat geoversion")
}  # type:dict[str, tuple[str, str]]

#
# some image globals
#


# it seems the "official" geoColorChoice is:
#       fg: color0
#       bg: color15

bgcol = c64colors[15]
if kwdbg:
    bgcol = c64colors[14]

#
# create color and bw "empty" image bands for the empty records in a geoPaint file
#

# color
databytes = bytes([bgcol[0], bgcol[1], bgcol[2]] * (640*16))
coldummy = PIL.Image.frombytes('RGB', (640, 16), databytes, decoder_name='raw')

# bw
databytes = bytes([0xff]*1280)
bwdummy = PIL.Image.frombytes('1', (640, 16), databytes, decoder_name='raw')


# currently accepted GEOS file types for conversion; fonts have their own file type
acceptedTypes = (
    'Paint Image V1.0',
    'Paint Image V1.1',
    'Paint Image v1.1',

    'photo album V1.0',
    'photo album V2.1',

    'Photo Scrap V1.0',
    'Photo Scrap V1.1',

    'Write Image V1.0',
    'Write Image V1.1',
    'Write Image V2.0',
    'Write Image V2.1',

    'text album  V1.0',
    'text album  V2.1',

    'Text  Scrap V1.0',
    'Text  Scrap V1.1',
    'Text  Scrap V2.0')

# all the GEOS text file types
textTypes = (
    'Write Image V1.0',
    'Write Image V1.1',
    'Write Image V2.0',
    'Write Image V2.1',

    'text album  V1.0',
    'text album  V2.1',

    'Text  Scrap V1.0',
    'Text  Scrap V1.1',
    'Text  Scrap V2.0')

imageTypes = (
    'Paint Image V1.0',
    'Paint Image V1.1',
    'Paint Image v1.1',

    'photo album V1.0',
    'photo album V2.1',

    'Photo Scrap V1.0',
    'Photo Scrap V1.1')

geoWriteVersions = {
    'Write Image V1.0': 10,
    'Write Image V1.1': 11,
    'Write Image V2.0': 20,
    'Write Image V2.1': 21}

albumWithNameTypes = (
    'photo album V2.1',
    'text album  V2.1')

#
# tools
#


def datestring(dt: typing.Optional[datetime.datetime] = None, dateonly=False, nospaces=False):
    """Convert a datetime object into a string representation."""
    if not dt:
        now = str(datetime.datetime.now())
    else:
        now = str(dt)
    if not dateonly:
        now = now[:19]
    else:
        now = now[:10]
    if nospaces:
        now = now.replace(" ", "_")
    return now


def makeunicode(s: typing.Union[str, bytes], enc="utf-8", errors='ignore') -> str:
    """This was originally written for the Python2 version -- now it's just a
    wrapper aound bytes.encode
    """
    if isinstance(s, bytes):
        s = s.encode(encoding=enc, errors=errors)
    return s
    # try:
    #     if type(s) != unicode:
    #         s = unicode(s, enc)
    # except:
    #     pass
    # s = unicodedata.normalize(normalizer, s)
    # return s


def iterateFolders(infolder: str, validExtensions=('.d64', '.d71', '.d81',
                                                   '.zip', '.gz',  '.cvt',
                                                   '.prg', '.seq')) -> typing.Iterator[tuple[str, str]]:
    """Iterator that walks a folder and returns all files."""

    # for folder in dirs:
    lastfolder = ""
    for root, _, files in os.walk(infolder):
        root = makeunicode(root)
        # result = {}
        # pathlist = []

        for thefile in files:
            thefile = makeunicode(thefile)
            _, ext = os.path.splitext(thefile)

            typ = ext.lower()

            if thefile.startswith('.'):
                continue

            filepath = os.path.join(root, thefile)
            # dummy, folder = os.path.split(root)
            if kwdbg or 1:
                if root != lastfolder:
                    lastfolder = root
                    print()
                    print("FOLDER:", repr(root))
            filepath = makeunicode(filepath)

            if typ not in validExtensions:
                # check for cvt file by scanning
                with open(filepath, 'rb') as f:
                    data = f.read(4096)
                fmt = data[0x1e:0x3a]

                formatOK = False
                if fmt.startswith(b"PRG formatted GEOS file"):
                    formatOK = True
                elif fmt.startswith(b"SEQ formatted GEOS file"):
                    # broken = True
                    pass

                if not formatOK:
                    continue
                typ = '.cvt'

            if kwlog or 1:
                print("FILE:", repr(filepath))
            yield typ, filepath


def getCompressedFile(path: str, acceptedOnly: bool = False) -> dict[str, list[VLIRFile]]:
    """Open a gzip or zip compressed file. Return the GEOS and c64 files in
    contained disk image(s)

    """
    result = {}  # type:dict[str, list[VLIRFile]]

    # limit size of files to 10MB
    # use a size limit?
    # if 0:  # s.st_size > 10*2**20:
    #     s = os.stat(path)
    #     return result

    _, filename = os.path.split(path)  # pylint:disable=redefined-outer-name
    basename, ext = os.path.splitext(filename)

    if ext.lower() in ('.gz', '.gzip'):
        with gzip.open(path, 'rb') as f:
            file_content = f.read()
        foldername = basename + '_gz'
        result[foldername] = []
        # only return those streams that have a chance of being an image
        if len(file_content) in imagesizeToExt:
            di = DiskImage(stream=file_content, tag=path)
            if acceptedOnly:
                for u in di.files:
                    if u.header.className in acceptedTypes:
                        result[foldername].append(u)
            else:
                result[foldername].extend(di.files)
            return result
    elif ext.lower() == '.zip':
        foldername = basename + '_zip'
        try:
            handle = zipfile.ZipFile(path, 'r')
            files = handle.infolist()
        except Exception as err:  # pylint:disable=broad-except
            print("ZIP ERROR", err)
            return result

        for zf in files:
            print("ZIPFILE:", repr(zf.filename))
            try:
                with handle.open(zf) as h:
                    data = h.read()
            except Exception:  # pylint:disable=broad-except
                continue
            if len(data) in imagesizeToExt:
                zfoldername = '/'.join((foldername, zf.filename))
                result[zfoldername] = []
                # pdb.set_trace()
                di = DiskImage(stream=data, tag=path)
                if acceptedOnly:
                    for u in di.files:
                        if u.header.className in acceptedTypes:
                            result[zfoldername].append(u)
                else:
                    result[zfoldername].extend(di.files)
        return result
    return result


class ImageBuffer(list[int]):
    """For debugging purposes mostly. Has a built in memory dump in
    monitor format."""

    # def __init__(self):
    #     super(ImageBuffer, self).__init__()

    def dump(self):
        hexdump(self)


def hexdump(s: bytes, col: int = 32):
    """Using this for debugging was so memory lane..."""

    cols = {
        8: (7, 0xfffffff8),
        16: (15, 0xfffffff0),
        32: (31, 0xffffffe0),
        64: (63, 0xffffffc0)}

    if col not in cols:
        col = 16
    minorMask, majorMask = cols.get(col)
    d = False
    # mask = col-1
    if type(s) in (list, tuple):  # ImageBuffer):
        d = True
    for i, c in enumerate(s):
        if d:
            t = hex(c)[2:]
        else:
            t = hex(c)[2:]
        t = t.rjust(2, '0')

        # spit out address
        if i % col == 0:
            a = hex(i)[2:]
            a = a.rjust(4, '0')
            sys.stdout.write(a+':  ')
        sys.stdout.write(t+' ')

        # spit out ascii line
        if i & minorMask == minorMask:
            offs = i & majorMask

            for j in range(col):
                c2 = s[offs+j]
                d2 = c2
                if 32 <= d2 < 127:
                    sys.stdout.write(c2)
                else:
                    sys.stdout.write('.')
            sys.stdout.write('\n')


def getAlbumNamesChain(vlir: VLIRFile) -> tuple[int, list[str]]:
    """extract clip names for (Photo|Text) Album V2.x"""
    clipnames = [""] * 127
    clipnameschain = 256
    if vlir.header.className in ("photo album V2.1", "text album  V2.1"):
        # scan for last chain
        if (0, 0) in vlir.chains:
            clipnameschain = vlir.chains.index((0, 0)) - 1
            if clipnameschain < 2:
                return 256, clipnames
            clipnamesstream = vlir.chains[clipnameschain]
            if len(clipnamesstream) < 17:
                return 256, clipnames
            noofentries = clipnamesstream[0]
            if len(clipnamesstream) != (noofentries + 1) * 17 + 1:
                if kwlog:
                    print("len(clipnamesstream)", len(clipnamesstream))
                    print("(noofentries + 1) * 17 + 1",
                          (noofentries + 1) * 17 + 1)
                    # if kwdbg:
                    #    pdb.set_trace()
                    #    print
                return 256, clipnames
            for i in range(noofentries):
                base = 1 + i*17
                namebytes = clipnamesstream[base:base+16]
                namebytes = namebytes.replace(b'\x00', b"")
                namebytes = namebytes.replace(b'/', b"-")
                namebytes = namebytes.replace(b':', b"_")
                try:
                    clipnames[i] = makeunicode(namebytes)
                except IndexError as err:
                    print()
                    print(err)
                    # pdb.set_trace()
                    print()
    return clipnameschain, clipnames

#
# file tools
#

#
# geos image conversion
#


def expandImageStream(s: bytes) -> ImageBuffer:
    """Expand a 640x16 compressed image stream as encountered in geoPaint files."""

    n = len(s)
    j = -1
    image = ImageBuffer()

    log = []
    while j < n-1:
        j += 1
        code = s[j]
        items = []  # type:list[int]
        roomleft = (n-1) - j
        # if 0:  # code == 0:
        #     break
        if code in (64, 128):
            if kwdbg:
                print("blank code 64,128 encountered.")
                # pdb.set_trace()
            continue

        if code < 64:
            if roomleft < 1:
                j += 1
                continue
            data = s[j+1:j+code+1]
            for i in data:
                items.append(i)
            j += len(data)
            image.extend(items)
            continue

        elif 64 <= code < 128:
            if roomleft < 8:
                j += 8
                continue
            c = code & 63
            pattern = s[j+1:j+9]
            pn = len(pattern)
            # cnt = pn * c
            for i in range(c):
                for k in range(pn):
                    p = pattern[k]
                    items.append(p)
            j += pn
            image.extend(items)
            continue

        elif 128 <= code:
            if roomleft < 1:
                j += 1
                continue
            c = code - 128
            data = s[j+1]
            t = [data] * c
            items = t
            image.extend(items)
            j += 1
            continue

        if kwdbg:
            log.append(items)
    return image


def expandScrapStream(s: bytes) -> list[int]:
    """Expand a variable compressed image stream as encountered in 'Photo Album',
       'Photo Scrap' and geoWrite files."""
    n = len(s)
    j = -1
    image = []  # type:list[int]
    while j < n-1:
        j += 1
        code = s[j]
        roomleft = (n-1) - j
        if code in (0, 128, 220):
            if kwdbg:
                print("ILLEGAL OPCODES...")
                # pdb.set_trace()
                print()
            continue
        elif code < 128:
            if roomleft < 1:
                j += 1
                continue
            data = s[j+1]
            t = [data] * code
            image.extend(t)
            j += 1
            continue
        elif 128 <= code <= 219:
            c = code - 128
            if roomleft < c:
                j += c
                continue
            data = s[j+1:j+c+1]
            for i in data:
                image.append(i)
            j += c
            continue

        else:
            # 220...255
            patsize = code - 220
            if roomleft < patsize+1:
                j += patsize+1
                continue
            repeat = s[j+1]
            # size = repeat * patsize
            pattern = s[j+2:j+2+patsize]
            for i in range(repeat):
                for p in pattern:
                    image.append(p)

            j += patsize+1
            continue
    return image


def photoScrap(s: typing.Union[None, tuple[int, ...], bytes]) -> tuple[typing.Union[False, ImgType], typing.Union[False, ImgType]]:
    """Convert binary scrap format data into a BW and a COLOR PNG."""

    # empty record
    if s in (None, (0, 255), (0, 0)):
        return False, False

    if len(s) < 3:
        return False, False

    cardsw = s[0]  # type:int
    w = cardsw * 8
    h = s[2] * 256 + s[1]  # type:int

    if w == 0 or h == 0:
        return False, False
    elif w > 4096 or h > 4096:
        return False, False

    # cardsh = h >> 3
    image = expandScrapStream(s[3:])
    if image:
        return imageband2PNG(image, cardsw, h, 0)
    return False, False


def geoPaintBand(s: typing.Union[None, tuple[int, ...], bytes]) -> tuple[typing.Union[False, ImgType], typing.Union[False, ImgType]]:
    if s in (None, (0, 255), (0, 0)):
        return False, False
    cardsw = 80
    cardsh = 2
    image = expandImageStream(s)
    col, bw = imageband2PNG(image, cardsw, cardsh*8, 1)
    if kwdbg and 0:
        col.save("lastband_col.png")
        bw.save("lastband_bw.png")
    return col, bw


def imageband2PNG(image: typing.Union[list[int], ImageBuffer], cardsw: int, h: int, isGeoPaint: typing.Union[bool, int]) -> tuple[ImgType, ImgType]:
    """Convert a list of expanded image bytes into a PNG. Due to my
    misunderstanding the formats, the last parameter was necessary.
    geoPaint and scrap format differ huge in how the image is stored
    and this should have been handled in expandXXXStream().

    See the 'if isGeoPaint:' part.

    Returns both a black and white and color version of the image.
    """
    cardsh = h >> 3  # 'cards' are C64 8x8 pixel tiles in GEOS parlance
    if h & 7 != 0:
        cardsh += 1
    w = cardsw * 8
    # h = cardsh * 8

    eightZeroBytes = [0] * 8

    noofcards = cardsw * cardsh
    noofbytes = noofcards * 8

    # noofcolorbands = cardsh

    # holds a list of card colors; one list per row
    colorbands = []  # type:list[list[int]]

    # check sizes
    n = len(image)
    bitmapsize = cardsw * h
    colormapsize = noofcards
    gap = 8
    expectedSize = bitmapsize + gap + colormapsize

    # repair section
    if n < bitmapsize:
        # actual bits missing
        # fill with 0
        # one colored image
        if kwdbg:
            # pdb.set_trace()
            print("BITMAP BITS MISSING", bitmapsize - n)

        # fill bitmap up
        image.extend([0] * (bitmapsize - n))

        # add gap
        image.extend(eightZeroBytes)

        # add color map
        image.extend([191] * colormapsize)

        n = len(image)

    elif n == bitmapsize:
        # one colored image
        if kwdbg:
            print("ONLY BITMAP BITS")
        # add gap
        image.extend(eightZeroBytes)

        # add color map
        image.extend([191] * colormapsize)

        n = len(image)

    elif n == bitmapsize + colormapsize:
        # colored image not created by geoPaint (I guess)
        if kwdbg:
            # pdb.set_trace()
            print("COLOR GAP MISSING")
        i0 = image[:bitmapsize]
        c0 = image[bitmapsize:]
        image = []
        image.extend(i0)
        image.extend(eightZeroBytes)
        image.extend(c0)
        n = len(image)

    elif n == expectedSize:
        # should be all ok and parts sitting where they're expected to be
        pass
    else:
        # TBD
        # Here is still work todo
        #
        # It's difficult to estimate what's here and what's missing.
        if n > expectedSize:
            i0 = image[:bitmapsize]
            c0 = image[-colormapsize:]
            # legap = image[bitmapsize:-colormapsize]
            # pdb.set_trace()
            # hexdump( legap )
            image = []
            image.extend(i0)
            image.extend([0] * 8)
            image.extend(c0)
            n = len(image)
        else:
            if kwlog or 1:
                print()
                print("UNUSUAL SIZE!!")
                print("cardsw, cardsh", cardsw, cardsh)
                print("cardsw * cardsh", cardsw * cardsh)
                print("n", n)
                print("expectedSize", expectedSize)
                # if kwdbg and 0:
                #    pdb.set_trace()
                print()

    # extract color data
    offset = cardsw * h + 8
    for row in range(cardsh):
        base = offset + row * cardsw
        end = base + cardsw
        band = image[base:end]
        if len(band) < cardsw:
            if kwdbg:
                print("color band extend", (cardsw - len(band)))
            band.extend([191] * (cardsw - len(band)))
        colorbands.append(band)

    # bring the image bytes into the right order
    if isGeoPaint:
        # this is only for geoPaint files
        databytes = bytearray(noofbytes)  # pylint:disable=redefined-outer-name
        # (the python2 version called those variables 'bytes' so this is an
        # improvement)
        ROWS = cardsh
        COLS = cardsw
        BYTESPERCARD = 8
        BYTESPERROW = COLS * BYTESPERCARD

        idx = -1
        for row in range(ROWS):
            for col in range(COLS):
                for byte in range(BYTESPERCARD):
                    idx += 1
                    # src = 0 + (BYTESPERROW * row) + col * BYTESPERCARD + byte
                    # 0-15
                    base = row * BYTESPERCARD
                    dst = base * 80 + byte * 80 + col
                    # dst = base * cardsw + byte * cardsw + col
                    try:
                        byte = image[idx]
                    except IndexError:
                        byte = 0

                    if dst >= noofbytes:
                        # pdb.set_trace()
                        print(row)
                        print(col)
                        print(byte)
                        print(row * BYTESPERCARD)
                    databytes[dst] = byte
    else:
        # scraps are easy
        databytes = bytearray(image)

    # separate
    colbytes = bytes(databytes)

    # invert bw bitmap
    # looks better most of the cases
    bwbytes = bytes(map(lambda i: i ^ 255, databytes))
    # bwbytes = [chr(i ^ 255) for i in databytes]

    # for the bitmap image
    bwbytes = ''.join(bwbytes)
    try:
        bwimg = PIL.Image.frombytes('1', (w, h), bwbytes, decoder_name='raw')
    except Exception as err:
        print()
        print(err)
        # pdb.set_trace()
        return None, None

    # a bw source for the color image; cards get copied in bw mode
    # colbytes = b''.join(colbytes)
    colsource = PIL.Image.frombytes('1', (w, h), colbytes, decoder_name='raw')

    # new image
    colimg = PIL.Image.new('RGB', (w, h), (1, 1, 1))

    for row in range(cardsh):
        # create the color image by
        # 1. painting background color 8x8 cards (draw.rectangle below)
        # 2. drawing the cards foreground data in bw with fg coloring (draw.bitmap)
        base = row * cardsw
        for col in range(cardsw):
            idx = base + col

            color = colorbands[row][col]
            bgi = color & 15
            bg = c64colors[bgi]
            fgi = (color >> 4) & 15
            fg = c64colors[fgi]

            draw = PIL.ImageDraw.Draw(colimg)

            # get coordinates for copy/paste
            x = col * 8
            y = row * 8

            # fill the card with background color
            draw.rectangle((x, y, x+8, y+8), fill=bg)

            # copy the bitmap data
            bwcard = colsource.crop((x, y, x+8, y+8))
            bwcard.load()
            card = bwcard.copy()

            # paste the bw bitmap into a color imaga, coloring the card
            draw.bitmap((x, y), card, fill=fg)

    return (colimg, bwimg)


def convertGeoPaintFile(vlir: VLIRFile, folder: str) -> None:
    """Save the given VLIR geoPaint file into the folder as two pngs, one in
    color and one in b&w.
    """
    # gpf, gdh
    outnamebase = vlir.dirEntry.fileName
    outnamebase = outnamebase.replace(":", "_")
    outnamebase = outnamebase.replace("/", "_")

    print(repr(outnamebase))

    colimg = PIL.Image.new('RGB', (80*8, 90*8), 1)
    bwimg = PIL.Image.new('1', (80*8, 90*8), 1)
    # pdb.set_trace()

    for i, chain in enumerate(vlir.chains):
        if chain == (0, 0):
            break
        # if chain == (0,255):
        if type(chain) in (list, tuple):
            # print("EMPTY BAND!")
            col, bw = coldummy.copy(), bwdummy.copy()
        else:
            col, bw = geoPaintBand(chain)
        if not col:
            # print("NO BAND!")
            col = coldummy.copy()
        colimg.paste(col, (0, i*16, 640, (i+1)*16))
        if not bw:
            bw = bwdummy.copy()
        bwimg.paste(bw, (0, i*16, 640, (i+1)*16))

    if not os.path.exists(folder):
        os.makedirs(folder)
    outfilecol = os.path.join(folder, outnamebase + "_col.png")
    outfilebw = os.path.join(folder, outnamebase + "_bw.png")
    if not os.path.exists(outfilecol):
        colimg.save(outfilecol)
    if not os.path.exists(outfilebw):
        bwimg.save(outfilebw)


def convertPhotoAlbumFile(vlir: VLIRFile, folder: str) -> None:
    """Save a photo album file as a series of pngs into the folder.
    """
    # f, gpf
    outnamebase = vlir.dirEntry.fileName
    outnamebase = outnamebase.replace(":", "_")
    outnamebase = outnamebase.replace("/", "_")
    # folder = gpf.folder
    print(repr(outnamebase))

    classname = vlir.header.className

    clipnameschain = -1
    clipnames = [""] * 127
    if classname in albumWithNameTypes:
        clipnameschain, clipnames = getAlbumNamesChain(vlir)

    for i, chain in enumerate(vlir.chains):
        if chain in ((0, 0), (0, 255), None, False):
            continue
        if classname in albumWithNameTypes and i == clipnameschain:
            # names record
            continue

        col, bw = photoScrap(chain)

        clipname = ""
        if clipnames[i]:
            clipname = '-"' + clipnames[i] + '"'
        if col:
            if not os.path.exists(folder):
                os.makedirs(folder)
            filename = (outnamebase
                        + '-' + str(i+1).rjust(3, '0')
                        + clipname + "_col.png")
            filename = filename.replace('/', '_')
            of = os.path.join(folder, filename)
            if not os.path.exists(of):
                col.save(of)
        else:
            print("No color image for vlir: %i" % i)
        if bw:
            if not os.path.exists(folder):
                os.makedirs(folder)
            filename = (outnamebase
                        + '-' + str(i+1).rjust(3, '0')
                        + clipname + "_bw.png")
            filename = filename.replace('/', '_')
            of = os.path.join(folder, filename)
            if not os.path.exists(of):
                bw.save(of)
        else:
            print("No bw image for vlir: %i" % i)


def convertPhotoScrapFile(vlir: VLIRFile, folder: str) -> None:
    """Convert a clipboard 'scrap' photo file into a b&w png and a color png
    and save the in the file.
    """

    outnamebase = vlir.dirEntry.fileName
    outnamebase = outnamebase.replace(":", "_")
    outnamebase = outnamebase.replace("/", "_")
    # folder = gpf.folder
    print(repr(outnamebase))

    for i, chain in enumerate(vlir.chains):
        if chain == (0, 0):
            break
        if chain == (0, 255):
            continue

        col, bw = photoScrap(chain)

        if col:
            if not os.path.exists(folder):
                os.makedirs(folder)
            suf = '-' + str(i+1).rjust(3, '0') + "_col.png"
            of = os.path.join(folder, outnamebase + suf)
            if not os.path.exists(of):
                col.save(of)
        if bw:
            if not os.path.exists(folder):
                os.makedirs(folder)
            suf = '-' + str(i+1).rjust(3, '0') + "_bw.png"
            of = os.path.join(folder, outnamebase + suf)
            if not os.path.exists(of):
                bw.save(of)


#
# geoWrite conversion tools
#

@dataclass
class ItemCollector(object):
    """Collect the rtf, html and image snippets for second pass assembly.
    """
    title: str = 'Untitled'
    textcollection: list[str] = field(default_factory=list)
    htmlcollection: list[str] = field(default_factory=list)
    rtfcollection: list[str] = field(default_factory=list)
    imagecollection: dict[str, tuple[int, int, ImgType]
                          ] = field(default_factory=dict)
    fontcollection: list[str] = field(default_factory=list)
    fontNameID: dict[str, int] = field(default_factory=dict)
    fontIDName: dict[int, str] = field(default_factory=dict)

    # def __init__(self):
    #     self.title = "Untitled"
    #     self.textcollection = []
    #     self.htmlcollection = []
    #     self.rtfcollection = []
    #     self.imagecollection = {}
    #     self.fontcollection = []
    #     self.fontNameID = {}
    #     self.fontIDName = {}

    def initDoc(self, title: str) -> None:
        self.title = title
        # moved to finishDoc so it get's called at the right moment (that is,
        # right before finishDoc

    def finishDoc(self, s: str = "") -> None:
        # this was once in initDoc
        if len(self.rtfcollection) > 0:
            self.rtfcollection.insert(0, "{\\rtf1 ")
        else:
            self.addRTF("{\\rtf1 ")

        # add fontdict here
        #
        fd = self.rtfFontDict()
        self.addRTF(fd)

        s = ("<!DOCTYPE html><html><head>"
             "<title>%s</title></head><body>") % self.title
        if len(self.htmlcollection) > 0:
            self.htmlcollection.insert(0, s)
        else:
            self.addHTML(s)

        self.addHTML("</body></html>")
        self.addRTF("}")

    def addHTML(self, s: str) -> None:
        self.htmlcollection.append(s)

    def addRTF(self, s: str) -> None:
        self.rtfcollection.append(s)

    def addTEXT(self, s: str) -> None:
        self.textcollection.append(s)

    def addImage(self, name: str, w: int, h: int, img: ImgType) -> None:
        self.imagecollection[name] = (w, h, img)

    def addFont(self, fontname: str) -> None:
        if fontname not in self.fontcollection:
            self.fontcollection.append(fontname)
        idx = self.fontcollection.index(fontname)
        self.fontNameID[fontname] = idx
        self.fontIDName[idx] = fontname

    def getFontID(self, fontname: str) -> int:
        if fontname not in self.fontNameID:
            self.addFont(fontname)
        return self.fontNameID[fontname]

    def rtfFontDict(self) -> str:
        if not self.fontNameID:
            return ""
        # pdb.set_trace()
        sstart = "{\\fonttbl"
        send = "}"
        sitem = "\\f%i\\fnil\\fcharset0 %s;"
        keys = self.fontIDName.keys()
        keys.sort()
        items = [sstart]
        for key in keys:
            v = self.fontIDName[key]
            items.append(sitem % (key, v))
        items.append(send)
        return ''.join(items)


# make this work on VLIRFile + index
def getGeoWriteStream(items: ItemCollector, chain: bytes, chains: list[bytes, tuple[int, int]], log: list[str], flags: tuple[int, int] = (0, 0), writeVersion=0) -> tuple[ItemCollector, list[str]]:
    """Decode a geoWrite Stream; usually a page of a document.

    IN: items   - collector for RTF, HTML and TXT snippets
        chain   - the stream to decode
        chains  - the whole vlir object. Needed for image reference
    """

    SUPPRESS_NUL, FF_TO_LF = flags
    style = 0
    font_size = 0
    font_id = 0
    # font_name = "Arial"
    n = len(chain)
    j = -1
    while j < n-1:
        j += 1
        dist = n - j
        if dist <= 2:
            # pdb.set_trace()
            pass
        c = makeunicode(chain[j])
        nc = chain[j]

        if nc == 0:
            if j == 0:
                if kwlog:
                    print("<<<Unknown Escape 0x00>>>")
                j += 19
                log.append("0x00 at start")
                continue
            if SUPPRESS_NUL:
                continue

        elif nc == 12:
            if FF_TO_LF:
                items.addRTF("\n\n")
                items.addHTML("<br/><br/>\n")
                items.addTEXT("\n\n")
                continue
            else:
                items.addRTF("\\page ")
                items.addTEXT(c)
                items.addHTML("<hr/>\n")
                log.append("LF")
                continue

        elif nc == 13:
            items.addRTF("\\\n")
            items.addHTML("<br/>\n")
            items.addTEXT("\n")
            log.append("RET")
            continue

        elif nc == 16:
            # graphics escape

            width = chain[j+1] * 8
            heightL = chain[j+2]
            heightH = chain[j+3]
            height = heightH * 256 + heightL
            chainindex = chain[j+4]

            if writeVersion in (10, 11, 20):
                # if kwdbg:
                #    pdb.set_trace()
                chainindex += 1
            if 63 <= chainindex <= 127:
                if not chains:
                    j += 4
                    continue
                try:
                    image, bwimg = photoScrap(chains[chainindex])
                except Exception as err:
                    j += 4
                    continue

                if not (width and height and image):
                    j += 4
                    continue

                imagename = str(chainindex).rjust(5, '0') + ".png"
                # image.save(imagename)
                rtfs = "{{\\NeXTGraphic %s \\width%i \\height%i} " + \
                    chr(0xac) + "}"
                items.addRTF(rtfs % (imagename, width, height))
                items.addHTML('<img src="%s" />' % (imagename,))
                items.addTEXT("\n\nIMAGEFILE(%i, %i, %s)\n\n" % (width,
                                                                 height,
                                                                 imagename))
                # items.addImage( imagename, width, height, image )
                items.addImage(imagename, width, height, image)

            else:
                # pdb.set_trace()
                print("INDEX ERROR")

            if kwlog:
                print(
                    f"<<<Graphics Escape>>> {width}:{height} @ VLIR:{chainindex}")

            j += 4
            log.append("GRPHX vlir:%i, w: %i, h: %i" %
                       (chainindex, width, height))
            continue

        elif nc == 17:
            # ruler escape
            leftMargin = struct.unpack("<H", chain[j+1:j+3])[0]
            rightMargin = struct.unpack("<H", chain[j+3:j+5])[0]

            s1 = j+5
            s2 = j+7
            dec = 2**15
            tabs = []

            exitIt = False
            for i in range(8):
                try:
                    tab = struct.unpack("<H", chain[s1:s2])[0]
                except Exception as err:
                    if kwlog:
                        print()
                        print(err)
                        print("roomleft", (n-1) - j)
                    # if kwdbg:
                    #    pdb.set_trace()
                    j = n
                    exitIt = True
                    break

                if tab & dec:
                    tab -= dec
                    tabs.append((tab, 1))
                else:
                    tabs.append((tab, 0))
                s1 += 2
                s2 += 2
            if exitIt:
                break

            paragraphMargin = struct.unpack("<H", chain[j+21:j+23])[0]

            justifiation = chain[j+23] & 3

            spacing = chain[j+23] >> 2 & 3

            color = chain[j+24]

            justifications = {
                0:  'left',
                1:  'center',
                2:  'right',
                3:  'justify'}
            spacings = {
                0: "\\sl240 ",
                1: "\\sl360 ",
                2: "\\sl480 "}

            items.addRTF(spacings.get(spacing, ""))
            items.addRTF("\\q%s " % (justifications[justifiation],))

            items.addHTML('<span align="%s">' %
                          (justifications[justifiation],))

            if kwlog:
                print("leftmargin:", repr(leftMargin))
                print("rightMargin:", repr(rightMargin))
                print("paragraphMargin:", repr(paragraphMargin))
                print("justifiation:", repr(justifiation))
                print("spacing:", repr(spacing))
                print("color:", repr(color))
                print("tabs:", tabs)

            for tab in tabs:
                tabpoint, decimal = tab
                if tabpoint >= rightMargin:
                    continue
                if decimal:
                    items.addRTF("\\tqdec")
                items.addRTF("\\tx%i" % (tabpoint * 20))

            j += 26
            log.append("RULER")
            continue

        elif nc == 23:
            # NEWCARDSET
            fontL = chain[j+1]
            fontH = chain[j+2]
            newfont = fontH * 256 + fontL
            fontid = newfont >> 5
            fontsize = newfont & 0x1f
            newstyle = chain[j+3]
            fontname = fontmapping.get(fontid, ("", "Arial"))
            if fontname[1]:
                fontname = fontname[1]
            else:
                fontname = "Arial"

            if kwlog:
                print("segment:", repr(chain[j:j+4]))
                print("<<<NEWCARDSET Escape>>>")
                print("fontID:", fontid)
                print("fontName:", fontname)
                print("font size:", fontsize)
                print("style:", bin(style))

            if fontid != font_id:
                if 1:  # ' ' in fontname:
                    items.addHTML(
                        '''<span style="font-family: '%s';">''' % fontname)
                else:
                    items.addHTML(
                        '''<span style="font-family: %s;">''' % fontname)

                # it looks like RTF needs a font dictionary... not now.
                # items.addRTF( "\\fn%s " % (fontname,) )
                rtfFontID = items.getFontID(fontname)
                items.addRTF("\\f%i " % (rtfFontID,))
                font_id = fontid
                font_name = fontname

            if fontsize != font_size:
                items.addHTML('<span style="font-size: %ipt">' % fontsize)
                items.addRTF("\\fs%i " % (fontsize * 2,))
                font_size = fontsize

            if style != newstyle:
                # if 0: #newstyle & 7 != 0:
                #    pdb.set_trace()
                bits = [2**i for i in range(1, 8)]  # type:list[int]
                # stylecodes = ['sub', 'sup', 'out', 'ita', 'rev', 'bld', 'uln']
                rtfcommands = (
                    ('\\nosupersub ', '\\sub '),
                    ('\\nosupersub ', '\\super '),
                    ('\\outl0\\strokewidth0 ', '\\outl\\strokewidth60 '),
                    ('\\i0 ', '\\i '),
                    ('{\\colortbl;\\red0\\green0\\blue0;\\red255\\green255\\blue255;}\\cb1\\cf2 ',
                     '{\\colortbl;\\red0\\green0\\blue0;\\red255\\green255\\blue255;}\\cb2\\cf1 '),
                    ('\\b0 ', '\\b '),
                    ('\\ulnone ', '\\ul '))

                rtfstyles = dict(zip(bits, rtfcommands))
                if kwdbg:
                    print("oldstyle", bin(style))
                    print("newstyle", bin(newstyle))
                # pdb.set_trace()

                for bit in bits:
                    curr = newstyle & bit
                    old = style & bit

                    if curr and old:
                        # no change
                        pass
                    elif not curr and not old:
                        # no change
                        pass
                    elif curr and not old:
                        # switch on
                        items.addRTF(rtfstyles[bit][1])
                    elif not curr and old:
                        # switch off
                        items.addRTF(rtfstyles[bit][0])
                style = newstyle
            log.append("NEWCARDSET")
            j += 3
            continue
        elif nc == 8 or c == 24:
            j += 19
            databytes = [hex(i) for i in chain[j:j+10]]
            pp(databytes)
            # pdb.set_trace()
            log.append("0x08 | 0x24")
            continue
        elif nc == 0xf5:
            j += 10
            log.append("0xF5")
            continue
        elif c in ('{', '}'):
            items.addRTF("\\%s" % c)
            items.addHTML(c)
            items.addTEXT(c)
            log.append("{}")
            continue

        items.addRTF(c)
        items.addHTML(c)
        items.addTEXT(c)
        if log:
            if log[-1] != "CHARS":
                log.append("CHARS")

    if kwlog:
        print("<<<New Page>>>")

    return items, log


def convertWriteImage(vlir: VLIRFile, folder: str, flags=(1, 1), rtf=True, html=True, txt=True) -> None:
    """Convert a VLIRFile to the approbriate text format. The GEOS file class must
    be one of textTypes.
    IN:
        vlir - the VLIRFile of a GEOS file
        folder - output directory
        flags - tuple (SUPPRESS_NUL, FF_TO_LF)
        rtf - if True write rtfd document with image
        html - if True write html document with images
        txt - if True write text document
    """
    # prepare
    log = []
    basename = vlir.dirEntry.fileName
    writeversion = 21
    try:
        writeImageVersion = vlir.header.className
        writeversion = geoWriteVersions.get(writeImageVersion, 21)
    except Exception as err:
        # should trap on scrap & albums
        print(err)
        # if kwlog:
        #    pdb.set_trace()
        print()

    ic = ItemCollector()
    # ic.initDoc( basename )
    chains = vlir.chains

    print(repr(basename))

    # page loop
    for idx, chain in enumerate(chains):
        # pdb.set_trace()
        if chain in ((0, 0), (0, 255), None, False):
            continue

        if idx >= 61:
            break

        ic, log = getGeoWriteStream(
            ic, chain, chains, log, flags, writeversion)

    # finish doc
    ic.finishDoc()
    ic.addRTF("}")

    # write out
    rtfs = ''.join(ic.rtfcollection)
    htmls = ''.join(ic.htmlcollection)
    texts = ''.join(ic.textcollection)

    if rtf:
        rtfoutfolder = os.path.join(folder, basename + ".rtfd")
        if not os.path.exists(rtfoutfolder):
            os.makedirs(rtfoutfolder)
        rtfoutfile = os.path.join(rtfoutfolder, "TXT.rtf")
        if not os.path.exists(rtfoutfile):
            with open(rtfoutfile, 'wb') as f:
                f.write(rtfs)

    if html:
        htmloutfolder = os.path.join(folder, basename + "_html")
        if not os.path.exists(htmloutfolder):
            os.makedirs(htmloutfolder)
        htmloutfile = os.path.join(htmloutfolder, "index.html")
        if not os.path.exists(htmloutfile):
            with open(htmloutfile, 'wb') as f:
                f.write(htmls)

    if txt:
        textoutfile = os.path.join(folder, basename + ".txt")
        if not os.path.exists(textoutfile):
            with open(textoutfile, 'wb') as f:
                f.write(texts)

    # write images
    for filename in ic.imagecollection:
        w, h, img = ic.imagecollection[filename]

        rtfimage = os.path.join(rtfoutfolder, filename)
        htmlimage = os.path.join(htmloutfolder, filename)
        if rtf:
            if not os.path.exists(rtfimage):
                img.save(rtfimage)
        if html:
            if not os.path.exists(htmlimage):
                img.save(htmlimage)

#
# disk image tools
#


@dataclass
class CBMConvertFile(object):
    folder: str
    filename: str
    direntry: bytes
    geosDirEntry: GEOSDirEntry
    geosHeaderBlock: GEOSHeaderBlock
    vlir: VLIRFile

    def __init__(self, filepath: str):

        infile = filepath
        infile = os.path.abspath(os.path.expanduser(infile))

        self.folder, filename = os.path.split(infile)
        # basename, ext = os.path.splitext(filename)

        with open(infile, 'rb') as f:
            data = f.read()

        self.direntry = data[0:0x1e]
        self.geosDirEntry = GEOSDirEntry(self.direntry)

        format = data[0x1e:0x3a]
        geoinfo = data[0xfe:0x1fc]
        self.geosHeaderBlock = GEOSHeaderBlock(geoinfo, infile)

        giwidth = geoinfo[0] * 8
        giheight = geoinfo[1]
        gibitmapType = geoinfo[2]
        # gispritedata = geoinfo[3:66]

        gidosfiletype = geoinfo[66]
        gigeosfiletype = geoinfo[67]
        gigeosfilestructure = geoinfo[68]

        if kwlog:
            print("icon width:", giwidth)
            print("icon height:", giheight)
            print("bitmap type", gibitmapType)
            print("DOS file type:", gidosfiletype)
            print("GEOS file type:", gigeosfiletype)
            print("GEOS file structure:", gigeosfilestructure)

        # pdb.set_trace()

        # v = VLIRFile()
        # v.header = self.geosHeaderBlock
        # v.dirEntry = self.geosDirEntry
        # v.filepath = infile
        self.vlir = VLIRFile([], self.geosHeaderBlock, self.direntry)
        self.vlir.filepath = self.direntry

        geofiletype = data[21]

        formatOK = False
        if format.startswith("PRG formatted GEOS file V1.0"):
            broken = False
            formatOK = True
        elif format.startswith("PRG formatted GEOS file"):
            broken = True
            formatOK = True
        elif format.startswith("SEQ formatted GEOS file"):
            # this is a new one
            broken = False
            formatOK = True
        else:
            print("ERROR: Unknown file format %s" % repr(format))
            formatOK = False
            broken = True

        if formatOK:
            if geofiletype == 0:
                # sequential file.
                # out of pure lazyness, store filadata in vlir[0]
                # why did I make the SEQFile class? Dismissed.
                self.vlir.chains[0] = data[0x1fc:]

            elif geofiletype == 1:
                vlirheader = data[0x1fc:0x2fa]

                payload = data[0x2FA:]

                consumedpayload = 0

                for i in range(127):
                    a1 = vlirheader[i * 2]
                    a2 = vlirheader[i * 2 + 1]
                    if kwlog:
                        print("<<<chain 0x%02x/0x%02x>>>" % (a1, a2))

                    # end of file
                    if a1 == 0 and a2 == 0:
                        self.vlir.chains[i] = (a1, a2)
                        break

                    if a1 == 0 and a2 == 255:
                        # v.chains[i] = (ai,a2)
                        continue

                    if broken:
                        chain_size = a1 * 254 + a2
                        gross_size = chain_size
                    else:
                        chain_size = (a1 - 1) * 254 + a2 - 1
                        gross_size = a1 * 254

                    chainstart = consumedpayload
                    chainend = consumedpayload + gross_size
                    chainlogicalend = consumedpayload + chain_size
                    chaindata = payload[chainstart:chainlogicalend]

                    self.vlir.chains[i] = chaindata

                    consumedpayload = chainend


@dataclass
class VLIRFile(object):
    """The main file holding object in this suite. This APPEARS to be used for
    both VLIR and ordinary files.

    self.chains -   A list of GEOS VLIR strings OR just the string of any sequential
                    type in chains[0]
    self.header -   the GEOS header block. A GEOSHeaderBlock
    self.dirEntry - The CBM/GEOS dirEntry.  A GEOSDirEntry
    """
    chains: list[typing.Union[bytes, tuple[int, int]]]
    header: GEOSHeaderBlock
    dirEntry: GEOSDirEntry

    # Should probably move the VLIR creation code here?

    def __init__(self, chains: list[typing.Union[bytes, tuple[int, int]]], header: GEOSHeaderBlock, dirEntry: GEOSDirEntry):
        self.chains = (chains + ([(0x00, 0xff)] * 127))[:127]  # Null fill
        self.header = header
        self.dirEntry = dirEntry
        # for saving
        self.folder = ""
        self.filename = ""
        # origin
        self.filepath = ""


def cleanupString(s: bytes) -> str:
    """Remove any bytes from stripchars and null-terminate, then convert to
    unicode string.
    """
    t = s.strip(stripchars)
    t = t.split(b'\x00')[0]  # Handles up to null bytes, better way?
    return makeunicode(t)


@dataclass
class GEOSHeaderBlock(object):
    """The GEOS specific header for a file."""
    filepath: str
    iconWidthCards: int
    iconWidth: int
    iconHeight: int
    iconByteLength: int
    iconDataRAW: bytes
    dosFileTypeRAW: int
    fileOK: bool
    fileProtected: bool
    fileType: str
    geosFileType: int
    geosFileTypeString: str
    geosFileStructure: int
    geosFileStructureString: str
    loadAddress: int
    endOfLoadAddress: int
    startAddress: int
    className: str
    fourtyEightyFlags: str
    author: str
    parentDisk: str
    creator: str
    applicationData: bytes
    firstPagenumber: int
    NLQPrint: bool
    titlePage: bool
    headerHeight: int
    footerHeight: int
    pageHeight: int
    fontID: int
    fontPointSizes: list[int]
    fontByteSizes: list[int]
    desktopNote: str

    def __init__(self, s: bytes, filepath: str):

        if kwdbg:
            self.rawdata = s
        # skip possible link bytes
        if s[0] == 0 and len(s) == 256:
            s = s[2:]
        # filepath is only needed for display purposes
        # have to think of sth for fileas from
        self.filepath = filepath
        self.iconWidthCards = s[0]
        self.iconWidth = self.iconWidthCards * 8
        self.iconHeight = s[1]
        self.iconByteLength = s[2] & 0x7f
        self.iconDataRAW = s[3:3+63]

        # ok up to here
        self.dosFileTypeRAW = s[66]
        self.fileOK = (self.dosFileTypeRAW & 128) > 0
        self.fileProtected = (self.dosFileTypeRAW & 64) > 0
        t = self.dosFileTypeRAW & 7
        self.fileType = dosFileTypes.get(t, "???")

        # ok up to here
        self.geosFileType = s[67]
        self.geosFileTypeString = geosFileTypes.get(
            self.geosFileType,
            f"UNKNOWN GEOS filetype:{self.geosFileType}")

        # ok up to here
        self.geosFileStructure = s[68]
        self.geosFileStructureString = ""
        if self.geosFileStructure == 0:
            self.geosFileStructureString = "Sequential"
        elif self.geosFileStructure == 1:
            self.geosFileStructureString = "VLIR"

        # ok up to here
        self.loadAddress = s[69] + s[70] * 256
        self.endOfLoadAddress = s[71] + s[72] * 256
        self.startAddress = s[73] + s[74] * 256

        # self.classNameRAW = s[75:95]
        self.className = cleanupString(s[75:91])

        self.fourtyEightyFlags = fourtyEightyFlags.get(s[94], "")

        authorOrParentDisk = cleanupString(s[95:115])
        creator = cleanupString(s[115:135])

        self.author = self.parentDisk = self.creator = ""

        if self.geosFileType in filetypesWithAuthor:
            self.author = authorOrParentDisk
            self.creator = creator
        elif self.geosFileType == 8:
            # it's a font file. no parent, no author
            pass
        else:
            self.parentDisk = authorOrParentDisk
            self.creator = creator

        self.applicationData = s[135:157]

        # geoWrite specific header data
        self.firstPagenumber = 1
        self.NLQPrint = self.titlePage = False
        self.headerHeight = self.footerHeight = self.pageHeight = 0
        self.fontID = -1
        self.fontPointSizes = []
        self.fontByteSizes = []

        if self.className.startswith("Write Image V"):
            # it's a geowrite file
            self.firstPagenumber = s[0x87] + s[0x88] * 256

            self.NLQPrint = (s[0x89] & 64) > 0
            self.titlePage = (s[0x89] & 128) > 0
            self.headerHeight = s[0x8a] + s[0x8b] * 256
            self.footerHeight = s[0x8c] + s[0x8d] * 256
            self.pageHeight = s[0x8e] + s[0x8f] * 256

        elif self.geosFileType == 8:
            # it's a font file
            self.fontID = s[0x7e] + s[0x7f] * 256

            for i in range(16):
                # get point size
                base = 0x80 + i * 2
                t = s[base] + s[base+1] * 256
                t1 = t & 0xffc0
                t1 >>= 6
                if t1 != self.fontID:
                    break
                t2 = t & 0x003f
                self.fontPointSizes.append(t2)

                # get byte size
                base = 0x5f + i * 2
                t = s[base] + s[base+1] * 256
                if t != 0:
                    self.fontByteSizes.append(t)

        self.desktopNote = cleanupString(s[158:])

    def prnt(self):
        print()
        print("GEOS Header Block for:", repr(self.filepath))

        # print(icon)
        print('-' * 24)
        for y in range(21):  # self.iconHeight):
            for x in range(3):  # self.iconWidthCards):
                # i = self.iconDataRAW[y*self.iconWidthCards+x]
                i = self.iconDataRAW[y*3+x]
                s = str(bin(i))
                s = s[2:]
                s = s.rjust(8, '0')
                s = s.replace('1', 'X')
                s = s.replace('0', ' ')
                sys.stdout.write(s)
                if x == 2:
                    sys.stdout.write('|')
            sys.stdout.write('\n')
        sys.stdout.flush()
        print('-' * 24)

        # print extended file attributes
        print("GEOS File Structure:", self.geosFileStructureString)
        print("GEOS File Type:", repr(self.geosFileTypeString))

        print("GEOS Class Name:", repr(self.className))
        if self.geosFileType in filetypesWithAuthor:
            print("GEOS Author Name:", repr(self.author))
        else:
            print("GEOS Parent Disk:", repr(self.parentDisk))
        print("GEOS Creator Name:", repr(self.creator))
        print("GEOS 40/80:", self.fourtyEightyFlags)
        print("GEOS Load Address:", hex(self.loadAddress))
        print("GEOS End Address:", hex(self.endOfLoadAddress))
        print("GEOS Exe Address:", hex(self.startAddress))
        if self.className.startswith("Write Image V"):
            print("geoWrite first page number:", self.firstPagenumber)
            print("geoWrite NLQ print:", self.NLQPrint)
            print("geoWrite first page is Title:", self.titlePage)
            print("geoWrite header height:", self.headerHeight)
            print("geoWrite footer height:", self.footerHeight)
            print("geoWrite page height:", self.pageHeight)
        elif self.geosFileType == 8:
            print("Font ID:", self.fontID)
            s = [str(t) for t in self.fontPointSizes]
            print("Font point sizes:", ', '.join(s))
            s = [str(t) for t in self.fontByteSizes]
            print("Font byte sizes:", ', '.join(s))
        print("GEOS DeskTop Comment:", repr(self.desktopNote))


@dataclass
class GEOSDirEntry(object):
    """A Commodore directory entry with additional GEOS attributes.    """
    fileSizeBlocks: int
    dirEntryBytes: bytes
    dosFileTypeRAW: int
    fileOK: bool
    fileProtected: bool
    fileType: str
    trackSector: tuple[int, int]
    filename: str
    geosHeaderTrackSector: tuple[int, int]
    geosHeaderTrackSector: tuple[int, int] = (0, 0)
    geosFileStructure: int = 0
    geosFileStructureString: str = ''
    geosFileTypeString: str = ''
    modfDate: typing.Union[datetime.datetime, str] = 'NO MODF DATE'
    isGEOSFile: bool = False
    geosFileType: int = 0
    modfDateRAW: bytes = bytes(0x1c-0x17)

    def __init__(self, dirEntryBytes: bytes, isGeos=True):

        if len(dirEntryBytes) == 32:
            dirEntryBytes = dirEntryBytes[2:]

        # save it for CVT file export
        self.dirEntryBytes = dirEntryBytes

        """The raw file type contains the file type itself ored with flags
        for locking (bit6 set if locked) and closed correctly (bit7 set, if
        bit7 is clear then the file is probably corrupted).
        """
        self.dosFileTypeRAW = dirEntryBytes[0]
        self.fileOK = (self.dosFileTypeRAW & 128) > 0
        self.fileProtected = (self.dosFileTypeRAW & 64) > 0
        t = self.dosFileTypeRAW & 7

        self.fileType = dosFileTypes.get(t, "???")
        self.trackSector = dirEntryBytes[1], dirEntryBytes[2]
        self.fileName = makeunicode(
            dirEntryBytes[0x03:0x13].rstrip(stripchars))

        self.geosHeaderTrackSector = (0, 0)
        self.fileSizeBlocks = dirEntryBytes[0x1c] + dirEntryBytes[0x1d] * 256

        if isGeos:
            # if not geos, this is REL side sector
            self.geosHeaderTrackSector = (
                dirEntryBytes[19], dirEntryBytes[20])
            # if not geos, this is REL record size
            self.geosFileStructure = dirEntryBytes[21]
            self.geosFileStructureString = ""
            self.geosFileTypeString = ""
            self.modfDate = "NO MODF DATE"
            self.isGEOSFile = False

            if self.fileType == 'USR':
                if self.geosFileStructure == 0:
                    self.geosFileStructureString = "Sequential"
                    self.isGEOSFile = True
                elif self.geosFileStructure == 1:
                    self.geosFileStructureString = "VLIR"
                    self.isGEOSFile = True

                self.geosFileType = dirEntryBytes[22]
                # self.geosFileTypeString = geosFileTypes[self.geosFileType]
                self.geosFileTypeString = geosFileTypes.get(self.geosFileType,
                                                            f"UNKNOWN GEOS filetype:{self.geosFileType}")

                self.modfDateRAW = dirEntryBytes[0x17:0x1c]
                y, m, d, h, mi = list(self.modfDateRAW)
                if 85 <= y <= 99:  # y2K fix, rip y'all in 2085
                    y += 1900
                else:
                    y += 2000
                try:
                    self.modfDate = datetime.datetime(y, m, d, h, mi)
                except Exception as err:
                    self.modfDate = f"ERROR WITH:  {y} {m} {d} {h} {mi}"

    def prnt(self):
        """Print out myself -- probably could do this better by making this a
        dataclass.
        """
        print()
        print('-' * 80)
        print("filename:", repr(self.fileName))
        print('-' * 16)
        print("file OK:", self.fileOK)
        print("file Protected:", self.fileProtected)
        print("file type:", self.fileType)
        print("file Track/Sector:", self.trackSector)
        print("GEOS Header Track/Sector:", self.geosHeaderTrackSector)
        print("GEOS File Structure:", self.geosFileStructureString)
        print("GEOS File Type:", self.geosFileTypeString)
        print("GEOS File Last Modified:", str(self.modfDate)[:19])
        print("GEOS Total Block Size:", self.fileSizeBlocks)
        print()

    def smallprnt(self):
        """Print a shorter version of myself.
        """
        print(repr(self.fileName).ljust(20),
              str(self.fileSizeBlocks).rjust(5),
              repr(self.fileType))


@dataclass
class DiskImage(object):
    """A representation of a C64 disk image -- formats currently supported are
    d64 and d81.
    """
    tag: str
    filepath: str
    stream: bytes
    isOK: bool
    files: list[VLIRFile]
    sectorOffsets: list[int]
    trackByteOffsets: list[int]
    sectorsPerTrack: list[int]
    dirSectorTS: tuple[int, int]
    minMaxTrack: tuple[int, int]
    diskName: str
    isGEOSDisk: bool
    DirEntries: list[GEOSDirEntry]
    deskBorder: list[GEOSDirEntry]

    def getTrackOffsetList(self, sizelist: typing.Sequence[int]) -> tuple[list[int], list[int], list[int]]:
        """calculate sectorOffset per Track, track Byte offstes and
           sectors per track lists."""

        offset = 0  # type:int
        sectorsize = 256  # type:int
        sectorOffsets = []  # type:list[int]
        trackByteOffsets = []  # type:list[int]
        sectorsPerTrack = []  # type:list[int]
        for start, end, sectors in sizelist:
            for track in range(start, end+1):
                offset += sectors
                sectorOffsets.append(offset)
                sectorsPerTrack.append(sectors)
        for start, end, sectors in sizelist:
            for track in range(start, end+1):
                if track == 0:
                    continue
                trackByteOffsets.append((sectorOffsets[track-1]) * sectorsize)
        return sectorOffsets, trackByteOffsets, sectorsPerTrack

    @staticmethod
    def readfile(path: str) -> bytes:
        """Utility function to read the bytes of a file."""
        with open(path, 'rb') as f:
            s = f.read()
        return s

    def getTS(self, t: int, s: int) -> tuple[str, bytes]:
        """Given a track and sector number, return a string error code (empty
        string if no error) and the bytes of the indicated sector.
        """
        error = ""
        if t == 0:
            return "", bytes()
        try:
            # size = 256
            if self.minMaxTrack[0] <= t <= self.minMaxTrack[1]:
                if 0 <= s <= self.sectorsPerTrack[t]:
                    adr = self.trackByteOffsets[t-1] + s * 256
                    data = self.stream[adr:adr+256]
                else:
                    return "", bytes()
            else:
                return "", bytes()

        except Exception as err:
            print(f"getTS({t},{s}) ERROR: {err}")
            return str(err), bytes()
            # pdb.set_trace()
            print()
            # print("adr", adr)
            # print("adr+256", adr+256)
            # print(len(self.stream))
            # error = err
        return error, data

    def getChain(self, t: int, s: int) -> tuple[str, bytes]:
        """Given an initial track and sector, assume the referred to block is
        the head of a chain of blocks. The first two bytes in the chain are
        the track and sector number (respectively) of the next block in the
        chain. Returns a string error code and the concatted bytes of all
        the blocks, MINUS the leading track and sector count bytes.

        In normal C64 disk format, track numbers are 1-indexed. If the
        initial track number is 0, the sector number is instead the number of
        bytes valid in this block.
        """
        error = ""
        readSoFar = set()  # type:set[tuple[int, int]]
        # pdb.set_trace()
        result = []  # type:list[bytes]
        tr, sc = t, s
        blocks = 0
        while True:
            blocks += 1
            err, b = self.getTS(tr, sc)
            readSoFar.add((tr, sc))
            if err != "":  # If error code from getTS
                return err, b''.join(result)
            if len(b) <= 2:  # No track and sector list
                # pdb.set_trace()
                break
            tr, sc = b[0], b[1]
            if tr == 0:
                result.append(b[2:sc+1])
                break
            elif (tr, sc) in readSoFar:
                # circular link
                # pdb.set_trace()
                if len(b) > 2:
                    result.append(b[2:])
                break
            elif tr > 80:
                break
            else:
                result.append(b[2:])
        return error, b''.join(result)

    def getDirEntries(self, t: int, s: int) -> tuple[str, list[GEOSDirEntry]]:
        """Read all directory entries from the disk starting at the given
        track and sector, returning an error code and a list of all entries.

        Only includes SEQ, PRG, and USR entries -- rest are ignored.
        """
        readSoFar = set()  # type:set[tuple[int, int]]
        error = ""
        result = []  # type:list[GEOSDirEntry]
        if t == 0:
            return "", result
        nextrack, nextsector = t, s
        while True:
            readSoFar.add((nextrack, nextsector))
            err, b = self.getTS(nextrack, nextsector)
            if err != "":
                break
                # return err, result
            if not b:  # no bytes
                break

            nextrack, nextsector = b[0], b[1]  # Get next link in chain
            if (nextrack, nextsector) in readSoFar:
                break
            # base = 0
            for i in range(8):  # Get directory entries
                offset = i * 32
                dirEntryRaw = b[offset:offset+32]
                gde = GEOSDirEntry(dirEntryRaw, self.isGEOSDisk)
                if gde.fileType in ('SEQ', 'PRG', 'USR'):
                    result.append(gde)
        return error, result

    def printDirectory(self):
        """Print out all directory entries. Probably this should return a
        string instead, also probably could do all this better by making
        this a dataclass and prettyprinting or sumpin.
        """
        print()
        print('#' * 40)
        print(repr(self.diskName))
        print('-' * 20)
        for i in self.DirEntries:
            i.smallprnt()
        if self.deskBorder:
            print()
            print("On Desktop border:")
        for i in self.deskBorder:
            i.smallprnt()
        print()

    def __init__(self, stream: bytes = None, filepath: str = None, tag: str = ""):
        # pdb.set_trace()
        # alternate path for streams
        self.tag = tag
        self.filepath = ""
        self.stream = bytes()
        if filepath:
            # Probably could fix this up with pathlike or sumpin
            if os.path.exists(filepath):
                self.filepath = os.path.abspath(os.path.expanduser(filepath))
                self.stream = self.readfile(self.filepath)
            else:
                print("No File ERROR!")
                # pdb.set_trace()
        elif stream:
            self.stream = stream
        else:
            # pdb.set_trace()
            print()
        self.isOK = False
        self.files = []  # type:list[VLIRFile]
        size = len(self.stream)
        typ, _ = imagesizeToExt.get(size, ("", 0))

        if typ in ('.d64', '.d81'):  # '.d71'):

            self.isOK = True

            o, p, t = self.getTrackOffsetList(sectorTables[typ])
            self.sectorOffsets, self.trackByteOffsets, self.sectorsPerTrack = o, p, t
            self.dirSectorTS = dirSectorsForDrives.get(typ, (0, 0))

            self.minMaxTrack = minMaxTrack[typ]

            dtr, dsc = self.dirSectorTS

            s, n = dirSectorStructures[typ]
            err, dirSec = self.getTS(dtr, dsc)
            # if err != "":
            #    pdb.set_trace()
            t = struct.unpack(s, dirSec)  # unpack_from??
            d = dict(zip(n.split(), t))
            s = d.get('dnam', b'NO DISK NAME')  # type:bytes
            s = s.rstrip(b'\xa0')
            self.diskName = makeunicode(s)

            self.isGEOSDisk = d['geoformat'] == b"GEOS format"

            err, self.DirEntries = self.getDirEntries(d['tr'], d['sc'])

            self.deskBorder = []  # type:list[GEOSDirEntry]
            if self.isGEOSDisk:
                err, self.deskBorder = self.getDirEntries(
                    d['dsktr'], d['dsksc'])

            # get files
            dirEntries = self.DirEntries.copy()
            if self.isGEOSDisk and self.deskBorder:
                # pdb.set_trace()
                dirEntries.extend(self.deskBorder)

            for dirEntry in dirEntries:
                #
                # dirEntry.smallprnt()

                # f = VLIRFile()
                # f.dirEntry = dirEntry

                chains = [(0x00, 0xFF)] * 127

                isGEOSFile = dirEntry.isGEOSFile
                isVLIR = dirEntry.geosFileStructureString == 'VLIR'

                # f.header = ""
                header = ''
                if isGEOSFile:
                    err, s = self.getTS(dirEntry.geosHeaderTrackSector[0],
                                        dirEntry.geosHeaderTrackSector[1])
                    if len(s) == 256:
                        src = "IMAGE:" + repr(dirEntry.fileName)
                        if self.filepath:
                            src = self.filepath
                        header = GEOSHeaderBlock(s, src)

                # file content
                t, s = dirEntry.trackSector
                if isGEOSFile:
                    if isVLIR:
                        # ATTN: due to the prior implementation of CBM-CVT files
                        # VLIR header (VLIRFile.__init__)is missing the link bytes
                        err, vlirhead = self.getTS(t, s)
                        if err:
                            print("NO VLIR")
                            # pdb.set_trace()
                            print()
                        if not vlirhead:
                            continue
                        # pdb.set_trace()
                        for i in range(127):
                            t = vlirhead[i*2+0]
                            s = vlirhead[i*2+1]
                            # print(i*2,t,s)
                            if t != 0:
                                err, chains[i] = self.getChain(t, s)
                            else:
                                chains[i] = (t, s)
                    else:
                        err, chains[0] = self.getChain(t, s)
                else:
                    err, chains[0] = self.getChain(t, s)

                f = VLIRFile(chains, header, dirEntry)
                self.files.append(f)
            if kwdbg:
                self.printDirectory()

# UNUSED


@dataclass
class FontRecord(object):
    baselineOffset: int
    bitstreamRowLength: int
    fontHeight: int
    indextableOffset: int
    bitstreamOffset: int
    indexTableSize: int
    indexTable: bytes
    bitstreamTable: bytes
    bitstreamTableSize: int

    def __init__(self, s: bytes, name, vlirIndex):
        self.baselineOffset = s[0]
        self.bitstreamRowLength = s[1] + s[2] * 256
        self.fontHeight = s[3]
        self.indextableOffset = s[4] + s[5] * 256
        self.bitstreamOffset = s[6] + s[7] * 256

        self.indexTableSize = self.bitstreamOffset - self.indextableOffset

        self.indexTable = s[self.indextableOffset:self.indextableOffset +
                            self.indexTableSize]

        self.bitstreamTable = s[self.bitstreamOffset:]

        self.bitstreamTableSize = self.fontHeight * self.bitstreamRowLength


def getFontChain(name: typing.Union[str, bytes], s: bytes, chainIndex) -> tuple[ImgType, ImgType]:
    """Parse a font, returning it as a black&white and color bitmap."""

    # font header
    #
    #  0 - baseline offset
    #  1 - bitstream width
    #  3 - font height
    #  4 - rel pointer to index table
    #  6 - rel pointer to character

    if len(s) < 8:
        return False, False
    baselineOffset = s[0]
    bitstreamRowLength = s[1] + s[2] * 256
    fontHeight = s[3]
    indextableOffset = s[4] + s[5] * 256
    bitstreamOffset = s[6] + s[7] * 256

    indexTableSize = bitstreamOffset - indextableOffset

    # indexTable = s[indextableOffset:indextableOffset+indexTableSize]

    bitstreamTable = s[bitstreamOffset:]

    bitstreamTableSize = fontHeight * bitstreamRowLength

    if len(bitstreamTable) == 0:
        return False, False

    # This should be an exception
    if len(bitstreamTable) != bitstreamTableSize:
        print("SIZE MISMATCH:")
        print("Name:", name)
        print("bitstreamTableSize", bitstreamTableSize)
        print("len(bitstreamTable)", len(bitstreamTable))
        if kwdbg:
            time.sleep(2)
        print()

    image = []  # type:list[int]
    idx = 0
    for y in range(fontHeight):
        for x in range(bitstreamRowLength):
            idx = y * bitstreamRowLength + x
            if idx >= len(bitstreamTable):
                # if kwdbg:
                #    pdb.set_trace()
                if kwlog:
                    print("chainIndex:", chainIndex)
                    print("baselineOffset:", baselineOffset)
                    print("bitstreamRowLength:", bitstreamRowLength)
                    print("fontHeight:", fontHeight)
                    print("indextableOffset:", indextableOffset)
                    print("bitstreamOffset:", bitstreamOffset)
                    print("indexTableSize:", indexTableSize)
                val = 0
            else:
                val = bitstreamTable[idx]
            image.append(val)
        # print()
    col, bw = imageband2PNG(image, bitstreamRowLength, fontHeight, 0)
    # pdb.set_trace()
    if False:
        # resize the image
        h, w = bw.size
        h *= 2
        w *= 2
        bw = bw.resize((h, w), PIL.Image.NEAREST)
    return col, bw


def convertFontFile(geosfile: VLIRFile, folder: str) -> None:
    """Read and convert all fonts in a file, saving them as PNGs in the
    folder.
    """
    gdh = geosfile.header
    gde = geosfile.dirEntry

    if gdh.geosFileType != 8:
        # pdb.set_trace()
        print("IGNORED:", repr(geosfile))
        return

    if kwdbg:
        print('-' * 20)
        print(gde.fileName)
        print(gdh.className)

    if kwlog:
        gdh.prnt()

    chains = geosfile.chains

    for idx, chain in enumerate(chains):

        if chain in ((0, 0), (0, 255), None, False):
            continue

        if type(chain) in (tuple, list):  # ??????????
            continue

        if chain == "":
            continue

        try:
            col, bw = getFontChain(gde.fileName, chain, idx)
        except IndexError as err:
            col = bw = False
            print("ERROR reading font stream", gde.filename)
            continue

        if col and bw:
            fname = "%s (vlir %i).png" % (gde.fileName, idx-1)
            if '/' in fname:
                fname = fname.replace('/', ':')
            path = os.path.join(folder, fname)
            if not os.path.exists(folder):
                os.makedirs(folder)
            if not os.path.exists(path):
                bw.save(path)
