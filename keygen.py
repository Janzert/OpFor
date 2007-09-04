
import random

from pypy.rlib.rarithmetic import r_ulonglong, intmask

BITS_ON_OFF_1 = r_ulonglong(0xAAAAAAAAAAAAAAAAL)
BITS_ON_OFF_2 = r_ulonglong(0xCCCCCCCCCCCCCCCCL)
BITS_ON_OFF_4 = r_ulonglong(0xF0F0F0F0F0F0F0F0L)
BITS_ON_OFF_8 = r_ulonglong(0xFF00FF00FF00FF00L)
BITS_ON_OFF_16 = r_ulonglong(0xFFFF0000FFFF0000L)
BITS_ON_OFF_32 = r_ulonglong(0xFFFFFFFF00000000L)
BITS_ON_64 = r_ulonglong(0xFFFFFFFFFFFFFFFFL)
BIG_ZERO = r_ulonglong(0)

def bitandix(val):
    assert isinstance(val, r_ulonglong)
    bit = val & ((val ^ BITS_ON_64)+1)
    idx = int((bit & BITS_ON_OFF_1) != BIG_ZERO)
    idx |= ((bit & BITS_ON_OFF_2) != BIG_ZERO) << 1
    idx |= ((bit & BITS_ON_OFF_4) != BIG_ZERO) << 2
    idx |= ((bit & BITS_ON_OFF_8) != BIG_ZERO) << 3
    idx |= ((bit & BITS_ON_OFF_16) != BIG_ZERO) << 4
    idx |= ((bit & BITS_ON_OFF_32) != BIG_ZERO) << 5
    return (bit, idx)

BITS_OFF_ON_1 = r_ulonglong(0x5555555555555555L)
BITS_OFF_ON_2 = r_ulonglong(0x3333333333333333L)
BITS_OFF_ON_4 = r_ulonglong(0x0F0F0F0F0F0F0F0FL)
SUM_POW = r_ulonglong(0x0101010101010101L)

def popcount(val):
    # See http://en.wikipedia.org/wiki/Hamming_weight
    assert isinstance(val, r_ulonglong)
    val -= (val >> 1) & BITS_OFF_ON_1
    val = (val & BITS_OFF_ON_2) + ((val >> 2) & BITS_OFF_ON_2)
    val = (val + (val >> 4)) & BITS_OFF_ON_4
    return intmask((val * SUM_POW) >> 56)

ZOBRIST_PIECE = []
ZOBRIST_LAST_PIECE = []
ZOBRIST_STEP = []
ZOBRIST_SIDE = None
ZOBRIST_INPUSH = None
#lowmask = r_ulonglong(0x3FFFF)
lowmask = r_ulonglong(0xFFFFF)
usedkeys = [r_ulonglong(0)]
highkeys = [r_ulonglong(0)]
lowkeys = [r_ulonglong(0)]

def genzobrist_newkey(rnd):
    candidate = 0
    while 1:
        candidate = r_ulonglong(rnd.randint(0, 2**64))
        lowcan = candidate & lowmask
        if (candidate & lowmask in lowkeys or
            candidate & ~lowmask in highkeys):
            continue
        if (popcount(candidate & lowmask) < 3):
            continue
        if min([popcount(k ^ lowcan) for k in lowkeys]) < 3:
            continue
        if min([popcount(k ^ candidate) for k in usedkeys]) < 5:
            continue
        if (candidate in usedkeys):
            continue
        break
    usedkeys.append(candidate)
    highkeys.append(candidate & ~lowmask)
    lowkeys.append(candidate & lowmask)
    return candidate
    
def generate_zobrist_keys():
    rnd = random.Random()
    rnd.seed(0xF00F)
    used_bits = 0
    # first zero keys for empty squares
    ZOBRIST_PIECE.append([])
    ZOBRIST_LAST_PIECE.append([])
    for index in xrange(65):
        ZOBRIST_PIECE[0].append(0)
        ZOBRIST_LAST_PIECE[0].append(0)
    # then the real keys for pieces
    for piece in xrange(1,13):
        ZOBRIST_PIECE.append([])
        ZOBRIST_LAST_PIECE.append([])
        for index in xrange(64):
            key = genzobrist_newkey(rnd)
            ZOBRIST_PIECE[piece].append(key)
            used_bits |= key
            key = genzobrist_newkey(rnd)
            ZOBRIST_LAST_PIECE[piece].append(key)
            used_bits |= key
        # Add zero key that won't change hash, used when adding and removing a piece from the board.
        ZOBRIST_PIECE[piece].append(0)
        ZOBRIST_LAST_PIECE[piece].append(0)
    assert used_bits == 2**64-1, "Didn't use all bits, %s" % hex(used_bits)
    ZOBRIST_STEP.append(0)
    for step in xrange(4):
        ZOBRIST_STEP.append(genzobrist_newkey(rnd))
    key = 0
    pop = 0
    while pop < 6:
        key = genzobrist_newkey(rnd)
        pop = popcount(key & 0x3FFFF)
    global ZOBRIST_SIDE
    ZOBRIST_SIDE = key
    global ZOBRIST_INPUSH
    key = genzobrist_newkey(rnd)
    ZOBRIST_INPUSH = key

def countbits(val, count):
    bit, ix = bitandix(val)
    while bit:
        val ^= bit
        count[ix] += 1
        bit, ix = bitandix(val)

generate_zobrist_keys()
print "bit distribution"
bitcounts = []
for i in xrange(64):
    bitcounts.append(0)
mindistance = 64
minpop = 64
minlowdist = 64
minlowpop = 64
for num, key in enumerate(usedkeys):
    countbits(key, bitcounts)
    for other in usedkeys[:num]:
        dist = popcount(key ^ other)
        lowdist = popcount((key ^ other) & lowmask)
        if other == 0:
            if dist < minpop:
                minpop = dist
            if lowdist < minlowpop:
                minlowpop = lowdist
            continue
        if lowdist < minlowdist:
            minlowdist = lowdist
        if dist < mindistance:
            mindistance = dist

print "numkeys %d/%g, mindist %d, minpop %d, lowdist %d, lowpop %d" % (
        len(usedkeys), len(usedkeys)/2.0, mindistance, minpop, minlowdist, minlowpop)

maxbit = -1
maxcount = 0
minbit = -1
mincount = 0xFFFFFFFF
tcount = 0
for bit, count in enumerate(bitcounts):
    if count > maxcount:
        maxcount = count
        maxbit = bit
    if count < mincount:
        mincount = count
        minbit = bit
    tcount += count
print "max %d: %d, min %d: %d, avg %.2f" % (maxbit, maxcount, minbit, mincount, tcount/64)

outfile = open('keys.txt', 'w')
outfile.write("// zobrist hash keys for arimaa position module\n\n")
outfile.write("const ulong[][] ZOBRIST_PIECE = [\n")
for piece in xrange(13):
    outfile.write("\t[\n")
    for index in xrange(65):
        outfile.write("\t\t%sUL,\n" % (hex(ZOBRIST_PIECE[piece][index]).rstrip('L')),)
    outfile.write("\t],\n")
outfile.write("];\n\n")

outfile.write("const ulong[][] ZOBRIST_LAST_PIECE = [\n")
for piece in xrange(13):
    outfile.write("\t[\n")
    for index in xrange(65):
        outfile.write("\t\t%sUL,\n" % (hex(ZOBRIST_LAST_PIECE[piece][index]).rstrip('L')),)
    outfile.write("\t],\n")
outfile.write("];\n\n")

outfile.write("const ulong[] ZOBRIST_STEP = [")
for step in xrange(5):
    outfile.write("%sUL," % (hex(ZOBRIST_STEP[step]).rstrip('L')))
outfile.write("];\n")
outfile.write("const ulong ZOBRIST_INPUSH = %sUL;\n" % (hex(ZOBRIST_INPUSH).rstrip('L')))
outfile.write("const ulong ZOBRIST_SIDE = %sUL;\n" % (hex(ZOBRIST_SIDE).rstrip('L')))
outfile.flush()
outfile.close()

