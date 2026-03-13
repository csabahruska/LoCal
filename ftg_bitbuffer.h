/* ftg_bitbuffer  - public domain library
   no warranty implied; use at your own risk

   Tightly pack values by bits into a stream of bytes.

   For example, a 1-bit bool and a 32-bit integer are packed into 33
   bits.

   Bitbuffers are intended for small amounts of data, like a few
   hundred network packets where size is important enough to remove
   padding bits, and the cpu overhead of packing/unpacking intermixed
   types is not a huge cost.

   FEATURES

    - Compiles C99 warnings-free on clang and visual c++

    - Pack integers with arbitrary numbers of bits

    - Supports quantized floating point packing

    - Possible to avoid heap allocations and copies on read

   USAGE

   Do this:
   #define FTG_IMPLEMENT_BITBUFFER

   before you include this file in one C or C++ file to create the
   implementation.

   It should look like this:
   #include ...
   #include ...
   #include ...
   #define FTG_IMPLEMENT_BITBUFFER
   #include "ftg_bitbuffer.h"

   REVISION HISTORY

   0.1  2023-01-12   Initial version

   USAGE NOTIFICATION REQUEST

   If permitted, emailing the author and notifying him that the
   software was used (and how) helps inform him of where he should
   spend his time.  This step is totally optional, but appreciated!

   AUTHOR

   Michael Labbe    https://www.frogtoss.com/pages/contact.html

   LICENSE

   This software is in the public domain. Where that dedication is not
   recognized, you are granted a perpetual, irrevocable license to
   copy, distribute, and modify this file as you see fit by sole
   copyright holder Frogtoss Games, Inc.

   SPECIAL THANKS

   Nick Waanders - quantization functions
*/

#ifndef BITBUF__INCLUDE_BITBUFFER_H
#define BITBUF__INCLUDE_BITBUFFER_H

//// DOCUMENTATION
////
// Known limitations:
//
//  - This code does not take any action to manage endianness.
//
//  - The buffer size must be known at start; bitbuffers are not stretchy
//
//  - The floating point quantization function is not guaranteed to
//    output out_min == in_min, or out_max == in_max, except for the
//    ranges [0,1] and [-1,1]
//
//// Basic Usage
//
//            write values to the buffer
//  bitbuf_buffer_t buf = bitbuf_alloc_buffer(256);
//  bitbuf_write_bool(&buf, true);
//  bitbuf_write_int32(&buf, -32);
//  bitbuf_write_cstr(&buf, "hello, world");
//  bitbuf_write_float(&buf, -325.32f);
//
//            check for truncation during writes
//  assert(!bitbuf_has_truncated(&buf));
//
//            read values from the buffer
//
//            a bitbuf_cursor_t aligns to the next bit to read.  After
//            writing completes, it is thread-safe to have multiple
//            read cursors for a single bitbuffer
//
// bitbuf_cursor_t read = bitbuf_cursor_init(&buf);
// assert(bitbuf_read_bool(&read) == true);
// assert(bitbuf_read_int32(&read) == -32);
//
//            read a cstring, up until serialized NULL terminator
// char str[256];
// bitbuf_read_cstr(&read, 256, str);
// assert(strcmp(str, "hello, world") == 0);
//
// assert(bitbuf_read_float(&read) == -325.32f);
//
//            free allocated buffer
// bitbuf_free_buffer(&buf);

#include <inttypes.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>

#if defined(__GNUC__) || defined(__clang__)
#    define BITBUF_EXT_unused __attribute__((unused))
#else
#    define BITBUF_EXT_unused
#endif

#ifdef BITBUF_BITBUFFER_STATIC
#    define BITBUFDEF static BITBUF_EXT_unused
#else
#    define BITBUFDEF extern
#endif

#if defined(BITBUF_MALLOC) && defined(BITBUF_FREE)
// okay
#elif !defined(BITBUF_MALLOC) && !defined(BITBUF_FREE)
// also okay
#else
#    error "Must define both or none of BITBUF_MALLOC and BITBUF_FREE"
#endif

#ifndef BITBUF_MALLOC
#    define BITBUF_MALLOC(size) malloc(size)
#    define BITBUF_FREE(ptr) free(ptr)
#endif

// include ftg_core.h ahead of this header to debug it
#ifdef FTG_ASSERT
#    define BITBUF__ASSERT(exp) FTG_ASSERT(exp)
#    define BITBUF__ASSERT_FAIL(exp) FTG_ASSERT_FAIL(exp)
#else
#    define BITBUF__ASSERT(exp) (assert(exp))
#    define BITBUF__ASSERT_FAIL(exp) (assert(exp))
#endif

#if defined(__GNUC__) || defined(__clang__)
#    if __STDC_VERSION__ < 199901L
#        define BITBUF_INLINE __inline
#    else
#        define BITBUF_INLINE inline
#    endif
#elif defined(_MSC_VER) && (_MSC_VER >= 1700)
#    define BITBUF_INLINE __inline
#endif

#ifdef __cplusplus
#    extern "C"
#endif


// API declaration starts here

typedef struct {
    // seg == data when at beginning
    uint64_t* seg;

    // indicates how many bytes into seg, <= 63
    int bits_into_seg;
} my_cursor_t;


// bitbuf write routines
BITBUFDEF void my_write_int64(my_cursor_t, int64_t value);
BITBUFDEF void my_write_int32(my_cursor_t, int32_t value);
BITBUFDEF void my_write_int16(my_cursor_t, int16_t value);
BITBUFDEF void my_write_int8(my_cursor_t, int8_t value);
BITBUFDEF void my_write_uint64(my_cursor_t, uint64_t value);
BITBUFDEF void my_write_uint32(my_cursor_t, uint32_t value);
BITBUFDEF void my_write_uint16(my_cursor_t, uint16_t value);
BITBUFDEF void my_write_uint8(my_cursor_t, uint8_t value);
BITBUFDEF void my_write_bool(my_cursor_t, bool);

// bitbuf read routines
BITBUFDEF int64_t  my_read_int64(my_cursor_t read);
BITBUFDEF int32_t  my_read_int32(my_cursor_t read);
BITBUFDEF int16_t  my_read_int16(my_cursor_t read);
BITBUFDEF int8_t   my_read_int8(my_cursor_t read);
BITBUFDEF uint64_t my_read_uint64(my_cursor_t read);
BITBUFDEF uint32_t my_read_uint32(my_cursor_t read);
BITBUFDEF uint16_t my_read_uint16(my_cursor_t read);
BITBUFDEF uint8_t  my_read_uint8(my_cursor_t read);
BITBUFDEF bool     my_read_bool(my_cursor_t read);


//
// End of header file
//
#endif /* BITBUF__INCLUDE_BITBUFFER_H */

/* implementation */
#if defined(FTG_IMPLEMENT_BITBUFFER)

#define BITBUF__SEG_BITS 64

#define BITBUF__PUN(in_type)                                                   \
    union pun_u {                                                              \
        in_type  value;                                                        \
        uint64_t u64;                                                          \
    } pun;

#define MY__READ_TYPE(in_type, bit_count)                                  \
    BITBUF__PUN(in_type)                                                       \
    pun.u64 = my__read_bits(read, bit_count);

#define MY__WRITE_TYPE(BUF, in_type)                                       \
    BITBUF__PUN(in_type)                                                       \
    pun.value = value;                                                         \
    my__write_bits(BUF, pun.u64, sizeof(in_type) * 8);

#define MY__DECL_WRITE(in_type, in_name)                                   \
    BITBUFDEF void my_write_##in_name(my_cursor_t buf, in_type value) \
    {                                                                          \
        MY__WRITE_TYPE(buf, in_type);                                      \
    }

#define MY__DECL_WRITE_T(in_type) MY__DECL_WRITE(in_type##_t, in_type)

#define MY__DECL_READ(in_type, in_name)                                    \
    BITBUFDEF in_type my_read_##in_name(my_cursor_t read)             \
    {                                                                          \
        MY__READ_TYPE(in_type, sizeof(in_type) * 8);                       \
        return pun.value;                                                      \
    }

#define MY__DECL_READ_T(in_type) MY__DECL_READ(in_type##_t, in_type)

/* clang-format off */
static const uint64_t bitbuf__spanmasktable[65] = {
    0,
    (1ull << 1) - 1, (1ull << 2) - 1, (1ull << 3) - 1, (1ull << 4) - 1,
    (1ull << 5) - 1, (1ull << 6) - 1, (1ull << 7) - 1, (1ull << 8) - 1,
    (1ull << 9) - 1, (1ull << 10) - 1, (1ull << 11) - 1, (1ull << 12) - 1,
    (1ull << 13) - 1, (1ull << 14) - 1, (1ull << 15) - 1, (1ull << 16) - 1,
    (1ull << 17) - 1, (1ull << 18) - 1, (1ull << 19) - 1, (1ull << 20) - 1,
    (1ull << 21) - 1, (1ull << 22) - 1, (1ull << 23) - 1, (1ull << 24) - 1,
    (1ull << 25) - 1, (1ull << 26) - 1, (1ull << 27) - 1, (1ull << 28) - 1,
    (1ull << 29) - 1, (1ull << 30) - 1, (1ull << 31) - 1, (1ull << 32) - 1,
    (1ull << 33) - 1, (1ull << 34) - 1, (1ull << 35) - 1, (1ull << 36) - 1,
    (1ull << 37) - 1, (1ull << 38) - 1, (1ull << 39) - 1, (1ull << 40) - 1,
    (1ull << 41) - 1, (1ull << 42) - 1, (1ull << 43) - 1, (1ull << 44) - 1,
    (1ull << 45) - 1, (1ull << 46) - 1, (1ull << 47) - 1, (1ull << 48) - 1,
    (1ull << 49) - 1, (1ull << 50) - 1, (1ull << 51) - 1, (1ull << 52) - 1,
    (1ull << 53) - 1, (1ull << 54) - 1, (1ull << 55) - 1, (1ull << 56) - 1,
    (1ull << 57) - 1, (1ull << 58) - 1, (1ull << 59) - 1, (1ull << 60) - 1,
    (1ull << 61) - 1, (1ull << 62) - 1, 0x7fffffffffffffff, 0xffffffffffffffff,
};
/* clang-format on */

static BITBUF_INLINE void
my__advance_cursor_seg(my_cursor_t* cursor)
{
    cursor->bits_into_seg = 0;
    cursor->seg++;
}

BITBUFDEF my_cursor_t
my__advance_cursor(my_cursor_t write, int num_bits)
{
    int bits_remaining_in_seg = BITBUF__SEG_BITS - write.bits_into_seg;

    // do the bits fit in the current seg?
    if (num_bits <= bits_remaining_in_seg) {

        write.bits_into_seg += num_bits;

        if (write.bits_into_seg == BITBUF__SEG_BITS) {
            my__advance_cursor_seg(&write);
        }
        return write;
    } else {
        // no - write the bits for the current segment and call recursively
        // to do the remainder

        my__advance_cursor_seg(&write);

        int num_bits_remaining_for_next_write = num_bits - bits_remaining_in_seg;
        my__advance_cursor(write, num_bits_remaining_for_next_write);
    }
}

BITBUFDEF void
my__write_bits(my_cursor_t write, uint64_t datum, int num_bits)
{
    int bits_remaining_in_seg = BITBUF__SEG_BITS - write.bits_into_seg;

    // do the bits fit in the current seg?
    if (num_bits <= bits_remaining_in_seg) {
        const uint64_t SRC_MASK = bitbuf__spanmasktable[num_bits];
        *write.seg |= (datum & SRC_MASK) << write.bits_into_seg;

    } else {
        // no - write the bits for the current segment and call recursively
        // to do the remainder
        const uint64_t SRC_MASK = bitbuf__spanmasktable[bits_remaining_in_seg];
        *write.seg |= (datum & SRC_MASK)
                              << (BITBUF__SEG_BITS - bits_remaining_in_seg);

        my__advance_cursor_seg(&write);

        int num_bits_remaining_for_next_write = num_bits - bits_remaining_in_seg;
        const uint64_t OVER_MASK =
            bitbuf__spanmasktable[num_bits_remaining_for_next_write]
            << (bits_remaining_in_seg);
        my__write_bits(write,
                           (datum & OVER_MASK) >> bits_remaining_in_seg,
                           num_bits_remaining_for_next_write);
    }
}

// read up to 64 bits into *out_bits
BITBUFDEF uint64_t
my__read_bits(my_cursor_t read, int num_bits)
{
    int bits_remaining_in_seg = BITBUF__SEG_BITS - read.bits_into_seg;

    // are there enough bits in the current seg?
    if (num_bits <= bits_remaining_in_seg) {
        const uint64_t DST_MASK = bitbuf__spanmasktable[num_bits] << read.bits_into_seg;

        uint64_t val = (*read.seg & DST_MASK) >> read.bits_into_seg;

        return val;
    } else {
        // no - read the bits for the current segment and then
        // subsequently read the rest
        const uint64_t DST_MASK = bitbuf__spanmasktable[bits_remaining_in_seg]
                                  << (BITBUF__SEG_BITS - bits_remaining_in_seg);

        uint64_t val =
            (*read.seg & DST_MASK) >> (BITBUF__SEG_BITS - bits_remaining_in_seg);

        my__advance_cursor_seg(&read);
        int next_read_num_bits = num_bits - bits_remaining_in_seg;

        uint64_t OVER_MASK = bitbuf__spanmasktable[next_read_num_bits];

        val |= (*read.seg & OVER_MASK) << bits_remaining_in_seg;

        return val;
    }
}

static BITBUF_INLINE
my_cursor_t my_alloc_buffer() {
  my_cursor_t c = {.seg = malloc(16*1024), .bits_into_seg = 0};
  return c;
}

static BITBUF_INLINE
int64_t cursor_to_int64(my_cursor_t c) {
  return ((int64_t)c.seg) << 3 | c.bits_into_seg;
}

static BITBUF_INLINE
my_cursor_t int64_to_cursor(int64_t i) {
  my_cursor_t c = {.seg = i >> 3, .bits_into_seg = i & 7};
  return c;
}

void my_copy_bits(my_cursor_t dst, my_cursor_t src, int len) {
  while (len >= BITBUF__SEG_BITS) {
    my__write_bits(dst, my__read_bits(src, BITBUF__SEG_BITS), BITBUF__SEG_BITS);
    dst = my__advance_cursor(dst, BITBUF__SEG_BITS);
    src = my__advance_cursor(src, BITBUF__SEG_BITS);
    len -= BITBUF__SEG_BITS;
  }
  if (len > 0) {
    my__write_bits(dst, my__read_bits(src, len), len);
  }
}

MY__DECL_WRITE_T(int64);
MY__DECL_WRITE_T(int32);
MY__DECL_WRITE_T(int16);
MY__DECL_WRITE_T(int8);
MY__DECL_WRITE_T(uint64);
MY__DECL_WRITE_T(uint32);
MY__DECL_WRITE_T(uint16);
MY__DECL_WRITE_T(uint8);

BITBUFDEF void
my_write_bool(my_cursor_t buf, bool value)
{
    BITBUF__PUN(bool);
    pun.value = value;
    my__write_bits(buf, pun.u64, 1);
}

MY__DECL_READ_T(int64);
MY__DECL_READ_T(int32);
MY__DECL_READ_T(int16);
MY__DECL_READ_T(int8);
MY__DECL_READ_T(uint64);
MY__DECL_READ_T(uint32);
MY__DECL_READ_T(uint16);
MY__DECL_READ_T(uint8);

BITBUFDEF bool
my_read_bool(my_cursor_t read)
{
    MY__READ_TYPE(bool, 1);
    return pun.value;
}


#endif /* defined(BITBUF_IMPLEMENT_BITBUFFER) */
