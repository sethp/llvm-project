// RUN: %clang_cc1 -verify -std=c++2a -fsyntax-only -fexperimental-new-constant-interpreter -triple x86_64-apple-macosx10.14.0 %s
// RUN: %clang_cc1 -verify -std=c++2a -fsyntax-only -fexperimental-new-constant-interpreter -triple x86_64-apple-macosx10.14.0 %s -fno-signed-char
// RUN: %clang_cc1 -verify -std=c++2a -fsyntax-only -fexperimental-new-constant-interpreter -triple aarch64_be-linux-gnu %s

#if __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
#  define LITTLE_END 1
#elif __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
#  define LITTLE_END 0
#else
#  error "huh?"
#endif

#if 0
namespace min {

// static_assert(__builtin_bit_cast(unsigned, (int)-1) == -1u);

static_assert(sizeof(int) == 4);
static_assert(sizeof(long long) == 8);

using uint8_t = unsigned char;
using uint16_t = unsigned __INT16_TYPE__;
using uint32_t = unsigned __INT32_TYPE__;
using uint64_t = unsigned __INT64_TYPE__;

template <int N, typename T = unsigned char, int Pad = 0>
struct bits {
  T : Pad;
  T bits : N;

  constexpr bool operator==(const T& rhs) const {
    return bits == rhs;
  }
};
template <int N, typename T, int P>
constexpr bool operator==(const struct bits<N, T, P>& lhs, const struct bits<N, T, P>& rhs) {
  return lhs.bits == rhs.bits;
}

template<int N>
struct bytes {
  using size_t = unsigned int;
  unsigned char d[N];

  constexpr unsigned char &operator[](size_t index) {
    if (index < N)
      return d[index];
  }
};


template <class To, class From>
constexpr To bit_cast(const From &from) {
  static_assert(sizeof(To) == sizeof(From));
  return __builtin_bit_cast(To, from);
}
namespace std {
enum byte : unsigned char {};
} // namespace std

struct R {
  unsigned int r : 31;
  unsigned int : 0;
  unsigned int : 32;
  constexpr bool operator==(R const &other) const {
    return r == other.r;
  }
};
using T = bits<31, signed __INT64_TYPE__>;

constexpr R r1 = {0x4ac0ffee};
constexpr R r{0x4ac0ffee};

namespace nested_structs {
  struct J {
    struct {
      uint16_t  k : 12;
    } K;
    struct {
      uint16_t  l : 4;
    } L;
  };

  static_assert(sizeof(J) == 4);
  constexpr J j = bit_cast<J>(0x8c0ffee5);

  static_assert(j.K.k == (LITTLE_END ? 0xee5 : 0x8c0));
  static_assert(j.L.l == 0xf /* yay symmetry */);
  static_assert(bit_cast<bits<4, uint16_t, 16>>(j) == 0xf);
  struct N {
    bits<12, uint16_t> k;
    uint16_t : 16;
  };
  static_assert(bit_cast<N>(j).k == j.K.k);

  struct M {
    bits<4, uint16_t, 0> m[2];
    constexpr bool operator==(const M& rhs) const {
      return m[0] == rhs.m[0] && m[1] == rhs.m[1];
    };
  };

  constexpr M got = bit_cast<M>(j);
  constexpr M want = bit_cast<M>(LITTLE_END == 1
          ? (const uint16_t[2]){0x5, 0xf}
          : (const uint16_t[2]){0x8000, 0xf000}
  );
  static_assert(got == want);
  static_assert(bit_cast<M>(j) == bit_cast<M>(want));
}


#if 0
namespace t {
     struct Q {
      // cf. CGBitFieldInfo
      // on a little-endian machine the bits "[count from] the
      // least-significant-bit."
      // so, by leaving a bit unused, we truncate the value's MSB.

      // however, on a big-endian machine we "imagine the bits
      // counting from the most-significant-bit", so we truncate
      // the LSB here.
      uint16_t q : 15;
    };
    constexpr unsigned char bytes[2] = {0xf3, 0xef};
    // constexpr Q q = bit_cast<Q>(bytes);
    constexpr auto q = __builtin_bit_cast(Q, (const unsigned char[2]){0xf3, 0xef});
    static_assert(q.q == (LITTLE_END ? 0x6ff3 : (0xf3ee >> 1)));
    // static_assert(bit_cast<uint16_t>(bytes) == (LITTLE_END
    // static_assert(__builtin_bit_cast(uint16_t,(const unsigned char[2]){0xf3, 0xef}) == (LITTLE_END
    static_assert(__builtin_bit_cast(uint16_t, bytes) == (LITTLE_END
                                                    ? 0xeff3
                                                    : 0xf3ef),
      "bit-field casting ought to match \"whole\"-field casting");

    // similarly, "skip 1 bit of padding" followed by "read 9 bits"
    // will truncate (shift out) either the LSB (little endian) or MSB (big endian)
    static_assert((0xf3ee >> 1) == 0x79f7);
    static_assert(0x01cf == (0xf3ef >> (16-9-1) & 0x1ff));
    // TODO[seth]: bit_cast<bits<9, uint16_t, 1>>(q)
    static_assert(__builtin_bit_cast(bits<9, uint16_t, 1>, Q{(LITTLE_END ? 0x6ff3 : (0xf3ee >> 1))}) == (LITTLE_END
                                                              ? (0xeff3 >> 1) & 0x1ff
                                                              : (0xf3ef >> (16-9-1)) & 0x1ff));
    static_assert(__builtin_bit_cast(bits<9, uint16_t, 1>, q) == (LITTLE_END
                                                              ? (0xeff3 >> 1) & 0x1ff
                                                              : (0xf3ef >> (16-9-1)) & 0x1ff));
    static_assert(bit_cast<bits<9, uint16_t, 1>>(q) == (LITTLE_END
                                                              ? (0xeff3 >> 1) & 0x1ff
                                                              : (0xf3ef >> (16-9-1)) & 0x1ff));

    #if LITTLE_END == 0
    // expected-note@+5 {{bit [0]}}
    #else
    // expected-note@+3 {{bit [15]}}
    #endif
    // expected-error@+1 {{constant expression}}
    constexpr auto _i = __builtin_bit_cast(bits<15, uint16_t, 1>, q);
    // expected-note@-1 {{indeterminate}}
}
#endif

void wrapper() {
  constexpr auto f = []() constexpr {
    // bits<24, unsigned int, LITTLE_END ? 0 : 8> B = {0xc0ffee};
    // constexpr struct { unsigned short b1; unsigned char b0;  } B = {0xc0ff, 0xee};
    // return bytes<4>{0xc0, 0xff, 0xee};
    // return (const char[4]){0xc0, 0xff, 0xee};
    return 0;
  };

  constexpr auto g = [](auto f) constexpr {
    return f();
  };
  // constexpr auto g = [f]() constexpr {
  //   return f();
  // };
  static_assert(g(f) == f());
}

// template <class Intermediate, class Init>
// constexpr Init round_trip(const Init &init) {
//   return bit_cast<Init>(bit_cast<Intermediate>(init));
// }
template <class Intermediate, class Init>
constexpr Init round_trip(const Init &init) {
  auto zz = bit_cast<Intermediate>(init);
  return bit_cast<Init>(zz);
}
void test_record() {
  struct int_splicer {
    unsigned x;
    unsigned y;

    constexpr bool operator==(const int_splicer &other) const {
      return other.x == x && other.y == y;
    }
  };

  constexpr int_splicer splice{0x0C05FEFE, 0xCAFEBABE};

  // static_assert(bit_cast<unsigned long long>(splice) == (LITTLE_END
  //                                                            ? 0xCAFEBABE0C05FEFE
  //                                                            : 0x0C05FEFECAFEBABE));

  // static_assert(bit_cast<int_splicer>(0xCAFEBABE0C05FEFE).x == (LITTLE_END
  //                                                                   ? 0x0C05FEFE
  //                                                                   : 0xCAFEBABE));

  // static_assert(round_trip<unsigned long long>(splice) == splice);
  // static_assert(round_trip<long long>(splice) == splice);

  struct base2 {
  };

  struct base3 {
    unsigned z;
  };


  struct bases : int_splicer, base2, base3 {
    unsigned doublez;
  };

  struct tuple4 {
    unsigned x, y, z, doublez;

    bool operator==(tuple4 const &other) const = default;
    constexpr bool operator==(bases const &other) const {
      return x == other.x && y == other.y &&
             z == other.z && doublez == other.doublez;
    }
  };
  // constexpr bases b = {{1, 2}, {}, {3}, 4};
  // constexpr tuple4 t4 = bit_cast<tuple4>(b);
  // static_assert(t4 == tuple4{1, 2, 3, 4});
  // static_assert(round_trip<tuple4>(b) == b);

  // static_assert(bit_cast<bases>(t4) == b);
  // constexpr auto b2 = bit_cast<bases>(t4);
  constexpr auto b3 = bit_cast<bases>(tuple4{1, 2, 3, 4});
  // static_assert(t4 == b2);

  // static_assert(round_trip<bases>(t4) == t4);

  // // constexpr bases bb;
  // // constexpr auto zzt = bit_cast<bases>(t4);
  // // static_assert(zzt.x == b.x);

  // constexpr auto zz = bit_cast<tuple4>(b);
  // static_assert(zz.doublez == b.doublez);
  // static_assert(bit_cast<bases>(zz) == b);
  // // static_assert(round_trip<tuple4>(b) == b);

  // constexpr auto BB = bit_cast<bases>(tuple4{1, 2, 3, 4});
  // static_assert(BB.x == 1 && BB.y == 2 && BB.z == 3 && BB.doublez == 4);
}


} // namespace min

#else
#include "./constexpr-builtin-bit-cast.cpp"
#endif
