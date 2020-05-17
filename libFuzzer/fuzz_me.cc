#include <stdint.h>
#include <stddef.h>

#include <stdio.h>
#include <stdlib.h>
#include <string>
#include <vector>

#include "bigint.h"
#include "divide.h"
#include "mp_core.h"

inline bool division_check(Botan::word q, Botan::word y2, Botan::word y1,
                           Botan::word x3, Botan::word x2, Botan::word x1)
   {
   /*
   Compute (y3,y2,y1) = (y2,y1) * q
   and return true if (y3,y2,y1) > (x3,x2,x1)
   */

   Botan::word y3 = 0;
   y1 = Botan::word_madd2(q, y1, &y3);
   y2 = Botan::word_madd2(q, y2, &y3);

   const Botan::word x[3] = { x1, x2, x3 };
   const Botan::word y[3] = { y1, y2, y3 };

   return Botan::bigint_ct_is_lt(x, 3, y, 3).is_set();
   }


/*
* Handle signed operands, if necessary
*/
void sign_fixup(const Botan::BigInt& x, const Botan::BigInt& y, Botan::BigInt& q, Botan::BigInt& r)
   {
   q.cond_flip_sign(x.sign() != y.sign());

   if(x.is_negative() && r.is_nonzero())
      {
      q -= 1;
      r = y.abs() - r;
      }
   }

/*
* Solve x = q * y + r
*
* See Handbook of Applied Cryptography section 14.2.5
*/
void divide(const Botan::BigInt& x, const Botan::BigInt& y_arg, Botan::BigInt& q_out, Botan::BigInt& r_out) {
    if(y_arg.is_zero())
        throw Botan::BigInt::DivideByZero();

    const size_t y_words = y_arg.sig_words();

    BOTAN_ASSERT_NOMSG(y_words > 0);

    Botan::BigInt y = y_arg;

    Botan::BigInt r = x;
    Botan::BigInt q = 0;
    Botan::secure_vector<Botan::word> ws;

    r.set_sign(Botan::BigInt::Positive);
    y.set_sign(Botan::BigInt::Positive);

    // Calculate shifts needed to normalize y with high bit set
    const size_t shifts = y.top_bits_free();

    y <<= shifts;
    r <<= shifts;

    // we know y has not changed size, since we only shifted up to set high bit
    const size_t t = y_words - 1;
    const size_t n = std::max(y_words, r.sig_words()) - 1; // r may have changed size however

    q.grow_to(n - t + 1);

    Botan::word* q_words = q.mutable_data();

    Botan::BigInt shifted_y = y << (BOTAN_MP_WORD_BITS * (n-t));

    // Set q_{n-t} to number of times r > shifted_y
    q_words[n-t] = r.reduce_below(shifted_y, ws);

    const Botan::word y_t0  = y.word_at(t);
    const Botan::word y_t1  = y.word_at(t-1);

    for(size_t j = n; j != t; --j) {
        const Botan::word x_j0  = r.word_at(j);
        const Botan::word x_j1 = r.word_at(j-1);
        const Botan::word x_j2 = r.word_at(j-2);

        Botan::word qjt = Botan::bigint_divop(x_j0, x_j1, y_t0);

        qjt = Botan::CT::Mask<Botan::word>::is_equal(x_j0, y_t0).select(Botan::MP_WORD_MAX, qjt);

        // Per HAC 14.23, this operation is required at most twice
        qjt -= division_check(qjt, y_t0, y_t1, x_j0, x_j1, x_j2);
        qjt -= division_check(qjt, y_t0, y_t1, x_j0, x_j1, x_j2);

        shifted_y >>= BOTAN_MP_WORD_BITS;
        // Now shifted_y == y << (BOTAN_MP_WORD_BITS * (j-t-1))

        r -= qjt * shifted_y;
        qjt -= r.is_negative();
        r += static_cast<Botan::word>(r.is_negative()) * shifted_y;

        q_words[j-t-1] = qjt;
    }

    r >>= shifts;

    sign_fixup(x, y_arg, q, r);

    r_out = r;
    q_out = q;
}

extern "C" int LLVMFuzzerTestOneInput(const uint8_t *Data, size_t Size) {
    static Botan::BigInt x, y, q, r;

    x = Botan::BigInt::decode(Data, Size / 2);
    y = Botan::BigInt::decode(Data + Size / 2, Size / 2);    

    divide(x, y, q, r);

    return 0;
}
