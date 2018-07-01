#ifndef XC_CLOUD_HPP
#define XC_CLOUD_HPP

#include <cassert>
#include <cstring> // memcpy
#include <limits>
#include <type_traits> // unsigned integral type check
#include <utility> // std::swap

namespace xc
{
using std::swap;
template <typename uint>
class cloud
{
  static const uint OFF = 0;
  static const uint ON = ~OFF;

  static constexpr uint* NONE() {return reinterpret_cast<uint*>(OFF);}
  static constexpr uint* ALL() {return reinterpret_cast<uint*>(ON);}
  static constexpr uint* INVALID() {return reinterpret_cast<uint*>(ON << 1);}

  static constexpr uint log(uint i) {return i >>= 1 ? 1 + log(i) : 0;}

  static const uint WIDTH = std::numeric_limits<uint>::digits;
  static const uint LSBS = WIDTH - 1;
  static const uint WIDTH_LOG = log(WIDTH);

  static_assert
  (
    std::numeric_limits<uint>::radix == 2 &&
    std::is_unsigned<uint>::value &&
    std::is_integral<uint>::value &&
    WIDTH && !(WIDTH & LSBS) && // checking WIDTH is a power of 2
    sizeof(uint) == sizeof(uint*),
    "'uint' must be a unsigned integral type with pointer size and 2^N binary digits"
  );

  static uint quo(const uint i) {return i >> WIDTH_LOG;} // quotient by WIDTH
  static uint pack(const uint i) {return uint(1) << (LSBS & i);}
  static uint unpack(uint pack, uint result = 0)
  {
    for (result <<= WIDTH_LOG; pack && !(1 & pack); ++result, pack >>= 1);
    return result;
  }

  uint* p;

  bool isEmpty() const {return p == NONE();}
  bool isFull() const {return p == ALL();}
  bool isAllocated() const {return !isEmpty() && !isFull();}

  uint begin() const {return assert(isAllocated()), p[0];}
  uint size() const {return assert(isAllocated()), p[1];}
  const uint* data() const {return assert(isAllocated()), p + 2;}

  uint* clone() const
  {
    assert(isAllocated());
    const uint pSz = size() + 2;
    static const uint SIZE_LOG = log(sizeof(uint));
    return reinterpret_cast<uint*>(memcpy(new uint[pSz], p, pSz << SIZE_LOG));
  }
  struct pair
  {
    uint b0, b1, e0, e1; const uint *d0, *d1;
    pair(const cloud& c0, const cloud& c1)
    :
      b0(quo(c0.begin())), b1(quo(c1.begin())),
      e0(b0 + c0.size()), e1(b1 + c1.size()),
      d0(c0.data()), d1(c1.data())
    {
      if (b1 < b0) swap(b0, b1), swap(d0, d1);
      if (e0 < e1) swap(e0, e1);
    }
    bool hasOverlap() const {return b1 < e1;}
  };
public:
  cloud(const bool isFull = false) : p(isFull ? ALL() : NONE()) {}
  cloud(const uint i) : p(new uint[3]{i, 1, pack(i)}) {}
  cloud(const cloud& c0, const cloud& c1)
  :
    p(c0.isFull() || c1.isFull() ? ALL() :
      c0.isEmpty() && c1.isEmpty() ? NONE() :
      c0.isEmpty() ? c1.clone() :
      c1.isEmpty() ? c0.clone() :
      INVALID())
  {
    if (p != INVALID()) return;
    pair u(c0, c1);
    const uint dSz = u.e0 - u.b0;
    uint* pI = p = new uint[dSz + 2];
    *pI = u.d0 == c0.data() ? c0.begin() : c1.begin(), *++pI = dSz, ++pI;
    const bool hasOverlap = u.hasOverlap();
    const uint* end = u.d0 + ((hasOverlap ? u.b1 : u.e1) - u.b0);
    for (; u.d0 < end; *pI = *u.d0, ++pI, ++u.d0);
    end = hasOverlap ? u.d1 + (u.e1 - u.b1) : u.d1;
    for (; u.d1 < end; *pI = *u.d0 | *u.d1, ++pI, ++u.d0, ++u.d1);
    for (end = hasOverlap ? pI : pI + (u.b1 - u.e1); pI < end; *pI = 0, ++pI);
    for (end = data() + size(); pI < end; *pI = *u.d1, ++pI, ++u.d1);
  }
  cloud(const cloud& c) : p(c.isFull() ? ALL() : c.isEmpty() ? NONE() : c.clone()) {}
  cloud(cloud&& c) : p(NONE()) {swap(p, c.p);}
  cloud& operator=(cloud c) {return swap(p, c.p), *this;}
  cloud& operator=(cloud&& c) {return swap(p, c.p), *this;}
  ~cloud() {if (isAllocated()) delete[] p;}

  enum Order {INC, DEC, EQU};
  Order cmp(const cloud& c) const
  {
    if (isEmpty()) return c.isEmpty() ? EQU : INC;
    if (c.isEmpty()) return DEC;
    if (isFull()) return c.isFull() ? EQU : DEC;
    if (c.isFull()) return INC;
    if (begin() != c.begin()) return begin() < c.begin() ? INC : DEC;
    if (size() != c.size()) return size() < c.size() ? INC : DEC;
    const uint *d0 = data(), *end = d0 + size(), *d1 = c.data();
    for (; d0 < end && *d0 == *d1; ++d0, ++d1);
    return d0 < end ? *d0 < *d1 ? INC : DEC : EQU;
  }
  enum IntersectionPolicy {DEFAULT, BY_CROSS};
  template<IntersectionPolicy policy = DEFAULT>
  bool isIntersecting(const cloud& c, uint& at0, uint& at1) const
  {
    if (isEmpty() || c.isEmpty()) return false;
    if (isFull() && c.isFull()) return at0 = at1 = ON, true;
    if (isFull()) return at0 = ON, at1 = c.begin(), true;
    if (c.isFull()) return at0 = begin(), at1 = ON, true;
    if (policy == BY_CROSS) return at0 = begin(), at1 = c.begin(), true;
    pair i(*this, c);
    if (!i.hasOverlap()) return false;
    i.d0 += i.b1 - i.b0;
    const uint* end = i.d0 + (i.e1 - i.b1);
    uint pack = 0;
    for (; i.d0 < end && !(pack = *i.d0 & *i.d1); ++i.d0, ++i.d1);
    return pack && (at0 = at1 = unpack(pack, i.e1 + (i.d0 - end)), true);
  }
  bool shift()
  {
    if (!isAllocated()) return false;
    uint sBegin = begin() - 1;
    const uint *pI = data(), *end = pI + size();
    const bool isLeaking = 1 & *pI;
    if (isLeaking)
    {
      if (*pI == 1) for (++pI; pI < end && !*pI; ++pI);
      if (pI == end) return delete[] p, p = NONE(), false;
      const bool noDrop = pI == data();
      sBegin += noDrop + (pI - data() << WIDTH_LOG);
      for (uint pack = *pI >> noDrop; !(1 & pack); ++sBegin, pack >>= 1);
    }
    const bool isReleaking = 1 & *pI, isShrinking = end[-1] == 1;
    const uint sSz = end - pI + isReleaking - isShrinking;
    const bool isReallocating = sSz != size();
    uint *sp = isReallocating ? new uint[sSz + 2] : p, *spI = sp, pB = *pI;
    *spI = sBegin, *++spI = sSz, end = ++spI + sSz, spI += isReleaking;
    for (uint pBn; ++spI < end; pBn = *++pI, spI[-1] = pBn << LSBS | pB >> 1, pB = pBn);
    sp[2] |= isReleaking << LSBS;
    spI[-1] = isShrinking << LSBS | pB >> 1;
    if (isReallocating) delete[] p, p = sp;
    return isLeaking;
  }
  cloud& operator|=(const cloud& c) {return *this = cloud(*this, c);}
};
}

#endif
