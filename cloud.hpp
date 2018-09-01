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

  static constexpr auto* NONE() {return reinterpret_cast<uint*>(OFF);}
  static constexpr auto* ALL() {return reinterpret_cast<uint*>(ON);}
  static constexpr auto* INVALID() {return reinterpret_cast<uint*>(ON << 1);}

  static constexpr uint log(uint i) {return i >>= 1, i ? 1 + log(i) : 0;}

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

  static auto quo(uint i) {return i >> WIDTH_LOG;} // quotient by WIDTH
  static auto pack(uint i) {return uint(1) << (LSBS & i);}
  static auto unpack(uint pack, uint result = 0)
  {
    for (result <<= WIDTH_LOG; pack && !(1 & pack); ++result, pack >>= 1);
    return result;
  }

  uint* p;

  bool isEmpty() const {return p == NONE();}
  bool isFull() const {return p == ALL();}
  bool isAllocated() const {return !isEmpty() && !isFull();}

  auto begin() const {return assert(isAllocated()), p[0];}
  auto size() const {return assert(isAllocated()), p[1];}
  auto* data() const {return assert(isAllocated()), p + 2;}

  auto* clone() const
  {
    assert(isAllocated());
    auto pSz = size() + 2;
    static const auto SIZE_LOG = log(sizeof(uint));
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
  cloud(uint* p) : p(p) {}
public:
  cloud(bool isFull = false) : p(isFull ? ALL() : NONE()) {}
  cloud(uint i) : p(new uint[3]{i, 1, pack(i)}) {}
  cloud(const cloud& c) : p(c.isFull() ? ALL() : c.isEmpty() ? NONE() : c.clone()) {}
  cloud(cloud&& c) : p(NONE()) {swap(p, c.p);}
  cloud& operator=(const cloud& c) {cloud cc(c); return swap(p, cc.p), *this;}
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
    auto *d0 = data(), *end = d0 + size(), *d1 = c.data();
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
    auto* end = i.d0 + (i.e1 - i.b1);
    uint pack = 0;
    for (; i.d0 < end && !(pack = *i.d0 & *i.d1); ++i.d0, ++i.d1);
    return pack && (at0 = at1 = unpack(pack, i.e1 + (i.d0 - end)), true);
  }
  bool shift()
  {
    if (!isAllocated()) return false;
    auto sBegin = begin() - 1;
    auto *pI = data(), *end = pI + size();
    bool isLeaking = 1 & *pI;
    if (isLeaking)
    {
      if (*pI == 1) for (++pI; pI < end && !*pI; ++pI);
      if (pI == end) return delete[] p, p = NONE(), false;
      bool noDrop = pI == data();
      sBegin += noDrop + ((pI - data()) << WIDTH_LOG);
      for (auto pack = *pI >> noDrop; !(1 & pack); ++sBegin, pack >>= 1);
    }
    bool isReleaking = 1 & *pI, isShrinking = end[-1] == 1;
    uint sSz = end - pI + isReleaking - isShrinking;
    bool isReallocating = sSz != size();
    auto *sp = isReallocating ? new uint[sSz + 2] : p, *spI = sp, pB = *pI;
    *spI = sBegin, *++spI = sSz, end = ++spI + sSz, spI += isReleaking;
    for (uint pBn; ++spI < end; pBn = *++pI, spI[-1] = pBn << LSBS | pB >> 1, pB = pBn);
    sp[2] |= uint(isReleaking) << LSBS;
    spI[-1] = uint(isShrinking) << LSBS | pB >> 1;
    if (isReallocating) delete[] p, p = sp;
    return isLeaking;
  }
  friend auto operator|(const cloud& c0, const cloud& c1)
  {
    if (c0.isFull() || c1.isFull()) return cloud(true);
    if (c0.isEmpty() && c1.isEmpty()) return cloud(false);
    if (c0.isEmpty()) return cloud(c1.clone());
    if (c1.isEmpty()) return cloud(c0.clone());
    pair u(c0, c1);
    auto dSz = u.e0 - u.b0;
    auto* p = new uint[dSz + 2], pI = p;
    *pI = u.d0 == c0.data() ? c0.begin() : c1.begin(), *++pI = dSz, ++pI;
    bool hasOverlap = u.hasOverlap();
    auto* end = u.d0 + ((hasOverlap ? u.b1 : u.e1) - u.b0);
    for (; u.d0 < end; *pI = *u.d0, ++pI, ++u.d0);
    end = hasOverlap ? u.d1 + (u.e1 - u.b1) : u.d1;
    for (; u.d1 < end; *pI = *u.d0 | *u.d1, ++pI, ++u.d0, ++u.d1);
    for (end = hasOverlap ? pI : pI + (u.b1 - u.e1); pI < end; *pI = 0, ++pI);
    for (end = p + dSz + 2; pI < end; *pI = *u.d1, ++pI, ++u.d1);
    return cloud(p);
  }
  auto& operator|=(const cloud& c) {return *this = *this | c;}
};
}

#endif
