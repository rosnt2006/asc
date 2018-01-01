#ifndef MODEL_HPP
#define MODEL_HPP

#include <cstdint>
#include <cstring>
#include <limits>
#include <type_traits>

namespace asc
{
template <typename Small = uint8_t, typename Big = uint64_t>
class Model
{
private:
  static_assert(std::is_unsigned<Small>::value);
  static_assert(std::is_unsigned<Big>::value);
  static_assert(std::numeric_limits<Small>::radix == 2);
  static_assert(std::numeric_limits<Big>::radix == 2);

  class Blob
  {
  private:
    static const Big M_0 = 0;
    static const Big M_1 = ~M_0;

    static const Big POS_INF = M_1 >> 1;
    static const Big NEG_INF = ~POS_INF;

    static const Big* NONE = &M_0;
    static const Big* ALL = &M_1;

    static const Small S_SZ = std::numeric_limits<Small>::digits;
    static const Small B_SZ = std::numeric_limits<Big>::digits;

    static template<Big b> Small log() {return 1 + log<b>>1>();}
    static template<> Small log<1>() {return 0;}
    static const Small S_SZ_LOG = log<S_SZ>();
    static const Small B_SZ_LOG = log<B_SZ>();
    static const Small BS_SZ_LOG = B_SZ_LOG - S_SZ_LOG;

    static template<Big b> Big modMsk() {return b | modMsk<b>>1>();}
    static template<> Big modMsk<0>() {return 0;}
    static const Big B_SZ_MOD_MSK = modMsk<B_SZ_LOG>>1>();

    static Big quo(const Big b) {return b >> B_SZ_LOG;}
    static Big mod(const Big b) {return B_SZ_MOD_MSK & b;}
    static Big modFlg(const Big b) {return 1 << mod(b);}
    static Big invDiv(Big quo, Big modFlg)
    {
      for (quo <<= B_SZ_LOG; modFlg && !(1 & modFlg); modFlg >>= 1, ++quo);
      return quo;
    }
    static Big sgnd(const Big i) {return i + NEG_INF;}
    static bool cmp(const Big b0, const Big b1) {return sgnd(b0) < sgnd(b1);}

    const Big* b = NONE;

    bool isEmpty() const {return b == NONE;}
    bool isFull() const {return b == ALL;}
    bool isAllocated() const {return !isEmpty() && !isFull();}
    Big begin() const {assert(isAllocated()); return b[0];}
    Big size() const {assert(isAllocated()); return b[1];}
    const Big* data() const {assert(isAllocated()); return b + 2;}

    void set(const Blob bo)
    {
      assert(isEmpty() && bo.isAllocated());
      const Big boSize = 2 + bo.size();
      Big* newBo = b = new Big[boSize];
      memcpy((void*)newBo, (void*)bo.data(), boSize << BS_SZ_LOG);
    }

  public:
    void set() {assert(isEmpty()); b = ALL;}
    void set(const Big i) {assert(isEmpty()); b = new Big[3]{quo(i), 1, modFlg(i)};}
    void set(const Blob b0, const Blob b1)
    {
      assert(isEmpty());
      if (b0.isFull() || b1.isFull()) return b = ALL, {};
      if (b0.isEmpty() && b1.isEmpty()) return b = NONE, {};
      if (b0.isEmpty()) return set(b1);
      if (b1.isEmpty()) return set(b0);
      Big begin0 = b0.begin();
      Big begin1 = b1.begin();
      Big end0 = begin0 + b0.size();
      Big end1 = begin1 + b1.size();
      const Big* bo0 = b0.data();
      const Big* bo1 = b1.data();
      if (cmp(begin1, begin0)) std::swap(begin0, begin1), std::swap(bo0, bo1);
      if (cmp(end0, end1)) std::swap(end0, end1);
      const bool overlap = cmp(begin1, end1);
      const Big size = end0 - begin0;
      Big* bo = b = new Big[size + 2];
      *bo = begin0, *++bo = size, ++bo;
      const Big* end = bo0 + ((overlap ? begin1 : end1) - begin0);
      for (; bo0 < end; *bo = *bo0, ++bo, ++bo0);
      end = overlap ? bo1 + (end1 - begin1) : bo1;
      for (; bo1 < end; *bo = *bo0 | *bo1, ++bo, ++bo0, ++bo1);
      for (end = overlap ? bo : bo + (begin1 - end1); bo < end; *bo = 0, ++bo);
      for (end = data() + size; bo < end; *bo = *bo1, ++bo, ++bo1);
    }
    enum Order : Small {INC, DEC, EQ};
    Order cmp(const Blob b) const
    {
      if (isEmpty()) return b.isEmpty() ? EQ : INC;
      if (b.isEmpty()) return isEmpty() ? EQ : DEC;
      if (isFull()) return b.isFull() ? EQ : DEC;
      if (b.isFull()) return isFull() ? EQ : INC;
      if (begin() != b.begin()) return cmp(begin(), b.begin()) ? INC : DEC;
      if (size() != b.size()) return size() < b.size() ? INC : DEC;
      const Big *bo0 = data(), *end = bo0 + size(), *bo1 = b.data();
      for (; bo0 < end && *bo0 == *bo1; ++bo0, ++bo1);
      return bo0 < end ? *bo0 < *bo1 ? INC : DEC : EQ;
    }
    template<bool force = false>
    bool contradicts(const Blob b, Blob& error) const
    {
      if (isEmpty() || b.isEmpty()) return false;
      if (isFull() && b.isFull()) return error = NEG_INF, true;
      if (isFull()) return error = invDiv(b.begin(), *b.data()), true;
      if (b.isFull() || force) return error = invDiv(begin(), *data()), true;
      Big begin0 = begin();
      Big begin1 = b.begin();
      Big end0 = begin0 + size();
      Big end1 = begin1 + b.size();
      const Big* bo0 = data();
      const Big* bo1 = b.data();
      if (cmp(begin1, begin0)) std::swap(begin0, begin1), std::swap(bo0, bo1);
      if (cmp(end0, end1)) std::swap(end0, end1);
      const bool overlap = cmp(begin1, end1);
      if (!overlap) return false;
      bo0 += begin1 - begin0;
      const Big* end = bo0 + (end1 - begin1);
      Big bo = 0;
      for (; bo0 < end && !(bo = *bo0 & *bo1); ++bo0, ++bo1);
      return bo ? (error = invDiv(end1 + (bo0 - end), bo), true) : false;
    }
    template<bool drop = false>
    void shift()
    {
      if (!isAllocated()) return;
      const bool leak = !drop && 1 & *data();
      const bool grow = leak && *(data() + size() - 1) != 1;
      Big *newB = grow ? new Big[size() + 3] : (Big*)b, *nbo = newB;
      *nbo = begin() - leak, *++nbo = size() + grow;
      const Big *bo = data(), *end = nbo + 1 + *nbo;
      if (leak) *++nbo = *bo << B_SZ_MOD_MSK;
      *++nbo = *bo >> 1;
      for (Big* nnbo = nbo + 1; nnbo < end; ++nbo, ++nnbo)
      {
        *nbo |= *++bo << B_SZ_MOD_MSK;
        *nnbo = *bo >> 1;
      }
      delete[] b, b = newB;
    }
    void clear() {if (isAllocated()) delete[] b; b = NONE;}
  };

  enum BlobType : Small
  {
    // 'E' stands for 'existential' quantifier
    // 'V' stands for 'universal' quantifier
    // '<' stands for 'membership' predicate
    eE       , // Ex..Ey(y<x)
    enE      , // Ex..Ey!(y<x)
    Ee       , // Ex..Ey (x<y)
    Ene      , // Ex..Ey!(x<y)
    N_E      , // number of 'existential' blob types
    ue  = N_E,
    une      ,
    eu       ,
    enu      ,
    uu       , // Vx..Vy (x<y)
    unu      , // Vx..Vy!(x<y)
    N_BLOBS  , // number of blob types
    // aliases
    uE  =  ue, // Ex..Vy (y<x)
    unE = une, // Ex..Vy!(y<x)
    Eu  =  eu, // Ex..Vy (x<y)
    Enu = enu, // Ex..Vy!(x<y)
    eU  =  eu, // Vx..Ey (y<x)
    enU = enu, // Vx..Ey!(y<x)
    Ue  =  ue, // Vx..Ey (x<y)
    Une = une, // Vx..Ey!(x<y)
  };
  Blob bs[N_BLOBS];

public:
  Model // atomic formula (x<y), 'necessarily' referencing current scope
  (
    const Big varId, // variable ID (index based on current scope, whose ID is 0)
    const bool isMember, // is 'varId' the 'left-hand-side' of the atomic formula
    const bool isUscope, // is current scope 'universally' quantified
    const bool isUvar, // is 'varId' an 'universally' quantified variable
    const bool isNeg // is the atomic formula 'negated', like !(x<y)
  )
  {
    isUscope ? isUvar ?            bs[isNeg ? unu : uu].set()
                      : isMember ? bs[isNeg ? Enu : Eu].set(varId)
                                 : bs[isNeg ? unE : uE].set(varId)
             : isUvar ? isMember : bs[isNeg ? Une : Ue].set(0)
                                 : bs[isNeg ? enU : eU].set(0)
                      : isMember ? bs[isNeg ? Ene : Ee].set(varId)
                                 : bs[isNeg ? enE : eE].set(varId);
  }
  Model(const Model& m0, const Model& m1) // binary operator
  {
    Blob *bo = bs, *end = bo + N_BLOBS, *bo0 = m0.bs, *bo1 = m1.bs;
    for (; bo < end; bo->set(*bo0, *bo1), ++bo, ++bo0, ++bo1);
  }
  bool cmp(const Model& m) const
  {
    Blob::Order o = Blob::EQ;
    Blob *bo0 = bs, *end = bo0 + N_BLOBS, *bo1 = m.bs;
    for (; bo0 < end && o == Blob::EQ; o = bo0->cmp(*bo1), ++bo0, ++bo1);
    return o == Blob::INC;
  }
  bool contradicts(const Model& m, Big* retError = nullptr) const
  {
    Big dummy, &error = retError ? *retError : dummy;
    return bs[uu].contradicts(m.bs[unu], error) ||
           bs[uu].contradicts(m.bs[enu], error) ||
           bs[uu].contradicts(m.bs[une], error) ||
           bs[uu].contradicts(m.bs[Ene], error) ||
           bs[uu].contradicts(m.bs[enE], error) ||

           bs[unu].contradicts(m.bs[uu], error) ||
           bs[unu].contradicts(m.bs[eu], error) ||
           bs[unu].contradicts(m.bs[ue], error) ||
           bs[unu].contradicts(m.bs[Ee], error) ||
           bs[unu].contradicts(m.bs[eE], error) ||

           bs[eu].contradicts<true>(m.bs[une], error) ||
           bs[ue].contradicts<true>(m.bs[enu], error) ||

           bs[enu].contradicts<true>(m.bs[ue], error) ||
           bs[une].contradicts<true>(m.bs[eu], error) ||

           bs[eu].contradicts(m.bs[enE], error) ||
           bs[eu].contradicts(m.bs[enu], error) ||
           bs[ue].contradicts(m.bs[Ene], error) ||
           bs[ue].contradicts(m.bs[une], error) ||

           bs[enu].contradicts(m.bs[eE], error) ||
           bs[enu].contradicts(m.bs[eu], error) ||
           bs[une].contradicts(m.bs[Ee], error) ||
           bs[une].contradicts(m.bs[ue], error) ||

           bs[eE].contradicts(m.bs[enE], error) ||
           bs[Ee].contradicts(m.bs[Ene], error) ||

           bs[enE].contradicts(m.bs[eE], error) ||
           bs[Ene].contradicts(m.bs[Ee], error);
  }
  void close()
  {
    for (Blob *b = bs, *end = bs + N_E; b < end; b->shift<true>(), ++b);
    for (Blob *b = bs + N_E, *end = bs + N_BLOBS; b < end; b->shift(), ++b);
  }
  void clear() {for (Blob *b = bs, *end = b + N_BLOBS; b < end; b->clear(), ++b);}
};
bool operator<(const Model& m0, const Model& m1) {return m0.cmp(m1);}
}

#endif
