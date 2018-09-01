#ifndef XC_MODEL_HPP
#define XC_MODEL_HPP

#include "cloud.hpp"

namespace xc
{
template <typename uint>
class model
{
  enum Type
  {
    A, // analysis
    S, // synthesis
    R, // root
    B, // branch
    V, // vacuum
    U, // universe
    D, // dark
    M, // multiverse
    NEGATION_OFFSET,
    N_TYPES = NEGATION_OFFSET << 1,
  };
  friend constexpr Type operator!(Type t) {return static_cast<Type>(t + NEGATION_OFFSET);}

  using dim = cloud<uint>;
  dim ds[N_TYPES];

  template<Type t0, Type t1, typename dim::IntersectionPolicy policy = dim::DEFAULT>
  bool isBlocking(const model& m, uint& at0, uint& at1) const
  {
    return ds[t0].template isIntersecting<policy>(m.ds[t1], at0, at1) ||
           ds[t1].template isIntersecting<policy>(m.ds[t0], at0, at1);
  }
  template<Type t0, Type t1, typename dim::IntersectionPolicy policy = dim::DEFAULT>
  bool isContradicting(const model& m, uint& at0, uint& at1) const
  {
    return isBlocking<t0, !t1, policy>(m, at0, at1) ||
           isBlocking<!t0, t1, policy>(m, at0, at1);
  }
  template<Type t>
  bool isContradicting(const model& m, uint& at0, uint& at1) const
  {
    return isBlocking<t, !t>(m, at0, at1);
  }
  template<Type t0, Type t1>
  bool isCrossing(const model& m, uint& at0, uint& at1) const
  {
    return isContradicting<t0, t1, dim::BY_CROSS>(m, at0, at1);
  }
  bool isBefore(const model& m) const
  {
    auto o = dim::EQU;
    auto *d0I = ds, *end = d0I + N_TYPES, *d1I = m.ds;
    for (; d0I < end && o == dim::EQU; o = d0I->cmp(*d1I), ++d0I, ++d1I);
    return o == dim::INC;
  }
public:
  model // atomic formula, 'necessarily' referencing current scope
  (
    uint variable, // index based on current scope, whose ID is 0
    bool isMember, // is 'variable' the 'left-hand-side' of the atomic formula
    bool isNegScope, // is current scope 'universally' quantified
    bool isNegVar, // is 'variable' an 'universally' quantified variable
    bool isNeg // is the atomic formula 'negated'
  )
  {
    assert(variable && (!isNegScope || !isNegVar));
    isNeg ^= isNegScope;
    isNegScope ?   	        isMember ? ds[isNeg ? !V : V] = variable
                                     : ds[isNeg ? !U : U] = variable
               : isNegVar ? isMember ? ds[isNeg ? !U : U] = uint(0)
                                     : ds[isNeg ? !V : V] = uint(0)
                          : isMember ? ds[isNeg ? !A : A] = variable
                                     : ds[isNeg ? !S : S] = variable;
  }
  model(const model& m0, const model& m1)
  {
    auto *dI = ds, *end = dI + N_TYPES;
    auto *d0I = m0.ds, *d1I = m1.ds;
    for (; dI < end; *dI = *d0I | *d1I, ++dI, ++d0I, ++d1I);
  }
  bool isIncompatible(const model& m) const
  {
    uint at0, at1;
    return isCrossing     <M, D>(m, at0, at1) ||
           isCrossing     <M, V>(m, at0, at1) ||
           isCrossing     <U, D>(m, at0, at1) ||
           isCrossing     <U, V>(m, at0, at1) ||
           
           isBlocking     <U, V>(m, at0, at1) ||
           isBlocking     <U, R>(m, at0, at1) ||
           isBlocking     <U, A>(m, at0, at1) ||
           isBlocking     <V, B>(m, at0, at1) ||
           isBlocking     <V, S>(m, at0, at1) ||
           isBlocking     <S, A>(m, at0, at1) ||

           isContradicting<U   >(m, at0, at1) ||
           isContradicting<U, B>(m, at0, at1) ||
           isContradicting<U, S>(m, at0, at1) ||
           isContradicting<V   >(m, at0, at1) ||
           isContradicting<V, R>(m, at0, at1) ||
           isContradicting<V, A>(m, at0, at1) ||
           isContradicting<S   >(m, at0, at1) ||
           isContradicting<A   >(m, at0, at1);
  }
  void lift()
  {
    ds[R] |= ds[A], ds[!R] |= ds[!A], ds[B] |= ds[S], ds[!B] |= ds[!S];
    ds[A] = ds[!A] = ds[S] = ds[!S] = false;
    ds[R].shift(), ds[!R].shift(), ds[B].shift(), ds[!B].shift();
    ds[D] |= ds[V].shift(), ds[!D] |= ds[!V].shift();
    ds[M] |= ds[U].shift(), ds[!M] |= ds[!U].shift();
  }
  friend bool operator<(const model& m0, const model& m1) {return m0.isBefore(m1);}
};
}

#endif
