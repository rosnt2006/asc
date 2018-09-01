#ifndef XC_CALCULATOR_HPP
#define XC_CALCULATOR_HPP

#include "model.hpp"

#include <condition_variable>
#include <functional>
#include <map>
#include <mutex>
#include <set>
#include <thread>
#include <unordered_map>
#include <vector>

namespace xc
{
struct exception {virtual ~exception() {}};
struct indefinition : exception {};
struct circularity : exception {};
struct collapse : exception {};

template <typename uint, uint N_WORKERS>
class calculator
{
  std::set<model<uint>> result;
  std::vector<std::shared_ptr<decltype(result)>> exprs;
  std::vector<uint> ops{0, 0};
  std::vector<bool> vars{false};
  struct depth
  {
    uint var, op;
    bool operator==(const depth& d) const {return var == d.var && op == d.op;}
    auto operator()(const depth& d) const
    {
      static const uint HALF_WIDTH = std::numeric_limits<uint>::digits >> 1;
      return d.var ^ (d.op << HALF_WIDTH | d.op >> HALF_WIDTH);
    }
  };
  std::unordered_map<depth, const exception*, depth> checks;
  uint idleWorkers{N_WORKERS};
  std::condition_variable barrier;
  std::mutex mutex;

  template<typename Task>
  void process(Task&& t)
  {
    {
      std::unique_lock<std::mutex> l(mutex);
      barrier.wait(l, [&]{return idleWorkers;});
      --idleWorkers;
    }
    std::thread(std::forward<Task>(t)).detach();
  }
  void combine(const model<uint>& m0, const model<uint>& m1)
  {
    if (!m0.isIncompatible(m1))
    {
      model<uint> m(m0, m1);
      {
        std::unique_lock<std::mutex> l(mutex);
        result.emplace(std::move(m));
        ++idleWorkers;
      }
      barrier.notify_all();
    }
  }
  void lift(const model<uint>& cm)
  {
    auto& m = const_cast<model<uint>&>(cm);
    m.lift();
    {
      std::unique_lock<std::mutex> l(mutex);
      result.emplace(std::move(m));
      ++idleWorkers;
    }
    barrier.notify_all();
  }
  void joinWorkers()
  {
    std::unique_lock<std::mutex> l(mutex);
    barrier.wait(l, [&]{return idleWorkers == N_WORKERS;});
  }
  uint nVars() const {return vars.size();}
  auto& nOps() const {return ops.back();}
  depth getDepth() const {return {nVars(), nOps()};}
  enum Negation {DEFAULT, SYN, SEM};
  template<Negation n = DEFAULT>
  bool isNeg() const {return n == SYN ? 1 & nOps() :
                             n == SEM ? vars.back() :
                                        isNeg<SYN>() ^ isNeg<SEM>();}
  auto& nOps() {return ops.back();}
  void pop() {exprs.pop_back();}
  auto& topPtr() {return exprs.back();}
  auto& top() {return *topPtr();}
  auto& subTop() {return **(exprs.end() - 2);}
  void take()
  {
    top().clear(), top().swap(result);
    auto cIt = checks.find(getDepth());
    if (cIt == checks.end()) return;
    if (top().empty()) pop(), throw *cIt->second;
    checks.erase(cIt);
  }
  void resolve()
  {
    for (bool isDone = false; (isDone = !isDone); )
    {
      for (; nOps() && exprs.size() > 1; --nOps(), isDone = false)
      {
        if (isNeg())
        {
          for (auto& c0 : subTop())
            for (auto& c1 : top()) process([&]{combine(c0, c1);});
          joinWorkers(), pop(), take();
        }
        else subTop().insert(top().begin(), top().end()), pop();
      }
      for (; !nOps() && nVars() > 1 && !exprs.empty(); isDone = false)
      {
        for (auto& c : top()) process([&]{lift(c);});
        joinWorkers(), take(), ops.pop_back(), vars.pop_back();
      }
    }
  }
  template<typename Expr> void push(Expr e) {exprs.emplace_back(e), resolve();}
public: using var = uint; private:
  template<bool isMember>
  void bind(const var v)
  {
    assert(v);
    if (v > nVars()) throw indefinition{};
    if (v == nVars()) throw circularity{};
    bool isNegScope = isNeg<SEM>();
    bool isNegVar = vars[v - 1];
    if (isNegScope && isNegVar) throw collapse{};
    auto expr = std::make_shared<decltype(result)>();
    expr->emplace(nVars() - v, isMember, isNegScope, isNegVar, isNeg<SYN>());
    push(expr);
  }
  var newVar() {return vars.emplace_back(isNeg()), ops.emplace_back(0), nVars();}
public:
  void check(const exception& error) {checks[getDepth()] = &error;}
  friend void operator<(calculator& c, const var v) {c.bind<false>(v);}
  friend void operator>(const var v, calculator& c) {c<v;}
  friend void operator<(const var v, calculator& c) {c.bind<true>(v);}
  friend void operator>(calculator& c, const var v) {v<c;}
  using expr = std::function<void()>;
  void opNor(const expr& e0, const expr& e1) {++nOps(), e0(), e1();}
  void opNot(const expr& e) {opNor(e, [this]{push(topPtr());});}
  void opOr(const expr& e0, const expr& e1) {opNot([&]{opNor(e0, e1);});}
  void opAnd(const expr& e0, const expr& e1) {opNor([&]{opNot(e0);}, [&]{opNot(e1);});}
  void opNand(const expr& e0, const expr& e1) {opNot([&]{opAnd(e0, e1);});}
  void opImp(const expr& e0, const expr& e1) {opOr([&]{opNot(e0);}, e1);}
  void opBimp(const expr& e0, const expr& e1)
  {
    nOps() += 3, e0(), e1();
    auto nor = topPtr();
    e0(), ++nOps(), e1(), push(nor);
  }
  using predicate = std::function<void(var)>;
  void exists(const predicate& p) {p(newVar());}
  void forAll(const predicate& p) {opNot([&]{exists([&](var v){opNot([&]{p(v);});});});}
};
}

#endif
