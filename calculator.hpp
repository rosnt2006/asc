#ifndef XC_CALCULATOR_HPP
#define XC_CALCULATOR_HPP

#include "model.hpp"

#include <condition_variable>
#include <functional>
#include <map>
#include <mutex>
#include <set>
#include <string>
#include <thread>
#include <unordered_map>
#include <vector>

namespace xc
{
template <typename uint, uint N_WORKERS>
class calculator
{
  using conjunction = model<uint>;
  using expression = std::set<conjunction>;
  template<typename...As>
  static auto newExpr(As...as) {return new expression(std::forward<As>(as)...);}
  std::shared_ptr<expression> result{newExpr()};
  std::vector<decltype(result)> exprs;
  std::vector<uint> ops = {0, 0};
  std::vector<bool> vars = {false};
  std::map<std::string, uint> symbols;
  std::vector<typename decltype(symbols)::value_type> context;
  struct depth {uint var, op;};
  struct depthHash
  {
    uint operator()(const depth& d) const
    {
      static const uint HALF_WIDTH = std::numeric_limits<uint>::digits >> 1;
      return d.var ^ (d.op << HALF_WIDTH | d.op >> HALF_WIDTH);
    }
  };
  std::unordered_map<depth, uint, depthHash> checks;
  uint idleWorkers = N_WORKERS;
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
  void combine(const conjunction& c0, const conjunction& c1)
  {
    if (!c0.isIncompatible(c1))
    {
      conjunction c(c0, c1);
      {
        std::unique_lock<std::mutex> l(mutex);
        result->emplace(std::move(c));
        ++idleWorkers;
      }
      barrier.notify_all();
    }
  }
  void lift(const conjunction& cc)
  {
    auto& c = const_cast<conjunction&>(cc);
    c.lift();
    {
      std::unique_lock<std::mutex> l(mutex);
      result->emplace(std::move(c));
      ++idleWorkers;
    }
    barrier.notify_all();
  }
  void joinWorkers()
  {
    std::unique_lock<std::mutex> l(mutex);
    barrier.wait(l, [&]{return idleWorkers == N_WORKERS;});
  }
  void save(const std::string& symbol)
  {
    auto sIt = symbols.emplace(symbol, 0);
    context.emplace_back(symbol, sIt.second ? 0 : *sIt.first);
    *sIt.first = nVars();
  }
  void restore()
  {
    auto& alias = context.back();
    if (alias.second) symbols[alias.first] = alias.second;
    else symbols.erase(alias.first);
    context.pop_back();
  }
  uint nVars() const {return vars.size();}
  uint& nOps() {return ops.back();}
  depth getDepth() const {return {nVars(), nOps()};}
  enum Negation {DEFAULT, SYN, SEM};
  template<Negation n = DEFAULT>
  bool isNeg() const {return n == SYN ? 1 & nOps() :
                             n == SEM ? vars.back() :
                                        isNeg<SYN>() ^ isNeg<SEM>();}
  void pop() {exprs.pop_back();}
  auto& top() {return *exprs.back();}
  auto& subTop() {return **(exprs.end() - 2);}
  void take()
  {
    top().clear(), top().swap(*result);
    auto cIt = checks.find(getDepth());
    if (cIt == checks.end()) return;
    if (top().empty()) throw pop(), cIt->second;
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
        joinWorkers(), take(), ops.pop_back(), vars.pop_back(), restore();
      }
    }
  }
  void push(const uint nOperators = 1) {nOps() += nOperators;}
  void push(const std::string& symbol)
  {
    vars.emplace_back(isNeg()), save(symbol), ops.emplace_back(0);
  }
  template<typename Expression> void push(Expression e) {exprs.emplace_back(e), resolve();}
public:
  void atom(const std::string& symbol, const bool isMember)
  {
    auto symbIt = symbols.find(symbol);
    if (symbIt == symbols.end()) throw symbol + " is undefined";
    const uint var = symbIt->second;
    if (var == nVars()) throw symbol + " is impredicative";
    assert(var && var < nVars());
    const bool isNegScope = isNeg<SEM>();
    const bool isNegVar = vars[var - 1];
    if (isNegScope && isNegVar) throw symbol + " colapsed";
    push(newExpr({{nVars() - var, isMember, isNegScope, isNegVar, isNeg<SYN>()}}));
  }
  using expr = std::function<void()>;
  void opNor(const expr& e0, const expr& e1) {push(), e0(), e1();}
  void opNot(const expr& e) {opNor(e, [this]{push(top());});}
  void opOr(const expr& e0, const expr& e1) {opNot([&]{opNor(e0, e1);});}
  void opAnd(const expr& e0, const expr& e1) {opNor([&]{opNot(e0);}, [&]{opNot(e1);});}
  void opNand(const expr& e0, const expr& e1) {opNot([&]{opAnd(e0, e1);});}
  void opImp(const expr& e0, const expr& e1) {opOr(opNot(e0), e1);}
  void opBimp(const expr& e0, const expr& e1)
  {
    push(3), e0(), e1();
    auto nor = top();
    e0(), push(), e1(), push(nor);
  }
  void exists(const std::string& symbol, const expr& e) {push(symbol), e();}
  void forAll(const std::string& symbol, const expr& e) {opNot([&]{exists(symbol, e);});}
  void check(const uint error) {checks[getDepth()] = error;}
};
}

#endif
