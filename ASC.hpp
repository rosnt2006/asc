#ifndef ASC_HPP
#define ASC_HPP

#include "Model.hpp"

#include <condition_variable>
#include <functional>
#include <map>
#include <mutex>
#include <set>
#include <string>
#include <thread>
#include <vector>

namespace asc
{
using std::string;
using std::vector;
template <typename Small = uint8_t, typename Big = uint64_t>
class ASC
{
private:
  using Model = asc::Model<Small, Big>;
  using ExprModel = set<Model>;
  using ModelStk = vector<ExprModel>;
  using NameToId = std::map<string, Big>;
  using Context = vector<NameToId::value_type>;
  using SynStk = vector<Big>;
  using SemStk = vector<bool>;
  using CondVar = std::condition_variable;
  using Mutex = std::mutex;
  using Lock = std::unique_lock<Mutex>;
  
  static const Big N_WORKERS = 8;

  ModelStk modelStk;
  ExprModel exprModel;
  NameToId varIds;
  Context context;
  SynStk synStk = {0};
  SemStk semStk;
  CondVar idle;
  Mutex mutex;
  Big idleWorkers = N_WORKERS;

  bool hasUnivScope() const {return !semStk.empty() && semStk.back();}
  bool hasUnivVar(const Big varId) const {return semStk[semStk.size() - 1 - varId];}
  bool hasNegScope() const {return hasUnivScope() ^ 1 & synStk.back();}

  void process(std::function<void()>&& f)
  {
    Lock l(mutex);
    idle.wait(l, [&]{return idleWorkers > 0;});
    std::thread(f).detach();
    --idleWorkers;
  }
  void joinWorkers()
  {
    Lock l(mutex);
    idle.wait(l, [&]{return idleWorkers == N_WORKERS;});
  }
  void combine(const Model& m0, const Model& m1)
  {
    if (!m0.contradicts(m1))
    {
      Model m(m0, m1);
      {
        Lock l(mutex);
        exprModel.insert(m);
        ++idleWorkers;
      }
      idle.notify_one();
    }
  }
  template<bool take = false>
  void pop()
  {
    for (auto& m : modelStk.back()) take ? exprModel.insert(m) : m.clear();
    modelStk.pop_back();
  }
  void saveContext(const string& varName)
  {
    Big& varId = varIds[varName];
    context.push_back(std::make_pair(varName, varId));
    varId = semStk.size();
  }
  void restoreContext()
  {
    Big& varId = varIds[context.back().first];
    varId = context.back().second;
    context.pop_back();
  }
  void push(const Big varId, const bool isMember)
  {
    assert(!semStk.empty() && varId < semStk.size());
    const bool isUscope = hasUnivScope();
    const bool isUvar = hasUnivVar(varId);
    const bool isNeg = hasNegScope();
    modelStk.push_back(ExprModel{Model{varId, isMember, isUscope, isUvar, isNeg}});
    for (bool done = false; done = !done; )
    {
      for (; synStk.back() && modelStk.size() > 1; --synStk.back(), done = false)
      {
        if (hasNegScope())
        {
          for (auto& m0 : modelStk[modelStk.size() - 2])
            for (auto& m1 : modelStk.back())
              process([&]{combine(m0, m1);});
          joinWorkers();
          pop(), pop();
        }
        else pop<true>(), pop<true>();
        modelStk.push_back(ExprModel{}), modelStk.back().swap(exprModel);
      }
      for (; !synStk.back() && !semStk.empty() && !modelStk.empty(); done = false)
      {
        for (auto& m : modelStk.back()) process([&]{m.close();});
        joinWorkers();
        synStk.pop_back(), semStk.pop_back();
        restoreContext();
      }
    }
  }

public:
  void push() {++synStk.back();}
  void push(const string& varName)
  {
    semStk.push_back(hasNegScope()), synStk.push_back(0);
    saveContext(varName);
  }
  void push(const string& varName, const bool isMember)
  {
    assert(varIds.count(varName));
    push(semStk.size() - varIds[varName], isMember);
  }
};
}

#endif
