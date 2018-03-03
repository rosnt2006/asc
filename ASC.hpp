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
class ASC
{
private:
  using Model = asc::Model<>;
  using ExprModel = std::set<Model>;
  using ModelStk = vector<ExprModel>;
  using uint = Model::VariableId;
  using NameToId = std::map<string, uint>;
  using Context = vector<NameToId::value_type>;
  using SynStk = vector<uint>;
  using SemStk = vector<bool>;
  using CondVar = std::condition_variable;
  using Mutex = std::mutex;
  using Lock = std::unique_lock<Mutex>;

  static const uint N_WORKERS = 8;

  ModelStk modelStk;
  ExprModel exprModel;
  NameToId varIds;
  Context context;
  SynStk synStk = {0};
  SemStk semStk;
  CondVar idle;
  Mutex mutex;
  uint idleWorkers = N_WORKERS;

  bool hasUnivScope() const {return !semStk.empty() && semStk.back();}
  bool hasUnivVar(const uint varId) const {return semStk[semStk.size() - 1 - varId];}
  bool hasNegScope() const {return hasUnivScope() ^ (1 & synStk.back());}

  void process(std::function<void()>&& f)
  {
    Lock l(mutex);
    idle.wait(l, [&]{return idleWorkers > 0;});
    --idleWorkers;
    std::thread(f).detach();
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
  void saveContext(const string& varName)
  {
    uint& varId = varIds[varName];
    context.emplace_back(varName, varId);
    varId = semStk.size();
  }
  void restoreContext()
  {
    auto& savedContext = context.back();
    varIds[savedContext.first] = savedContext.second;
    context.pop_back();
  }
  void push(const uint varId, const bool isMember)
  {
    assert(!semStk.empty() && varId < semStk.size());
    const bool isUscope = hasUnivScope();
    const bool isUvar = hasUnivVar(varId);
    const bool isNeg = hasNegScope();
    modelStk.emplace_back();
    modelStk.back().emplace(varId, isMember, isUscope, isUvar, isNeg);
    for (bool done = false; (done = !done); )
    {
      for (; synStk.back() && modelStk.size() > 1; --synStk.back(), done = false)
      {
        if (hasNegScope())
        {
          for (auto& m0 : modelStk[modelStk.size() - 2])
            for (auto& m1 : modelStk.back())
              process([&]{combine(m0, m1);});
          joinWorkers();
          for (auto& m : modelStk.back()) ((Model&)m).clear();
          modelStk.pop_back();
          for (auto& m : modelStk.back()) ((Model&)m).clear();
          modelStk.back().clear(), modelStk.back().swap(exprModel);
        }
        else
        {
          auto& exprModel = modelStk[modelStk.size() - 2];
          for (auto& m : modelStk.back()) exprModel.insert(m);
          modelStk.pop_back();
        }
      }
      for (; !synStk.back() && !semStk.empty() && !modelStk.empty(); done = false)
      {
        for (auto& m : modelStk.back()) process([&]{((Model&)m).close();});
        joinWorkers();
        synStk.pop_back(), semStk.pop_back();
        restoreContext();
      }
    }
  }

public:
  void push(const uint numOperators = 1) {synStk.back() += numOperators;}
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
