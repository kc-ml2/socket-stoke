// Copyright 2013-2016 Stanford University
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include "src/cost/expr.h"

using namespace stoke;
using namespace std;


ExprCost& ExprCost::setup_test_sandbox(Sandbox* sb) {

  test_sandbox_ = sb;
  for (auto cf : all_leaf_functions()) {
    cf->setup_test_sandbox(sb);
  }
  return *this;
}

ExprCost& ExprCost::setup_perf_sandbox(Sandbox* sb) {

  perf_sandbox_ = sb;
  for (auto cf : all_leaf_functions()) {
    cf->setup_perf_sandbox(sb);
  }
  return *this;
}

set<CostFunction*> ExprCost::all_leaf_functions() const {

  auto leaves = leaf_functions();
  if (correctness_) {
    auto more_leaves = correctness_->leaf_functions();
    leaves.insert(more_leaves.begin(), more_leaves.end());
  }
  return leaves;

}

set<CostFunction*> ExprCost::leaf_functions() const {

  if (arity_ == 0) {
    return set<CostFunction*>();
  }

  if (arity_ == 1) {
    auto s = set<CostFunction*>();
    s.insert(a1_);
    return s;
  }

  if (arity_ == 2) {
    auto lhs = (static_cast<ExprCost*>(a1_))->leaf_functions();
    auto rhs = (static_cast<ExprCost*>(a2_))->leaf_functions();
    lhs.insert(rhs.begin(), rhs.end());
    return lhs;
  }

  assert(false);
  return set<CostFunction*>();

}
ExprCost::result_type ExprCost::operator()(int client, const Cfg& cfg, Cost max) {
  // Get the full list of leaf functions
  auto leaves = all_leaf_functions();

  // run the sandbox, if needed
  if (need_test_sandbox_)
    run_test_sandbox(cfg);
  if (need_perf_sandbox_)
    run_perf_sandbox(cfg);

  // build the environment (i.e. run the actual cost functions)
  std::map<CostFunction*, Cost> env;
  for (auto it : leaves) {
    env[it] = (*it)(client, cfg, max).second;
  }

  // compute cost and correctness (i.e. combine the results together)
  Cost cost = run(env);

  bool correct = true;
  if (correctness_) {
    correct = (correctness_->run(env) != 0);
  }

  return result_type(correct, cost);
}
ExprCost::result_type ExprCost::operator()(const Cfg& cfg, Cost max) {

  // Get the full list of leaf functions
  auto leaves = all_leaf_functions();

  // run the sandbox, if needed
  if (need_test_sandbox_)
    run_test_sandbox(cfg);
  if (need_perf_sandbox_)
    run_perf_sandbox(cfg);

  // build the environment (i.e. run the actual cost functions)
  std::map<CostFunction*, Cost> env;
  for (auto it : leaves) {
    env[it] = (*it)(cfg, max).second;
  }

  // compute cost and correctness (i.e. combine the results together)
  Cost cost = run(env);

  bool correct = true;
  if (correctness_) {
    correct = (correctness_->run(env) != 0);
  }

  return result_type(correct, cost);
}
/*
ExprCost::result_type ExprCost::operator()(int client, const Cfg& cfg, Cost max) {

  // Get the full list of leaf functions
  auto leaves = all_leaf_functions();

  // run the sandbox, if needed
  if (need_test_sandbox_)
    run_test_sandbox(cfg);
  if (need_perf_sandbox_)
    run_perf_sandbox(cfg);

  // build the environment (i.e. run the actual cost functions)
  std::map<CostFunction*, Cost> env;
  for (auto it : leaves) {
    env[it] = (*it)(cfg, max).second;
  }

  // compute cost and correctness (i.e. combine the results together)
  Cost cost = run(env);

  bool correct = true;
  if (correctness_) {
    correct = (correctness_->run(env) != 0);
  }

  return result_type(correct, cost);
}

*/



Cost ExprCost::run(const std::map<CostFunction*, Cost>& env) const {

  if (arity_ == 0) {
    return constant_;
  } else if (arity_ == 1) {
    assert(a1_);
    assert(env.count(a1_) > 0);
    return env.at(a1_);
  } else if (arity_ == 2) {
    assert(a1_);
    assert(a2_);
    auto c1 = static_cast<ExprCost*>(a1_)->run(env);
    auto c2 = static_cast<ExprCost*>(a2_)->run(env);

    switch (op_) {
    case NONE:
      assert(false);
    case PLUS:
      return c1+c2;
    case MINUS:
      return c1-c2;
    case TIMES:
      return c1*c2;
    case DIV:
      return c1/c2;
    case MOD:
      return c1%c2;
    case AND:
      return c1&c2;
    case OR:
      return c1|c2;
    case SHL:
      return c1 << c2;
    case SHR:
      return c1 >> c2;
    case LT:
      return c1 < c2;
    case LTE:
      return c1 <= c2;
    case GT:
      return c1 > c2;
    case GTE:
      return c1 >= c2;
    case EQ:
      return c1 == c2;
    default:
      assert(false);
    }
  }
  assert(false);
  return 0;
}

