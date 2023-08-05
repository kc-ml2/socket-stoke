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

#ifndef STOKE_SRC_COST_EXPR_H
#define STOKE_SRC_COST_EXPR_H

#include "src/cost/cost_function.h"
#include "gtest/gtest_prod.h"

#include <set>

namespace stoke {


// TODO: this really should just reuse the functionality in
// src/expr/expr.h.  Before changing things here, consider reusing
// that code.
class ExprCost : public CostFunction {
  friend class CostParserTest;
  FRIEND_TEST(CostParserTest, LeafFunctions);
  FRIEND_TEST(CostParserTest, NoLeafFunctions);
  FRIEND_TEST(CostParserTest, TwoLeafFunctions);

public:

  enum Operator {
    NONE, //represents error condition in parser
    PLUS,
    MINUS,
    TIMES,
    DIV,
    MOD,
    AND,
    OR,
    SHL,
    SHR,
    LT,
    GT,
    LTE,
    GTE,
    EQ
  };

  /** Constructs a binary operation on two other expressions*/
  ExprCost(ExprCost* a1, ExprCost* a2, Operator op) :
    a1_(a1), a2_(a2), op_(op), arity_(2), correctness_(NULL) {
    reset();

    if (a1_ && a2_) // if there's a parse error, one could be null
      need_test_sandbox_ = a1->need_test_sandbox() || a2->need_test_sandbox();
    if (a1_ && a2_) // if there's a parse error, one could be null
      need_perf_sandbox_ = a1->need_perf_sandbox() || a2->need_perf_sandbox();
  }
  /** Constructs a reference to a "leaf" cost function.
      (i.e. one that does real work) */
  ExprCost(CostFunction* a1) : a1_(a1), arity_(1), correctness_(NULL) {
    //we'll handle running the sandbox here.
    reset();

    if (a1_) { //could be null if there's a parse error
      a1->set_run_test_sandbox(false);
      need_test_sandbox_ = a1->need_test_sandbox();
      a1->set_run_perf_sandbox(false);
      need_perf_sandbox_ = a1->need_perf_sandbox();
    }
  }
  /** Constructs a constant operation */
  ExprCost(Cost constant) : constant_(constant), arity_(0) {
    reset();
  }

  /** Compute the cost of this expression. */
  result_type operator()(const Cfg& cfg, Cost max = max_cost);
  result_type operator()(int client, const Cfg& cfg, Cost max = max_cost);
  result_type test_operator(int client, const Cfg& cfg, Cost max = max_cost) {
    return (*this)(cfg, max);
  }
  /** Set the correctness term to another expression. */
  ExprCost& set_correctness(ExprCost* correctness) {
    correctness_ = correctness;
    return *this;
  }

  /** Figure out if we need to do any cost function setup. */
  bool need_test_sandbox() {
    return need_test_sandbox_;
  }
  bool need_perf_sandbox() {
    return need_perf_sandbox_;
  }

  /** Do any necessary cost function setup. */
  ExprCost& setup_test_sandbox(Sandbox* sb);
  ExprCost& setup_perf_sandbox(Sandbox* sb);

private:
  /** Called by all constructors. */
  void reset() {
    correctness_ = NULL;
    need_test_sandbox_ = false;
    need_perf_sandbox_ = false;
  }

  /** Compute the cost associated with this node. */
  Cost run(const std::map<CostFunction*, Cost>& environment) const;

  /** Do we need a sandbox? */
  bool need_test_sandbox_;
  bool need_perf_sandbox_;

  /** Returns the pointers to leaf cost functions used in this expression. */
  std::set<CostFunction*> leaf_functions() const;
  /** Like leaf_functions(), but also inspects correctness term. */
  std::set<CostFunction*> all_leaf_functions() const;

  /** A constant (for arity 0) */
  Cost constant_;
  /** The LHS cost function */
  CostFunction* a1_;
  /** The RHS cost function */
  CostFunction* a2_;
  /** The chosen operator */
  Operator op_;

  /** How many operands does this cost expression take? */
  size_t arity_;
  /** Set the correctness term */
  ExprCost* correctness_;



};

} // namespace stoke

#endif
