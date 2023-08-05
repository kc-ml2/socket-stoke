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

#ifndef STOKE_TOOLS_GADGETS_CORRECTNESS_COST_H
#define STOKE_TOOLS_GADGETS_CORRECTNESS_COST_H

#include "src/cfg/cfg.h"
#include "src/cost/correctness.h"
#include "src/cost/cost_function.h"
#include "src/sandbox/sandbox.h"
#include "tools/args/correctness.inc"
#include "tools/args/in_out.inc"

namespace stoke {

class CorrectnessCostGadget : public CorrectnessCost {
public:
  CorrectnessCostGadget(const Cfg& target, Sandbox* sb) : CorrectnessCost(sb) {
    set_target(target, stack_out_arg, heap_out_arg);

    set_distance(distance_arg);
    set_sse(sse_width_arg, sse_count_arg);
    set_relax(!no_relax_reg_arg, relax_mem_arg, blocked_heap_opt_arg);
    set_penalty(misalign_penalty_arg, sig_penalty_arg);
    set_min_ulp(min_ulp_arg);
    set_reduction(reduction_arg);
  }

};

} // namespace stoke

#endif
