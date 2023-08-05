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

#ifndef STOKE_SRC_COST_BINSIZE_H
#define STOKE_SRC_COST_BINSIZE_H

namespace stoke {

class BinSizeCost : public CostFunction {

public:

  /** Return the size, in bytes, of the assembled CFG
      (less unreachable blocks and nops) */
  result_type operator()(const Cfg& cfg, Cost max = max_cost) {

    const auto& code = cfg.get_code();

    x64asm::Function buffer;
    buffer.reserve(code.size()*15 + 15);
    assm_.start(buffer);

    for (auto instr : code)
      assm_.assemble(instr);

    return result_type(true, buffer.size());
  }
  /*

  result_type test_operator(int client, const Cfg& cfg, Cost max = max_cost) {
    return (*this)(cfg, max);
  }
  */
  result_type operator()(int client, const Cfg& cfg, Cost max = max_cost) {
    return (*this)(cfg, max);
  }

private:

  x64asm::Assembler assm_;

};

} // namespace stoke

#endif
