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

#include "src/transform/instruction.h"

using namespace std;
using namespace stoke;
using namespace x64asm;


namespace stoke {

TransformInfo InstructionTransform::operator()(Cfg& cfg) {
  TransformInfo ti;
  ti.success = false;

  // Grab the index of an old instruction
  Cfg::id_type bb = cfg.get_entry();
  size_t block_idx = 0;
  if (!get_indices(cfg, bb, block_idx, ti.undo_index[0])) {
    return ti;
  }

  // Record the old value
  ti.undo_instr = cfg.get_code()[ti.undo_index[0]];

  // Try generating a new instruction
  auto instr = ti.undo_instr;

  auto opc = RET;
  if (!pools_.get_control_free(opc)) {
    return ti;
  }
  instr.set_opcode(opc);

  const auto& rs = cfg.def_ins({bb, block_idx});
  for (size_t i = 0, ie = instr.arity(); i < ie; ++i) {
    Operand o = instr.get_operand<R64>(i);
    if (instr.maybe_read(i)) {
      if (!pools_.get_read_op(instr.get_opcode(), i, rs, o)) {
        return ti;
      }
    } else {
      if (!pools_.get_write_op(instr.get_opcode(), i, rs, o)) {
        return ti;
      }
    }
    instr.set_operand(i, o);
  }

  // Check that the instruction is valid
  if (!instr.check()) {
    return ti;
  }

  // Success: Any failure beyond here will require undoing the move
  // Operands come from the global pool so this rip will need rescaling
  cfg.get_function().replace(ti.undo_index[0], instr, false, true);
  cfg.recompute_defs();
  if (!cfg.check_invariants()) {
    undo(cfg, ti);
    return ti;
  }

  ti.success = true;
  assert(cfg.invariant_no_undef_reads());
  assert(cfg.get_function().check_invariants());

  return ti;
}
TransformInfo InstructionTransform::operator()(int opcode_action, Cfg& cfg) {
  TransformInfo ti;
  ti.success = false;

  // Grab the index of an old instruction
  Cfg::id_type bb = cfg.get_entry();
  size_t block_idx = 0;
  if (!get_indices(cfg, bb, block_idx, ti.undo_index[0])) {
    return ti;
  }
  ti.undo_index[0] = instruction_index;
  // Record the old value
  ti.undo_instr = cfg.get_code()[ti.undo_index[0]];

  // Try generating a new instruction
  auto instr = ti.undo_instr;

  auto opc = RET;
  if (!pools_.get_control_free(opcode_action, opc)) {
    return ti;
  }
  instr.set_opcode(opc);

  const auto& rs = cfg.def_ins({bb, block_idx});
  for (size_t i = 0, ie = instr.arity(); i < ie; ++i) {
    Operand o = instr.get_operand<R64>(i);
    if (instr.maybe_read(i)) {
      if (!pools_.get_read_op(instr.get_opcode(), i, rs, o)) {
        return ti;
      }
    } else {
      if (!pools_.get_write_op(instr.get_opcode(), i, rs, o)) {
        return ti;
      }
    }
    instr.set_operand(i, o);
  }

  // Check that the instruction is valid
  if (!instr.check()) {
    return ti;
  }

  // Success: Any failure beyond here will require undoing the move
  // Operands come from the global pool so this rip will need rescaling
  cfg.get_function().replace(ti.undo_index[0], instr, false, true);
  cfg.recompute_defs();
  if (!cfg.check_invariants()) {
    undo(cfg, ti);
    return ti;
  }

  ti.success = true;
  assert(cfg.invariant_no_undef_reads());
  assert(cfg.get_function().check_invariants());
  instruction_index += 1;
  return ti;
}

void InstructionTransform::undo(Cfg& cfg, const TransformInfo& ti) const {

  cfg.get_function().replace(ti.undo_index[0], ti.undo_instr, true);
  cfg.recompute_defs();


  assert(cfg.invariant_no_undef_reads());
  assert(cfg.get_function().check_invariants());
}



} // namespace stoke
