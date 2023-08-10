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

#include <algorithm>
#include <regex>

#include "src/ext/x64asm/include/x64asm.h"
#include "src/state/cpu_state.h"
#include "src/symstate/memory.h"

using namespace cpputil;
using namespace std;
using namespace x64asm;

namespace stoke {

uint64_t CpuState::get_addr(Mem ref) const {

  uint64_t address = 0;

  // get the displacement
  uint32_t displacement = ref.get_disp();

  // sign extend to 64 bits
  if (displacement & 0x80000000) {
    address = 0xffffffff00000000 | (uint64_t)displacement;
  } else {
    address = (uint64_t) displacement;
  }

  // check if memory has base
  if (ref.contains_base()) {
    address = address + gp[ref.get_base()].get_fixed_quad(0);
  }

  // check for index
  if (ref.contains_index()) {
    uint64_t index = gp[ref.get_index()].get_fixed_quad(0);

    switch (ref.get_scale()) {
    case Scale::TIMES_1:
      address = address + index;
      break;
    case Scale::TIMES_2:
      address = address + (index << 1);
      break;
    case Scale::TIMES_4:
      address = address + (index << 2);
      break;
    case Scale::TIMES_8:
      address = address + (index << 3);
      break;
    default:
      assert(false);
      break;
    }
  }

  // check for 32-bit override
  if (ref.addr_or()) {
    address = address & 0xffffffff;
  }

  return address;


}

/** Get the memory address corresponding to a memory operand */
uint64_t CpuState::get_addr(M8 ref) const {

  uint64_t address = 0;

  // get the displacement
  uint32_t displacement = ref.get_disp();

  // sign extend to 64 bits
  if (displacement & 0x80000000) {
    address = 0xffffffff00000000 | (uint64_t)displacement;
  } else {
    address = (uint64_t) displacement;
  }

  // check if memory has base
  if (ref.contains_base()) {
    address = address + gp[ref.get_base()].get_fixed_quad(0);
  }

  // check for index
  if (ref.contains_index()) {
    uint64_t index = gp[ref.get_index()].get_fixed_quad(0);

    switch (ref.get_scale()) {
    case Scale::TIMES_1:
      address = address + index;
      break;
    case Scale::TIMES_2:
      address = address + (index << 1);
      break;
    case Scale::TIMES_4:
      address = address + (index << 2);
      break;
    case Scale::TIMES_8:
      address = address + (index << 3);
      break;
    default:
      assert(false);
      break;
    }
  }

  // check for 32-bit override
  if (ref.addr_or()) {
    address = address & 0xffffffff;
  }

  return address;

}

/** Get the memory address corresponding to an instruction */
uint64_t CpuState::get_addr(x64asm::Instruction instr) const {
  assert(instr.is_memory_dereference());

  if (instr.is_explicit_memory_dereference()) {
    return get_addr(instr.get_operand<M8>(instr.mem_index()));
  } else if (instr.is_push()) {
    size_t bytes = 2;
    switch (instr.get_opcode()) {
    case PUSHQ_IMM32:
    case PUSHQ_IMM16:
    case PUSHQ_IMM8:
    case PUSH_M64:
    case PUSH_R64:
    case PUSH_R64_1:
      bytes = 8;
      break;
    default:
      bytes = 2;
    }
    return gp[x64asm::rsp].get_fixed_quad(0) - bytes;
  } else if (instr.is_pop()) {
    return gp[x64asm::rsp].get_fixed_quad(0);
  } else if (instr.is_ret()) {
    return gp[x64asm::rsp].get_fixed_quad(0);
  }

  // instruction not supported
  assert(false);
  return 0;
}

bool CpuState::memory_from_map(std::unordered_map<uint64_t, BitVector>& concrete) {

  // We can get a list of concrete addresses accessed, and need to split these
  // addresses into heap/stack.  My goal is to just optimize the size of each
  // of the heap and the stack; the algorithm is to just sort the addresses and
  // try every possible place to split them.  This is O(n^2) where n is the
  // number of addresses.  The sorting O(n*log n) is dominated by the loop
  // where we check the goodness of each split; calculating the goodness costs
  // O(n) and we need to do this O(n) times.

  stack.resize(0x700000000, 0);
  heap.resize(0x100000000, 0);
  data.resize(0x000000000, 0);

  if (concrete.size() == 0) {
    // no memory
    return true;
  }

  vector<pair<uint64_t, BitVector>> concrete_vector;
  concrete_vector.insert(concrete_vector.begin(), concrete.begin(), concrete.end());

  auto compare = [] (const pair<uint64_t, BitVector>& p1, const pair<uint64_t, BitVector>& p2) {
    if (p1.first == p2.first)
      return p1.second.num_fixed_bytes() < p2.second.num_fixed_bytes();
    return p1.first < p2.first;
  };
  sort(concrete_vector.begin(), concrete_vector.end(), compare);

  vector<Memory> my_segments;

  // Create memory segments as needed so that there's no 16-byte invalid gap.
  Memory* last_segment = NULL;
  uint64_t max_addr = 0;

  // Build the first segment
  Memory first_segment;
  uint64_t first_address = concrete_vector[0].first;
  size_t size = concrete_vector[0].second.num_fixed_bytes();

  first_segment.resize(first_address, size);
  for (size_t i = 0; i < size; ++i) {
    first_segment.set_valid(first_address + i, true);
    first_segment[first_address + i] = concrete_vector[0].second.get_fixed_byte(i);
  }

  max_addr = first_address + size;
  my_segments.push_back(first_segment);
  last_segment = &my_segments[0];

  // Build remaining segments
  for (size_t i = 1; i < concrete_vector.size(); ++i) {
    auto pair = concrete_vector[i];
    uint64_t address = pair.first;
    size_t size = pair.second.num_fixed_bytes();

    // Three cases:
    // Case 1: address + size < max_addr, and neither has overflowed
    // (do nothing)
    // Case 2: address - max_addr < 32
    // (expand existing region)
    // Case 3: address - max_addr >= 32
    // (create new region)
    if (!(address < max_addr && address + size <= max_addr)) {
      if (address - max_addr < 32) {
        uint64_t new_size = address + size - last_segment->lower_bound();
        last_segment->resize(last_segment->lower_bound(), new_size);
      } else {
        Memory m;
        m.resize(address, size);
        my_segments.push_back(m);
        last_segment = &my_segments[my_segments.size()-1];
      }
    }

    for (size_t i = 0; i < size; ++i) {
      last_segment->set_valid(address + i, true);
      (*last_segment)[address + i] = pair.second.get_fixed_byte(i);
    }
    max_addr = address+size;
  }

  // If there's no segment corresponding to the stack, create one.
  switch (my_segments.size()) {
  default:
  case 3:
    data = my_segments[2];
  case 2:
    stack = my_segments[1];
  case 1:
    heap = my_segments[0];
  case 0:
    break;
  }

  segments.clear();
  for (size_t i = 3; i < my_segments.size(); ++i) {
    segments.push_back(my_segments[i]);
  }

  return true;
}



ostream& CpuState::write_text(ostream& os) const {
  const char* gps[] = {
    "%rax", "%rcx", "%rdx", "%rbx", "%rsp", "%rbp", "%rsi", "%rdi",
    "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15"
  };

  // SSE register names will vary depending on target
  const char* sses[] = {
    "%ymm0", "%ymm1", "%ymm2", "%ymm3", "%ymm4", "%ymm5", "%ymm6", "%ymm7",
    "%ymm8", "%ymm9", "%ymm10", "%ymm11", "%ymm12", "%ymm13", "%ymm14", "%ymm15"
  };

  const char* rflags[] = {
    "%cf", "%1", "%pf", "%0", "%af", "%0", "%zf", "%sf", "%tf", "%if",
    "%df", "%of", "%iopl[0]", "%iopl[1]", "%nt", "%0", "%rf", "%vm", "%ac", "%vif",
    "%vip", "%id"
  };

  os << "SIGNAL " << static_cast<int>(code) << " [" << readable_error_code(code) << "]";
  os << endl;
  os << endl;

  //os << "gps" << endl;
  gp.write_text(os, gps, 5);
  os << endl;
  os << endl;

  //os << "sses" << endl;
  sse.write_text(os, sses, 3);
  os << endl;
  os << endl;

  //os << "rflags" << endl;
  rf.write_text(os, rflags, 1);
  os << endl;
  os << endl;

  //os << "stack" << endl;
  stack.write_text(os);
  os << endl;
  os << endl;

  //os << "heap" << endl;
  heap.write_text(os);
  os << endl;
  os << endl;

  //os << "data" << endl;
  data.write_text(os);
  os << endl;
  os << endl;

  os << segments.size() << " more segment(s)" << endl;

  for (auto seg: segments) {
    os << endl;
    os << endl;
    seg.write_text(os);
  }

  return os;
}

// This reads the rest of the memory of the testcase.  We only do this if the
// segments are listed for backward compatibility.  One day someone can merge
// this code into the main algorithm, once we no longer need old files.
istream& CpuState::read_text_segments(istream& is) {
  string s;

  int n;
  is >> n;
  getline(is, s);
  if (s != " more segment(s)") {
    fail(is) << "Expected segment count.  Got \"" << s << "\"." << endl;
    return is;
  }

  for (int i = 0; i < n; ++i) {
    Memory m;
    is >> ws;
    m.read_text(is);
    segments.push_back(m);
  }
  is >> ws;

  return is;
}

istream& CpuState::read_text(istream& is) {
  const char* gps[] = {
    "%rax", "%rcx", "%rdx", "%rbx", "%rsp", "%rbp", "%rsi", "%rdi",
    "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15"
  };

  // SSE register names will vary depending on target
  const char* sses[] = {
    "%ymm0", "%ymm1", "%ymm2", "%ymm3", "%ymm4", "%ymm5", "%ymm6", "%ymm7",
    "%ymm8", "%ymm9", "%ymm10", "%ymm11", "%ymm12", "%ymm13", "%ymm14", "%ymm15"
  };

  const char* rflags[] = {
    "%cf", "%1", "%pf", "%0", "%af", "%0", "%zf", "%sf", "%tf", "%if",
    "%df", "%of", "%iopl[0]", "%iopl[1]", "%nt", "%0", "%rf", "%vm", "%ac", "%vif",
    "%vip", "%id"
  };

  string s;
  int temp;

  is >> s >> temp;
  if (!regex_match(s, regex("SIGNAL"))) {
    fail(is) << "Expected \"SIGNAL\" but got \"" << s << "\"" << endl;
    return is;
  }
  getline(is, s);
  if (!regex_match(s, regex(" *\\[.*\\]"))) {
    fail(is) << "Expected '[" << readable_error_code(code) << "]' (or similar) but got "
             << "'" << s << "'" << endl;
    return is;
  }

  code = static_cast<ErrorCode>(temp);
  is >> ws;

  gp.read_text(is, gps);
  is >> ws;

  sse.read_text(is, sses);
  is >> ws;

  rf.read_text(is, rflags);
  is >> ws;

  stack.read_text(is);
  is >> ws;

  heap.read_text(is);
  is >> ws;

  data.read_text(is);
  is >> ws;

  // Figure out of we're reading an old version of the testcase format (in
  // which case we're done), or if there's more to do.  One day we can skip the
  // check and just assume the new version. -- BRC
  char future = is.peek();
  if (future >= '0' && future <= '9') {
    read_text_segments(is);
  }

  return is;
}

ostream& CpuState::write_bin(ostream& os) const {
  os.write((const char*)&code, sizeof(ErrorCode));
  gp.write_bin(os);
  sse.write_bin(os);
  rf.write_bin(os);
  stack.write_bin(os);
  heap.write_bin(os);
  data.write_bin(os);

  // Write other segments
  size_t seg_count = segments.size();
  os.write((const char*)&seg_count, sizeof(size_t));
  for (auto seg : segments)
    seg.write_bin(os);

  return os;
}

istream& CpuState::read_bin(istream& is) {
  is.read((char*)&code, sizeof(ErrorCode));
  gp.read_bin(is);
  sse.read_bin(is);
  rf.read_bin(is);
  stack.read_bin(is);
  heap.read_bin(is);
  data.read_bin(is);

  // Read other segments
  size_t seg_count;
  is.read((char*)&seg_count, sizeof(size_t));
  for (size_t i = 0; i < seg_count; ++i) {
    Memory seg;
    seg.read_bin(is);
    segments.push_back(seg);
  }


  return is;
}

} // namespace stoke



