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
#include <iostream>
#include <cstring>
#include <arpa/inet.h>
#include <sys/socket.h>
#include <unistd.h>


#ifndef STOKE_SRC_TRANSFORM_WEIGHTED_H
#define STOKE_SRC_TRANSFORM_WEIGHTED_H

#include <iostream>

#include <algorithm>
#include <cassert>
#include <random>
#include <set>
#include <vector>

#include "src/transform/transform.h"

using namespace std;

namespace stoke {

class WeightedTransform : public Transform {
public:
  /** Creates a new transformation helper; guaranteed to pass invariants. */
  WeightedTransform(TransformPools& pools) : Transform(pools) {
  }

  std::string get_name() const {
    return "Weighted";
  }
  TransformInfo operator()(Cfg& cfg) {
    size_t pool_index = gen_() % transform_pool_.size();
    size_t tform_index = transform_pool_[pool_index];
    Transform* tr = transforms_[tform_index];
    auto ti = (*tr)(cfg);
    ti.move_type = tform_index;
    return ti;
  }
  TransformInfo operator()(int opcode_action, Cfg& cfg){
    return (*this)(cfg);
  };
  TransformInfo transform_test(int client, Cfg& cfg){
    int restart;
    int action;
    recv(client, &restart, sizeof(restart), 0);
		recv(client, &action, sizeof(action), 0);

    if (restart == 1){
      std::string dynamic_length_string = "reset";
      int data_length = dynamic_length_string.size();

      // Send the length buffer and then the data
      send(client, &data_length, sizeof(int), 0);
      send(client, dynamic_length_string.c_str(), data_length, 0);
      throw std::runtime_error("restart");
    }

    size_t instruction_add_index = 2; // it is the tform_index type. not the pool_index type.
    Transform* instruction_add = transforms_[instruction_add_index];
    size_t opcode_pool_size = instruction_add->pools_.opcode_pool_.size() - 1;
    size_t total_size = opcode_pool_size + transform_pool_.size();

    size_t instruction_num = action % (opcode_pool_size + 1);
    auto ti = (*instruction_add)(instruction_num, cfg);
    ti.move_type = instruction_add_index;
    return ti;
  }

  void undo(Cfg& cfg, const TransformInfo& info) const {
    transforms_[info.move_type]->undo(cfg, info);
  }

  /** Add a transform to the set. */
  void insert_transform(Transform* tr, size_t weight = 1) {
    size_t label = transforms_.size();
    transforms_.push_back(tr);
    for (size_t i = 0; i < weight; ++i)
      transform_pool_.push_back(label);
  }

  /** Get a pointer to a transform at a given index.  This is
    useful to identify what transform was used by looking at the
    move_type field of TransformInfo(). */
  Transform* get_transform(size_t index) const {
    assert(index < transforms_.size());
    return transforms_[index];
  }

  /** Returns the number of transforms available to choose from. */
  size_t size() const {
    return transforms_.size();
  }

  /** Set a seed for the random number generator. */
  virtual void set_seed(std::default_random_engine::result_type seed) {
    for (auto tform : transforms_)
      tform->set_seed(seed);
    gen_.seed(seed);
  }

protected:

  /** Transforms that we have available to use. */
  std::vector<Transform*> transforms_;

  /** Members are indexes into transforms_ vector.  The indexes are
    repeated based on the given weight of the transform. */
  std::vector<size_t> transform_pool_;
};

} // namespace stoke

#endif
