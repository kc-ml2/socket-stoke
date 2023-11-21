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
#include <cstring>
#include <arpa/inet.h>
#include <sys/socket.h>
#include <unistd.h>

#include <fstream>
#include <string>

#include <chrono>
#include <iostream>
#include <sys/time.h>

#include "src/ext/cpputil/include/command_line/command_line.h"
#include "src/ext/cpputil/include/io/column.h"
#include "src/ext/cpputil/include/io/console.h"
#include "src/ext/cpputil/include/io/filterstream.h"
#include "src/ext/cpputil/include/signal/debug_handler.h"

#include "src/cfg/cfg_transforms.h"
#include "src/expr/expr.h"
#include "src/expr/expr_parser.h"
#include "src/tunit/tunit.h"
#include "src/search/progress_callback.h"
#include "src/search/new_best_correct_callback.h"
#include "src/search/statistics_callback.h"
#include "src/search/failed_verification_action.h"
#include "src/search/postprocessing.h"

#include "tools/args/search.inc"
#include "tools/args/target.inc"
#include "tools/gadgets/cost_function.h"
#include "tools/gadgets/correctness_cost.h"
#include "tools/gadgets/functions.h"
#include "tools/gadgets/sandbox.h"
#include "tools/gadgets/search.h"
#include "tools/gadgets/search_state.h"
#include "tools/gadgets/seed.h"
#include "tools/gadgets/solver.h"
#include "tools/gadgets/target.h"
#include "tools/gadgets/testcases.h"
#include "tools/gadgets/transform_pools.h"
#include "tools/gadgets/validator.h"
#include "tools/gadgets/verifier.h"
#include "tools/gadgets/weighted_transform.h"
#include "tools/io/postprocessing.h"
#include "tools/io/failed_verification_action.h"

#include <boost/filesystem/operations.hpp>
#include <boost/filesystem/path.hpp>
namespace fs = boost::filesystem;

using namespace cpputil;
using namespace std;
using namespace stoke;
using namespace chrono;

auto& io = Heading::create("Output Options:");
auto& out = ValueArg<string>::create("out")
            .alternate("o")
            .usage("<path/to/file.s>")
            .description("File to write successful results to")
            .default_val("result.s");

auto& results_arg = ValueArg<string>::create("results")
                    .usage("<path/to/dir>")
                    .description("Path to the directory where new best correct rewrites are being stored.  Rewrites are verified before being stored (using the same verification settings as the final verification).")
                    .default_val("");

auto& machine_output_arg = ValueArg<string>::create("machine_output")
                           .usage("<path/to/file.s>")
                           .description("Machine-readable output (result and statistics)");

auto& stats = Heading::create("Statistics Options:");
auto& stat_int =
  ValueArg<size_t>::create("statistics_interval")
  .usage("<int>")
  .description("Number of iterations between statistics updates")
  .default_val(1000000);

auto& automation_heading = Heading::create("Automation Options:");

auto& timeout_iterations_arg =
  cpputil::ValueArg<size_t>::create("timeout_iterations")
  .usage("<int>")
  .description("Total number of iterations before giving up (across all cycles)")
  .default_val(100000000);

auto& timeout_seconds_arg =
  cpputil::ValueArg<double>::create("timeout_seconds")
  .usage("<double>")
  .description("Total number of seconds before giving up (across all cycles), or 0 for no timeout")
  .default_val(0);

auto& failed_verification_action =
  ValueArg<FailedVerificationAction, FailedVerificationActionReader, FailedVerificationActionWriter>::create("failed_verification_action")
  .usage("(quit|add_counterexample)")
  .description("Action to take when the verification at the end fails")
  .default_val(FailedVerificationAction::ADD_COUNTEREXAMPLE);

auto& cycle_timeout_arg =
  ValueArg<string, cpputil::LineReader<>>::create("cycle_timeout")
  .usage("<string>")
  .description("The timeout (as number of iterations) per cycle.  Can be a comma-separated list, where the first element is used for the first cycle, and so on.  Can also be an expression involving the variable 'i' that refers to the current cycle (starting at 1); expressions include integer constants, the variable 'i', and binary operators: +, -, *, /, ** (exponentiation), >>, << (shifts), ==, !=, <=, <, >, >= (comparisons), % (modulo), |, & (binary and/or).  The last expression in the list is used for all following cycles.")
  .default_val("10000, 10000, 10000, 10000, 10000, 2**i * 1000");

auto& postprocessing_arg =
  ValueArg<Postprocessing, PostprocessingReader, PostprocessingWriter>::create("postprocessing")
  .usage("(none|simple|full)")
  .description("Postprocessing of the program found by STOKE (simple removes nops and unreachable blocks, and full additionally removes redundant statements without side-effects)")
  .default_val(Postprocessing::FULL);

auto& no_progress_update_arg =
  cpputil::FlagArg::create("no_progress_update")
  .description("Don't show a progress update whenever a new best program is discovered");

void send_string(int client, string message){
    int data_length = message.size();

    // Send the length buffer and then the data
    send(client, &data_length, sizeof(int), 0);
    send(client, message.c_str(), data_length, 0);

}

int interaction(int client, int cost, SearchStateGadget& state, CostFunctionGadget& fxn) {
    int restart;
    int instruction_index;
    int instruction_length;
    recv(client, &restart, sizeof(restart), 0);
    recv(client, &instruction_index, sizeof(instruction_index), 0);
    recv(client, &instruction_length, sizeof(instruction_length), 0);
    char buffer[instruction_length];
    recv(client, buffer, instruction_length, 0);

    
    string instruction_string(buffer, instruction_length);
    auto undo_instruction = state.current.get_code()[instruction_index];
    auto instruction = state.current.get_code()[instruction_index];
    std::istringstream inputStringStream(instruction_string);
    instruction.read_att(inputStringStream);
    bool valid_instruction_string = ! (undo_instruction == instruction);
    //cout << "undo_instruction : " << undo_instruction << endl;
    //cout << "instruction : " << instruction << endl;
    //cout << "same test : " << valid_instruction_string << endl;
    auto valid_instruction = instruction.check();
    valid_instruction = valid_instruction && valid_instruction_string ;
    bool valid_assembly = false;
    if (valid_instruction){
        state.current.get_function().replace(instruction_index, instruction, false, true);
        state.current.recompute_defs();
        //valid_assembly = state.current.check_invariants();

        auto cost_ = fxn(client, state.current, cost);
        cost = cost_.second;
    } else{
      send_string(client, "invalid instruction");
    }
    bool valid = valid_instruction ;

    assert(state.current.invariant_no_undef_reads());
    assert(state.current.get_function().check_invariants());
    auto cfg_code = state.current.get_code();
    std::ostringstream code;
    code << cfg_code;
    std::string cfg_code_string = code.str();
    int cfg_data_length = cfg_code_string.size();
    send(client, &cfg_data_length, sizeof(int), 0);
    send(client, cfg_code_string.c_str(), cfg_data_length, 0);

    
    send(client, &cost, sizeof(int), 0);
    send(client, &valid, sizeof(bool), 0);
    return cost;
}

void sep(ostream& os, string c = "*") {
  for (size_t i = 0; i < 80; ++i) {
    os << c;
  }
  os << endl << endl;
}

static Cost lowest_cost = 0;
static Cost lowest_correct = 0;
static Cost starting_cost = 0;

void show_state(const SearchState& state, ostream& os) {
  ofilterstream<Column> ofs(os);
  ofs.filter().padding(5);

  auto best_yet = state.best_yet;
  CfgTransforms::remove_unreachable(best_yet);
  CfgTransforms::remove_nop(best_yet);

  lowest_cost = state.best_yet_cost;
  ofs << "Lowest Cost Discovered (" << state.best_yet_cost << ")" << endl;
  ofs << endl;
  ofs << best_yet.get_code();
  ofs.filter().next();

  auto best_correct = state.best_correct;
  CfgTransforms::remove_unreachable(best_correct);
  CfgTransforms::remove_nop(best_correct);

  lowest_correct = state.best_correct_cost;
  ofs << "Lowest Known Correct Cost (" << state.best_correct_cost << ")" << endl;
  ofs << endl;
  ofs << best_correct.get_code();
  ofs.filter().done();
}

void pcb(const ProgressCallbackData& data, void* arg) {
  ostream& os = *((ostream*)arg);

  os << "Progress Update: " << endl;
  os << endl;

  show_state(data.state, os);

  os << endl << endl;
  sep(os);
}

struct ScbArg {
  ostream* os;
  uint32_t** cost_stats;
};

void show_statistics(const StatisticsCallbackData& data, ostream& os) {
  os << "Iterations:                    " << data.iterations << endl;
  os << "Elapsed Time:                  " << data.elapsed.count() << "s" << endl;
  os << "Iterations/s:                  " << (data.iterations / data.elapsed.count()) << endl;
  os << endl;
  os << "Starting cost:                 " << starting_cost << endl;
  os << "Lowest cost:                   " << lowest_cost << endl;
  os << "Lowest correct cost:           " << lowest_correct << endl;
  os << endl;


  ofilterstream<Column> ofs(os);
  ofs.filter().padding(5);

  const WeightedTransform* transform = static_cast<const WeightedTransform*>(data.transform);

  Statistics total;
  for (size_t i = 0; i < transform->size(); ++i) {
    total += data.move_statistics[i];
  }

  ofs << "Move Type" << endl;
  ofs << endl;
  for (size_t i = 0; i < transform->size(); ++i) {
    ofs << transform->get_transform(i)->get_name() << endl;
  }
  ofs << endl;
  ofs << "Total";
  ofs.filter().next();

  ofs << "Proposed" << endl;
  ofs << endl;
  for (size_t i = 0; i < transform->size(); ++i) {
    ofs << 100 * (double)data.move_statistics[i].num_proposed / data.iterations << "%" << endl;
  }
  ofs << endl;
  ofs << 100 * (double)total.num_proposed / data.iterations << "%";
  ofs.filter().next();

  ofs << "Succeeded" << endl;
  ofs << endl;
  for (size_t i = 0; i < transform->size(); ++i) {
    ofs << 100 * (double)data.move_statistics[i].num_succeeded / data.iterations << "%" << endl;
  }
  ofs << endl;
  ofs << 100 * (double)total.num_succeeded / data.iterations << "%";
  ofs.filter().next();

  ofs << "Accepted" << endl;
  ofs << endl;
  for (size_t i = 0; i < transform->size(); ++i) {
    ofs << 100 * (double)data.move_statistics[i].num_accepted / data.iterations << "%" << endl;
  }
  ofs << endl;
  ofs << 100 * (double)total.num_accepted / data.iterations << "%";
  ofs.filter().done();
}

void scb(const StatisticsCallbackData& data, void* arg) {
  ScbArg sa = *((ScbArg*)arg);
  ostream& os = *(sa.os);
  uint32_t** cost_stats = sa.cost_stats;

  os << "Statistics Update: " << endl;
  os << endl;
  show_statistics(data, os);

  os << endl << endl;
  sep(os);
}

void show_final_update(const StatisticsCallbackData& stats, SearchState& state,
                       size_t total_restarts,
                       size_t total_iterations, time_point<steady_clock> start,
                       duration<double> search_elapsed,
                       bool verified,
                       bool timeout) {
  auto total_elapsed = duration_cast<duration<double>>(steady_clock::now() - start);
  sep(Console::msg(), "#");
  Console::msg() << "Final update:" << endl << endl;
  Console::msg() << "Total search iterations:       " << total_iterations << endl;
  Console::msg() << "Number of attempted searches:  " << total_restarts << endl;
  Console::msg() << "Total search time:             " << search_elapsed.count() << "s" << endl;
  Console::msg() << "Total time:                    " << total_elapsed.count() << "s" << endl;
  Console::msg() << endl << "Statistics of last search" << endl << endl;
  // get the state first (because it updates some static variables)
  ostringstream stream;
  show_state(state, stream);
  show_statistics(stats, Console::msg());
  Console::msg() << endl << endl;
  Console::msg() << stream.str();
  Console::msg() << endl << endl;
  sep(Console::msg(), "#");

  // output machine-readable result
  if (machine_output_arg.has_been_provided()) {
    auto code_to_string = [](x64asm::Code code) {
      stringstream ss;
      ss << code;
      auto res = regex_replace(ss.str(), regex("\n"), "\\n");
      return res;
    };

    ofstream f;
    f.open(machine_output_arg.value());
    f << "{" << endl;
    f << "  \"success\": " << (state.success ? "true" : "false") << "," << endl;
    f << "  \"interrupted\": " << (state.interrupted ? "true" : "false") << "," << endl;
    f << "  \"timeout\": " << (timeout ? "true" : "false") << "," << endl;
    f << "  \"verified\": " << (verified ? "true" : "false") << "," << endl;
    f << "  \"statistics\": {" << endl;
    f << "    \"total_iterations\": " << total_iterations << "," << endl;
    f << "    \"total_attempted_searches\": " << total_restarts << "," << endl;
    f << "    \"total_search_time\": " << search_elapsed.count() << "," << endl;
    f << "    \"total_time\": " << total_elapsed.count() << endl;
    f << "  }," << endl;
    f << "  \"best_yet\": {" << endl;
    f << "    \"cost\": " << state.best_yet_cost << "," << endl;
    f << "    \"code\": \"" << code_to_string(state.best_yet.get_code()) << "\"" << endl;
    f << "  }," << endl;
    f << "  \"best_correct\": {" << endl;
    f << "    \"cost\": " << state.best_correct_cost << "," << endl;
    f << "    \"code\": \"" << code_to_string(state.best_correct.get_code()) << "\"" << endl;
    f << "  }" << endl;
    f << "}" << endl;
    f.close();
  }
}

void new_best_correct_callback(const NewBestCorrectCallbackData& data, void* arg) {

  if (results_arg.has_been_provided()) {
    Console::msg() << "Verifying improved rewrite..." << endl;

    auto state = data.state;
    auto data = (pair<VerifierGadget&, TargetGadget&>*)arg;
    auto verifier = data->first;
    auto target = data->second;

    // perform the postprocessing
    Cfg res(state.current);
    if (postprocessing_arg == Postprocessing::FULL) {
      CfgTransforms::remove_redundant(res);
      CfgTransforms::remove_unreachable(res);
      CfgTransforms::remove_nop(res);
    } else if (postprocessing_arg == Postprocessing::SIMPLE) {
      CfgTransforms::remove_unreachable(res);
      CfgTransforms::remove_nop(res);
    } else {
      // Do nothing.
    }

    // verify the new best correct rewrite
    const auto verified = verifier.verify(target, res);

    if (verifier.has_error()) {
      Console::msg() << "The verifier encountered an error: " << verifier.error() << endl << endl;
    }

    // save to file if verified
    if (verified) {
      Console::msg() << "Verified!  Saving result..." << endl << endl;
      // next name for result file
      string name = "";
      bool done = false;
      do {
        name = results_arg.value() + "/result-" + to_string(state.last_result_id) + ".s";
        state.last_result_id += 1;
        ifstream f(name.c_str());
        done = !f.good();
      } while (!done);

      // write output
      ofstream outfile;
      outfile.open(name);
      outfile << res.get_function();
      outfile.close();
    } else {
      Console::msg() << "Verification failed."  << endl << endl;
      if (verifier.counter_examples_available()) {
        Console::msg() << "Counterexample: " << endl;
        for (auto it : verifier.get_counter_examples()) {
          Console::msg() << it << endl;
        }
      }
    }

  } else {
    cout << "No action on new best correct" << endl;

  }

}

vector<string>& split(string& s, const string& delim, vector<string>& result) {
  auto pos = string::npos;
  while ((pos = s.find(delim)) != string::npos) {
    result.push_back(s.substr(0, pos));
    s.erase(0, pos + delim.length());
  }
  result.push_back(s);
  return result;
}

int main(int argc, char** argv) {
  int client;
  int portnum = std::stoi(argv[6]);
  
  argc -= 2; 
  const char* ip = "127.0.0.1";
  
  struct sockaddr_in serv_addr;

  client = socket(AF_INET, SOCK_STREAM, 0);
  if (client < 0) {
    cout << "ERROR establishing socket\n" << endl;
    exit(1);
  }

  serv_addr.sin_family = AF_INET;
  serv_addr.sin_port = htons(portnum);
  inet_pton(AF_INET, ip, &serv_addr.sin_addr);

  cout << "\n--> Socket client created...\n";


  if (connect(client, (const struct sockaddr*)&serv_addr, sizeof(serv_addr)) == 0) {
    cout << "--> Connection to the server " << inet_ntoa(serv_addr.sin_addr) 
	<< " with port number: " 
	<< portnum << endl;		 
  }


  cout << "--> Waiting for server to confirm...\n";
  // recv(client, buffer, bufsize, 0);
  cout << "--> Connection confirmed..\n";
  
  
  const auto start = steady_clock::now();
  duration<double> search_elapsed = duration<double>(0.0);

  CommandLineConfig::strict_with_convenience(argc, argv);
  DebugHandler::install_sigsegv();
  DebugHandler::install_sigill();

  // create results dir if necessary
  if (results_arg.has_been_provided()) {
    fs::path result_dir(results_arg.value());
    if (!fs::is_directory(result_dir)) {
      fs::create_directories(result_dir);
    }
  }

  SeedGadget seed;
  FunctionsGadget aux_fxns;
  TargetGadget target(aux_fxns, init_arg == Init::ZERO);

  TrainingSetGadget training_set(seed);
  SandboxGadget training_sb(training_set, aux_fxns);

  TransformPoolsGadget transform_pools(target, aux_fxns, seed);
  WeightedTransformGadget transform(transform_pools, seed);
  SearchGadget search(&transform, seed);

  TestSetGadget test_set(seed);
  SandboxGadget test_sb(test_set, aux_fxns);

  PerformanceSetGadget perf_set(seed);
  SandboxGadget perf_sb(perf_set, aux_fxns);

  CorrectnessCostGadget holdout_fxn(target, &test_sb);
  VerifierGadget verifier(test_sb, holdout_fxn);

  ScbArg scb_arg {&Console::msg(), nullptr};
  search.set_statistics_callback(scb, &scb_arg)
  .set_statistics_interval(stat_int);
  if (!no_progress_update_arg.value()) {
    search.set_progress_callback(pcb, &Console::msg());
  }
  auto nbcc_data = pair<VerifierGadget&, TargetGadget&>(verifier, target);
  search.set_new_best_correct_callback(new_best_correct_callback, &nbcc_data);

  size_t total_iterations = 0;
  size_t total_restarts = 0;

  // attempt to parse cycle_timeout argument
  vector<string> parts;
  vector<Expr<size_t>*> cycle_timeouts;
  for (auto& part : split(cycle_timeout_arg.value(), ",", parts)) {
    function<bool (const string&)> f = [](const string& s) -> bool { return s == "i"; };
    auto parser = ExprParser<size_t>(part, f);
    if (parser.has_error()) {
      Console::error() << "Error parsing cycle timeout expression '" << part << "': " << parser.get_error() << endl;
    }
    cycle_timeouts.push_back(parser.get());
  }

  if (strategy_arg.value() == "none" &&
      failed_verification_action.value() == FailedVerificationAction::ADD_COUNTEREXAMPLE) {
    Console::error() << "No verification is performed, thus no counterexample can be added (--failed_verification_action add_counterexample and --strategy none are not compatible)." << endl;
  }

  string final_msg;
  SearchStateGadget state(target, aux_fxns);
  CostFunctionGadget fxn(target, &training_sb, &perf_sb);

  //////////////////////////send initial cpu state///////////////////////////
  std::ifstream inputFile("/home/stoke/stoke/examples/hacker/p01/test.tc"); ///need to get from server

  // Check if the file is open
  if (!inputFile.is_open()) {
      std::cerr << "Error opening file!" << std::endl;
      return 1;
  }

  // Variable to store the contents of the file
  std::string fileContents((std::istreambuf_iterator<char>(inputFile)),
                          std::istreambuf_iterator<char>());

  // Read the file and append each line to the variable
  std::string line;
  while (std::getline(inputFile, line)) {
      fileContents += line + "\n";  // Add newline character for each line
  }

  // Close the file
  inputFile.close();
  send_string(client, fileContents);
  //////////////////////////send initial cpu state///////////////////////////
  //////////////////////////send target cpu state///////////////////////////
  CorrectnessCostGadget holdout_fxn1(target, &training_sb);
  holdout_fxn1.set_target(client, target, stack_out_arg, heap_out_arg);
  //////////////////////////send target cpu state///////////////////////////
  state = SearchStateGadget(target, aux_fxns);
  
  int cost = 100000;
  int valid = 1;
  auto cost_ = fxn(client, state.current, cost);
  cost = cost_.second;
  
  auto cfg_code = state.current.get_code();
  std::ostringstream code;
  code << cfg_code;
  std::string cfg_code_string = code.str();
  int cfg_data_length = cfg_code_string.size();
  send(client, &cfg_data_length, sizeof(int), 0);
  send(client, cfg_code_string.c_str(), cfg_data_length, 0);
  send(client, &cost, sizeof(int), 0);
  send(client, &valid, sizeof(bool), 0);
  
  while (cost > 0){
    cost = interaction(client, cost, state, fxn);
  }

  const auto verified = verifier.verify(target, state.best_correct);
  if (verifier.has_error()) {
    Console::msg() << "The verifier encountered an error:" << endl;
    Console::msg() << verifier.error() << endl;
  }
  if (!verified){
      Console::msg() << "Unable to verify new rewrite..." << endl << endl;
  }
  if (postprocessing_arg == Postprocessing::FULL) {
    CfgTransforms::remove_redundant(state.current);
    CfgTransforms::remove_unreachable(state.current);
    CfgTransforms::remove_nop(state.current);
  } else if (postprocessing_arg == Postprocessing::SIMPLE) {
    CfgTransforms::remove_unreachable(state.current);
    CfgTransforms::remove_nop(state.current);
  } else {
    // Do nothing.
  }
  cout << "result : " << state.current.get_code() << endl;
  cout << "verified! : " << verified << endl;
  /*
      for (size_t i = 0; ; ++i) {

        // Run the initial cost function
        
        
        const auto verified = verifier.verify(target, state.best_correct);

        if (verifier.has_error()) {
          Console::msg() << "The verifier encountered an error:" << endl;
          Console::msg() << verifier.error() << endl;
        }
        if (!verified){
            Console::msg() << "Unable to verify new rewrite..." << endl << endl;
        }
        
        sep(Console::msg());



      if (postprocessing_arg == Postprocessing::FULL) {
        CfgTransforms::remove_redundant(state.best_correct);
        CfgTransforms::remove_unreachable(state.best_correct);
        CfgTransforms::remove_nop(state.best_correct);
      } else if (postprocessing_arg == Postprocessing::SIMPLE) {
        CfgTransforms::remove_unreachable(state.best_correct);
        CfgTransforms::remove_nop(state.best_correct);
      } else {
        // Do nothing.
      }
      ofstream ofs(out.value());
      ofs << state.best_correct.get_function();
      //reset end

        
        


  }
  */
  return 0;
}