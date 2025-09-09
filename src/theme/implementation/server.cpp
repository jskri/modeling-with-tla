#include <algorithm>
#include <chrono>
#include <iostream>
#include <sstream>
#include <stdexcept>
#include <string_view>
#include <thread>
#include <zmqpp/zmqpp.hpp>
#include "common.hpp"

// This is an implementation of Theme3!Server2 (see `ThemeServer2.tla`),
// including the environment fragment (company adds a pack):
//
// spec: Theme3!Server2!Spec

// spec: `request` and `reply` are represented in the underlying messaging
// system, and so are not explicitly present in the following code.

using namespace theme;

struct State {
  std::set<Pack> packs;
  std::set<Pack> unsentPacks;
};

auto logState(std::string_view event, State const& state, std::optional<Pack> optPack = {}) -> void {
  std::cout << timestamp()
            << ":" << event
            << ":packs=" << state.packs
            << ":unsentPacks=" << state.unsentPacks;
  if (event == "ServerHandlesListRequest") {
    auto ss = std::ostringstream();
    logSet(state.unsentPacks, ss, [](auto const& pack) {return pack.id;});
    std::cout << ":ids=" << ss.str();
  } else if (event == "ServerHandlesGetRequest" && optPack.has_value()) {
    auto const& p = optPack.value();
    std::cout << ":pack=<<" << p.id << ",\"" << p.data << "\"," << p.version << ">>";
  }
  std::cout << std::endl;
}

// spec: Theme3!Server2!ServerHandlesListRequest
auto handleListRequest(Socket& socket, State const& state) -> void {
  // spec: reply' = [op |-> "list", ids |-> {PackId[p] : p \in unsentPacks}]
  auto msg = Message{};
  msg << MessageType::List;
  for (auto const& pack: state.unsentPacks) msg << pack.id;
  logState("ServerHandlesListRequest", state);
  socket.send(msg);
}

// spec: Theme3!Server2!ServerHandlesGetRequest
auto handleGetRequest(Socket& socket, Id id, State& state) -> void {
  // spec: \E p \in unsentPacks : PackId[p] = request.id
  auto it = std::ranges::find_if(state.unsentPacks, [id](auto const& pack) { return pack.id == id; });
  if (it == state.unsentPacks.end()) {
    std::cerr << "Id " << id << " not found in unsent packs. Request ignored.\n";
    return;
  }
  // spec: reply' = [op |-> "get", pack |-> p]
  auto msg = Message{};
  msg << MessageType::Get << it->id << it->data << it->version;
  // spec: packs' = packs \union {p}
  auto [it2, _] = state.packs.insert(*std::move(it));
  // spec: unsentPacks' = unsentPacks \ {p}
  state.unsentPacks.erase(it);
  logState("ServerHandlesGetRequest", state, *it2);
  socket.send(msg);
}

auto checkAddedPacks(std::string_view packFilePath, State& state) -> void {
  auto packs = readPacks(packFilePath, state.packs);
  if (packs.empty()) return;
  // spec: Theme3!Server2!CompanyAddsAPack
  // note: `p \notin (packs \union unsentPacks)` is not taken into account.
  state.unsentPacks.merge(std::move(packs));
  logState("CompanyAddsAPack", state); 
}

auto main(int argc, char* argv[]) -> int {
  if (argc != 4) {
    std::cerr << "Usage: " << argv[0] << " <initial_pack_file> <pack_file> <bind_endpoint>\n";
    return EXIT_FAILURE;
  }
  auto initialPackFilePath = std::string_view(argv[1]);
  auto packFilePath = std::string_view(argv[2]);
  auto bindEndpoint = Endpoint{argv[3]};
  auto context = Context{};
  auto socket = Socket{context, SocketType::reply};
  socket.bind(bindEndpoint);
  auto packs = std::set<Pack>{};
  auto unsentPacks = std::set<Pack>{};
  auto msg = Message{};
  auto msgType = MessageType{};
  auto state = State{};
  state.packs = readPacks(initialPackFilePath, state.packs);
  while (true) {
    checkAddedPacks(packFilePath, state);
    socket.receive(msg);
    msg >> (uint8_t&)msgType;
    switch (msgType) {
    case MessageType::List:
      // spec: Theme3!Server2!ServerHandlesListRequest: request \in [op : {"list"}]
      handleListRequest(socket, state);
      break;
    case MessageType::Get: {
      // spec: Theme3!Server2!ServerHandlesGetRequest: request \in [op : {"get"}, id : Id]
      auto id = Id{};
      msg >> id;  
      handleGetRequest(socket, id, state);
      break;
    }
    default:
      std::cerr << "Unknown request type: " << msgType << ". Request ignored.\n";
    }
    std::this_thread::sleep_for(sleep_time());
  }
  return EXIT_SUCCESS;
}
